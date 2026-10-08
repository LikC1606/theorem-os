import fs from 'node:fs';
import path from 'node:path';
import { createHash, randomUUID } from 'node:crypto';
import { spawnSync } from 'node:child_process';
import { z } from 'zod';
import { isolationContains, readMathModelIsolationPolicy, type MathModelIsolationPolicy } from "./mathModelIsolation";
import { canonicalMathJson } from "./mathRuntimeIo";

const hash = z.string().regex(/^[a-f0-9]{64}$/u);
const identifier = z.string().regex(/^[a-zA-Z0-9_-]{1,128}$/u);
const namespace = z.string().regex(/^[a-z]+:\[[0-9]+\]$/u);
const processIdentitySchema = z
  .object({ pid: z.number().int().positive(), startTimeTicks: z.string().regex(/^[0-9]+$/u) })
  .strict();
const bindingSchema = z
  .object({
    schema: z.literal('deepscientist.math.model-isolation-run.v1'),
    runId: z.string().min(1).max(256),
    runNonce: z.string().uuid(),
    policyDigest: hash,
    workspace: z.string(),
    registeredAt: z.string().datetime(),
    conversationIds: z.array(identifier).min(1),
  })
  .strict();
export type MathModelIsolationRun = z.infer<typeof bindingSchema>;
const registrationSchema = bindingSchema
  .omit({ schema: true, conversationIds: true })
  .extend({
    schema: z.literal('deepscientist.math.model-isolation-registration.v1'),
    conversationId: identifier,
    status: z.enum(['active', 'sealed']),
  })
  .strict();
const receiptSchema = z
  .object({
    schema: z.literal('deepscientist.math.model-isolation-receipt.v1'),
    conversationId: identifier,
    instanceId: z.string().uuid(),
    runId: z.string(),
    runNonce: z.string().uuid(),
    policyDigest: hash,
    workspace: z.string(),
    startedAt: z.string().datetime(),
    finishedAt: z.string().datetime().optional(),
    status: z.enum(['starting', 'running', 'closed', 'failed']),
    supervisor: processIdentitySchema,
    sandbox: processIdentitySchema.nullable(),
    namespaceProcess: processIdentitySchema.nullable(),
    namespaces: z
      .object({ mnt: namespace, pid: namespace, net: namespace, user: namespace, ipc: namespace, uts: namespace })
      .strict()
      .nullable(),
    mcpServers: z.array(z.string()),
    enforcement: z.literal('linux-bwrap'),
    model: z.string().min(1).max(128),
    provider: z.string().min(1).max(128),
  })
  .strict();
type Receipt = z.infer<typeof receiptSchema>;
const terminationSchema = z
  .object({
    schema: z.literal('deepscientist.math.model-isolation-termination.v1'),
    binding: bindingSchema,
    checkedAt: z.string().datetime(),
    /** Registered slots that were never launched before this run stopped. */
    unstartedConversationIds: z.array(identifier).optional(),
    receipts: z
      .array(
        z
          .object({
            path: z.string(),
            sha256: hash,
            conversationId: identifier,
            instanceId: z.string().uuid(),
            termination: z.enum(['launcher_closed', 'host_confirmed_stopped']),
            supervisor: processIdentitySchema,
            sandbox: processIdentitySchema,
            namespaceProcess: processIdentitySchema,
          })
          .strict()
      )
      .min(1),
  })
  .strict();

function digestBytes(bytes: string | Buffer): string {
  return createHash('sha256').update(bytes).digest('hex');
}
function readPrivateJson(file: string, limit = 65536): { bytes: Buffer; value: unknown } {
  const stat = fs.lstatSync(file);
  if (
    !stat.isFile() ||
    stat.nlink !== 1 ||
    stat.size > limit ||
    (stat.mode & 0o077) !== 0 ||
    stat.uid !== process.getuid?.()
  )
    throw new Error('math_isolation_evidence_file_invalid');
  const bytes = fs.readFileSync(file);
  return { bytes, value: JSON.parse(bytes.toString('utf8')) };
}
function privateDirectory(directory: string) {
  fs.mkdirSync(directory, { recursive: true, mode: 0o700 });
  const stat = fs.lstatSync(directory);
  if (!stat.isDirectory() || (stat.mode & 0o077) !== 0 || fs.realpathSync(directory) !== directory)
    throw new Error('math_isolation_evidence_directory_invalid');
}
function writePrivateJson(file: string, value: unknown) {
  const temporary = `${file}.${randomUUID()}.tmp`;
  const fd = fs.openSync(temporary, 'wx', 0o600);
  try {
    fs.writeFileSync(fd, `${canonicalMathJson(value)}\n`);
    fs.fsyncSync(fd);
  } finally {
    fs.closeSync(fd);
  }
  fs.renameSync(temporary, file);
}
function restorePrivateBytes(file: string, bytes: Buffer | undefined) {
  if (bytes === undefined) {
    fs.rmSync(file, { force: true });
    return;
  }
  const temporary = `${file}.${randomUUID()}.tmp`;
  fs.writeFileSync(temporary, bytes, { mode: 0o600, flag: 'wx' });
  fs.renameSync(temporary, file);
}
function registrationFor(binding: MathModelIsolationRun, conversationId: string, status: 'active' | 'sealed') {
  const { schema: _schema, conversationIds: _conversations, ...identity } = binding;
  return { schema: 'deepscientist.math.model-isolation-registration.v1' as const, ...identity, conversationId, status };
}
function checkBinding(
  binding: MathModelIsolationRun,
  input: { expectedDigest: string; workspace: string; conversationIds: readonly string[]; runId: string }
) {
  if (
    binding.policyDigest !== input.expectedDigest ||
    binding.workspace !== input.workspace ||
    binding.runId !== input.runId ||
    canonicalMathJson(binding.conversationIds) !== canonicalMathJson([...new Set(input.conversationIds)].toSorted())
  )
    throw new Error('math_isolation_evidence_binding_mismatch');
}

export function verifyMathModelIsolationCore(input: {
  policyFile: string;
  coreCapabilities: unknown;
  launcher: string;
  workspace: string;
  models?: readonly string[];
}) {
  verifyMathModelIsolationHost();
  const { policy, digest } = readMathModelIsolationPolicy(input.policyFile);
  const capability = z
    .object({
      runtime_process_id: z.number().int().positive(),
      math_acp_isolation: z.object({ enabled: z.literal(true), protocol_version: z.literal(1) }),
    })
    .parse(input.coreCapabilities);
  if (!policy.workspaces.includes(input.workspace) || policy.launcher !== input.launcher)
    throw new Error('math_isolation_core_policy_mismatch');
  if (input.models?.some((model) => model !== (policy.model ?? 'deepseek')))
    throw new Error('math_isolation_model_policy_mismatch');
  const environment = fs.readFileSync(`/proc/${capability.runtime_process_id}/environ`, 'utf8').split('\0');
  for (const [key, value] of Object.entries({
    DEEPSCIENTIST_MATH_ACP_ISOLATION_POLICY: input.policyFile,
    DEEPSCIENTIST_MATH_ACP_ISOLATION_LAUNCHER: input.launcher,
    DEEPSCIENTIST_MATH_ACP_ISOLATION_NODE: policy.nodeExecutable,
  }))
    if (!environment.includes(`${key}=${value}`)) throw new Error('math_isolation_core_environment_mismatch');
  return { policy, digest };
}

export function verifyMathModelIsolationHost(): void {
  if (process.platform !== 'linux') throw new Error('math_isolation_platform_unsupported');
  const bwrap = '/usr/bin/bwrap';
  let sandboxCheck;
  try {
    const stat = fs.lstatSync(bwrap);
    sandboxCheck =
      stat.isFile() && (stat.mode & 0o111) !== 0
        ? spawnSync(bwrap, ['--unshare-all', '--die-with-parent', '--ro-bind', '/', '/', '--', 'true'], {
            encoding: 'utf8',
            timeout: 5000,
            stdio: ['ignore', 'ignore', 'ignore'],
          })
        : undefined;
  } catch {
    sandboxCheck = undefined;
  }
  if (!sandboxCheck || sandboxCheck.error || sandboxCheck.status !== 0)
    throw new Error('math_isolation_sandbox_unavailable');
}

/** Register every conversation before Core is allowed to start an ACP process. */
export function registerMathModelIsolationRun(input: {
  policyFile: string;
  expectedDigest: string;
  workspace: string;
  conversationIds: readonly string[];
  runId: string;
  retained?: unknown;
}): MathModelIsolationRun {
  const { policy, digest } = readMathModelIsolationPolicy(input.policyFile);
  if (digest !== input.expectedDigest || !policy.workspaces.includes(input.workspace) || !input.conversationIds.length)
    throw new Error('math_isolation_evidence_binding_mismatch');
  const directory = path.join(policy.stateDirectory, 'registrations');
  privateDirectory(directory);
  let binding = input.retained === undefined ? undefined : bindingSchema.parse(input.retained);
  if (binding) {
    checkBinding(binding, input);
    const registrations = binding.conversationIds.map((id) =>
      registrationSchema.parse(readPrivateJson(path.join(directory, `${id}.json`)).value)
    );
    if (
      registrations.some(
        (record) =>
          canonicalMathJson(record) !==
          canonicalMathJson(registrationFor(binding!, record.conversationId, record.status))
      )
    )
      throw new Error('math_isolation_registration_mismatch');
    if (registrations.every((record) => record.status === 'active')) return binding;
    if (!registrations.every((record) => record.status === 'sealed'))
      throw new Error('math_isolation_registration_mismatch');
    // A completed attempt never lends its receipts to a later resumed attempt.
    binding = undefined;
  }
  binding = bindingSchema.parse({
    schema: 'deepscientist.math.model-isolation-run.v1',
    runId: input.runId,
    runNonce: randomUUID(),
    policyDigest: digest,
    workspace: input.workspace,
    registeredAt: new Date().toISOString(),
    conversationIds: [...new Set(input.conversationIds)].toSorted(),
  });
  const snapshots = new Map<string, Buffer | undefined>();
  try {
    // Validate every existing registration before changing any file. This keeps
    // a mixed active/sealed set from leaving a partially-created run behind.
    for (const id of binding.conversationIds) {
      const file = path.join(directory, `${id}.json`);
      if (!fs.existsSync(file)) {
        snapshots.set(file, undefined);
        continue;
      }
      const prior = readPrivateJson(file);
      snapshots.set(file, prior.bytes);
      const registration = registrationSchema.parse(prior.value);
      if (registration.status !== 'sealed' || input.retained === undefined)
        throw new Error('math_isolation_registration_already_exists');
    }
    for (const id of binding.conversationIds)
      writePrivateJson(path.join(directory, `${id}.json`), registrationFor(binding, id, 'active'));
  } catch (error) {
    for (const [file, bytes] of snapshots) {
      try {
        restorePrivateBytes(file, bytes);
      } catch {
        // Preserve the original registration error; the next read will fail
        // closed if a rollback itself cannot be completed.
      }
    }
    throw error;
  }
  return binding;
}

export function sealMathModelIsolationRun(input: { policyFile: string; binding: MathModelIsolationRun }): void {
  const binding = bindingSchema.parse(input.binding);
  const { policy, digest } = readMathModelIsolationPolicy(input.policyFile);
  if (digest !== binding.policyDigest) throw new Error('math_isolation_evidence_binding_mismatch');
  for (const id of binding.conversationIds) {
    const file = path.join(policy.stateDirectory, 'registrations', `${id}.json`);
    const registration = registrationSchema.parse(readPrivateJson(file).value);
    if (canonicalMathJson(registration) !== canonicalMathJson(registrationFor(binding, id, registration.status)))
      throw new Error('math_isolation_registration_mismatch');
    writePrivateJson(file, registrationFor(binding, id, 'sealed'));
  }
}

/**
 * Core can replace a Worker process while it is still starting (TeamMcpRebuild
 * killed one 0.8 s after spawn in run 23). That instance closed inside a real
 * sandbox but never opened an MCP session or sent a single provider request,
 * yet its empty mcpServers made the whole run's evidence invalid. Only such an
 * aborted launch is tolerated: any provider traffic or prompt from the instance
 * still requires complete evidence.
 */
function isAbortedLaunch(stateDirectory: string, record: Receipt): boolean {
  if (
    (record.status !== 'closed' && record.status !== 'failed') ||
    record.mcpServers.length ||
    !record.sandbox ||
    !record.namespaces ||
    !record.finishedAt ||
    Date.parse(record.finishedAt) < Date.parse(record.startedAt)
  )
    return false;
  const stem = path.join(stateDirectory, `${record.conversationId}-${record.instanceId}`);
  for (const suffix of ['.requests.jsonl', '.protocol.jsonl']) {
    const stat = fs.lstatSync(`${stem}${suffix}`, { throwIfNoEntry: false });
    if (stat && (!stat.isFile() || stat.size > 0)) return false;
  }
  return true;
}

function readRunReceipts(
  policy: MathModelIsolationPolicy,
  binding: MathModelIsolationRun,
  options: { requireComplete?: boolean; unstartedConversationIds?: readonly string[] } = {}
) {
  const { stateDirectory } = policy;
  const receipts: { path: string; sha256: string; record: Receipt }[] = [];
  const covered = new Set<string>();
  for (const name of fs.readdirSync(stateDirectory)) {
    if (!name.endsWith('.json') || !binding.conversationIds.some((id) => name.startsWith(`${id}-`))) continue;
    const file = path.join(stateDirectory, name);
    const { bytes, value } = readPrivateJson(file, 16384);
    const record = receiptSchema.parse(value);
    if (record.runNonce !== binding.runNonce) continue;
    if (
      record.runId !== binding.runId ||
      record.policyDigest !== binding.policyDigest ||
      record.model !== (policy.model ?? 'deepseek') ||
      record.provider !== (policy.provider ?? 'WestlakeHPC') ||
      !binding.conversationIds.includes(record.conversationId) ||
      name !== `${record.conversationId}-${record.instanceId}.json` ||
      !isolationContains(binding.workspace, record.workspace) ||
      Date.parse(record.startedAt) < Date.parse(binding.registeredAt)
    )
      throw new Error('math_isolation_evidence_identity_mismatch');
    if (options.requireComplete !== false && isAbortedLaunch(stateDirectory, record)) {
      // Recorded, but it cannot stand in for the conversation's real instance.
      receipts.push({ path: file, sha256: digestBytes(bytes), record });
      continue;
    }
    if (
      options.requireComplete !== false &&
      (record.status === 'failed' ||
        record.status === 'starting' ||
        !record.namespaces ||
        !record.sandbox ||
        !record.namespaceProcess ||
        !record.mcpServers.length ||
        (record.status === 'closed' &&
          (!record.finishedAt || Date.parse(record.finishedAt) < Date.parse(record.startedAt))))
    )
      throw new Error('math_isolation_evidence_incomplete');
    covered.add(record.conversationId);
    receipts.push({ path: file, sha256: digestBytes(bytes), record });
  }
  const unstarted = new Set(options.unstartedConversationIds ?? []);
  if (
    unstarted.size !== (options.unstartedConversationIds?.length ?? 0) ||
    [...unstarted].some(
      (id) => !binding.conversationIds.includes(id) || receipts.some(({ record }) => record.conversationId === id)
    )
  )
    throw new Error('math_isolation_instance_set_changed');
  if (options.requireComplete !== false && covered.size + unstarted.size !== binding.conversationIds.length)
    throw new Error('math_isolation_evidence_missing');
  return receipts.toSorted((a, b) => a.path.localeCompare(b.path));
}

type ProcessIdentity = z.infer<typeof processIdentitySchema>;
/** PID reuse is distinguished using the kernel's process start time. */
type ProcessSnapshot = ProcessIdentity & { ppid: number; state: string };
function readProcessSnapshot(pid: number): ProcessSnapshot | undefined {
  let stat: string;
  try {
    stat = fs.readFileSync(`/proc/${pid}/stat`, 'utf8');
  } catch (error) {
    if ((error as NodeJS.ErrnoException).code === 'ENOENT' || (error as NodeJS.ErrnoException).code === 'ESRCH')
      return undefined;
    throw new Error('math_isolation_process_observation_unavailable', { cause: error });
  }
  const fields = stat
    .slice(stat.lastIndexOf(')') + 2)
    .trim()
    .split(/\s+/u);
  if (fields.length < 20 || !/^[0-9]+$/u.test(fields[19]))
    throw new Error('math_isolation_process_observation_invalid');
  if (!/^\d+$/u.test(fields[1])) throw new Error('math_isolation_process_observation_invalid');
  return { pid, ppid: Number(fields[1]), state: fields[0], startTimeTicks: fields[19] };
}
function processStillRunning(identity: ProcessIdentity): boolean {
  const snapshot = readProcessSnapshot(identity.pid);
  return Boolean(
    snapshot && snapshot.startTimeTicks === identity.startTimeTicks && !['Z', 'X'].includes(snapshot.state)
  );
}

function readProcessTree(roots: readonly ProcessIdentity[]): ProcessSnapshot[] {
  const snapshots: ProcessSnapshot[] = [];
  for (const name of fs.readdirSync('/proc')) {
    if (!/^\d+$/u.test(name)) continue;
    const snapshot = readProcessSnapshot(Number(name));
    if (snapshot && !['Z', 'X'].includes(snapshot.state)) snapshots.push(snapshot);
  }
  const byParent = new Map<number, ProcessSnapshot[]>();
  for (const snapshot of snapshots) {
    const children = byParent.get(snapshot.ppid) ?? [];
    children.push(snapshot);
    byParent.set(snapshot.ppid, children);
  }
  const owned = new Map<number, ProcessSnapshot>();
  const queue: ProcessSnapshot[] = [];
  for (const root of roots) {
    const snapshot = readProcessSnapshot(root.pid);
    if (!snapshot) continue;
    if (snapshot.startTimeTicks !== root.startTimeTicks) throw new Error('math_isolation_process_identity_changed');
    if (!['Z', 'X'].includes(snapshot.state)) {
      owned.set(snapshot.pid, snapshot);
      queue.push(snapshot);
    }
  }
  while (queue.length) {
    const parent = queue.shift()!;
    for (const child of byParent.get(parent.pid) ?? []) {
      if (owned.has(child.pid)) continue;
      owned.set(child.pid, child);
      queue.push(child);
    }
  }
  return [...owned.values()];
}

function signalProcesses(processes: readonly ProcessIdentity[], signal: NodeJS.Signals): void {
  for (const process of processes) {
    const current = readProcessSnapshot(process.pid);
    if (!current || current.startTimeTicks !== process.startTimeTicks || ['Z', 'X'].includes(current.state)) continue;
    try {
      processKill(process.pid, signal);
    } catch (error) {
      const code = (error as NodeJS.ErrnoException).code;
      if (!['ENOENT', 'ESRCH'].includes(code ?? ''))
        throw new Error('math_isolation_process_cleanup_failed', { cause: error });
    }
  }
}

const processKill = (pid: number, signal: NodeJS.Signals): void => {
  process.kill(pid, signal);
};

function assertRegistrationsSealed(policy: MathModelIsolationPolicy, binding: MathModelIsolationRun): void {
  for (const id of binding.conversationIds) {
    const registration = registrationSchema.parse(
      readPrivateJson(path.join(policy.stateDirectory, 'registrations', `${id}.json`)).value
    );
    if (canonicalMathJson(registration) !== canonicalMathJson(registrationFor(binding, id, 'sealed')))
      throw new Error('math_isolation_registration_not_sealed');
  }
}

/** Stop the receipt-bound supervisor and every descendant it created.
 *
 * Core's session DELETE is asynchronous and bwrap starts a separate session,
 * so relying on the supervisor's own exit handler can leave a live sandbox.
 * Every target is revalidated by PID and kernel start time immediately before
 * signalling; descendants are selected only through a validated parent chain.
 */
export async function cleanupMathModelIsolationProcesses(input: {
  policyFile: string;
  binding: MathModelIsolationRun;
  timeoutMs?: number;
}): Promise<void> {
  const binding = bindingSchema.parse(input.binding);
  const { policy, digest } = readMathModelIsolationPolicy(input.policyFile);
  if (digest !== binding.policyDigest) throw new Error('math_isolation_evidence_binding_mismatch');
  // Startup failures may have only a supervisor identity, or may never have
  // launched every conversation. Proof completeness remains a finalization gate.
  assertRegistrationsSealed(policy, binding);
  const receipts = readRunReceipts(policy, binding, { requireComplete: false });
  const roots = receipts.flatMap(({ record }) =>
    [record.supervisor, record.sandbox, record.namespaceProcess].filter(
      (identity): identity is ProcessIdentity => identity !== null
    )
  );
  const deadline = Date.now() + (input.timeoutMs ?? 5000);
  let targets = readProcessTree(roots);
  const retainDiscoveredProcesses = () => {
    const known = new Map(targets.map((target) => [`${target.pid}:${target.startTimeTicks}`, target]));
    for (const target of readProcessTree(roots)) known.set(`${target.pid}:${target.startTimeTicks}`, target);
    targets = [...known.values()];
  };
  signalProcesses(targets, 'SIGTERM');
  while (targets.some(processStillRunning) && Date.now() < deadline) {
    // Process termination must be observed sequentially until the deadline.
    // eslint-disable-next-line no-await-in-loop
    await new Promise<void>((resolve) => setTimeout(resolve, 50));
    // Keep the original identities even if a child is reparented after its
    // supervisor exits; otherwise an orphan could disappear from the next
    // parent-chain scan and be mistaken for a clean shutdown.
    retainDiscoveredProcesses();
  }
  if (targets.some(processStillRunning)) {
    signalProcesses(targets, 'SIGKILL');
    const killDeadline = Date.now() + 1000;
    while (targets.some(processStillRunning) && Date.now() < killDeadline) {
      // eslint-disable-next-line no-await-in-loop
      await new Promise<void>((resolve) => setTimeout(resolve, 25));
      retainDiscoveredProcesses();
    }
  }
  if (targets.some(processStillRunning)) throw new Error('math_isolation_processes_running');
}
function assertProcessesStopped(receipts: ReturnType<typeof readRunReceipts>) {
  for (const { record } of receipts) {
    if ([record.supervisor, record.sandbox!, record.namespaceProcess!].some(processStillRunning))
      throw new Error('math_isolation_processes_running');
  }
  // Core starts each supervisor as a process-group leader. A dead launcher
  // alone is insufficient when a broker or another child still owns that group.
  const groups = new Set(receipts.map(({ record }) => record.supervisor.pid));
  const namespaces = new Set(receipts.map(({ record }) => record.namespaces!.pid));
  for (const name of fs.readdirSync('/proc')) {
    if (!/^[0-9]+$/u.test(name)) continue;
    try {
      const stat = fs.readFileSync(`/proc/${name}/stat`, 'utf8');
      const fields = stat
        .slice(stat.lastIndexOf(')') + 2)
        .trim()
        .split(/\s+/u);
      if (['Z', 'X'].includes(fields[0])) continue;
      if (groups.has(Number(fields[2]))) throw new Error('math_isolation_processes_running');
      if (
        fs.statSync(`/proc/${name}`).uid === process.getuid?.() &&
        namespaces.has(fs.readlinkSync(`/proc/${name}/ns/pid`))
      )
        throw new Error('math_isolation_processes_running');
    } catch (error) {
      if (error instanceof Error && error.message === 'math_isolation_processes_running') throw error;
      const code = (error as NodeJS.ErrnoException).code;
      if (!['ENOENT', 'ESRCH', 'EACCES', 'EPERM'].includes(code ?? ''))
        throw new Error('math_isolation_process_observation_unavailable', { cause: error });
    }
  }
}

/** Call only after sealing registrations and stopping the Core Team session. */
export async function finalizeMathModelIsolationRun(input: {
  policyFile: string;
  binding: MathModelIsolationRun;
  timeoutMs?: number;
  /** Lazy Worker slots may remain registered without ever being launched. */
  allowUnstartedConversations?: boolean;
}) {
  const binding = bindingSchema.parse(input.binding);
  const { policy, digest } = readMathModelIsolationPolicy(input.policyFile);
  if (digest !== binding.policyDigest) throw new Error('math_isolation_evidence_binding_mismatch');
  assertRegistrationsSealed(policy, binding);
  const deadline = Date.now() + (input.timeoutMs ?? 15000);
  const launched = readRunReceipts(policy, binding, { requireComplete: false });
  const unstartedConversationIds = input.allowUnstartedConversations
    ? binding.conversationIds.filter((id) => !launched.some(({ record }) => record.conversationId === id))
    : [];
  const readOptions = { unstartedConversationIds };
  let receipts = readRunReceipts(policy, binding, readOptions);
  while (true) {
    receipts = readRunReceipts(policy, binding, readOptions);
    try {
      assertProcessesStopped(receipts);
      break;
    } catch (error) {
      if (!(error instanceof Error) || error.message !== 'math_isolation_processes_running' || Date.now() >= deadline)
        throw error;
      // Process termination must be observed sequentially until the deadline.
      // eslint-disable-next-line no-await-in-loop
      await new Promise<void>((resolve) => setTimeout(resolve, 100));
    }
  }
  const certificate = terminationSchema.parse({
    schema: 'deepscientist.math.model-isolation-termination.v1',
    binding,
    checkedAt: new Date().toISOString(),
    ...(unstartedConversationIds.length ? { unstartedConversationIds } : {}),
    receipts: receipts.map(({ path: file, sha256, record }) => ({
      path: file,
      sha256,
      conversationId: record.conversationId,
      instanceId: record.instanceId,
      termination: record.status === 'closed' ? 'launcher_closed' : 'host_confirmed_stopped',
      supervisor: record.supervisor,
      sandbox: record.sandbox,
      namespaceProcess: record.namespaceProcess,
    })),
  });
  const directory = path.join(policy.stateDirectory, 'terminations');
  privateDirectory(directory);
  const file = path.join(directory, `${binding.runNonce}.json`);
  if (fs.existsSync(file)) {
    const existing = terminationSchema.parse(readPrivateJson(file).value);
    if (
      canonicalMathJson(existing.binding) !== canonicalMathJson(binding) ||
      canonicalMathJson(existing.unstartedConversationIds ?? []) !== canonicalMathJson(unstartedConversationIds) ||
      canonicalMathJson(existing.receipts) !== canonicalMathJson(certificate.receipts)
    )
      throw new Error('math_isolation_termination_changed');
  } else writePrivateJson(file, certificate);
  return collectMathModelIsolationEvidence({
    policyFile: input.policyFile,
    expectedDigest: digest,
    workspace: binding.workspace,
    conversationIds: binding.conversationIds,
    runId: binding.runId,
    runNonce: binding.runNonce,
  });
}

export function collectMathModelIsolationEvidence(input: {
  policyFile: string;
  expectedDigest: string;
  workspace: string;
  conversationIds: readonly string[];
  runId: string;
  runNonce: string;
}) {
  const { policy, digest } = readMathModelIsolationPolicy(input.policyFile);
  if (digest !== input.expectedDigest || !policy.workspaces.includes(input.workspace))
    throw new Error('math_isolation_evidence_binding_mismatch');
  const certificateFile = path.join(
    policy.stateDirectory,
    'terminations',
    `${z.string().uuid().parse(input.runNonce)}.json`
  );
  const { bytes, value } = readPrivateJson(certificateFile);
  const certificate = terminationSchema.parse(value);
  checkBinding(certificate.binding, input);
  if (
    certificate.binding.runNonce !== input.runNonce ||
    Date.parse(certificate.checkedAt) < Date.parse(certificate.binding.registeredAt)
  )
    throw new Error('math_isolation_evidence_binding_mismatch');
  const receipts = readRunReceipts(policy, certificate.binding, {
    unstartedConversationIds: certificate.unstartedConversationIds,
  });
  if (
    canonicalMathJson(certificate.receipts.map(({ path: file, sha256 }) => ({ path: file, sha256 }))) !==
    canonicalMathJson(receipts.map(({ path: file, sha256 }) => ({ path: file, sha256 })))
  )
    throw new Error('math_isolation_instance_set_changed');
  for (const [index, { record }] of receipts.entries()) {
    const item = certificate.receipts[index];
    if (
      item.conversationId !== record.conversationId ||
      item.instanceId !== record.instanceId ||
      item.termination !== (record.status === 'closed' ? 'launcher_closed' : 'host_confirmed_stopped') ||
      canonicalMathJson([item.supervisor, item.sandbox, item.namespaceProcess]) !==
        canonicalMathJson([record.supervisor, record.sandbox, record.namespaceProcess])
    )
      throw new Error('math_isolation_termination_changed');
  }
  assertProcessesStopped(receipts);
  return {
    schema: 'deepscientist.math.model-isolation-evidence.v1',
    policyFile: input.policyFile,
    policyDigest: digest,
    enforcement: 'linux-bwrap',
    runId: certificate.binding.runId,
    runNonce: certificate.binding.runNonce,
    conversationIds: certificate.binding.conversationIds,
    ...(certificate.unstartedConversationIds ? { unstartedConversationIds: certificate.unstartedConversationIds } : {}),
    termination: { path: certificateFile, sha256: digestBytes(bytes), checkedAt: certificate.checkedAt },
    receipts: certificate.receipts.map(
      ({ supervisor: _supervisor, sandbox: _sandbox, namespaceProcess: _namespaceProcess, ...item }) => item
    ),
  };
}
