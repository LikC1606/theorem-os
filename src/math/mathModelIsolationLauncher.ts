import fs from 'node:fs';
import path from 'node:path';
import os from 'node:os';
import net from 'node:net';
import http from 'node:http';
import { spawn, spawnSync, type ChildProcess } from 'node:child_process';
import { createInterface } from 'node:readline';
import { createHash, randomBytes, randomUUID } from 'node:crypto';
import { once } from 'node:events';
import { z } from 'zod';
import {
  readMathModelIsolationPolicy,
  mathModelIsolationMounts,
  mathModelIsolationMcpMounts,
  validateMathIsolatedMcp,
  isolationCanonical,
  isolationContains,
  type MathModelIsolationPolicy,
} from "./mathModelIsolation";
import { startMathIsolatedProvider, type MathIsolatedProviderEvent } from "./mathIsolatedProvider";
import { MATH_RUN_INPUTS_ENV, verifyMathRunInputs } from "./mathRunInputs";
import {
  MATH_PROOF_ENVIRONMENT_ENV,
  MATH_PROOF_ENVIRONMENT_SANDBOX_ENV,
  openMathProofEnvironmentSandboxBinding,
} from "./mathProofEnvironment";
import { readMathRunBinding } from "./mathRunBinding";
import type { MathRunBinding } from "../common/types/team/mathRuntimeContracts";
import {
  MATH_RECEIPT_KEY_PATH_ENV as RECEIPT_KEY_PATH_ENV,
  MATH_RECEIPT_SECRET_ENV as RECEIPT_SECRET_ENV,
  resolveMathReceiptKeyPath,
} from "./receiptKey";

const insideRoot = '/run/math-isolation';
const insideLauncher = '/opt/math-model-isolation.js';
const fixedError = (code: string) => process.stderr.write(`${code}\n`);
const baselineMarkerSchema = z
  .object({
    schema: z.literal('deepscientist.math.model-isolation-git-baseline.v1'),
    workspace: z.string(),
    policyDigest: z.string().regex(/^[a-f0-9]{64}$/u),
    runId: z.string().min(1),
    baselineCommit: z.string().regex(/^[a-f0-9]{40,64}$/u),
  })
  .strict();
const registrationSchema = z
  .object({
    schema: z.literal('deepscientist.math.model-isolation-registration.v1'),
    conversationId: z.string(),
    runId: z.string().min(1),
    runNonce: z.string().uuid(),
    policyDigest: z.string().regex(/^[a-f0-9]{64}$/u),
    workspace: z.string(),
    registeredAt: z.string().datetime(),
    status: z.enum(['active', 'sealed']),
  })
  .strict();

function writeJsonLine(stream: NodeJS.WritableStream, value: unknown): boolean {
  return stream.write(`${JSON.stringify(value)}\n`);
}

function processIdentity(pid: number) {
  const stat = fs.readFileSync(`/proc/${pid}/stat`, 'utf8');
  const startTimeTicks = stat.slice(stat.lastIndexOf(')') + 2).split(' ')[19];
  if (!/^\d+$/u.test(startTimeTicks)) throw new Error('math_isolation_process_invalid');
  return { pid, startTimeTicks };
}
const safeEnv = (): NodeJS.ProcessEnv => ({
  PATH: '/opt/math-tools:/usr/bin:/bin',
  LANG: 'C.UTF-8',
  HOME: '/home/model',
  CODEX_HOME: '/home/model/.codex',
  SHELL: '/bin/bash',
  TMPDIR: '/tmp',
});

const MCP_ENV_ALLOWLIST = new Set([
  'AIONUI_BASE_URL',
  'AIONUI_USER_ID',
  'AIONUI_CONVERSATION_ID',
  'AIONUI_RUNTIME_TOKEN',
  'TEAM_MCP_PORT',
  'DEEPSCIENTIST_RESEARCH_TEAM_CAPABILITY_SCHEMA',
  'DEEPSCIENTIST_RESEARCH_TEAM_PROFILE',
  'DEEPSCIENTIST_RESEARCH_TEAM_WORKFLOW',
  'DEEPSCIENTIST_RESEARCH_TEAM_ROLE',
  'DEEPSCIENTIST_RESEARCH_TEAM_ROLE_KIND',
  'DEEPSCIENTIST_RESEARCH_TEAM_ACTIONS',
  'DEEPSCIENTIST_RESEARCH_TEAM_PROJECT_ROOT',
  'DEEPSCIENTIST_RESEARCH_TEAM_ID',
  'DEEPSCIENTIST_RESEARCH_TEAM_SLOT_ID',
  'DEEPSCIENTIST_RESEARCH_TEAM_AGENT_LIMIT',
  'DEEPSCIENTIST_RESEARCH_TEAM_REASONING_CONCURRENCY',
  'DEEPSCIENTIST_RESEARCH_TEAM_ROSTER',
  'DEEPSCIENTIST_RESEARCH_TEAM_TOOL_POLICY_SCHEMA',
  'DEEPSCIENTIST_RESEARCH_TEAM_TOOL_POLICY_ALLOWED',
  'DEEPSCIENTIST_RESEARCH_TEAM_TOOL_POLICY_DENIED',
  'DEEPSCIENTIST_MATH_ENV_FILE',
  'DEEPSCIENTIST_MATH_RUN_INPUTS',
  'DEEPSCIENTIST_MATH_RETRIEVAL_CORPUS',
  'DEEPSCIENTIST_MATH_RETRIEVAL_CORPUS_SHA256',
  'DEEPSCIENTIST_LEAN_EVAL_ROOT',
]);

/** Sandbox path of the host receipt key; only trusted MCP children receive it. */
export const MATH_ISOLATION_RECEIPT_KEY_PATH = '/run/math-receipt/receipt-signing.key';

export function resolveMathIsolationReceiptKeyPath(env: NodeJS.ProcessEnv = process.env): string {
  return resolveMathReceiptKeyPath(env);
}

/**
 * Ensure the host receipt key exists and is a private regular file, then return
 * its path. Before run 23 attempt 16 the MCP sandbox's private /tmp made the MCP
 * mint its own key, so every solver-ready receipt failed host verification.
 */
function ensureMathIsolationReceiptKey(env: NodeJS.ProcessEnv = process.env): string {
  // An env-only secret cannot be handed to the sandbox without exposing it on a
  // bwrap command line; require the file form instead.
  if (env[RECEIPT_SECRET_ENV]?.trim()) throw new Error('math_isolation_receipt_secret_env_unsupported');
  const file = resolveMathIsolationReceiptKeyPath(env);
  if (!path.isAbsolute(file)) throw new Error('math_isolation_receipt_key_invalid');
  fs.mkdirSync(path.dirname(file), { recursive: true });
  try {
    const fd = fs.openSync(file, 'wx', 0o600);
    try {
      fs.writeFileSync(fd, `${randomBytes(32).toString('hex')}\n`, 'utf8');
    } finally {
      fs.closeSync(fd);
    }
  } catch (error) {
    if ((error as NodeJS.ErrnoException).code !== 'EEXIST') throw new Error('math_isolation_receipt_key_invalid');
  }
  const stat = fs.lstatSync(file);
  if (!stat.isFile() || stat.nlink !== 1 || (stat.mode & 0o077) !== 0 || !fs.readFileSync(file, 'utf8').trim())
    throw new Error('math_isolation_receipt_key_invalid');
  return file;
}

function isolatedMcpEnv(entries: readonly { name: string; value: string }[]): NodeJS.ProcessEnv {
  const env = safeEnv();
  env.DEEPSCIENTIST_MATH_ISOLATION_WORKSPACE = process.cwd();
  for (const entry of entries) if (MCP_ENV_ALLOWLIST.has(entry.name)) env[entry.name] = entry.value;
  return env;
}

function isBoundWorkerWorktree(workspace: string, cwd: string): boolean {
  try {
    const workers = path.join(workspace, '.deepscientist/agent-worktrees');
    if (cwd === workers || !isolationContains(workers, cwd)) return false;
    isolationCanonical(workspace);
    isolationCanonical(cwd);
    const readPointer = (file: string) => {
      isolationCanonical(file);
      const stat = fs.lstatSync(file);
      if (!stat.isFile() || stat.size > 4096) throw new Error();
      return fs.readFileSync(file, 'utf8').trimEnd();
    };
    const gitFile = path.join(cwd, '.git');
    const pointer = /^gitdir: ([^\r\n]+)$/u.exec(readPointer(gitFile));
    if (!pointer) return false;
    const gitDir = path.resolve(cwd, pointer[1]);
    const commonGit = isolationCanonical(path.join(workspace, '.git'));
    // Require the reciprocal Git registration, not just a pointer into an
    // authorized repository copied from another worker.
    return (
      path.dirname(gitDir) === path.join(commonGit, 'worktrees') &&
      path.resolve(gitDir, readPointer(path.join(gitDir, 'gitdir'))) === gitFile &&
      path.resolve(gitDir, readPointer(path.join(gitDir, 'commondir'))) === commonGit
    );
  } catch {
    return false;
  }
}

export function validateMathMcpProjectRoot(
  projectRoot: string,
  cwd: string,
  binding?: Pick<MathRunBinding, 'workspace' | 'projectRoot'>
): void {
  const canonicalProjectRoot = path.resolve(projectRoot);
  if (canonicalProjectRoot !== projectRoot || !fs.existsSync(projectRoot))
    throw new Error('math_isolation_mcp_project_root_invalid');
  isolationCanonical(projectRoot);
  if (binding) {
    const authorizedRoots = new Set([binding.projectRoot, binding.workspace].map((root) => path.resolve(root)));
    const canonicalCwd = path.resolve(cwd);
    isolationCanonical(cwd);
    if (
      !authorizedRoots.has(canonicalProjectRoot) ||
      (!authorizedRoots.has(canonicalCwd) && !isBoundWorkerWorktree(binding.workspace, cwd))
    )
      throw new Error('math_isolation_mcp_project_root_mismatch');
    return;
  }
  if (!isolationContains(cwd, projectRoot)) throw new Error('math_isolation_mcp_project_root_invalid');
}

function isolatedMcpMounts(
  policy: MathModelIsolationPolicy,
  cwd: string,
  socketDirectory: string,
  policyDigest: string,
  shareNetwork: boolean,
  env: NodeJS.ProcessEnv
): { mounts: string[]; proofEnvironment?: { fd: number; args: string[]; mapping: string } } {
  const marker = readInheritedGitBaselineMarker(policy, cwd, policyDigest);
  if (!marker) throw new Error('math_isolation_git_baseline_missing');
  const mounts = mathModelIsolationMounts(policy, cwd, { baselineCommit: marker.baselineCommit });
  const unshareIndex = mounts.indexOf('--unshare-all');
  if (unshareIndex < 0) throw new Error('math_isolation_mounts_invalid');
  // Only the Core-backed Team MCP needs the local Core endpoint. Ordinary MCP
  // bundles retain the isolated network namespace.
  if (shareNetwork) mounts.splice(unshareIndex + 1, 0, '--share-net');
  if (!path.isAbsolute(socketDirectory) || !fs.existsSync(socketDirectory))
    throw new Error('math_isolation_mcp_socket_invalid');
  mounts.push('--ro-bind', socketDirectory, insideRoot);
  let readOnlyPaths: string[] = [];
  let writablePaths: string[] = [];
  let runBinding: Pick<MathRunBinding, 'workspace' | 'projectRoot'> | undefined;
  let runEnvironment: Record<string, string> | undefined;
  const encodedInputs = env[MATH_RUN_INPUTS_ENV];
  if (encodedInputs) {
    try {
      const inputs = verifyMathRunInputs(JSON.parse(encodedInputs));
      const binding = readMathRunBinding(inputs);
      runBinding = binding;
      const environment = JSON.parse(fs.readFileSync(inputs.environment.path, 'utf8')) as Record<string, string>;
      runEnvironment = environment;
      const toolManifest = environment.DEEPSCIENTIST_LEAN_EVAL_TOOL_MANIFEST;
      const retrievalCorpus = environment.DEEPSCIENTIST_MATH_RETRIEVAL_CORPUS;
      readOnlyPaths = [
        inputs.root,
        inputs.task.path,
        inputs.environment.path,
        inputs.binding.path,
        binding.buildManifestRef,
        ...(toolManifest ? [toolManifest] : []),
        ...(retrievalCorpus ? [retrievalCorpus] : []),
      ];
      writablePaths = [path.dirname(binding.artifactStoreRoot)];
    } catch {
      throw new Error('math_isolation_mcp_run_binding_invalid');
    }
  }
  const projectRoot = env.DEEPSCIENTIST_RESEARCH_TEAM_PROJECT_ROOT;
  if (projectRoot) {
    validateMathMcpProjectRoot(projectRoot, cwd, runBinding);
    // The outer workspace is already writable through the base namespace mount.
    // Rebinding it here would unmask the private .deepscientist state directory.
    if (projectRoot !== cwd) writablePaths.push(projectRoot);
  }
  for (const stateRoot of [path.join(cwd, '.deepscientist'), projectRoot && path.join(projectRoot, '.deepscientist')])
    if (stateRoot && fs.existsSync(stateRoot)) writablePaths.push(stateRoot);
  mounts.push(...mathModelIsolationMcpMounts(policy, cwd, { readOnlyPaths, writablePaths }));
  // Trusted built-in MCP bundles sign solver-ready receipts that the host runner
  // verifies. Hand them the host key read-only at a fixed path under /run, which
  // neither the model namespace nor the nested Lean sandbox mounts.
  if (shareNetwork) {
    const receiptKey = ensureMathIsolationReceiptKey();
    mounts.push(
      '--dir',
      path.dirname(MATH_ISOLATION_RECEIPT_KEY_PATH),
      '--ro-bind',
      receiptKey,
      MATH_ISOLATION_RECEIPT_KEY_PATH
    );
  }
  // The host pid behind a sealed proof environment is invisible in this PID
  // namespace. Hand over the verified root and lease socket instead. If the
  // host check fails, bind nothing: the MCP then fails closed as before.
  let proofEnvironment: { fd: number; args: string[]; mapping: string } | undefined;
  if (runBinding && runEnvironment?.[MATH_PROOF_ENVIRONMENT_ENV]) {
    try {
      proofEnvironment = openMathProofEnvironmentSandboxBinding(
        runBinding.projectRoot,
        runEnvironment,
        '/run/math-proof'
      );
    } catch {
      proofEnvironment = undefined;
    }
  }
  return { mounts, ...(proofEnvironment ? { proofEnvironment } : {}) };
}

function gitBaselineMarkerPath(policy: MathModelIsolationPolicy, workspace: string): string {
  const key = createHash('sha256').update(workspace).digest('hex');
  return path.join(policy.stateDirectory, 'git-baselines', `${key}.json`);
}

function readGitBaselineMarker(policy: MathModelIsolationPolicy, workspace: string, policyDigest: string) {
  const file = gitBaselineMarkerPath(policy, workspace);
  let stat: fs.Stats;
  try {
    stat = fs.lstatSync(file);
  } catch (error) {
    if ((error as NodeJS.ErrnoException).code === 'ENOENT') return undefined;
    throw error;
  }
  if (!stat.isFile() || stat.nlink !== 1 || stat.size > 4096 || (stat.mode & 0o077) !== 0)
    throw new Error('math_isolation_git_baseline_invalid');
  const marker = baselineMarkerSchema.parse(JSON.parse(fs.readFileSync(file, 'utf8')));
  // The baseline is durable across launcher runs. runId records provenance but
  // must not gate a later run with a fresh registration identity.
  if (marker.workspace !== workspace || marker.policyDigest !== policyDigest)
    throw new Error('math_isolation_git_baseline_mismatch');
  return marker;
}

/**
 * A Worker worktree created mid-run has no marker of its own. Its baseline is
 * the one pinned for the trial root when the Lead first launched there: the
 * shared repository already holds this run's Worker commits, so the
 * single-commit check would deny every later Worker (run 23 died this way).
 * Without a trial-root marker the strict single-commit check still applies.
 */
export function readInheritedGitBaselineMarker(
  policy: MathModelIsolationPolicy,
  workspace: string,
  policyDigest: string
) {
  const own = readGitBaselineMarker(policy, workspace, policyDigest);
  if (own) return own;
  const trial = policy.workspaces.find((root) => root !== workspace && isolationContains(root, workspace));
  return trial ? readGitBaselineMarker(policy, trial, policyDigest) : undefined;
}

function writeGitBaselineMarker(
  policy: MathModelIsolationPolicy,
  workspace: string,
  policyDigest: string,
  runId: string,
  baselineCommit: string
): void {
  const directory = path.join(policy.stateDirectory, 'git-baselines');
  fs.mkdirSync(directory, { recursive: true, mode: 0o700 });
  const file = gitBaselineMarkerPath(policy, workspace);
  const value = baselineMarkerSchema.parse({
    schema: 'deepscientist.math.model-isolation-git-baseline.v1',
    workspace,
    policyDigest,
    runId,
    baselineCommit,
  });
  const temporary = `${file}.${randomUUID()}.tmp`;
  fs.writeFileSync(temporary, `${JSON.stringify(value)}\n`, { mode: 0o600, flag: 'wx' });
  fs.renameSync(temporary, file);
}

function currentGitHead(workspace: string): string {
  const result = spawnSync('git', ['-C', workspace, 'rev-parse', '--verify', 'HEAD'], {
    encoding: 'utf8',
    stdio: ['ignore', 'pipe', 'ignore'],
  });
  const head = result.status === 0 ? result.stdout.trim() : '';
  if (!/^[a-f0-9]{40,64}$/u.test(head)) throw new Error('math_isolation_git_baseline_invalid');
  return head;
}

async function isolatedRelay(socket: string): Promise<void> {
  if (!/^\/run\/math-isolation\/mcp-[a-f0-9-]+\.sock$/u.test(socket)) throw new Error('math_isolation_relay_denied');
  const connection = net.createConnection(socket);
  connection.once('error', () => process.exit(1));
  process.stdin.pipe(connection);
  connection.pipe(process.stdout);
  connection.once('close', () => process.exit(0));
}

const MATH_ISOLATION_REASONING_EFFORTS: readonly string[] = ['low', 'medium', 'high', 'xhigh'];

/**
 * Codex has no bundled metadata for custom models, so it falls back to metadata
 * without reasoning support and sends `reasoning: null` even when
 * `model_reasoning_effort` is set. A one-model catalog declaring the supported
 * levels makes Codex send `reasoning.effort` and makes codex-acp advertise a
 * thought_level option, so Core can apply each role's configured level.
 */
export function mathIsolationModelCatalog(model: string, defaultEffort: string): Record<string, unknown> {
  return {
    models: [
      {
        slug: model,
        display_name: model,
        description: `${model} via the isolated Responses provider.`,
        default_reasoning_level: defaultEffort,
        supported_reasoning_levels: MATH_ISOLATION_REASONING_EFFORTS.map((effort) => ({ effort, description: effort })),
        default_reasoning_summary: 'none',
        supports_reasoning_summaries: true,
        supports_reasoning_summary_parameter: false,
        shell_type: 'shell_command',
        visibility: 'list',
        supported_in_api: true,
        priority: 1,
        context_window: 272000,
        max_context_window: 272000,
        effective_context_window_percent: 95,
        auto_compact_token_limit: null,
        truncation_policy: { mode: 'bytes', limit: 10000 },
        supports_parallel_tool_calls: true,
        supports_image_detail_original: false,
        supports_search_tool: false,
        support_verbosity: false,
        default_verbosity: null,
        input_modalities: ['text'],
        base_instructions: 'You are Codex, a coding agent.',
        apply_patch_tool_type: null,
        web_search_tool_type: 'text',
        experimental_supported_tools: [],
        additional_speed_tiers: [],
        service_tiers: [],
        default_service_tier: null,
        include_skills_usage_instructions: false,
        use_responses_lite: false,
        minimal_client_version: [0, 1, 0],
        model_messages: null,
        multi_agent_version: null,
        tool_mode: null,
        upgrade: null,
        availability_nux: null,
        auto_review_model_override: null,
        comp_hash: null,
      },
    ],
  };
}

function writeMathIsolationModelCatalog(file: string, model: string, effort: string): void {
  fs.writeFileSync(file, `${JSON.stringify(mathIsolationModelCatalog(model, effort), null, 2)}\n`, { mode: 0o600 });
}

async function isolatedInside(args: string[]): Promise<void> {
  const [node, codex, acp, modelArgument, providerArgument, effortArgument, ...acpArgs] = args;
  if (!node || !codex || !acp) throw new Error('math_isolation_inside_invalid');
  const model = modelArgument ?? 'deepseek';
  const providerName = providerArgument ?? 'WestlakeHPC';
  // '-' is the host's explicit "no declared effort" sentinel; anything else must
  // be a known level so a malformed argument can never reach the TOML below.
  const reasoningEffort = effortArgument === '-' ? undefined : effortArgument;
  if (reasoningEffort !== undefined && !MATH_ISOLATION_REASONING_EFFORTS.includes(reasoningEffort))
    throw new Error('math_isolation_inside_invalid');
  const catalogPath = '/home/model/.codex/models.json';
  if (reasoningEffort) writeMathIsolationModelCatalog(catalogPath, model, reasoningEffort);
  const provider = http.createServer((req, res) => {
    if (req.method !== 'POST' || req.url !== '/v1/responses') {
      res.writeHead(403).end();
      return;
    }
    const upstream = http.request(
      {
        socketPath: `${insideRoot}/provider.sock`,
        path: req.url,
        method: 'POST',
        headers: { 'content-type': 'application/json' },
      },
      (reply) => {
        res.writeHead(reply.statusCode ?? 502, { 'content-type': 'text/event-stream' });
        reply.pipe(res);
      }
    );
    upstream.once('error', () => {
      if (!res.headersSent) res.writeHead(502).end();
      else res.destroy();
    });
    res.once('close', () => {
      if (!res.writableFinished) upstream.destroy();
    });
    req.pipe(upstream);
  });
  provider.on('connect', (_req, socket) => socket.destroy());
  provider.on('upgrade', (_req, socket) => socket.destroy());
  await new Promise<void>((resolve, reject) => {
    provider.once('error', reject);
    provider.listen(0, '127.0.0.1', resolve);
  });
  const address = provider.address();
  if (!address || typeof address === 'string') throw new Error('math_isolation_provider_start_failed');
  fs.writeFileSync(
    '/home/model/.codex/config.toml',
    [
      `model_provider = ${JSON.stringify(providerName)}`,
      `model = ${JSON.stringify(model)}`,
      ...(reasoningEffort
        ? [
            `model_reasoning_effort = ${JSON.stringify(reasoningEffort)}`,
            `model_catalog_json = ${JSON.stringify(catalogPath)}`,
          ]
        : []),
      'approval_policy = "never"',
      'sandbox_mode = "danger-full-access"',
      'web_search = "disabled"',
      'allow_login_shell = false',
      '[features]',
      'shell_snapshot = false',
      'multi_agent = false',
      `[model_providers.${providerName}]`,
      `name = ${JSON.stringify(providerName)}`,
      'wire_api = "responses"',
      `base_url = "http://127.0.0.1:${address.port}/v1"`,
      'env_key = "MATH_ISOLATED_PROVIDER_TOKEN"',
      'requires_openai_auth = false',
      '',
    ].join('\n'),
    { mode: 0o600 }
  );
  const child = spawn(node, [acp, ...acpArgs], {
    env: {
      ...safeEnv(),
      CODEX_PATH: codex,
      MATH_ISOLATED_PROVIDER_TOKEN: 'namespace-local',
      CODEX_CONFIG: JSON.stringify({
        allow_login_shell: false,
        web_search: 'disabled',
        features: { shell_snapshot: false, multi_agent: false },
        sandbox_mode: 'danger-full-access',
      }),
    },
    stdio: ['inherit', 'inherit', 'ignore'],
  });
  child.once('error', () => process.exit(1));
  child.once('exit', (code) => {
    provider.closeAllConnections();
    provider.close();
    process.exit(code ?? 1);
  });
}

/** Core starts this trusted supervisor; neither policy nor host environment enters the namespace. */
export async function launchMathModelIsolation(argv: string[]): Promise<void> {
  const divider = argv.indexOf('--');
  const policyIndex = argv.indexOf('--policy');
  const conversationIndex = argv.indexOf('--conversation-id');
  if (divider < 0 || policyIndex < 0 || conversationIndex < 0) throw new Error('math_isolation_arguments_invalid');
  const conversationId = argv[conversationIndex + 1];
  if (!conversationId || !/^[a-zA-Z0-9_-]{1,128}$/u.test(conversationId))
    throw new Error('math_isolation_conversation_invalid');
  const { policy, digest } = readMathModelIsolationPolicy(argv[policyIndex + 1]);
  const registrationPath = path.join(policy.stateDirectory, 'registrations', `${conversationId}.json`);
  const readRegistration = () => {
    isolationCanonical(registrationPath);
    const stat = fs.lstatSync(registrationPath);
    if (!stat.isFile() || stat.nlink !== 1 || stat.size > 65536 || (stat.mode & 0o077) !== 0)
      throw new Error('math_isolation_registration_invalid');
    const registration = registrationSchema.parse(JSON.parse(fs.readFileSync(registrationPath, 'utf8')));
    if (
      registration.status !== 'active' ||
      registration.conversationId !== conversationId ||
      registration.policyDigest !== digest ||
      !policy.workspaces.includes(registration.workspace) ||
      !isolationContains(registration.workspace, process.cwd())
    )
      throw new Error('math_isolation_registration_denied');
    return registration;
  };
  const registration = readRegistration();
  const [command, acp, ...acpArgs] = argv.slice(divider + 1);
  // Core may discover another system Node. Execute only the policy-pinned
  // runtime below; the caller's program is never executed by this supervisor.
  if (!command || !path.isAbsolute(command) || path.basename(fs.realpathSync(command)) !== 'node')
    throw new Error('math_isolation_node_mismatch');
  if (
    !acp ||
    !path.isAbsolute(acp) ||
    createHash('sha256').update(fs.readFileSync(acp)).digest('hex') !==
      createHash('sha256').update(fs.readFileSync(policy.acpScript)).digest('hex')
  )
    throw new Error('math_isolation_acp_mismatch');
  const workspacePath = process.cwd();
  const ownMarker = readGitBaselineMarker(policy, workspacePath, digest);
  const baselineMarker = ownMarker ?? readInheritedGitBaselineMarker(policy, workspacePath, digest);
  const mounts = mathModelIsolationMounts(
    policy,
    workspacePath,
    baselineMarker ? { baselineCommit: baselineMarker.baselineCommit } : {}
  );
  if (!ownMarker)
    writeGitBaselineMarker(
      policy,
      workspacePath,
      digest,
      registration.runId,
      baselineMarker?.baselineCommit ?? currentGitHead(workspacePath)
    );
  const instanceId = randomUUID();
  const sockets = fs.mkdtempSync(path.join(os.tmpdir(), 'math-model-'));
  fs.chmodSync(sockets, 0o700);
  const children = new Set<ChildProcess>();
  const servers = new Set<net.Server>();
  const connections = new Set<net.Socket>();
  const startedAt = new Date().toISOString();
  const receiptPath = path.join(policy.stateDirectory, `${conversationId}-${instanceId}.json`);
  const record: Record<string, unknown> = {
    schema: 'deepscientist.math.model-isolation-receipt.v1',
    conversationId,
    instanceId,
    runId: registration.runId,
    runNonce: registration.runNonce,
    supervisor: processIdentity(process.pid),
    sandbox: null,
    namespaceProcess: null,
    policyDigest: digest,
    workspace: process.cwd(),
    startedAt,
    status: 'starting',
    namespaces: null,
    mcpServers: [],
    enforcement: 'linux-bwrap',
    model: policy.model ?? 'deepseek',
    provider: policy.provider ?? 'WestlakeHPC',
  };
  const persist = () => {
    const temp = `${receiptPath}.tmp`;
    fs.writeFileSync(temp, `${JSON.stringify(record)}\n`, { mode: 0o600 });
    fs.renameSync(temp, receiptPath);
  };
  const pendingPrompts = new Map<string | number, number>();
  const recordPrompt = (event: Record<string, unknown>) =>
    fs.appendFileSync(
      path.join(policy.stateDirectory, `${conversationId}-${instanceId}.protocol.jsonl`),
      `${JSON.stringify({ conversationId, instanceId, runId: registration.runId, runNonce: registration.runNonce, at: new Date().toISOString(), ...event })}\n`,
      { mode: 0o600 }
    );
  persist();
  let handleProviderEvent!: (event: MathIsolatedProviderEvent) => void;
  let provider: Awaited<ReturnType<typeof startMathIsolatedProvider>> | undefined;
  try {
    provider = await startMathIsolatedProvider({
      socketPath: path.join(sockets, 'provider.sock'),
      baseUrl: policy.providerBaseUrl,
      apiKey: process.env[policy.apiKeyEnv ?? 'WESTLAKEHPC_API_KEY'] ?? '',
      model: policy.model ?? 'deepseek',
      record: (event) => {
        fs.appendFileSync(
          path.join(policy.stateDirectory, `${conversationId}-${instanceId}.requests.jsonl`),
          `${JSON.stringify({ conversationId, instanceId, policyDigest: digest, ...event })}\n`,
          { mode: 0o600 }
        );
        handleProviderEvent(event);
      },
    });
  } catch {
    record.status = 'failed';
    record.finishedAt = new Date().toISOString();
    persist();
    fs.rmSync(sockets, { recursive: true, force: true });
    throw new Error('math_isolation_provider_start_failed');
  }
  let sandbox: ChildProcess | undefined;
  let stopping = false;
  let fatalPolicyRejection = false;
  const stop = async (code: number) => {
    if (stopping) return;
    stopping = true;
    record.status = code === 0 ? 'closed' : 'failed';
    record.finishedAt = new Date().toISOString();
    try {
      persist();
    } catch {
      code = 1;
    }
    for (const socket of connections) socket.destroy();
    for (const server of servers) server.close();
    for (const child of children) child.kill('SIGTERM');
    const kill = setTimeout(() => {
      for (const child of children) child.kill('SIGKILL');
    }, 1000);
    kill.unref();
    await provider?.close();
    await Promise.race([
      Promise.all(
        [...children].map((child) =>
          child.exitCode !== null || child.signalCode !== null ? undefined : once(child, 'exit').catch(() => {})
        )
      ),
      new Promise<void>((resolve) => setTimeout(resolve, 1500)),
    ]);
    clearTimeout(kill);
    fs.rmSync(sockets, { recursive: true, force: true });
    process.exit(code);
  };
  handleProviderEvent = (event) => {
    // A deterministic request-policy rejection cannot recover by retrying the
    // same prompt. Return one static JSON-RPC error to Core and close the ACP
    // session; transient capacity/upstream failures retain normal retry paths.
    if (
      stopping ||
      fatalPolicyRejection ||
      event.outcome !== 'rejected' ||
      event.httpStatus !== 400 ||
      !event.rejectionCode
    )
      return;
    fatalPolicyRejection = true;
    const errorCode = -32091;
    const pending = [...pendingPrompts.entries()];
    pendingPrompts.clear();
    for (const [id, started] of pending) {
      recordPrompt({
        event: 'prompt_finished',
        durationMs: performance.now() - started,
        stopReason: null,
        errorCode,
        rejectionCode: event.rejectionCode,
      });
      writeJsonLine(process.stdout, {
        jsonrpc: '2.0',
        id,
        error: { code: errorCode, message: 'Math model request rejected by isolation policy.' },
      });
    }
    setImmediate(() => void stop(1));
  };
  process.once('SIGTERM', () => void stop(0));
  process.once('SIGINT', () => void stop(0));
  process.stdin.once('end', () => void stop(0));
  const mcp = new Map<string, { fingerprint: string; descriptor: unknown }>();
  const prepareMcp = async (value: unknown) => {
    const original = validateMathIsolatedMcp(policy, value);
    const fingerprint = JSON.stringify(original);
    const retained = mcp.get(original.name);
    if (retained) {
      if (retained.fingerprint !== fingerprint) throw new Error('math_isolation_mcp_changed');
      return retained.descriptor;
    }
    if (mcp.size >= 8) throw new Error('math_isolation_mcp_limit');
    const file = `mcp-${randomUUID()}.sock`;
    const coreBacked =
      original.command === policy.coreExecutable && original.args.length === 1 && original.args[0] === 'mcp-team-stdio';
    // Built-in Node MCP bundles are trusted Core clients. They need the
    // local Core endpoint, while the model and ordinary child processes keep
    // their network namespace isolated.
    const trustedCoreClient = coreBacked || path.basename(original.command) === 'node';
    const mcpEnv = isolatedMcpEnv(
      original.env.flatMap((entry) =>
        entry.name !== undefined && entry.value !== undefined ? [{ name: entry.name, value: entry.value }] : []
      )
    );
    const prepareMcpArgs = () => {
      const prepared = isolatedMcpMounts(policy, process.cwd(), sockets, digest, trustedCoreClient, mcpEnv);
      return {
        args: [
          ...prepared.mounts,
          ...(prepared.proofEnvironment?.args ?? []),
          // Restore only the filtered MCP variables inside the namespace.
          ...Object.entries(mcpEnv).flatMap(([name, envValue]) =>
            envValue === undefined ? [] : ['--setenv', name, envValue]
          ),
          ...(prepared.proofEnvironment
            ? ['--setenv', MATH_PROOF_ENVIRONMENT_SANDBOX_ENV, prepared.proofEnvironment.mapping]
            : []),
          ...(trustedCoreClient ? ['--setenv', RECEIPT_KEY_PATH_ENV, MATH_ISOLATION_RECEIPT_KEY_PATH] : []),
          '--',
          original.command,
          ...original.args,
        ],
        fd: prepared.proofEnvironment?.fd,
      };
    };
    // Reject invalid sessions before handing Core a descriptor, then validate
    // mutable workspace paths again on every connection immediately before use.
    const validated = prepareMcpArgs();
    if (validated.fd !== undefined) fs.closeSync(validated.fd);
    let connected = false;
    const server = net.createServer((socket) => {
      if (connected || stopping) {
        socket.destroy();
        return;
      }
      connected = true;
      connections.add(socket);
      socket.on('error', () => socket.destroy());
      let child: ChildProcess;
      try {
        const prepared = prepareMcpArgs();
        try {
          // The sealed root, when present, must be child fd 3 for --ro-bind-fd.
          child = spawn('/usr/bin/bwrap', prepared.args, {
            env: mcpEnv,
            stdio: prepared.fd === undefined ? ['pipe', 'pipe', 'pipe'] : ['pipe', 'pipe', 'pipe', prepared.fd],
          });
        } finally {
          if (prepared.fd !== undefined) fs.closeSync(prepared.fd);
        }
      } catch {
        fixedError('math_isolation_mcp_start_failed');
        socket.destroy();
        void stop(1);
        return;
      }
      children.add(child);
      child.stderr?.on('data', (chunk) => process.stderr.write(chunk));
      child.stdin!.on('error', () => socket.destroy());
      child.once('error', () => {
        socket.destroy();
        void stop(1);
      });
      socket.pipe(child.stdin!);
      child.stdout!.pipe(socket);
      child.once('exit', () => {
        children.delete(child);
        socket.destroy();
        connected = false;
      });
      socket.once('close', () => {
        connections.delete(socket);
        child.kill('SIGTERM');
      });
    });
    servers.add(server);
    await new Promise<void>((resolve, reject) => {
      server.once('error', reject);
      server.listen(path.join(sockets, file), resolve);
    });
    fs.chmodSync(path.join(sockets, file), 0o600);
    const descriptor = {
      name: original.name,
      command: policy.nodeExecutable,
      args: [insideLauncher, '--relay', `${insideRoot}/${file}`],
      env: [] as { name: string; value: string }[],
    };
    mcp.set(original.name, { fingerprint, descriptor });
    record.mcpServers = [...mcp.keys()];
    persist();
    return descriptor;
  };
  try {
    const args = [
      ...mounts,
      '--ro-bind',
      policy.launcher,
      insideLauncher,
      '--ro-bind',
      sockets,
      insideRoot,
      '--json-status-fd',
      '3',
      '--',
      policy.nodeExecutable,
      insideLauncher,
      '--inside',
      policy.nodeExecutable,
      policy.codexExecutable,
      policy.acpScript,
      policy.model ?? 'deepseek',
      policy.provider ?? 'WestlakeHPC',
      policy.reasoningEffort ?? '-',
      ...acpArgs,
    ];
    sandbox = spawn('/usr/bin/bwrap', args, {
      env: safeEnv(),
      stdio: ['pipe', 'pipe', 'pipe', 'pipe'],
    });
    if (!sandbox.pid) throw new Error('math_isolation_sandbox_start_failed');
    record.sandbox = processIdentity(sandbox.pid);
    persist();
    children.add(sandbox);
    sandbox.stderr?.on('data', (chunk) => process.stderr.write(chunk));
    sandbox.once('error', () => void stop(1));
    sandbox.once('exit', (code) => {
      children.delete(sandbox!);
      void stop(fatalPolicyRejection ? 1 : (code ?? 1));
    });
    const sandboxInput = sandbox.stdin!;
    const statusStream = sandbox.stdio[3]! as NodeJS.ReadableStream;
    let statusText = '';
    statusStream.on('data', (chunk) => {
      statusText += chunk.toString();
      if (statusText.length > 16384) {
        void stop(1);
        return;
      }
      const pid = /"child-pid"\s*:\s*(\d+)/u.exec(statusText)?.[1];
      if (!pid || record.namespaces) return;
      try {
        const namespaces = Object.fromEntries(
          ['mnt', 'pid', 'net', 'user', 'ipc', 'uts'].map((name) => {
            const host = fs.readlinkSync(`/proc/self/ns/${name}`);
            const isolated = fs.readlinkSync(`/proc/${pid}/ns/${name}`);
            if (host === isolated) throw new Error();
            return [name, isolated];
          })
        );
        record.namespaces = namespaces;
        record.namespaceProcess = processIdentity(Number(pid));
        record.status = 'running';
        persist();
      } catch {
        void stop(1);
      }
    });
    const outbound = createInterface({ input: sandbox.stdout!, crlfDelay: Infinity });
    outbound.on('line', (line) => {
      if (fatalPolicyRejection) return;
      try {
        if (Buffer.byteLength(line) > 32 * 1024 * 1024) throw new Error();
        const message = JSON.parse(line);
        if (!message.method && pendingPrompts.has(message.id)) {
          const started = pendingPrompts.get(message.id)!;
          pendingPrompts.delete(message.id);
          const stopReason = ['end_turn', 'max_tokens', 'max_turn_requests', 'refusal', 'cancelled'].includes(
            message.result?.stopReason
          )
            ? message.result.stopReason
            : null;
          recordPrompt({
            event: 'prompt_finished',
            durationMs: performance.now() - started,
            stopReason,
            errorCode: Number.isSafeInteger(message.error?.code) ? message.error.code : null,
          });
        }
        if (message.method && message.id !== undefined && message.method !== 'session/request_permission') {
          writeJsonLine(sandboxInput, {
            jsonrpc: '2.0',
            id: message.id,
            error: { code: -32601, message: 'Host access is disabled in isolated mathematics sessions.' },
          });
        } else if (!message.method || ['session/update', 'session/request_permission'].includes(message.method)) {
          writeJsonLine(process.stdout, message);
        }
      } catch {
        void stop(1);
      }
    });
    const inbound = createInterface({ input: process.stdin, crlfDelay: Infinity });
    let queue = Promise.resolve();
    inbound.on('line', (line) => {
      let requestId: string | number | undefined;
      queue = queue
        .then(async () => {
          if (stopping || fatalPolicyRejection || Buffer.byteLength(line) > 32 * 1024 * 1024) throw new Error();
          const message = JSON.parse(line);
          if (typeof message.id === 'string' || typeof message.id === 'number') requestId = message.id;
          if (message.method === 'initialize' && message.params) {
            message.params.clientCapabilities = {
              ...message.params.clientCapabilities,
              fs: { readTextFile: false, writeTextFile: false },
              terminal: false,
            };
          }
          if (['session/new', 'session/load'].includes(message.method)) {
            if (
              message.params?.cwd !== process.cwd() ||
              ((message.method === 'session/new' || message.params?.mcpServers !== undefined) &&
                !Array.isArray(message.params?.mcpServers))
            )
              throw new Error('math_isolation_session_mismatch');
            message.params.mcpServers = await Promise.all((message.params.mcpServers ?? []).map(prepareMcp));
          }
          if (message.method === 'session/prompt') {
            const current = readRegistration();
            if (current.runId !== registration.runId || current.runNonce !== registration.runNonce)
              throw new Error('math_isolation_registration_changed');
            if (!record.namespaces) throw new Error('math_isolation_attestation_missing');
            if (typeof message.id !== 'string' && typeof message.id !== 'number')
              throw new Error('math_isolation_prompt_id_invalid');
            pendingPrompts.set(message.id, performance.now());
            recordPrompt({ event: 'prompt_started' });
          }
          writeJsonLine(sandboxInput, message);
        })
        .catch((): void => {
          fixedError('math_isolation_session_rejected');
          if (requestId !== undefined)
            writeJsonLine(process.stdout, {
              jsonrpc: '2.0',
              id: requestId,
              error: { code: -32092, message: 'Math session rejected by isolation policy.' },
            });
          void stop(1);
        });
    });
  } catch {
    await stop(1);
  }
}

async function main() {
  const args = process.argv.slice(2);
  if (args[0] === '--relay') await isolatedRelay(args[1]);
  else if (args[0] === '--inside') await isolatedInside(args.slice(1));
  else await launchMathModelIsolation(args);
}
if (require.main === module)
  void main().catch((error: unknown) => {
    const code =
      error instanceof Error && /^math_isolation_[a-z_]+$/u.test(error.message)
        ? error.message
        : 'math_model_isolation_failed';
    fixedError(code);
    process.exit(1);
  });
