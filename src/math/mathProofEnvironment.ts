import fs from 'node:fs';
import { closeMathProcess } from './mathProcess';
import path from 'node:path';
import crypto from 'node:crypto';
import net from 'node:net';
import { setTimeout as delay } from 'node:timers/promises';
import { parse as parseToml } from 'smol-toml';
import { spawn, spawnSync, type ChildProcessWithoutNullStreams } from 'node:child_process';
import { z } from 'zod';
import { assertMathCanonicalPath } from "./paths";
import { canonicalMathJson, mathDigest, readMathFile, withMathRuntimeLease } from "./mathRuntimeIo";
import { listLeanProbePackageInputs, readLeanProbeSnapshotFile } from "./leanProbeSnapshot";
import { MATH_SEALED_ENVIRONMENT_HELPER } from "./mathSealedEnvironmentHelper";
import { openMathProofEnvironmentCache } from "./mathProofEnvironmentCache";

/** Host-generated reference, retained in the existing frozen run environment. */
export const MATH_PROOF_ENVIRONMENT_ENV = 'DEEPSCIENTIST_MATH_PROOF_ENVIRONMENT';
/**
 * Set only by the host isolation launcher. An isolated MCP runs in its own PID
 * namespace, where the descriptor's host pid and /proc/<pid>/fd root do not
 * exist, so every lean_workspace call returned unavailable (run 23). The
 * launcher verifies the descriptor on the host, then binds the already opened
 * root and the lease socket into the sandbox and names them here.
 */
export const MATH_PROOF_ENVIRONMENT_SANDBOX_ENV = 'DEEPSCIENTIST_MATH_PROOF_ENVIRONMENT_SANDBOX';
const METADATA = '.deepscientist-proof-environment.json';
const CONFIG_FILES = [
  'lean-toolchain',
  'lakefile.toml',
  'lakefile.lean',
  'lake-manifest.json',
  '.lake/package-overrides.json',
];
const hash = z.string().regex(/^[a-f0-9]{64}$/u);
const statistics = z
  .object({ files: z.number().int().nonnegative(), bytes: z.number().int().nonnegative(), publications: z.literal(1) })
  .strict();
const descriptorSchema = z
  .object({
    schema: z.literal('deepscientist.math.proof-environment.v1'),
    pid: z.number().int().positive(),
    rootFd: z.number().int().nonnegative(),
    rootPath: z.string(),
    device: z.string(),
    inode: z.string(),
    startTime: z.string(),
    imageSha256: hash,
    imageBytes: z.number().int().positive(),
    seals: z.union([z.literal(0), z.literal(15)]),
    metadataHash: hash,
    identity: hash,
    stats: statistics,
    leaseSocket: z.string().min(1),
    leaseToken: z.string().min(16),
  })
  .strict();
const sandboxMappingSchema = z
  .object({
    schema: z.literal('deepscientist.math.proof-environment-sandbox.v1'),
    identity: hash,
    rootPath: z.string().startsWith('/'),
    leaseSocket: z.string().startsWith('/'),
  })
  .strict();

/** The mapping applies only to the exact descriptor it was created for. */
function readSandboxMapping(
  descriptor: z.infer<typeof descriptorSchema>,
  env: NodeJS.ProcessEnv
): z.infer<typeof sandboxMappingSchema> | undefined {
  const encoded = env[MATH_PROOF_ENVIRONMENT_SANDBOX_ENV] ?? process.env[MATH_PROOF_ENVIRONMENT_SANDBOX_ENV];
  if (!encoded) return undefined;
  const mapping = sandboxMappingSchema.parse(JSON.parse(encoded));
  return mapping.identity === descriptor.identity ? mapping : undefined;
}

const metadataSchema = z
  .object({
    schema: z.literal('deepscientist.math.proof-environment-inputs.v1'),
    sourceCacheRoot: z.string(),
    config: z.record(z.string(), hash.nullable()),
    sourceIdentity: hash,
    stats: statistics,
  })
  .strict();

function proofEnvironmentBlocked(message: unknown): Error {
  const reason = [
    'requires Linux',
    'insufficient available disk',
    'requires squashfuse, fusermount, and mksquashfs',
    'mksquashfs failed',
    'squashfuse failed',
    'could not detach immutable mount',
    'image is not squashfs',
    'cached image digest changed',
  ].find(known => String(message ?? '').includes(known)) ?? 'helper failed before publication';
  return new Error(`Proof environment blocked: ${reason}.`);
}
type JsonLineRead<T> = Readonly<{ data: NodeJS.EventEmitter; owner: NodeJS.EventEmitter; end: 'close' | 'exit'; limit: number;
  timeoutMs?: number; signal?: AbortSignal; timedOut: () => Error; aborted: () => Error; ended: string; invalid: string;
  accept: (value: Record<string, unknown> | null) => T }>;

/** First newline-terminated JSON value on `data`; every outcome detaches the listeners, timer and abort hook it added. */
function readJsonLine<T>(read: JsonLineRead<T>): Promise<T> {
  return new Promise<T>((resolve, reject) => {
    let text = '', settled = false;
    const finish = (error?: Error, value?: T) => {
      if (settled) return;
      settled = true;
      clearTimeout(timer);
      read.signal?.removeEventListener('abort', aborted);
      read.data.off('data', data);
      read.owner.off('error', finish).off(read.end, ended);
      if (error) reject(error); else resolve(value!);
    };
    const ended = () => finish(new Error(read.ended)), aborted = () => finish(read.aborted());
    const timer = read.timeoutMs === undefined ? undefined : setTimeout(() => finish(read.timedOut()), read.timeoutMs);
    const data = (chunk: Buffer) => {
      text += chunk.toString();
      if (text.length > read.limit) return finish(new Error(read.invalid));
      const newline = text.indexOf('\n');
      if (newline < 0) return;
      let value: Record<string, unknown> | null;
      try { value = JSON.parse(text.slice(0, newline)); } catch { return finish(new Error(read.invalid)); }
      try { finish(undefined, read.accept(value)); } catch (error) { finish(error as Error); }
    };
    read.data.on('data', data);
    read.owner.on('error', finish).on(read.end, ended);
    read.signal?.addEventListener('abort', aborted, { once: true });
    if (read.signal?.aborted) aborted();
  });
}
export type MathProofEnvironment = Readonly<{
  packagesRoot: string;
  identity: string;
  stats: z.infer<typeof statistics>;
  verify: () => void;
}>;

function processStartTime(pid: number): string {
  const value = fs.readFileSync(`/proc/${pid}/stat`, 'utf8');
  const fields = value
    .slice(value.lastIndexOf(')') + 2)
    .trim()
    .split(/\s+/u);
  if (!fields[19] || fields[0] === 'Z') throw new Error('Sealed proof environment process is unavailable.');
  return fields[19];
}

function consumerConfiguration(config: Record<string, string | null>): Record<string, string | null> {
  // Sandbox execution mounts host-generated path overrides when using sealed
  // packages. Preserve the source override in provenance, but detached consumers
  // need only match the configuration actually used by that sandbox.
  const { ['.lake/package-overrides.json']: _sourceOverride, ...consumed } = config;
  return consumed;
}

function projectConfiguration(root: string): Record<string, string | null> {
  assertMathCanonicalPath(root);
  return Object.fromEntries(
    CONFIG_FILES.map((relative) => {
      const file = path.join(root, relative);
      try {
        if (relative === 'lakefile.toml' || relative === 'lake-manifest.json') {
          // The root package label does not change the dependency payload. Keep every
          // other option and pinned revision bound, including nested package names.
          const text = readMathFile(file, 16 * 1024 * 1024).bytes.toString('utf8');
          const { name: _name, ...configuration } = relative.endsWith('.toml') ? parseToml(text) : JSON.parse(text);
          return [relative, mathDigest(canonicalMathJson(configuration))];
        }
        return [relative, readLeanProbeSnapshotFile(file, () => {}).digest];
      } catch (error) {
        if ((error as NodeJS.ErrnoException).code === 'ENOENT') return [relative, null];
        throw error;
      }
    })
  );
}

/** Validate an already host-bound reference. Never discover or silently replace a dead base. */
export function resolveMathProofEnvironment(
  projectRoot: string,
  env: NodeJS.ProcessEnv = process.env
): MathProofEnvironment | undefined {
  const encoded = env[MATH_PROOF_ENVIRONMENT_ENV];
  if (encoded === undefined) return undefined;
  const descriptor = descriptorSchema.parse(JSON.parse(encoded));
  const hostPath = `/proc/${descriptor.pid}/fd/${descriptor.rootFd}`;
  if (descriptor.rootPath !== hostPath) throw new Error('Sealed proof environment descriptor is invalid.');
  const mapping = readSandboxMapping(descriptor, env);
  // Inside the isolation sandbox the host pid is invisible; the launcher already
  // checked it on the host. The mapped root must still be the same sealed mount
  // (device, inode, metadata and project configuration are verified below).
  const expectedPath = mapping?.rootPath ?? hostPath;
  const verify = () => {
    if (!mapping && processStartTime(descriptor.pid) !== descriptor.startTime)
      throw new Error('Sealed proof environment process identity changed.');
    const stat = fs.statSync(expectedPath, { bigint: true });
    if (!stat.isDirectory() || String(stat.dev) !== descriptor.device || String(stat.ino) !== descriptor.inode)
      throw new Error('Sealed proof environment root identity changed.');
    const bytes = fs.readFileSync(path.join(expectedPath, METADATA));
    if (mathDigest(bytes) !== descriptor.metadataHash) throw new Error('Sealed proof environment metadata changed.');
    const metadata = metadataSchema.parse(JSON.parse(bytes.toString('utf8')));
    if (
      canonicalMathJson(consumerConfiguration(metadata.config)) !==
      canonicalMathJson(consumerConfiguration(projectConfiguration(projectRoot)))
    )
      throw new Error('Sealed proof environment does not match the project configuration.');
    if (
      canonicalMathJson(metadata.stats) !== canonicalMathJson(descriptor.stats) ||
      mathDigest(canonicalMathJson({ metadataHash: descriptor.metadataHash, imageSha256: descriptor.imageSha256 })) !==
        descriptor.identity
    )
      throw new Error('Sealed proof environment binding changed.');
  };
  verify();
  return Object.freeze({
    packagesRoot: expectedPath,
    identity: descriptor.identity,
    stats: Object.freeze(descriptor.stats),
    verify,
  });
}

/** Codex mounts the host filesystem read-only but replaces /proc in its PID namespace. */
export function mathProofEnvironmentWorkerEnvironment(projectRoot: string, env: NodeJS.ProcessEnv): NodeJS.ProcessEnv {
  const environment = resolveMathProofEnvironment(projectRoot, env);
  if (!environment) return env;
  const descriptor = descriptorSchema.parse(JSON.parse(env[MATH_PROOF_ENVIRONMENT_ENV]!));
  const mapped = { ...env, [MATH_PROOF_ENVIRONMENT_SANDBOX_ENV]: JSON.stringify({
    schema: 'deepscientist.math.proof-environment-sandbox.v1',
    identity: environment.identity,
    rootPath: fs.realpathSync(environment.packagesRoot),
    leaseSocket: descriptor.leaseSocket,
  }) };
  // The attached path must still name the exact verified immutable root.
  resolveMathProofEnvironment(projectRoot, mapped);
  return mapped;
}

/** A live socket pins the helper and base across sandbox execution and owner shutdown. */
export async function acquireMathProofEnvironmentLease(
  projectRoot: string,
  env: NodeJS.ProcessEnv = process.env,
  signal?: AbortSignal,
  deadlineAt?: number
): Promise<Readonly<{ packagesRoot: string; release: () => Promise<void> }> | undefined> {
  const environment = resolveMathProofEnvironment(projectRoot, env);
  if (!environment) return undefined;
  signal?.throwIfAborted();
  if (deadlineAt !== undefined && Date.now() >= deadlineAt)
    throw new DOMException('Proof environment lease deadline exceeded.', 'TimeoutError');
  const descriptor = descriptorSchema.parse(JSON.parse(env[MATH_PROOF_ENVIRONMENT_ENV]!));
  const socket = net.createConnection(readSandboxMapping(descriptor, env)?.leaseSocket ?? descriptor.leaseSocket);
  try {
    socket.once('connect', () => socket.write(`${JSON.stringify({ token: descriptor.leaseToken })}\n`));
    await readJsonLine({ data: socket, owner: socket, end: 'close', limit: 1024, signal,
      timeoutMs: Math.max(1, Math.min(5000, deadlineAt === undefined ? 5000 : deadlineAt - Date.now())),
      timedOut: () => new DOMException('Proof environment lease handshake timed out.', 'TimeoutError'),
      aborted: () => new DOMException('Proof environment lease cancelled.', 'AbortError'),
      ended: 'Proof environment lease closed before acknowledgement.', invalid: 'Invalid proof environment lease acknowledgement.',
      accept: value => { if (value?.ok !== true) throw new Error('Proof environment lease was rejected.'); } });
    environment.verify();
    signal?.throwIfAborted();
    socket.on('error', () => {});
    return Object.freeze({
      packagesRoot: environment.packagesRoot,
      release: async () => {
        if (socket.destroyed) return;
        const closed = new Promise<void>((resolve) => socket.once('close', () => resolve()));
        socket.destroy();
        await closed;
      },
    });
  } catch (error) {
    socket.destroy();
    throw error;
  }
}

/** Once per new run; callers authorize the source cache against the pinned manifest first. */
type PreparationOptions = Readonly<{
  env?: NodeJS.ProcessEnv;
  signal?: AbortSignal;
  deadlineAt?: number;
  cacheRoot?: string;
  onProgress?: (phase: string, details: Readonly<Record<string, number | boolean>>) => void;
}>;

export function prepareMathProofEnvironment(projectRoot: string, authorizedPackagesRoot: string, options: PreparationOptions = {}) {
  return prepareEnvironment(projectRoot, authorizedPackagesRoot, options);
}

async function prepareEnvironment(
  projectRoot: string,
  authorizedPackagesRoot: string,
  options: PreparationOptions,
  lockedFingerprint?: string
): Promise<Readonly<{ environmentValue: string; dispose: () => Promise<void>; stats: z.infer<typeof statistics> }>> {
  const checkpoint = () => {
    options.signal?.throwIfAborted();
    if (options.deadlineAt !== undefined && Date.now() >= options.deadlineAt)
      throw new Error('Sealed proof environment preparation deadline exceeded.');
  };
  checkpoint();
  const started = Date.now();
  let lastProgress = 0;
  let previousPhase = '';
  const report = (phase: string, details: Record<string, number | boolean> = {}) => {
    if (phase !== previousPhase || Date.now() - lastProgress >= 1000) {
      options.onProgress?.(phase, { elapsedMs: Date.now() - started, ...details });
      previousPhase = phase;
      lastProgress = Date.now();
    }
  };
  assertMathCanonicalPath(authorizedPackagesRoot);
  report('enumerating_dependencies');
  const config = projectConfiguration(projectRoot);
  const inputs = listLeanProbePackageInputs(authorizedPackagesRoot, checkpoint);
  if (inputs.some((input) => input.relative === METADATA)) throw new Error('Reserved proof environment metadata path.');
  if (
    inputs.some(
      ({ relative }) =>
        path.isAbsolute(relative) ||
        relative.split(/[\\/]/u).some((part) => !part || part === '.' || part === '..' || part === 'Solution.lean')
    )
  )
    throw new Error('Lean probe snapshot contains an unauthorized path.');
  const bytes = inputs.reduce((sum, input) => sum + fs.statSync(input.source).size, 0);
  const sourceFingerprint = (
    packageInputs = listLeanProbePackageInputs(authorizedPackagesRoot, checkpoint),
    configuration = projectConfiguration(projectRoot)
  ) =>
    mathDigest(
      canonicalMathJson({
        helper: mathDigest(MATH_SEALED_ENVIRONMENT_HELPER),
        sourceCacheRoot: authorizedPackagesRoot,
        config: configuration,
        inputs: packageInputs.map((input) => ({
          ...input,
          // links already contains each link's path, metadata, and target.
          identities: [input.source].map((file) => {
            checkpoint();
            const stat = fs.lstatSync(file, { bigint: true });
            return [stat.dev, stat.ino, stat.size, stat.mode, stat.mtimeNs, stat.ctimeNs].map(String);
          }),
        })),
      })
    );
  const cache = options.cacheRoot ? openMathProofEnvironmentCache(options.cacheRoot) : undefined;
  // Reuse the inventory just checked above. The final fingerprint still takes
  // a fresh inventory, including links and project configuration, before use.
  const fingerprint = cache ? sourceFingerprint(inputs, config) : undefined;
  if (lockedFingerprint && fingerprint !== lockedFingerprint)
    throw new Error('Proof environment dependency changed while waiting for preparation.');
  const cached = fingerprint ? cache?.read(fingerprint) : undefined;
  if (cache && fingerprint && !cached && !lockedFingerprint) {
    // Independent problem processes share one build; each still opens its own
    // immutable image and verifies its project and source identity afterward.
    for (;;) {
      checkpoint();
      try {
        return await withMathRuntimeLease({ lockPath: path.join(options.cacheRoot!, `${fingerprint}.lock`),
          flockExecutable: '/usr/bin/flock', signal: options.signal },
        () => prepareEnvironment(projectRoot, authorizedPackagesRoot, options, fingerprint));
      } catch (error) {
        if (!(error instanceof Error) || error.message !== 'math_runtime_lease_busy') throw error;
        report('waiting_for_cached_image');
        await delay(1000, undefined, { signal: options.signal });
      }
    }
  }
  report(cached ? 'cache_hit' : 'cache_miss', { files: inputs.length, bytes, cacheHit: Boolean(cached) });
  const preflight = spawnSync('/usr/bin/python3', [
    '-c', MATH_SEALED_ENVIRONMENT_HELPER, '--check-tools', cached ? 'mount' : 'build',
  ], {
    env: options.env ?? process.env, encoding: 'utf8', maxBuffer: 4096,
    timeout: Math.max(1, Math.min(5000, (options.deadlineAt ?? Infinity) - Date.now())),
  });
  let readiness: { state?: unknown; error?: unknown } | null;
  try { readiness = JSON.parse(preflight.stdout || ''); }
  catch { throw proofEnvironmentBlocked(undefined); }
  if (preflight.error || preflight.status !== 0 || readiness?.state !== 'ready')
    throw proofEnvironmentBlocked(readiness?.error);
  checkpoint();
  // Source staging and its immutable disk image may coexist. This is a preparation
  // resource check, independent from the unchanged private editable-source quota.
  const capacity = fs.statfsSync('/var/tmp', { bigint: true });
  const requiredBytes = cached ? BigInt(cached.imageBytes) : BigInt(bytes) * BigInt(cache ? 3 : 2);
  if (requiredBytes + BigInt(64 * 1024 * 1024) > capacity.bavail * capacity.bsize)
    throw new Error('Insufficient disk capacity for complete proof environment preparation.');
  const temporary = fs.realpathSync(fs.mkdtempSync(path.join('/var/tmp', 'math-proof-environment-')));
  const source = path.join(temporary, 'packages');
  fs.mkdirSync(source, { mode: 0o700 });
  let child: ChildProcessWithoutNullStreams | undefined;
  let disposal: Promise<void> | undefined;
  let published = false;
  const exportedImage = cache && fingerprint && !cached ? cache.createImagePath(fingerprint) : undefined;
  const dispose = () => disposal ??= (async () => {
    if (child) await closeMathProcess(child, published);
    fs.rmSync(temporary, { recursive: true, force: true });
    if (!published && exportedImage) fs.rmSync(exportedImage, { force: true });
  })();
  try {
    const buffer = Buffer.alloc(1024 * 1024);
    const readInput = (file: string, target?: string) =>
      readLeanProbeSnapshotFile(file, checkpoint, target, buffer);
    const files: { path: string; digest: string; identity: string; mode: number }[] = [];
    for (const [index, input] of (cached ? [] : inputs).entries()) {
      report('copying_dependencies', { files: index, bytes });
      const target = path.join(source, input.relative);
      const copied = readInput(input.source, target);
      files.push({ path: input.relative, digest: copied.digest, identity: copied.identity, mode: copied.mode });
      if (index % 64 === 0) await new Promise<void>((resolve) => setImmediate(resolve));
    }
    const stats = cached?.stats ?? { files: files.length, bytes, publications: 1 as const };
    const verifySource = async () => {
      if (
        canonicalMathJson(listLeanProbePackageInputs(authorizedPackagesRoot, checkpoint)) !== canonicalMathJson(inputs)
      )
        throw new Error('Proof environment dependency set changed during preparation.');
      for (const [index, input] of inputs.entries()) {
        report('verifying_source', { files: index, bytes });
        const current = readInput(input.source);
        if (current.digest !== files[index].digest || current.identity !== files[index].identity)
          throw new Error('Proof environment dependency changed during preparation.');
        if (index % 64 === 0) await new Promise<void>((resolve) => setImmediate(resolve));
      }
      if (canonicalMathJson(projectConfiguration(projectRoot)) !== canonicalMathJson(config))
        throw new Error('Proof environment project configuration changed during preparation.');
    };
    const metadataBytes = Buffer.from(
      canonicalMathJson({
        schema: 'deepscientist.math.proof-environment-inputs.v1',
        sourceCacheRoot: authorizedPackagesRoot,
        config,
        sourceIdentity: mathDigest(canonicalMathJson(files)),
        stats,
      })
    );
    if (!cached) {
      fs.writeFileSync(path.join(source, METADATA), metadataBytes, { flag: 'wx', mode: 0o400 });
      report('verifying_source', { files: files.length, bytes });
      await verifySource();
    }
    checkpoint();
    report(cached ? 'mounting_cached_image' : 'building_image', { cacheHit: Boolean(cached) });
    child = spawn(
      '/usr/bin/python3',
      [
        '-c',
        MATH_SEALED_ENVIRONMENT_HELPER,
        ...(cached
          ? ['--image', cache!.imagePath(cached), '--expected-image-sha256', cached.imageSha256]
          : ['--source', source, ...(exportedImage ? ['--export-image', exportedImage] : [])]),
      ],
      {
        env: options.env ?? process.env,
        detached: process.platform !== 'win32',
        stdio: ['pipe', 'pipe', 'pipe'],
      }
    );
    // Heartbeats keep long image builds visible; stdout keeps draining shutdown diagnostics without retaining them.
    const heartbeat = setInterval(() => report(cached ? 'mounting_cached_image' : 'building_image', { cacheHit: Boolean(cached) }), 5000);
    child.stderr.resume();
    const ready = await readJsonLine({ data: child.stdout, owner: child, end: 'exit', limit: 64 * 1024, signal: options.signal,
      timeoutMs: options.deadlineAt === undefined ? undefined : Math.max(1, options.deadlineAt - Date.now()),
      timedOut: () => new Error('Proof environment preparation deadline exceeded.'),
      aborted: () => new Error('Proof environment preparation cancelled.'),
      ended: 'Proof environment helper exited before readiness.', invalid: 'Invalid proof environment helper response.',
      accept: value => { if (value?.state !== 'ready') throw proofEnvironmentBlocked(value?.error); return value; },
    }).finally(() => { clearInterval(heartbeat); child!.stdout.resume(); });
    checkpoint();
    if (ready.pid !== child.pid)
      throw new Error('Proof environment helper process identity does not match its launcher.');
    const metadataHash = cached?.metadataHash ?? mathDigest(metadataBytes);
    if (cached && (ready.imageSha256 !== cached.imageSha256 || ready.imageBytes !== cached.imageBytes))
      throw new Error('Cached proof environment image changed.');
    const descriptor = descriptorSchema.parse({
      schema: 'deepscientist.math.proof-environment.v1',
      pid: ready.pid,
      rootFd: ready.rootFd,
      rootPath: ready.rootPath,
      device: String(ready.device),
      inode: String(ready.inode),
      startTime: processStartTime(Number(ready.pid)),
      imageSha256: ready.imageSha256,
      imageBytes: ready.imageBytes,
      seals: ready.seals,
      metadataHash,
      identity: mathDigest(canonicalMathJson({ metadataHash, imageSha256: ready.imageSha256 })),
      stats,
      leaseSocket: ready.leaseSocket,
      leaseToken: ready.leaseToken,
    });
    const environmentValue = JSON.stringify(descriptor);
    const sealed = resolveMathProofEnvironment(projectRoot, { [MATH_PROOF_ENVIRONMENT_ENV]: environmentValue })!;
    // The staging directory is not an authority. Verify the actual immutable
    // mounted bytes against the complete source manifest before publication.
    const sealedPaths: string[] = [];
    const visitSealed = (relative: string) => {
      checkpoint();
      const directory = path.join(sealed.packagesRoot, relative);
      for (const entry of fs.readdirSync(directory, { withFileTypes: true })) {
        const name = path.join(relative, entry.name);
        if (entry.isDirectory()) visitSealed(name);
        else if (entry.isFile()) {
          if (name !== METADATA) sealedPaths.push(name);
        } else throw new Error('Sealed proof environment contains an unexpected path kind.');
      }
    };
    if (!cached) visitSealed('');
    if (
      !cached &&
      canonicalMathJson(sealedPaths.toSorted()) !== canonicalMathJson(files.map((file) => file.path).toSorted())
    )
      throw new Error('Sealed proof environment input set differs from the authorized source.');
    for (const [index, file] of files.entries()) {
      report('verifying_mounted_dependencies', { files: index, bytes });
      const fd = fs.openSync(
        path.join(sealed.packagesRoot, file.path),
        fs.constants.O_RDONLY | fs.constants.O_NOFOLLOW
      );
      try {
        const sealedMode = fs.fstatSync(fd).mode & 0o777;
        if (sealedMode !== (0o400 | (file.mode & 0o111)))
          throw new Error('Sealed proof environment executable permissions differ from the authorized source.');
        const digest = crypto.createHash('sha256');
        for (let size = fs.readSync(fd, buffer); size; size = fs.readSync(fd, buffer)) {
          checkpoint();
          digest.update(buffer.subarray(0, size));
        }
        if (digest.digest('hex') !== file.digest)
          throw new Error('Sealed proof environment bytes differ from the authorized source.');
      } finally {
        fs.closeSync(fd);
      }
      if (index % 64 === 0) await new Promise<void>((resolve) => setImmediate(resolve));
    }
    sealed.verify();
    if (cached) {
      report('verifying_cache_identity', { files: inputs.length, bytes });
    } else {
      report('verifying_source', { files: files.length, bytes });
      await verifySource();
    }
    if (fingerprint && sourceFingerprint() !== fingerprint)
      throw new Error('Proof environment dependency changed during preparation.');
    checkpoint();
    if (cache && fingerprint && exportedImage)
      cache.publish({
        schema: 'deepscientist.math.proof-environment-cache.v1',
        fingerprint,
        imageName: path.basename(exportedImage),
        imageSha256: descriptor.imageSha256,
        imageBytes: descriptor.imageBytes,
        metadataHash,
        stats,
      });
    fs.rmSync(temporary, { recursive: true, force: true });
    published = true;
    report('ready', { files: stats.files, bytes, cacheHit: Boolean(cached) });
    return Object.freeze({ environmentValue, dispose, stats: Object.freeze(stats) });
  } catch (error) {
    await dispose();
    if (
      cached &&
      cache &&
      fingerprint &&
      error instanceof Error &&
      /cached image digest changed|Cached proof environment image changed|image is not squashfs/u.test(error.message)
    ) {
      cache.invalidate(fingerprint);
      report('cache_invalidated');
      return prepareEnvironment(projectRoot, authorizedPackagesRoot, options, lockedFingerprint);
    }
    throw error;
  }
}
