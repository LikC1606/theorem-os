import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import net from 'node:net';
import { spawn, type ChildProcessWithoutNullStreams } from 'node:child_process';
import { z } from 'zod';
import { assertMathCanonicalPath } from "./mathRunBinding";
import { canonicalMathJson, mathDigest } from "./mathRuntimeIo";
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

/**
 * Host side of the sandbox handoff: verify the descriptor while the host pid is
 * visible, open its root, and return the bwrap arguments that bind that exact
 * directory and the lease socket at fixed sandbox paths. The caller passes the
 * returned fd as child fd 3 and closes it after spawn.
 */
export function openMathProofEnvironmentSandboxBinding(
  projectRoot: string,
  env: NodeJS.ProcessEnv,
  sandboxRoot: string
): Readonly<{ fd: number; args: string[]; mapping: string }> | undefined {
  const encoded = env[MATH_PROOF_ENVIRONMENT_ENV];
  if (encoded === undefined) return undefined;
  const { [MATH_PROOF_ENVIRONMENT_SANDBOX_ENV]: _ignored, ...hostEnv } = env;
  const sealed = resolveMathProofEnvironment(projectRoot, hostEnv)!;
  const descriptor = descriptorSchema.parse(JSON.parse(encoded));
  const fd = fs.openSync(sealed.packagesRoot, fs.constants.O_RDONLY | fs.constants.O_DIRECTORY);
  try {
    const opened = fs.fstatSync(fd, { bigint: true });
    if (!opened.isDirectory() || String(opened.dev) !== descriptor.device || String(opened.ino) !== descriptor.inode)
      throw new Error('Sealed proof environment root changed before sandbox binding.');
    const rootPath = path.posix.join(sandboxRoot, 'proof-environment');
    const leaseSocket = path.posix.join(sandboxRoot, 'proof-environment.sock');
    const mapping = JSON.stringify(
      sandboxMappingSchema.parse({
        schema: 'deepscientist.math.proof-environment-sandbox.v1',
        identity: descriptor.identity,
        rootPath,
        leaseSocket,
      })
    );
    return Object.freeze({
      fd,
      args: ['--ro-bind-fd', '3', rootPath, '--bind', descriptor.leaseSocket, leaseSocket],
      mapping,
    });
  } catch (error) {
    fs.closeSync(fd);
    throw error;
  }
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
    await new Promise<void>((resolve, reject) => {
      let text = '';
      const timer = setTimeout(
        () => finish(new DOMException('Proof environment lease handshake timed out.', 'TimeoutError')),
        Math.max(1, Math.min(5000, deadlineAt === undefined ? 5000 : deadlineAt - Date.now()))
      );
      const abort = () => finish(new DOMException('Proof environment lease cancelled.', 'AbortError'));
      const finish = (error?: Error) => {
        clearTimeout(timer);
        signal?.removeEventListener('abort', abort);
        socket.off('error', fail);
        socket.off('close', closed);
        socket.off('data', data);
        if (error) reject(error);
        else resolve();
      };
      const fail = (error: Error) => finish(error);
      const closed = () => finish(new Error('Proof environment lease closed before acknowledgement.'));
      const data = (chunk: Buffer) => {
        text += chunk.toString();
        if (text.length > 1024) return finish(new Error('Invalid proof environment lease acknowledgement.'));
        if (!text.includes('\n')) return;
        try {
          if (JSON.parse(text.slice(0, text.indexOf('\n'))).ok !== true) throw new Error();
          finish();
        } catch {
          finish(new Error('Proof environment lease was rejected.'));
        }
      };
      socket.once('connect', () => socket.write(`${JSON.stringify({ token: descriptor.leaseToken })}\n`));
      socket.on('error', fail);
      socket.on('close', closed);
      socket.on('data', data);
      signal?.addEventListener('abort', abort, { once: true });
      if (signal?.aborted) abort();
    });
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
export async function prepareMathProofEnvironment(
  projectRoot: string,
  authorizedPackagesRoot: string,
  options: Readonly<{
    env?: NodeJS.ProcessEnv;
    signal?: AbortSignal;
    deadlineAt?: number;
    cacheRoot?: string;
    onProgress?: (phase: string, details: Readonly<Record<string, number | boolean>>) => void;
  }> = {}
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
  const cached = fingerprint ? cache?.read(fingerprint) : undefined;
  report(cached ? 'cache_hit' : 'cache_miss', { files: inputs.length, bytes, cacheHit: Boolean(cached) });
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
  let disposed = false;
  let published = false;
  const exportedImage = cache && fingerprint && !cached ? cache.createImagePath(fingerprint) : undefined;
  const dispose = async () => {
    if (disposed) return;
    disposed = true;
    if (child && child.exitCode === null && child.signalCode === null) {
      const stopped = new Promise<void>((resolve) => child!.once('close', () => resolve()));
      child.stdin.end();
      if (!published) child.kill('SIGTERM');
      await stopped;
    }
    fs.rmSync(temporary, { recursive: true, force: true });
    if (!published && exportedImage) fs.rmSync(exportedImage, { force: true });
  };
  try {
    const files: { path: string; digest: string; identity: string; mode: number }[] = [];
    for (const [index, input] of (cached ? [] : inputs).entries()) {
      report('copying_dependencies', { files: index, bytes });
      const target = path.join(source, input.relative);
      const copied = readLeanProbeSnapshotFile(input.source, checkpoint, target);
      const times = fs.statSync(input.source);
      fs.utimesSync(target, times.atime, times.mtime);
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
        const current = readLeanProbeSnapshotFile(input.source, checkpoint);
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
        stdio: ['pipe', 'pipe', 'pipe'],
      }
    );
    const ready = await new Promise<Record<string, unknown>>((resolve, reject) => {
      let output = '';
      let settled = false;
      const abort = () => finish(new Error('Proof environment preparation cancelled.'));
      const timer =
        options.deadlineAt === undefined
          ? undefined
          : setTimeout(
              () => finish(new Error('Proof environment preparation deadline exceeded.')),
              Math.max(1, options.deadlineAt - Date.now())
            );
      const heartbeat = setInterval(
        () =>
          report(cached ? 'mounting_cached_image' : 'building_image', {
            cacheHit: Boolean(cached),
          }),
        5000
      );
      const finish = (error?: Error, value?: Record<string, unknown>) => {
        if (settled) return;
        settled = true;
        if (timer) clearTimeout(timer);
        clearInterval(heartbeat);
        options.signal?.removeEventListener('abort', abort);
        child!.stdout.off('data', data);
        child!.off('error', failed);
        child!.off('exit', exited);
        // Continue draining any shutdown diagnostics without retaining contents.
        child!.stdout.resume();
        if (error) reject(error);
        else resolve(value!);
      };
      const failed = (error: Error) => finish(error);
      const exited = () => finish(new Error('Proof environment helper exited before readiness.'));
      const data = (chunk: Buffer) => {
        output += chunk.toString();
        if (output.length > 64 * 1024) return finish(new Error('Invalid proof environment helper response.'));
        const newline = output.indexOf('\n');
        if (newline < 0) return;
        try {
          const value = JSON.parse(output.slice(0, newline));
          if (value.state !== 'ready') {
            const message = String(value.error ?? '');
            const reason =
              [
                'requires Linux',
                'insufficient available disk',
                'requires squashfuse, fusermount, and mksquashfs',
                'mksquashfs failed',
                'squashfuse failed',
                'could not detach immutable mount',
                'image is not squashfs',
                'cached image digest changed',
              ].find((known) => message.includes(known)) ?? 'helper failed before publication';
            return finish(new Error(`Proof environment blocked: ${reason}.`));
          }
          finish(undefined, value);
        } catch {
          finish(new Error('Invalid proof environment helper response.'));
        }
      };
      child!.stdout.on('data', data);
      child!.stderr.resume();
      child!.once('error', failed);
      child!.once('exit', exited);
      options.signal?.addEventListener('abort', abort, { once: true });
      if (options.signal?.aborted) abort();
    });
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
    const buffer = Buffer.alloc(1024 * 1024);
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
      return prepareMathProofEnvironment(projectRoot, authorizedPackagesRoot, options);
    }
    throw error;
  }
}
