import crypto from 'node:crypto';
import fs from 'node:fs';
import path from 'node:path';
import { spawn } from 'node:child_process';

/** Content-addressed proof-session records, never Lean source or arbitrary drafts. */
export const isMathWorkerProofRuntimeRecordPath = (relative: string): boolean =>
  /^\.deepscientist\/math\/worker-proof\/[a-f0-9]{64}(?:(?:\.branch-[a-f0-9]{64}|\.identity|\.branches\.index)?\.json|\.(?:actions|attempts|observations)\.jsonl)$/u.test(
    relative
  );

const normalizeJson = (item: unknown): unknown => {
  if (Array.isArray(item)) return item.map(normalizeJson);
  if (item && typeof item === 'object') {
    const prototype = Object.getPrototypeOf(item);
    if (prototype !== Object.prototype && prototype !== null) throw new Error('math_runtime_invalid_json');
    return Object.fromEntries(
      Object.entries(item)
        .filter(([, entry]) => entry !== undefined)
        .toSorted(([a], [b]) => (a < b ? -1 : a > b ? 1 : 0))
        .map(([key, entry]) => [key, normalizeJson(entry)])
    );
  }
  if (
    item === null ||
    typeof item === 'string' ||
    typeof item === 'boolean' ||
    (typeof item === 'number' && Number.isFinite(item))
  )
    return item;
  throw new Error('math_runtime_invalid_json');
};

export function canonicalMathJson(value: unknown): string {
  return JSON.stringify(normalizeJson(value));
}

export const mathDigest = (value: string | Uint8Array): string =>
  crypto.createHash('sha256').update(value).digest('hex');

export function syncMathDirectory(directory: string): void {
  const descriptor = fs.openSync(directory, fs.constants.O_RDONLY | fs.constants.O_DIRECTORY | fs.constants.O_NOFOLLOW);
  try {
    fs.fsyncSync(descriptor);
  } finally {
    fs.closeSync(descriptor);
  }
}

/** Directory must already be a validated runtime-owned directory. */
export function writeMathJsonDurable(file: string, value: unknown, mode: 0o600 | 0o400 = 0o600): void {
  const temporary = `${file}.${crypto.randomUUID()}.tmp`;
  const descriptor = fs.openSync(
    temporary,
    fs.constants.O_CREAT | fs.constants.O_EXCL | fs.constants.O_WRONLY | fs.constants.O_NOFOLLOW,
    0o600
  );
  try {
    fs.writeFileSync(descriptor, canonicalMathJson(value), 'utf8');
    fs.fchmodSync(descriptor, mode);
    fs.fsyncSync(descriptor);
  } finally {
    fs.closeSync(descriptor);
  }
  // On failure retain the temporary file as diagnostic evidence, not a successful commit.
  fs.renameSync(temporary, file);
  syncMathDirectory(path.dirname(file));
}

export function readMathJson(file: string): unknown {
  const descriptor = fs.openSync(file, fs.constants.O_RDONLY | fs.constants.O_NOFOLLOW | fs.constants.O_NONBLOCK);
  try {
    const before = fs.fstatSync(descriptor, { bigint: true });
    if (!before.isFile() || before.nlink !== BigInt(1)) throw new Error('math_runtime_integrity');
    const value = new TextDecoder('utf-8', { fatal: true }).decode(fs.readFileSync(descriptor));
    const after = fs.fstatSync(descriptor, { bigint: true });
    const current = fs.lstatSync(file, { bigint: true });
    if (
      before.size !== after.size ||
      before.mtimeNs !== after.mtimeNs ||
      before.ctimeNs !== after.ctimeNs ||
      current.dev !== before.dev ||
      current.ino !== before.ino
    )
      throw new Error('math_runtime_integrity');
    return JSON.parse(value);
  } finally {
    fs.closeSync(descriptor);
  }
}

export type MathLease = Readonly<{
  signal: AbortSignal;
  assertHeld: () => void;
  /** Explicitly inherit only into a runtime-owned supervisor that must outlive its caller. */
  inheritedDescriptor: number;
}>;

/** flock locks an inherited open-file description; this process retains it until the operation ends. */
export async function withMathRuntimeLease<T>(
  input: Readonly<{
    lockPath: string;
    flockExecutable: string;
    shared?: boolean;
    signal?: AbortSignal;
  }>,
  operation: (lease: MathLease) => Promise<T>
): Promise<T> {
  if (process.platform !== 'linux') throw new Error('math_runtime_os_lease_unavailable');
  if (input.signal?.aborted) throw new Error('math_runtime_aborted');
  const directory = path.dirname(input.lockPath);
  if (fs.realpathSync(directory) !== directory || !fs.lstatSync(directory).isDirectory())
    throw new Error('math_runtime_integrity');
  const descriptor = fs.openSync(
    input.lockPath,
    fs.constants.O_CREAT | fs.constants.O_RDWR | fs.constants.O_NOFOLLOW,
    0o600
  );
  const lockStat = fs.fstatSync(descriptor);
  if (!lockStat.isFile() || lockStat.nlink !== 1 || (lockStat.mode & 0o777) !== 0o600) {
    fs.closeSync(descriptor);
    throw new Error('math_runtime_integrity');
  }
  const controller = new AbortController();
  const abort = (): void => controller.abort();
  input.signal?.addEventListener('abort', abort, { once: true });
  try {
    await new Promise<void>((resolve, reject) => {
      const child = spawn(
        input.flockExecutable,
        [input.shared ? '--shared' : '--exclusive', '--nonblock', '--conflict-exit-code', '73', '3'],
        { stdio: ['ignore', 'ignore', 'ignore', descriptor], windowsHide: true }
      );
      let spawnFailed = false;
      child.once('error', () => {
        spawnFailed = true;
      });
      const timeout = setTimeout(() => {
        child.kill('SIGKILL');
      }, 10_000);
      child.once('close', (code) => {
        clearTimeout(timeout);
        if (!spawnFailed && code === 0) resolve();
        else reject(new Error(code === 73 ? 'math_runtime_lease_busy' : 'math_runtime_os_lease_unavailable'));
      });
    });
    const assertHeld = (): void => {
      if (controller.signal.aborted || input.signal?.aborted) throw new Error('math_runtime_lease_lost');
      const current = fs.lstatSync(input.lockPath);
      if (current.dev !== lockStat.dev || current.ino !== lockStat.ino || current.nlink !== 1 || !current.isFile())
        throw new Error('math_runtime_lease_lost');
    };
    assertHeld();
    const result = await operation({ signal: controller.signal, assertHeld, inheritedDescriptor: descriptor });
    assertHeld();
    return result;
  } finally {
    input.signal?.removeEventListener('abort', abort);
    fs.closeSync(descriptor);
    controller.abort();
  }
}
