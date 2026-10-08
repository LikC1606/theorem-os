import crypto from 'node:crypto';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { execFileSync } from 'node:child_process';
import { assertMathCanonicalPath } from "./mathRunBinding";
import { canonicalMathJson, mathDigest } from "./mathRuntimeIo";

type SnapshotFile = Readonly<{
  source: string;
  target: string;
  relative: string;
  digest: string;
  identity: string;
  targetIdentity: string;
  mode: number;
  generated: boolean;
}>;
const MAX_FILES = 250_000;
const MAX_BYTES = 8 * 1024 * 1024 * 1024;
const MAX_PROJECT_BYTES = 256 * 1024 * 1024;
const HARD_MAX_BYTES = 32 * 1024 * 1024 * 1024;
type CopyAccounting = {
  clonedBytes: number;
  copiedBytes: number;
  unsupportedDevices: Set<string>;
};
const metadata = (stat: fs.BigIntStats): string =>
  [stat.dev, stat.ino, stat.size, stat.mode, stat.mtimeNs, stat.ctimeNs].join(':');
const snapshotLimit = (value: number | undefined, fallback: number, ceiling: number) => {
  const selected = value ?? fallback;
  if (!Number.isSafeInteger(selected) || selected < 1 || selected > ceiling)
    throw new Error('Lean probe snapshot byte limit is invalid.');
  return selected;
};

export function readLeanProbeSnapshotFile(
  source: string,
  checkpoint: () => void,
  target?: string,
  accounting?: CopyAccounting,
  maxBytes = MAX_BYTES,
  buffer = Buffer.alloc(1024 * 1024)
): Readonly<{ digest: string; identity: string; bytes: number; mode: number }> {
  checkpoint();
  assertMathCanonicalPath(source);
  const fd = fs.openSync(source, fs.constants.O_RDONLY | fs.constants.O_NOFOLLOW | fs.constants.O_NONBLOCK);
  let output: number | undefined;
  try {
    const before = fs.fstatSync(fd, { bigint: true });
    if (!before.isFile() || before.size > BigInt(maxBytes)) throw new Error('Lean probe snapshot input is invalid.');
    let cloned = false;
    if (target) {
      fs.mkdirSync(path.dirname(target), { recursive: true, mode: 0o700 });
      const devices = `${before.dev}:${fs.statSync(path.dirname(target), { bigint: true }).dev}`;
      if (accounting && !accounting.unsupportedDevices.has(devices)) {
        try {
          // FORCE never silently copies: observability must distinguish real COW
          // from the bounded streaming fallback. The clone is a distinct inode,
          // not an immutable shared environment or a hard link.
          fs.copyFileSync(source, target, fs.constants.COPYFILE_FICLONE_FORCE | fs.constants.COPYFILE_EXCL);
          cloned = true;
        } catch (error) {
          if (
            !['ENOTSUP', 'EOPNOTSUPP', 'ENOSYS', 'EXDEV', 'EINVAL'].includes(
              (error as NodeJS.ErrnoException).code ?? ''
            )
          )
            throw error;
          accounting.unsupportedDevices.add(devices);
        }
      }
      output = fs.openSync(
        target,
        cloned
          ? fs.constants.O_RDONLY | fs.constants.O_NOFOLLOW
          : fs.constants.O_WRONLY | fs.constants.O_CREAT | fs.constants.O_EXCL,
        0o600
      );
      const copied = fs.fstatSync(output, { bigint: true });
      if (!copied.isFile() || (copied.dev === before.dev && copied.ino === before.ino))
        throw new Error('Lean probe snapshot requires an independent regular file.');
    }
    const digest = crypto.createHash('sha256');
    let bytes = 0;
    for (let size = fs.readSync(fd, buffer); size; size = fs.readSync(fd, buffer)) {
      checkpoint();
      bytes += size;
      if (bytes > maxBytes) throw new Error('Lean probe snapshot exceeds its byte limit.');
      digest.update(buffer.subarray(0, size));
      if (output !== undefined && !cloned) fs.writeFileSync(output, buffer.subarray(0, size));
    }
    const identity = metadata(before);
    if (
      BigInt(bytes) !== before.size ||
      identity !== metadata(fs.fstatSync(fd, { bigint: true })) ||
      identity !== metadata(fs.lstatSync(source, { bigint: true }))
    )
      throw new Error('Lean probe dependency changed during snapshot creation.');
    if (output !== undefined) fs.fchmodSync(output, 0o400 | Number(before.mode & BigInt(0o111)));
    if (target && accounting) {
      if (cloned) accounting.clonedBytes += bytes;
      else accounting.copiedBytes += bytes;
    }
    return { digest: digest.digest('hex'), identity, bytes, mode: Number(before.mode & BigInt(0o777)) };
  } finally {
    if (output !== undefined) fs.closeSync(output);
    fs.closeSync(fd);
  }
}

function projectFiles(root: string): string[] {
  const output = execFileSync(
    'git',
    ['-C', root, 'ls-files', '-z', '--cached', '--others', '--exclude-standard', '--', '.'],
    {
      encoding: 'utf8',
      maxBuffer: 32 * 1024 * 1024,
      timeout: 10_000,
    }
  );
  return [...new Set(output.split('\0').filter(Boolean))]
    .filter((file) => !file.split('/').some((part) => ['.git', '.lake', '.deepscientist'].includes(part)))
    .toSorted();
}

type PackageInput = Readonly<{ relative: string; source: string; links: readonly string[] }>;

export type SealedLeanPackageInput = Readonly<{
  path: string;
  source: string;
  sha256: string;
  bytes: number;
  mode: number;
}>;

export type ImmutableLeanProbePackages = Readonly<{
  sourceRoot: string;
  digest: string;
  fileCount: number;
  bytes: number;
  packageNames: readonly string[];
  verify: () => void;
}>;

/** Resolve every link component inside the already authorized package root. */
function packageInput(root: string, relative: string): PackageInput {
  const segments = relative.split(path.sep).filter(Boolean);
  let cursor = root;
  const links: string[] = [];
  const visited = new Set<string>();
  while (segments.length) {
    const segment = segments.shift()!;
    if (segment === '.') continue;
    if (segment === '..') {
      if (cursor === root) throw new Error('Lean probe package link escapes the authorized package root.');
      cursor = path.dirname(cursor);
      continue;
    }
    if (segment === '.git') throw new Error('Lean probe package link targets excluded Git metadata.');
    cursor = path.join(cursor, segment);
    const stat = fs.lstatSync(cursor, { bigint: true });
    if (!stat.isSymbolicLink()) continue;
    if (visited.has(cursor) || links.length >= 40) throw new Error('Lean probe package link cycle.');
    visited.add(cursor);
    const link = fs.readlinkSync(cursor);
    let targetSegments: string[];
    if (path.isAbsolute(link)) {
      if (link !== root && !link.startsWith(`${root}${path.sep}`))
        throw new Error('Lean probe package link escapes the authorized package root.');
      targetSegments = link.slice(root.length).split(path.sep).filter(Boolean);
    } else {
      targetSegments = [
        ...path.relative(root, path.dirname(cursor)).split(path.sep).filter(Boolean),
        ...link.split(path.sep).filter(Boolean),
      ];
    }
    links.push(`${cursor}:${metadata(stat)}:${link}`);
    segments.unshift(...targetSegments);
    cursor = root;
  }
  assertMathCanonicalPath(cursor);
  return { relative, source: cursor, links };
}

export function listLeanProbePackageInputs(root: string, checkpoint: () => void): PackageInput[] {
  assertMathCanonicalPath(root);
  const files: PackageInput[] = [];
  let entries = 0;
  const visit = (relative: string, ancestors: ReadonlySet<string>): void => {
    checkpoint();
    if (++entries > MAX_FILES) throw new Error('Lean probe package snapshot exceeds its entry limit.');
    const input = packageInput(root, relative);
    const stat = fs.lstatSync(input.source);
    if (stat.isDirectory()) {
      if (ancestors.has(input.source)) throw new Error('Lean probe package directory link cycle.');
      const next = new Set(ancestors).add(input.source);
      for (const name of fs.readdirSync(input.source).toSorted()) {
        if (name !== '.git') visit(path.join(relative, name), next);
      }
    } else if (stat.isFile()) files.push(input);
    else throw new Error('Lean probe package snapshot requires regular files.');
  };
  visit('', new Set());
  return files;
}

const readFile = readLeanProbeSnapshotFile;
const packageFiles = listLeanProbePackageInputs;

/** Inventory actual bytes before a protected broker seals them. No metadata-only cache identity. */
export function captureLeanProbePackages(
  sourceRoot: string,
  options: Readonly<{ signal?: AbortSignal; deadlineAt?: number; maxBytes?: number }> = {}
) {
  const limit = snapshotLimit(options.maxBytes, MAX_BYTES, HARD_MAX_BYTES);
  const checkpoint = () => {
    if (options.signal?.aborted || (options.deadlineAt !== undefined && Date.now() >= options.deadlineAt))
      throw new Error('Source probe deadline exceeded or cancelled.');
  };
  const inputs = packageFiles(sourceRoot, checkpoint);
  const buffer = Buffer.alloc(1024 * 1024);
  let bytes = 0;
  const identities: string[] = [];
  const files = inputs.map((input): SealedLeanPackageInput => {
    if (input.relative.split(path.sep).includes('Solution.lean'))
      throw new Error('Lean probe snapshot contains an unauthorized path.');
    const captured = readFile(input.source, checkpoint, undefined, undefined, limit - bytes, buffer);
    bytes += captured.bytes;
    identities.push(captured.identity);
    return {
      path: input.relative.replaceAll(path.sep, '/'),
      source: input.source,
      sha256: captured.digest,
      bytes: captured.bytes,
      mode: captured.mode,
    };
  });
  const verify = () => {
    if (canonicalMathJson(packageFiles(sourceRoot, checkpoint)) !== canonicalMathJson(inputs))
      throw new Error('Lean probe dependency set changed during the probe.');
    for (let index = 0; index < files.length; index++) {
      const current = readFile(files[index].source, checkpoint, undefined, undefined, limit, buffer);
      if (current.digest !== files[index].sha256 || current.identity !== identities[index])
        throw new Error('Lean probe dependency changed during the probe.');
    }
  };
  return Object.freeze({
    sourceRoot,
    files,
    bytes,
    fileCount: files.length,
    packageNames: Object.freeze([...new Set(files.map((file) => file.path.split('/')[0]))].toSorted()),
    digest: mathDigest(canonicalMathJson(files.map(({ path: name, sha256, mode }) => ({ path: name, sha256, mode })))),
    verify,
  });
}

/** Freeze current editable sources and actual package inputs, including package OLeans. */
export function createLeanProbeSnapshot(
  projectRoot: string,
  sourceFile: string,
  packagesRoot?: string,
  options: Readonly<{
    signal?: AbortSignal;
    deadlineAt?: number;
    /** Host-only limits. Never accept these from model tool arguments. */
    maxProjectBytes?: number;
    maxPackageBytes?: number;
    maxTotalBytes?: number;
    /** Host-created lease whose data is sealed by the operating system. */
    immutablePackages?: ImmutableLeanProbePackages;
    /** Run-bound sealed package root mounted by the sandbox instead of a copy. */
    proofEnvironment?: Readonly<{ packagesRoot: string; identity: string; verify: () => void }>;
  }> = {}
) {
  const started = performance.now();
  const projectLimit = snapshotLimit(options.maxProjectBytes, MAX_PROJECT_BYTES, MAX_PROJECT_BYTES);
  const packageLimit = snapshotLimit(options.maxPackageBytes, MAX_BYTES, HARD_MAX_BYTES);
  const totalLimit = snapshotLimit(options.maxTotalBytes, MAX_BYTES, HARD_MAX_BYTES);
  // All reads are synchronous and scoped to one snapshot. Reuse one buffer
  // instead of allocating a megabyte for every small Mathlib build artifact.
  const readBuffer = Buffer.alloc(1024 * 1024);
  const checkpoint = () => {
    if (options.signal?.aborted || (options.deadlineAt !== undefined && Date.now() >= options.deadlineAt))
      throw new Error('Source probe deadline exceeded or cancelled.');
  };
  checkpoint();
  assertMathCanonicalPath(projectRoot);
  const immutable = options.immutablePackages;
  if (immutable && (!packagesRoot || immutable.sourceRoot !== packagesRoot))
    throw new Error('Lean probe immutable package root does not match its authorized cache.');
  const sources = projectFiles(projectRoot);
  if (!sources.includes(sourceFile)) throw new Error('Lean probe source is absent from the project snapshot.');
  const sealed = options.proofEnvironment;
  if (sealed && immutable) throw new Error('Lean probe cannot combine sealed and shared package environments.');
  if (sealed && sealed.packagesRoot !== packagesRoot) throw new Error('Lean probe sealed package identity mismatch.');
  sealed?.verify();
  const packages = packagesRoot && !immutable && !sealed ? packageFiles(packagesRoot, checkpoint) : [];
  if (sources.length + (immutable?.fileCount ?? packages.length) > MAX_FILES)
    throw new Error('Lean probe snapshot exceeds its file limit.');
  // Neither COW nor chmod seals bytes against a same-UID process. Continue to
  // hash actual bytes, and bound even sparse/COW logical sizes before allocation.
  const sum = (paths: string[]) =>
    paths.reduce((total, file) => {
      checkpoint();
      return total + fs.lstatSync(file, { bigint: true }).size;
    }, BigInt(0));
  const projectBytes = sum(sources.map((file) => path.join(projectRoot, file)));
  const packageBytes = immutable ? BigInt(immutable.bytes) : sum(packages.map((file) => file.source));
  if (
    projectBytes > BigInt(projectLimit) ||
    packageBytes > BigInt(packageLimit) ||
    projectBytes + packageBytes > BigInt(totalLimit)
  )
    throw new Error('Lean probe snapshot exceeds its byte limit.');
  const root = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'deepscientist-lean-probe-snapshot-')));
  const workspaceRoot = path.join(root, 'project');
  const lakePackagesPath =
    sealed?.packagesRoot ?? (packagesRoot ? path.join(workspaceRoot, '.lake', 'packages') : undefined);
  const files: SnapshotFile[] = [];
  let packageOverrides: Readonly<{ path: string; digest: string; identity: string }> | undefined;
  let bytes = 0;
  let actualProjectBytes = 0;
  let actualPackageBytes = immutable?.bytes ?? 0;
  const accounting: CopyAccounting = { clonedBytes: 0, copiedBytes: 0, unsupportedDevices: new Set() };
  let verificationMs = 0;
  let verificationCount = 0;
  let verifiedBytes = 0;
  let disposed = false;
  const copy = (sourceRoot: string, targetRoot: string, relative: string, prefix: string, resolvedSource?: string) => {
    checkpoint();
    if (
      path.isAbsolute(relative) ||
      relative.split(/[\\/]/u).some((part) => !part || part === '.' || part === '..' || part === 'Solution.lean')
    )
      throw new Error('Lean probe snapshot contains an unauthorized path.');
    const source = resolvedSource ?? path.join(sourceRoot, relative);
    const target = path.join(targetRoot, relative);
    const stat = fs.lstatSync(source, { bigint: true });
    const remaining = Math.min(
      totalLimit - bytes - (immutable?.bytes ?? 0),
      prefix === 'project' ? projectLimit - actualProjectBytes : packageLimit - actualPackageBytes
    );
    if (stat.size > BigInt(remaining)) throw new Error('Lean probe snapshot exceeds its byte limit.');
    const result = readFile(source, checkpoint, target, accounting, remaining, readBuffer);
    const packageRelative = relative.split(path.sep).slice(1).join('/');
    const generated =
      prefix === 'packages' &&
      (packageRelative.startsWith('.lake/build/') || /^\.lake\/lakefile\.[^/]+$/u.test(packageRelative));
    if (generated) fs.chmodSync(target, 0o600 | (result.mode & 0o111));
    bytes += result.bytes;
    if (prefix === 'project') actualProjectBytes += result.bytes;
    else actualPackageBytes += result.bytes;
    files.push({
      source,
      target,
      relative: `${prefix}/${relative}`,
      digest: result.digest,
      identity: result.identity,
      targetIdentity: metadata(fs.lstatSync(target, { bigint: true })),
      mode: result.mode,
      generated,
    });
  };
  const dispose = () => {
    fs.rmSync(root, { recursive: true, force: true });
    disposed = true;
  };
  try {
    fs.mkdirSync(workspaceRoot, { mode: 0o700 });
    if (lakePackagesPath && !sealed) fs.mkdirSync(lakePackagesPath, { recursive: true, mode: 0o700 });
    for (const file of sources) copy(projectRoot, workspaceRoot, file, 'project');
    if (packagesRoot && lakePackagesPath && !sealed)
      for (const file of packages) copy(packagesRoot, lakePackagesPath, file.relative, 'packages', file.source);
    if (packagesRoot && lakePackagesPath && !sealed) {
      const manifestPath = path.join(workspaceRoot, 'lake-manifest.json');
      if (fs.existsSync(manifestPath)) {
        const manifest = JSON.parse(fs.readFileSync(manifestPath, 'utf8')) as { packages?: unknown[] };
        const overrides = (manifest.packages ?? []).map((item) => {
          if (!item || typeof item !== 'object' || Array.isArray(item))
            throw new Error('Invalid Lake package manifest.');
          const entry = item as Record<string, unknown>;
          const name = typeof entry.name === 'string' ? entry.name : '';
          if (
            !name ||
            name === '.' ||
            name === '..' ||
            /[/\\]/u.test(name) ||
            name.includes('\0') ||
            path.isAbsolute(name)
          )
            throw new Error('Invalid Lake package name.');
          const directory = [name, name.replace(/^«(.+)»$/u, '$1')].find((candidate) =>
            immutable
              ? immutable.packageNames.includes(candidate)
              : fs.existsSync(path.join(lakePackagesPath, candidate))
          );
          if (!directory) throw new Error(`Lake package ${name} is absent from the snapshot.`);
          const override: Record<string, unknown> = {
            name,
            type: 'path',
            dir: path.posix.join('/workspace', '.lake', 'packages', directory),
            inherited: typeof entry.inherited === 'boolean' ? entry.inherited : false,
          };
          if (typeof entry.scope === 'string') override.scope = entry.scope;
          for (const field of ['configFile', 'manifestFile'] as const) {
            const value = entry[field];
            if (value === undefined || value === null) continue;
            if (
              typeof value !== 'string' ||
              path.isAbsolute(value) ||
              /^[A-Za-z]:/u.test(value) ||
              value.split(/[/\\]/u).some((part) => !part || part === '.' || part === '..' || part.includes('\0'))
            )
              throw new Error('Invalid Lake package configuration path.');
            override[field] = value;
          }
          return override;
        });
        fs.mkdirSync(path.join(workspaceRoot, '.lake'), { recursive: true, mode: 0o700 });
        fs.writeFileSync(
          path.join(workspaceRoot, '.lake', 'package-overrides.json'),
          `${JSON.stringify({ schemaVersion: '1.2.0', packages: overrides })}\n`,
          { mode: 0o400 }
        );
        const overridesPath = path.join(workspaceRoot, '.lake', 'package-overrides.json');
        packageOverrides = {
          path: overridesPath,
          ...readFile(overridesPath, checkpoint, undefined, undefined, totalLimit, readBuffer),
        };
      }
    }
    const verify = (initial = false) => {
      if (disposed) throw new Error('Lean probe snapshot has been disposed.');
      const verifyStarted = performance.now();
      try {
        checkpoint();
        sealed?.verify();
        if (packageOverrides) {
          const current = readFile(packageOverrides.path, checkpoint, undefined, undefined, totalLimit, readBuffer);
          if (current.digest !== packageOverrides.digest || current.identity !== packageOverrides.identity)
            throw new Error('Lean probe package binding changed during the probe.');
        }
        if (
          canonicalMathJson(projectFiles(projectRoot)) !== canonicalMathJson(sources) ||
          (packagesRoot &&
            !immutable &&
            !sealed &&
            canonicalMathJson(packageFiles(packagesRoot, checkpoint)) !== canonicalMathJson(packages))
        )
          throw new Error('Lean probe dependency set changed during the probe.');
        for (const file of files) {
          // Creation already read each source through an O_NOFOLLOW descriptor.
          // Stable inode/ctime binds that completed read; later verification still
          // hashes source bytes and never substitutes metadata as content proof.
          const original = initial
            ? { identity: metadata(fs.lstatSync(file.source, { bigint: true })), digest: file.digest, bytes: 0 }
            : readFile(file.source, checkpoint, undefined, undefined, totalLimit, readBuffer);
          // Lake may rebuild generated files in its private copy. Original cache inputs remain immutable.
          const copied =
            !initial && file.generated
              ? undefined
              : readFile(file.target, checkpoint, undefined, undefined, totalLimit, readBuffer);
          verifiedBytes += original.bytes + (copied?.bytes ?? 0);
          if (
            original.identity !== file.identity ||
            original.digest !== file.digest ||
            (copied && (copied.digest !== file.digest || copied.identity !== file.targetIdentity))
          )
            throw new Error('Lean probe dependency changed during the probe.');
        }
        if (immutable && !initial) {
          immutable.verify();
          verifiedBytes += immutable.bytes;
        }
      } finally {
        verificationMs += performance.now() - verifyStarted;
        verificationCount++;
      }
    };
    verify(true);
    const preparationMs = performance.now() - started;
    return Object.freeze({
      workspaceRoot,
      lakePackagesPath,
      digest: mathDigest(
        canonicalMathJson({
          files: files.map(({ relative, digest, mode }) => ({ path: relative, sha256: digest, mode })),
          packageOverrides: packageOverrides?.digest ?? null,
          ...(immutable ? { immutablePackages: immutable.digest } : {}),
          ...(sealed ? { proofEnvironment: sealed.identity } : {}),
        })
      ),
      fileCount: files.length + (immutable?.fileCount ?? 0),
      bytes: bytes + (immutable?.bytes ?? 0),
      verify: () => verify(),
      metrics: () =>
        Object.freeze({
          preparationMs,
          verificationMs,
          verificationCount,
          verifiedBytes,
          clonedBytes: accounting.clonedBytes,
          copiedBytes: accounting.copiedBytes,
          projectBytes: actualProjectBytes,
          packageBytes: actualPackageBytes,
          sharedImmutableEnvironment: Boolean(immutable),
        }),
      dispose,
    });
  } catch (error) {
    dispose();
    throw error;
  }
}
