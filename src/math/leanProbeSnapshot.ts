import crypto from 'node:crypto';
import fs from 'node:fs';
import path from 'node:path';
import { assertMathCanonicalPath } from "./paths";
import { mathFileIdentity as metadata } from './mathRuntimeIo';
const MAX_FILES = 250_000;
const MAX_BYTES = 8 * 1024 * 1024 * 1024;

export function readLeanProbeSnapshotFile(
  source: string,
  checkpoint: () => void,
  target?: string,
  buffer = Buffer.alloc(1024 * 1024)
): Readonly<{ digest: string; identity: string; bytes: number; mode: number }> {
  checkpoint();
  assertMathCanonicalPath(source);
  const fd = fs.openSync(source, fs.constants.O_RDONLY | fs.constants.O_NOFOLLOW | fs.constants.O_NONBLOCK);
  let output: number | undefined;
  try {
    const before = fs.fstatSync(fd, { bigint: true });
    if (!before.isFile() || before.size > BigInt(MAX_BYTES)) throw new Error('Lean probe snapshot input is invalid.');
    if (target) {
      fs.mkdirSync(path.dirname(target), { recursive: true, mode: 0o700 });
      output = fs.openSync(
        target,
        fs.constants.O_WRONLY | fs.constants.O_CREAT | fs.constants.O_EXCL,
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
      if (bytes > MAX_BYTES) throw new Error('Lean probe snapshot exceeds its byte limit.');
      digest.update(buffer.subarray(0, size));
      if (output !== undefined) fs.writeFileSync(output, buffer.subarray(0, size));
    }
    const identity = metadata(before);
    const after = fs.fstatSync(fd, { bigint: true });
    if (
      BigInt(bytes) !== before.size ||
      identity !== metadata(after) ||
      identity !== metadata(fs.lstatSync(source, { bigint: true }))
    )
      throw new Error('Lean probe dependency changed during snapshot creation.');
    if (output !== undefined) {
      fs.futimesSync(output, Number(after.atimeNs) / 1e9, Number(after.mtimeNs) / 1e9);
      fs.fchmodSync(output, 0o400 | Number(before.mode & BigInt(0o111)));
    }
    return { digest: digest.digest('hex'), identity, bytes, mode: Number(before.mode & BigInt(0o777)) };
  } finally {
    if (output !== undefined) fs.closeSync(output);
    fs.closeSync(fd);
  }
}

type PackageInput = Readonly<{ relative: string; source: string; links: readonly string[] }>;
type ResolvedPackageInput = Readonly<{ input: PackageInput; visited: ReadonlySet<string> }>;

/** Resolve every link component inside the already authorized package root. */
function packageInput(root: string, relative: string, parent?: ResolvedPackageInput): ResolvedPackageInput {
  const segments = parent ? [path.basename(relative)] : relative.split(path.sep).filter(Boolean);
  let cursor = parent?.input.source ?? root;
  const links: string[] = [...(parent?.input.links ?? [])];
  const visited = new Set(parent?.visited);
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
  // The parent was already resolved by this traversal. Check the complete
  // physical path natively so replacing an ancestor with a link still fails.
  if (fs.realpathSync.native(cursor) !== cursor) throw new Error('math_path_invalid');
  return { input: { relative, source: cursor, links }, visited };
}

export function listLeanProbePackageInputs(root: string, checkpoint: () => void): PackageInput[] {
  assertMathCanonicalPath(root);
  const files: PackageInput[] = [];
  const ancestors = new Set<string>();
  let entries = 0;
  const visit = (relative: string, parent?: ResolvedPackageInput): void => {
    checkpoint();
    if (++entries > MAX_FILES) throw new Error('Lean probe package snapshot exceeds its entry limit.');
    const resolved = packageInput(root, relative, parent);
    const { input } = resolved;
    const stat = fs.lstatSync(input.source);
    if (stat.isDirectory()) {
      if (ancestors.has(input.source)) throw new Error('Lean probe package directory link cycle.');
      ancestors.add(input.source);
      for (const name of fs.readdirSync(input.source).toSorted()) {
        if (name !== '.git') visit(path.join(relative, name), resolved);
      }
      ancestors.delete(input.source);
    } else if (stat.isFile()) files.push(input);
    else throw new Error('Lean probe package snapshot requires regular files.');
  };
  visit('');
  return files;
}
