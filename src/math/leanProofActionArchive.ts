import fs from 'node:fs';
import path from 'node:path';
import type { MathProofAction } from "../common/types/team/mathematicsTeam";
import { syncMathDirectory } from "./mathRuntimeIo";

const archiveIndexes = new Map<string, { identity: string; ids: Set<string> }>();
const fileIdentity = (stat: fs.BigIntStats) => [stat.dev, stat.ino, stat.size, stat.mtimeNs, stat.ctimeNs].join(':');

/** Archive before removing actions from a checkpoint's active history window. */
export function archiveLeanProofActions(
  workspaceRoot: string,
  relativePath: string,
  actions: readonly MathProofAction[]
): void {
  if (!actions.length) return;
  const root = fs.realpathSync(workspaceRoot);
  const parts = relativePath.split('/');
  if (parts.some((part) => !part || part === '.' || part === '..') || path.isAbsolute(relativePath)) {
    throw new Error('Invalid proof action archive path');
  }
  let directory = root;
  for (const part of parts.slice(0, -1)) {
    const parent = directory;
    directory = path.join(directory, part);
    try {
      fs.mkdirSync(directory, { mode: 0o700 });
      syncMathDirectory(parent);
    } catch (error) {
      if ((error as NodeJS.ErrnoException).code !== 'EEXIST') throw error;
    }
    const stat = fs.lstatSync(directory);
    if (!stat.isDirectory() || stat.isSymbolicLink()) throw new Error('Proof action archive directory is not regular');
  }
  const archivePath = path.join(root, relativePath);
  const descriptor = fs.openSync(
    archivePath,
    fs.constants.O_APPEND | fs.constants.O_CREAT | fs.constants.O_RDWR | fs.constants.O_NOFOLLOW,
    0o600
  );
  try {
    if (!fs.fstatSync(descriptor).isFile()) throw new Error('Proof action archive is not a regular file');
    const identity = fileIdentity(fs.fstatSync(descriptor, { bigint: true }));
    let cached = archiveIndexes.get(archivePath);
    let separator = '';
    if (cached?.identity !== identity) {
      const text = fs.readFileSync(descriptor, 'utf8');
      const ids = new Set<string>();
      for (const line of text.split('\n')) {
        try {
          const value = JSON.parse(line);
          if (typeof value.actionId === 'string') ids.add(value.actionId);
        } catch {
          /* An interrupted final line cannot suppress a complete action. */
        }
      }
      separator = text && !text.endsWith('\n') ? '\n' : '';
      cached = { identity, ids };
    }
    const added = new Set<string>();
    const fresh = actions.filter((action) => {
      if (cached.ids.has(action.actionId) || added.has(action.actionId)) return false;
      added.add(action.actionId);
      return true;
    });
    if (!fresh.length) return;
    fs.writeFileSync(descriptor, separator + fresh.map((action) => JSON.stringify(action)).join('\n') + '\n');
    fs.fsyncSync(descriptor);
    for (const id of added) cached.ids.add(id);
    cached.identity = fileIdentity(fs.fstatSync(descriptor, { bigint: true }));
    archiveIndexes.set(archivePath, cached);
  } finally {
    fs.closeSync(descriptor);
  }
  syncMathDirectory(directory);
}
