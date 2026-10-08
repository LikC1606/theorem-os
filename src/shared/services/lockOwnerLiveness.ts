import fs from 'node:fs';

/**
 * Lock files record the writer's PID so a crashed writer's lock can be
 * recovered. A PID is meaningful only in the PID namespace that wrote it: an
 * isolated MCP writes its in-sandbox PID (often 2), which names an unrelated
 * live process from any other namespace. Run 23 lost a whole run to such a
 * lock that could never expire. Record the namespace and only probe a PID that
 * was written in the current one.
 */
export const currentPidNamespace = (): string | null => {
  try {
    return fs.readlinkSync('/proc/self/ns/pid');
  } catch {
    return null;
  }
};

/** Owner fields to spread into a lock record. */
export const lockOwnerRecord = (): Readonly<{ pid: number; pidNamespace?: string }> => {
  const pidNamespace = currentPidNamespace();
  return Object.freeze({ pid: process.pid, ...(pidNamespace ? { pidNamespace } : {}) });
};

/**
 * 'alive' or 'dead' when the owner can be probed in this namespace; 'unknown'
 * when it was written elsewhere (or by a version that did not record the
 * namespace), in which case the caller's age rule decides.
 */
export const lockOwnerState = (value: unknown): 'alive' | 'dead' | 'unknown' => {
  const owner = value as { pid?: unknown; pidNamespace?: unknown } | null;
  if (!owner || typeof owner !== 'object' || !Number.isSafeInteger(owner.pid) || Number(owner.pid) <= 0) return 'dead';
  const local = currentPidNamespace();
  if (local !== null && owner.pidNamespace !== local) return 'unknown';
  try {
    process.kill(Number(owner.pid), 0);
    return 'alive';
  } catch (error) {
    return (error as NodeJS.ErrnoException).code === 'EPERM' ? 'alive' : 'dead';
  }
};

/** True while a lock file is younger than the stale-recovery age. */
export const lockIsFresh = (lockPath: string, maxAgeMs = 30_000): boolean => {
  try {
    return Date.now() - fs.statSync(lockPath).mtimeMs <= maxAgeMs;
  } catch {
    return false;
  }
};
