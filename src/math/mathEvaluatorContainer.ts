import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import { spawnSync } from 'node:child_process';
import { assertMathCanonicalPath, isMathPathWithin } from "./mathRunBinding";

export type MathEvaluatorContainer = Readonly<{
  root: string;
  directory: string;
  device: string;
  inode: string;
  bootId: string;
}>;
const bootId = (): string => fs.readFileSync('/proc/sys/kernel/random/boot_id', 'utf8').trim();
export const mathEvaluatorBootIdentity = bootId;

export function validateMathEvaluatorContainerRoot(root: string): void {
  try {
    if (process.platform !== 'linux') throw new Error();
    assertMathCanonicalPath(root);
    if (
      root === '/sys/fs/cgroup' ||
      !isMathPathWithin('/sys/fs/cgroup', root) ||
      Number(fs.statfsSync(root).type) !== 0x63677270
    )
      throw new Error();
    fs.accessSync(root, fs.constants.R_OK | fs.constants.W_OK | fs.constants.X_OK);
  } catch {
    throw new Error('math_evaluator_container_unavailable');
  }
}

export function createMathEvaluatorContainer(root: string, attemptId: string): MathEvaluatorContainer {
  validateMathEvaluatorContainerRoot(root);
  if (!/^[a-f0-9-]{36}$/u.test(attemptId)) throw new Error('math_evaluator_container_identity');
  const directory = path.join(root, `math-eval-${attemptId}`);
  fs.mkdirSync(directory);
  const stat = fs.lstatSync(directory, { bigint: true });
  const container = { root, directory, device: String(stat.dev), inode: String(stat.ino), bootId: bootId() };
  try {
    fs.accessSync(path.join(directory, 'cgroup.procs'), fs.constants.W_OK);
    fs.accessSync(path.join(directory, 'cgroup.kill'), fs.constants.W_OK);
    fs.accessSync(path.join(directory, 'cgroup.events'), fs.constants.R_OK);
    return container;
  } catch (error) {
    fs.rmdirSync(directory);
    throw error;
  }
}

export function assertMathEvaluatorContainer(container: MathEvaluatorContainer): void {
  validateMathEvaluatorContainerRoot(container.root);
  if (
    path.dirname(container.directory) !== container.root ||
    !/^math-eval-[a-f0-9-]{36}$/u.test(path.basename(container.directory)) ||
    container.bootId !== bootId()
  )
    throw new Error('math_evaluator_container_identity');
  assertMathCanonicalPath(container.directory);
  const stat = fs.lstatSync(container.directory, { bigint: true });
  if (!stat.isDirectory() || String(stat.dev) !== container.device || String(stat.ino) !== container.inode)
    throw new Error('math_evaluator_container_identity');
}

export function mathEvaluatorContainerEmpty(container: MathEvaluatorContainer): boolean {
  assertMathEvaluatorContainer(container);
  const data = fs.readFileSync(path.join(container.directory, 'cgroup.events'), 'utf8');
  const populated = /^populated ([01])$/mu.exec(data);
  if (!populated) throw new Error('math_evaluator_container_state_invalid');
  return populated[1] === '0';
}

export async function emptyMathEvaluatorContainer(container: MathEvaluatorContainer): Promise<void> {
  assertMathEvaluatorContainer(container);
  if (!mathEvaluatorContainerEmpty(container)) fs.writeFileSync(path.join(container.directory, 'cgroup.kill'), '1');
  const deadline = Date.now() + 10_000;
  while (!mathEvaluatorContainerEmpty(container)) {
    if (Date.now() >= deadline) throw new Error('math_evaluator_container_not_empty');
    await new Promise<void>((resolve) => setTimeout(resolve, 20));
  }
}

/** A reboot proves old processes are gone only when their named container is absent. */
export async function recoverMathEvaluatorContainer(container: MathEvaluatorContainer): Promise<void> {
  if (container.bootId === bootId()) {
    await emptyMathEvaluatorContainer(container);
    return;
  }
  assertMathCanonicalPath(container.root);
  assertMathCanonicalPath(container.directory);
  if (
    path.dirname(container.directory) !== container.root ||
    !/^math-eval-[a-f0-9-]{36}$/u.test(path.basename(container.directory))
  )
    throw new Error('math_evaluator_container_identity');
  try {
    fs.lstatSync(container.directory);
  } catch (error) {
    if ((error as NodeJS.ErrnoException).code === 'ENOENT') return;
    throw error;
  }
  // A reused path belongs to this boot, not to the recorded attempt. Never kill it.
  throw new Error('math_evaluator_container_identity');
}

/** Validate actual delegated operations before any model starts. Never fall back to PID-only cleanup. */
export async function preflightMathEvaluatorContainer(root: string): Promise<void> {
  const container = createMathEvaluatorContainer(root, crypto.randomUUID());
  try {
    // Writable destination files alone do not imply migration permission:
    // cgroup v2 also checks the common ancestor of the current and destination
    // groups. Probe from the same process context as the future supervisor.
    const probe = spawnSync(
      process.execPath,
      [
        '-e',
        "require('node:fs').writeFileSync(process.argv[1], String(process.pid))",
        path.join(container.directory, 'cgroup.procs'),
      ],
      { stdio: 'ignore', timeout: 10_000 }
    );
    if (probe.error || probe.status !== 0) {
      throw new Error('math_evaluator_container_entry_denied: start the runner in the delegated user service');
    }
  } finally {
    await emptyMathEvaluatorContainer(container);
    fs.rmdirSync(container.directory);
  }
}

/** Reconcile the mkdir-to-journal crash window without guessing that an occupied container is ours. */
export async function recoverPreparedMathEvaluatorContainer(
  root: string,
  attemptId: string,
  bootIdentity: string
): Promise<void> {
  if (!/^[a-f0-9-]{36}$/u.test(attemptId)) throw new Error('math_evaluator_container_identity');
  const directory = path.join(root, `math-eval-${attemptId}`);
  if (bootIdentity !== bootId()) {
    await recoverMathEvaluatorContainer({ root, directory, device: '0', inode: '0', bootId: bootIdentity });
    return;
  }
  validateMathEvaluatorContainerRoot(root);
  let stat: fs.BigIntStats;
  try {
    stat = fs.lstatSync(directory, { bigint: true });
  } catch (error) {
    if ((error as NodeJS.ErrnoException).code === 'ENOENT') return;
    throw error;
  }
  if (bootIdentity !== bootId()) throw new Error('math_evaluator_container_identity');
  const container = { root, directory, device: String(stat.dev), inode: String(stat.ino), bootId: bootIdentity };
  if (!mathEvaluatorContainerEmpty(container)) throw new Error('math_evaluator_unjournaled_processes');
  fs.rmdirSync(directory);
}
