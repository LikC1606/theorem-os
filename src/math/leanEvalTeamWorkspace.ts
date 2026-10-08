/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

import crypto from 'node:crypto';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import {
  bootstrapLeanEvalProblem,
  cleanupLeanEvalBootstrap,
  readLeanEvalBootstrapReceipt,
  type LeanEvalBootstrapReceipt,
} from "./leanEvalBootstrap";
import { reapLeanEvalArtifacts } from "./leanEvalCleanup";
import { lockOwnerRecord, lockOwnerState } from "../shared/services/lockOwnerLiveness";
import { runProjectGitRepositoryMutation } from "../project-git/ProjectGitService";

const INDEX_DIRECTORY = path.join('.deepscientist', 'math', 'lean-eval-team');
const INDEX_SCHEMA = 'deepscientist.mathematics.lean-eval-team-workspace.v1' as const;
const FULL_OID = /^(?:[0-9a-f]{40}|[0-9a-f]{64})$/u;

const isWithin = (parent: string, candidate: string): boolean => {
  const relative = path.relative(path.resolve(parent), path.resolve(candidate));
  return relative === '' || (!relative.startsWith(`..${path.sep}`) && relative !== '..' && !path.isAbsolute(relative));
};

export type LeanEvalTeamWorkspaceRequest = Readonly<{
  repositoryRoot: string;
  projectRoot: string;
  assignmentId: string;
  problemId: string;
  expectedBaseCommit: string;
  branch: string;
  /** Reuse the durable solver workspace of a same-slot candidate repair. */
  sourceAssignmentId?: string;
}>;

export type LeanEvalTeamWorkspacePreparation = Readonly<{
  ok: true;
  workspace: string;
  baseCommit: string;
  branch: string;
  actualBaseCommit: string;
  /** Private solver HEAD when this assignment started. */
  progressBaseCommit: string;
  receiptPath: string;
  solverProjectRoot: string;
  verifierProjectRoot: string;
  sourceProjectRoot: string;
}>;

export type LeanEvalTeamWorkspaceIntegration = Readonly<{
  ok: boolean;
  alreadyIntegrated?: boolean;
  mergedCommit?: string;
  branch?: Readonly<{
    name: string;
    ref: string;
    head: string;
    shortHead: string;
    active: boolean;
    status: 'candidate' | 'completed';
    baseCommit: string;
    worktreePath: string;
    worktreeState: 'clean' | 'dirty' | 'missing';
  }>;
  error?: string;
}>;

type WorkspaceIndex = Readonly<{
  schema: typeof INDEX_SCHEMA;
  assignmentId: string;
  problemId: string;
  teamId: string;
  slotId: string;
  expectedBaseCommit: string;
  branch: string;
  repositoryRoot: string;
  projectRoot: string;
  workspace: string;
  receiptPath: string;
  solverProjectRoot: string;
  verifierProjectRoot: string;
  sourceProjectRoot: string;
  actualBaseCommit: string;
  /** Private solver HEAD when this assignment started. */
  progressBaseCommit: string;
  /** Assignment that owns the physical solver repository, when this is an alias. */
  workspaceOwnerAssignmentId?: string;
  /** Previous assignment whose solver repository is being resumed. */
  sharedFromAssignmentId?: string;
  integrated?: boolean;
  integratedAt?: number;
  /** Private solver HEAD whose authorized delta was promoted. */
  deliveredHead?: string;
  /** Canonical Project Git commit created by promotion. */
  mergedCommit?: string;
}>;

const git = (cwd: string, args: readonly string[]): string => {
  const result = spawnSync('git', ['-C', cwd, ...args], { encoding: 'utf8', maxBuffer: 8 * 1024 * 1024 });
  if (result.status !== 0) throw new Error(result.stderr?.trim() || `git ${args.join(' ')} failed`);
  return result.stdout.trim();
};

const safeSegment = (value: string, label: string): string => {
  const normalized = value.trim();
  if (
    !normalized ||
    normalized === '.' ||
    normalized === '..' ||
    normalized.includes('/') ||
    normalized.includes('\\')
  ) {
    throw new Error(`${label} must be a single path segment`);
  }
  return normalized;
};

const indexDirectory = (projectRoot: string, create = false): string => {
  const root = path.resolve(projectRoot);
  const rootStat = fs.lstatSync(root);
  if (rootStat.isSymbolicLink() || !rootStat.isDirectory()) {
    throw new Error('Lean-Eval workspace index project root is not a regular directory');
  }
  let cursor = root;
  for (const segment of INDEX_DIRECTORY.split(path.sep)) {
    cursor = path.join(cursor, segment);
    if (!fs.existsSync(cursor)) {
      if (create) {
        fs.mkdirSync(cursor, { mode: 0o700 });
        continue;
      }
      break;
    }
    const stat = fs.lstatSync(cursor);
    if (stat.isSymbolicLink() || !stat.isDirectory()) {
      throw new Error('Lean-Eval workspace index directory is not a regular directory');
    }
  }
  return path.join(root, INDEX_DIRECTORY);
};

const indexPath = (projectRoot: string, assignmentId: string, createDirectory = false): string =>
  path.join(indexDirectory(projectRoot, createDirectory), `${safeSegment(assignmentId, 'assignmentId')}.json`);

type AssignmentLock = Readonly<{ path: string; token: string; descriptor: number }>;

const sleep = (milliseconds: number): Promise<void> => new Promise((resolve) => setTimeout(resolve, milliseconds));

const acquireAssignmentLock = async (projectRoot: string, assignmentId: string): Promise<AssignmentLock> => {
  const lockPath = `${indexPath(projectRoot, assignmentId, true)}.lock`;
  const token = `${process.pid}-${crypto.randomUUID()}`;
  const deadline = Date.now() + 30_000;
  const noFollow = typeof fs.constants.O_NOFOLLOW === 'number' ? fs.constants.O_NOFOLLOW : 0;
  for (;;) {
    try {
      const descriptor = fs.openSync(
        lockPath,
        fs.constants.O_WRONLY | fs.constants.O_CREAT | fs.constants.O_EXCL | noFollow,
        0o600
      );
      fs.writeFileSync(
        descriptor,
        `${JSON.stringify({ ...lockOwnerRecord(), token, createdAt: Date.now() })}\n`,
        'utf8'
      );
      fs.fsyncSync(descriptor);
      return Object.freeze({ path: lockPath, token, descriptor });
    } catch (error) {
      if ((error as NodeJS.ErrnoException).code !== 'EEXIST' || Date.now() >= deadline) throw error;
      let stale = false;
      try {
        const stat = fs.lstatSync(lockPath);
        const value: unknown = JSON.parse(fs.readFileSync(lockPath, 'utf8'));
        stale = stat.isFile() && Date.now() - stat.mtimeMs > 30_000 && lockOwnerState(value) !== 'alive';
      } catch {
        // A concurrent creator may still be writing the lock.
      }
      if (stale) {
        try {
          fs.rmSync(lockPath, { force: true });
        } catch {
          // The lock owner may have replaced the file; retry and re-read it.
        }
        continue;
      }
      // eslint-disable-next-line no-await-in-loop
      await sleep(25);
    }
  }
};

const releaseAssignmentLock = (lock: AssignmentLock): void => {
  try {
    fs.closeSync(lock.descriptor);
  } finally {
    try {
      const value = JSON.parse(fs.readFileSync(lock.path, 'utf8')) as { token?: unknown };
      if (value.token === lock.token) fs.rmSync(lock.path, { force: true });
    } catch {
      // A stale lock is recoverable by the next preparation attempt.
    }
  }
};

const writeIndex = (index: WorkspaceIndex): void => {
  const target = indexPath(index.projectRoot, index.assignmentId, true);
  const temporary = `${target}.${process.pid}.${crypto.randomUUID()}.tmp`;
  const noFollow = typeof fs.constants.O_NOFOLLOW === 'number' ? fs.constants.O_NOFOLLOW : 0;
  const flags = fs.constants.O_WRONLY | fs.constants.O_CREAT | fs.constants.O_EXCL | noFollow;
  let descriptor: number | undefined;
  try {
    descriptor = fs.openSync(temporary, flags, 0o600);
    fs.writeFileSync(descriptor, `${JSON.stringify(index, null, 2)}\n`, 'utf8');
    fs.fsyncSync(descriptor);
    fs.closeSync(descriptor);
    descriptor = undefined;
    fs.renameSync(temporary, target);
    try {
      const directory = fs.openSync(path.dirname(target), 'r');
      try {
        fs.fsyncSync(directory);
      } finally {
        fs.closeSync(directory);
      }
    } catch {
      // Directory fsync is unavailable on some supported filesystems.
    }
  } finally {
    if (descriptor !== undefined) fs.closeSync(descriptor);
    fs.rmSync(temporary, { force: true });
  }
};

const readIndex = (file: string): WorkspaceIndex => {
  const stat = fs.lstatSync(file);
  if (stat.isSymbolicLink() || !stat.isFile()) throw new Error('Lean-Eval workspace index is not a regular file');
  const value = JSON.parse(fs.readFileSync(file, 'utf8')) as Partial<WorkspaceIndex>;
  if (
    value.schema !== INDEX_SCHEMA ||
    typeof value.assignmentId !== 'string' ||
    typeof value.problemId !== 'string' ||
    typeof value.teamId !== 'string' ||
    typeof value.slotId !== 'string' ||
    typeof value.expectedBaseCommit !== 'string' ||
    typeof value.branch !== 'string' ||
    typeof value.repositoryRoot !== 'string' ||
    typeof value.projectRoot !== 'string' ||
    typeof value.workspace !== 'string' ||
    typeof value.receiptPath !== 'string' ||
    typeof value.solverProjectRoot !== 'string' ||
    typeof value.verifierProjectRoot !== 'string' ||
    typeof value.sourceProjectRoot !== 'string' ||
    typeof value.actualBaseCommit !== 'string' ||
    typeof value.progressBaseCommit !== 'string'
  ) {
    throw new Error('Lean-Eval workspace index is invalid');
  }
  if (
    !FULL_OID.test(value.expectedBaseCommit) ||
    !FULL_OID.test(value.actualBaseCommit) ||
    !FULL_OID.test(value.progressBaseCommit)
  ) {
    throw new Error('Lean-Eval workspace index contains an invalid commit identity');
  }
  if (value.workspaceOwnerAssignmentId !== undefined) {
    safeSegment(value.workspaceOwnerAssignmentId, 'workspaceOwnerAssignmentId');
  }
  if (value.sharedFromAssignmentId !== undefined) {
    safeSegment(value.sharedFromAssignmentId, 'sharedFromAssignmentId');
    if (value.sharedFromAssignmentId === value.assignmentId) {
      throw new Error('Lean-Eval workspace index cannot share from itself');
    }
  }
  if (
    (value.deliveredHead !== undefined && !FULL_OID.test(value.deliveredHead)) ||
    (value.mergedCommit !== undefined && !FULL_OID.test(value.mergedCommit))
  ) {
    throw new Error('Lean-Eval workspace index contains an invalid integration identity');
  }
  for (const [label, candidate] of [
    ['repositoryRoot', value.repositoryRoot],
    ['projectRoot', value.projectRoot],
    ['workspace', value.workspace],
    ['receiptPath', value.receiptPath],
    ['solverProjectRoot', value.solverProjectRoot],
    ['verifierProjectRoot', value.verifierProjectRoot],
    ['sourceProjectRoot', value.sourceProjectRoot],
  ] as const) {
    if (!path.isAbsolute(candidate)) throw new Error(`Lean-Eval workspace index ${label} must be absolute`);
  }
  const workspace = path.resolve(value.workspace);
  if (!path.basename(workspace).startsWith('deepscientist-lean-eval-')) {
    throw new Error('Lean-Eval workspace index workspace is not runtime-owned');
  }
  if (
    path.resolve(value.verifierProjectRoot) !== `${workspace}.git` ||
    path.resolve(value.sourceProjectRoot) !== `${workspace}.source`
  ) {
    throw new Error('Lean-Eval workspace index detached worktree paths are inconsistent');
  }
  const receipt = path.resolve(value.receiptPath);
  if (!isWithin(workspace, receipt) || path.basename(receipt) !== 'active-problem.json') {
    throw new Error('Lean-Eval workspace index receipt path is outside the solver workspace');
  }
  if (!isWithin(workspace, value.solverProjectRoot)) {
    throw new Error('Lean-Eval workspace index solver project is outside the solver workspace');
  }
  return Object.freeze(value as WorkspaceIndex);
};

const assertSolverSurface = (workspace: string): void => {
  const visit = (directory: string): void => {
    for (const entry of fs.readdirSync(directory)) {
      if (['Solution.lean', 'WorkspaceTest.lean', 'README.md'].includes(entry)) {
        throw new Error(`Lean-Eval solver workspace contains excluded ${entry}`);
      }
      const absolute = path.join(directory, entry);
      const stat = fs.lstatSync(absolute);
      if (stat.isSymbolicLink()) throw new Error(`Lean-Eval solver workspace contains a symlink: ${entry}`);
      if (stat.isDirectory() && entry !== '.git') visit(absolute);
    }
  };
  visit(workspace);
};

const initializeSolverGit = (workspace: string, branch: string): string => {
  fs.writeFileSync(
    path.join(workspace, '.gitignore'),
    '.lake/\n.deepscientist/math/lean-eval-proof/\n.deepscientist/math/lean-eval-outcomes.jsonl\n.deepscientist/math/run-history/\n',
    { encoding: 'utf8', mode: 0o600 }
  );
  git(workspace, ['init', '--quiet']);
  git(workspace, ['config', 'user.name', 'DeepScientist Lean-Eval Worker']);
  git(workspace, ['config', 'user.email', 'lean-eval-worker@deepscientist.invalid']);
  git(workspace, ['checkout', '-b', branch]);
  git(workspace, ['add', '--all']);
  const commit = spawnSync(
    'git',
    ['-C', workspace, 'commit', '--no-gpg-sign', '-m', 'Lean-Eval public solver baseline'],
    { encoding: 'utf8', maxBuffer: 8 * 1024 * 1024 }
  );
  if (commit.status !== 0) throw new Error(commit.stderr?.trim() || 'Unable to initialize Lean-Eval solver Git');
  return git(workspace, ['rev-parse', 'HEAD']).toLowerCase();
};

const loadReceipt = (receiptPath: string): LeanEvalBootstrapReceipt => readLeanEvalBootstrapReceipt(receiptPath);

/** Validate the durable index against its bootstrap receipt after a restart. */
export const assertLeanEvalTeamWorkspaceReceiptBinding = (
  receipt: LeanEvalBootstrapReceipt,
  index: Pick<
    WorkspaceIndex,
    'problemId' | 'workspace' | 'solverProjectRoot' | 'verifierProjectRoot' | 'sourceProjectRoot'
  >
): void => {
  if (
    receipt.problemId !== index.problemId ||
    path.resolve(receipt.workspaceRoot) !== path.resolve(index.workspace) ||
    path.resolve(receipt.projectRoot) !== path.resolve(index.solverProjectRoot) ||
    path.resolve(receipt.verifierProjectRoot || '') !== path.resolve(index.verifierProjectRoot) ||
    path.resolve(receipt.sourceProjectRoot || '') !== path.resolve(index.sourceProjectRoot)
  ) {
    throw new Error('Lean-Eval workspace index and bootstrap receipt identities do not match');
  }
};

/** Create or resume a sanitized, per-assignment solver repository. */
async function prepareLeanEvalTeamWorkspaceUnlocked(
  request: LeanEvalTeamWorkspaceRequest & Readonly<{ teamId: string; slotId: string }>
): Promise<LeanEvalTeamWorkspacePreparation> {
  const projectRoot = fs.realpathSync(path.resolve(request.projectRoot));
  const repositoryRoot = fs.realpathSync(path.resolve(request.repositoryRoot));
  const assignmentId = safeSegment(request.assignmentId, 'assignmentId');
  const branch = request.branch.trim();
  if (!branch || branch.startsWith('-') || branch.includes('..')) throw new Error('Lean-Eval branch name is invalid');
  if (!FULL_OID.test(request.expectedBaseCommit)) throw new Error('Lean-Eval assignment baseCommit is invalid');
  const existingPath = indexPath(projectRoot, assignmentId);
  if (fs.existsSync(existingPath)) {
    const existing = readIndex(existingPath);
    if (
      existing.problemId !== request.problemId ||
      existing.teamId !== request.teamId ||
      existing.slotId !== request.slotId ||
      existing.expectedBaseCommit !== request.expectedBaseCommit ||
      (existing.branch !== branch && !existing.sharedFromAssignmentId) ||
      existing.repositoryRoot !== repositoryRoot ||
      existing.projectRoot !== projectRoot
    ) {
      throw new Error('Lean-Eval assignment already has a different durable solver workspace');
    }
    if (
      !isWithin(os.tmpdir(), existing.workspace) ||
      !isWithin(os.tmpdir(), existing.verifierProjectRoot) ||
      !isWithin(os.tmpdir(), existing.sourceProjectRoot)
    ) {
      throw new Error('Lean-Eval durable solver workspace is outside the runtime temporary directory');
    }
    if (!fs.existsSync(existing.workspace) || !fs.existsSync(existing.receiptPath)) {
      throw new Error('Lean-Eval durable solver workspace is missing; discard the stale assignment and retry');
    }
    for (const [label, candidate] of [
      ['solver', existing.workspace],
      ['verifier', existing.verifierProjectRoot],
      ['source', existing.sourceProjectRoot],
    ] as const) {
      const stat = fs.lstatSync(candidate);
      if (stat.isSymbolicLink() || !stat.isDirectory()) {
        throw new Error(`Lean-Eval ${label} worktree is not a regular directory`);
      }
    }
    assertSolverSurface(existing.workspace);
    const existingReceipt = loadReceipt(existing.receiptPath);
    assertLeanEvalTeamWorkspaceReceiptBinding(existingReceipt, existing);
    return Object.freeze({
      ok: true,
      workspace: existing.workspace,
      baseCommit: existing.expectedBaseCommit,
      branch: existing.branch,
      actualBaseCommit: existing.actualBaseCommit,
      progressBaseCommit: existing.progressBaseCommit,
      receiptPath: existing.receiptPath,
      solverProjectRoot: existing.solverProjectRoot,
      verifierProjectRoot: existing.verifierProjectRoot,
      sourceProjectRoot: existing.sourceProjectRoot,
    });
  }

  // A candidate repair is a new durable assignment, but it must not create a
  // second solver repository. Reuse the source assignment's physical
  // workspace and branch, while writing a separate index for the new WAL
  // identity. The source index remains the owner and is therefore never
  // removed when the alias is discarded.
  const sourceAssignmentId = request.sourceAssignmentId
    ? safeSegment(request.sourceAssignmentId, 'sourceAssignmentId')
    : undefined;
  if (sourceAssignmentId) {
    if (sourceAssignmentId === assignmentId) {
      throw new Error('Lean-Eval sourceAssignmentId must differ from assignmentId');
    }
    const sourcePath = indexPath(projectRoot, sourceAssignmentId);
    if (!fs.existsSync(sourcePath)) {
      throw new Error(`Lean-Eval continuation source workspace is missing: ${sourceAssignmentId}`);
    }
    const source = readIndex(sourcePath);
    if (
      source.problemId !== request.problemId ||
      source.teamId !== request.teamId ||
      source.slotId !== request.slotId ||
      source.expectedBaseCommit !== request.expectedBaseCommit ||
      source.repositoryRoot !== repositoryRoot ||
      source.projectRoot !== projectRoot
    ) {
      throw new Error('Lean-Eval continuation source workspace identity does not match the repair assignment');
    }
    if (
      !isWithin(os.tmpdir(), source.workspace) ||
      !isWithin(os.tmpdir(), source.verifierProjectRoot) ||
      !isWithin(os.tmpdir(), source.sourceProjectRoot)
    ) {
      throw new Error('Lean-Eval continuation source workspace is outside the runtime temporary directory');
    }
    if (!fs.existsSync(source.workspace) || !fs.existsSync(source.receiptPath)) {
      throw new Error('Lean-Eval continuation source workspace is missing; recovery cannot start a new repository');
    }
    assertSolverSurface(source.workspace);
    const sourceReceipt = loadReceipt(source.receiptPath);
    assertLeanEvalTeamWorkspaceReceiptBinding(sourceReceipt, source);
    const sourceStatus = porcelainOutsideRuntimeMetadata(
      source.workspace,
      path.join(source.workspace, '.deepscientist')
    );
    if (sourceStatus) {
      throw new Error('Lean-Eval continuation source workspace must be clean before reuse');
    }
    const progressBaseCommit = git(source.workspace, ['rev-parse', 'HEAD']).toLowerCase();
    const ownerAssignmentId = source.workspaceOwnerAssignmentId || source.assignmentId;
    const alias: WorkspaceIndex = Object.freeze({
      ...source,
      assignmentId,
      workspaceOwnerAssignmentId: ownerAssignmentId,
      sharedFromAssignmentId: source.assignmentId,
      progressBaseCommit,
      integrated: undefined,
      integratedAt: undefined,
      deliveredHead: undefined,
      mergedCommit: undefined,
    });
    writeIndex(alias);
    return Object.freeze({
      ok: true,
      workspace: alias.workspace,
      baseCommit: alias.expectedBaseCommit,
      branch: alias.branch,
      actualBaseCommit: alias.actualBaseCommit,
      progressBaseCommit: alias.progressBaseCommit,
      receiptPath: alias.receiptPath,
      solverProjectRoot: alias.solverProjectRoot,
      verifierProjectRoot: alias.verifierProjectRoot,
      sourceProjectRoot: alias.sourceProjectRoot,
    });
  }

  let bootstrapped: Awaited<ReturnType<typeof bootstrapLeanEvalProblem>> | undefined;
  bootstrapped = await bootstrapLeanEvalProblem({
    repositoryRoot,
    problemId: request.problemId,
    workspaceParent: os.tmpdir(),
    useOfficialCredits: true,
  });
  try {
    assertSolverSurface(bootstrapped.receipt.workspaceRoot);
    const actualBaseCommit = initializeSolverGit(bootstrapped.receipt.workspaceRoot, branch);
    const index: WorkspaceIndex = Object.freeze({
      schema: INDEX_SCHEMA,
      assignmentId,
      problemId: request.problemId,
      teamId: request.teamId,
      slotId: request.slotId,
      expectedBaseCommit: request.expectedBaseCommit,
      branch,
      repositoryRoot,
      projectRoot,
      workspace: bootstrapped.receipt.workspaceRoot,
      receiptPath: bootstrapped.receipt.activeProblemPath,
      solverProjectRoot: bootstrapped.receipt.projectRoot,
      verifierProjectRoot: bootstrapped.receipt.verifierProjectRoot,
      sourceProjectRoot: bootstrapped.receipt.sourceProjectRoot,
      actualBaseCommit,
      progressBaseCommit: actualBaseCommit,
      workspaceOwnerAssignmentId: assignmentId,
    });
    writeIndex(index);
    const winner = readIndex(indexPath(projectRoot, assignmentId));
    if (
      winner.problemId !== index.problemId ||
      winner.teamId !== index.teamId ||
      winner.slotId !== index.slotId ||
      winner.workspace !== index.workspace
    ) {
      throw new Error('Lean-Eval assignment workspace index was replaced by a different preparation');
    }
    return Object.freeze({
      ok: true,
      workspace: index.workspace,
      baseCommit: index.expectedBaseCommit,
      branch: index.branch,
      actualBaseCommit,
      progressBaseCommit: index.progressBaseCommit,
      receiptPath: index.receiptPath,
      solverProjectRoot: index.solverProjectRoot,
      verifierProjectRoot: index.verifierProjectRoot,
      sourceProjectRoot: index.sourceProjectRoot,
    });
  } catch (error) {
    discardLeanEvalTeamWorkspace({ projectRoot, assignmentId });
    if (bootstrapped) {
      try {
        cleanupLeanEvalBootstrap(bootstrapped);
      } catch {
        // The artifact reaper handles detached worktrees left by a failed cleanup.
      }
    }
    throw error;
  }
}

export async function prepareLeanEvalTeamWorkspace(
  request: LeanEvalTeamWorkspaceRequest & Readonly<{ teamId: string; slotId: string }>
): Promise<LeanEvalTeamWorkspacePreparation> {
  const projectRoot = fs.realpathSync(path.resolve(request.projectRoot));
  const assignmentId = safeSegment(request.assignmentId, 'assignmentId');
  const lock = await acquireAssignmentLock(projectRoot, assignmentId);
  try {
    return await prepareLeanEvalTeamWorkspaceUnlocked(request);
  } finally {
    releaseAssignmentLock(lock);
  }
}

const branchDescriptor = (index: WorkspaceIndex, head: string, state: 'clean' | 'dirty' | 'missing') =>
  Object.freeze({
    name: index.branch,
    ref: `refs/heads/${index.branch}`,
    head,
    shortHead: head.slice(0, 8),
    active: false,
    status: index.integrated ? ('completed' as const) : ('candidate' as const),
    baseCommit: index.expectedBaseCommit,
    worktreePath: index.workspace,
    worktreeState: state,
  });

const porcelainOutsideRuntimeMetadata = (workspace: string, runtimeMetadataRoot: string): string => {
  const metadataRelative = path.relative(workspace, runtimeMetadataRoot).replaceAll(path.sep, '/');
  return git(workspace, ['status', '--porcelain=v1', '--untracked-files=all'])
    .split(/\r?\n/u)
    .map((line) => line.trimEnd())
    .filter(Boolean)
    .filter((line) => {
      if (!line.startsWith('?? ')) return true;
      const candidate = line.slice(3).replaceAll('\\', '/');
      return candidate !== metadataRelative && !candidate.startsWith(`${metadataRelative}/`);
    })
    .join('\n');
};

const gitBlob = (workspace: string, commit: string, relativePath: string): Buffer | undefined => {
  const result = spawnSync('git', ['-C', workspace, 'show', `${commit}:${relativePath}`], {
    encoding: 'buffer',
    maxBuffer: 16 * 1024 * 1024,
  });
  if (result.status !== 0) return undefined;
  return Buffer.isBuffer(result.stdout) ? result.stdout : Buffer.from(result.stdout || '');
};

const gitNameStatus = (
  workspace: string,
  from: string,
  to: string
): readonly Readonly<{ status: string; relativePath: string }>[] => {
  const result = spawnSync('git', ['-C', workspace, 'diff', '--name-status', '--no-renames', '-z', from, to], {
    encoding: 'utf8',
    maxBuffer: 8 * 1024 * 1024,
  });
  if (result.status !== 0) throw new Error(result.stderr?.trim() || 'Unable to inspect the Lean-Eval solver delta');
  const fields = result.stdout.split('\0');
  const entries: Array<Readonly<{ status: string; relativePath: string }>> = [];
  for (let cursor = 0; cursor + 1 < fields.length; cursor += 2) {
    const status = fields[cursor]?.trim() || '';
    const relativePath = fields[cursor + 1]?.replaceAll('\\', '/') || '';
    if (status && relativePath) entries.push(Object.freeze({ status, relativePath }));
  }
  return Object.freeze(entries);
};

const mergeLeanSource = (current: Buffer, base: Buffer, candidate: Buffer): Buffer => {
  if (current.equals(candidate) || candidate.equals(base)) return current;
  if (current.equals(base)) return candidate;
  const temporaryRoot = fs.mkdtempSync(path.join(os.tmpdir(), 'deepscientist-lean-eval-merge-'));
  try {
    const currentPath = path.join(temporaryRoot, 'current');
    const basePath = path.join(temporaryRoot, 'base');
    const candidatePath = path.join(temporaryRoot, 'candidate');
    fs.writeFileSync(currentPath, current, { mode: 0o600 });
    fs.writeFileSync(basePath, base, { mode: 0o600 });
    fs.writeFileSync(candidatePath, candidate, { mode: 0o600 });
    const result = spawnSync('git', ['merge-file', '-p', currentPath, basePath, candidatePath], {
      encoding: 'buffer',
      maxBuffer: 16 * 1024 * 1024,
    });
    if (result.status !== 0) {
      throw new Error(
        result.status === 1
          ? 'The Lean-Eval solver delta conflicts with canonical mathematical progress'
          : Buffer.from(result.stderr || '')
              .toString('utf8')
              .trim() || 'Unable to merge the Lean-Eval solver delta'
      );
    }
    return Buffer.isBuffer(result.stdout) ? result.stdout : Buffer.from(result.stdout || '');
  } finally {
    fs.rmSync(temporaryRoot, { recursive: true, force: true });
  }
};

const writeFileAtomic = (target: string, contents: Buffer): void => {
  const temporary = `${target}.${process.pid}.${crypto.randomUUID()}.tmp`;
  try {
    fs.writeFileSync(temporary, contents, { flag: 'wx', mode: 0o600 });
    fs.renameSync(temporary, target);
  } finally {
    fs.rmSync(temporary, { force: true });
  }
};

/** Promote only the receipt-authorized solver delta into canonical Project Git. */
function integrateLeanEvalTeamWorkspaceUnlocked(
  request: Readonly<{
    projectRoot: string;
    assignmentId: string;
    branch: string;
    expectedHead?: string;
    summary?: string;
  }>
): LeanEvalTeamWorkspaceIntegration {
  try {
    const index = readIndex(indexPath(request.projectRoot, request.assignmentId));
    if (index.branch !== request.branch) throw new Error('Lean-Eval branch does not match the assignment workspace');
    if (!fs.existsSync(index.workspace)) throw new Error('Lean-Eval solver workspace no longer exists');
    const canonicalProjectRoot = fs.realpathSync(path.resolve(request.projectRoot));
    if (canonicalProjectRoot !== fs.realpathSync(index.projectRoot)) {
      throw new Error('Lean-Eval integration target does not match the canonical project workspace');
    }
    const receipt = loadReceipt(index.receiptPath);
    assertLeanEvalTeamWorkspaceReceiptBinding(receipt, index);
    const head = git(index.workspace, ['rev-parse', 'HEAD']).toLowerCase();
    if (request.expectedHead && request.expectedHead.toLowerCase() !== head) {
      throw new Error('The delivered Lean-Eval commit is not the current solver branch head');
    }
    if (index.integrated && index.deliveredHead && index.mergedCommit) {
      if (index.deliveredHead !== head) {
        throw new Error('The integrated Lean-Eval solver branch advanced after its recorded delivery');
      }
      const canonicalHead = git(canonicalProjectRoot, ['rev-parse', 'HEAD']).toLowerCase();
      try {
        git(canonicalProjectRoot, ['merge-base', '--is-ancestor', index.mergedCommit!, canonicalHead]);
      } catch {
        throw new Error('The recorded Lean-Eval integration is absent from canonical Project Git');
      }
      return Object.freeze({
        ok: true,
        alreadyIntegrated: true,
        mergedCommit: index.mergedCommit,
        branch: branchDescriptor(index, head, 'clean'),
      });
    }

    const solverStatus = porcelainOutsideRuntimeMetadata(index.workspace, path.join(index.workspace, '.deepscientist'));
    if (solverStatus) throw new Error('Lean-Eval solver workspace must be clean before integration');
    try {
      git(index.workspace, ['merge-base', '--is-ancestor', index.actualBaseCommit, head]);
    } catch {
      throw new Error('The delivered Lean-Eval commit does not descend from the private solver baseline');
    }

    const canonicalRepositoryRoot = fs.realpathSync(git(canonicalProjectRoot, ['rev-parse', '--show-toplevel']));
    const metadataRoot = indexDirectory(canonicalProjectRoot);
    const canonicalStatus = porcelainOutsideRuntimeMetadata(canonicalRepositoryRoot, metadataRoot);
    if (canonicalStatus) throw new Error('Canonical Project Git must be clean before Lean-Eval integration');
    const canonicalHead = git(canonicalRepositoryRoot, ['rev-parse', 'HEAD']).toLowerCase();
    try {
      git(canonicalRepositoryRoot, ['merge-base', '--is-ancestor', index.expectedBaseCommit, canonicalHead]);
    } catch {
      throw new Error('Canonical Project Git no longer descends from the Team assignment baseCommit');
    }

    const solverPrefix = path.relative(index.workspace, index.solverProjectRoot).replaceAll(path.sep, '/');
    if (!solverPrefix || solverPrefix.startsWith('../') || path.isAbsolute(solverPrefix)) {
      throw new Error('Lean-Eval solver project path is outside its private repository');
    }
    const allowed = new Map<string, string>(
      receipt.solverOwnedFiles.map((relativePath) => [`${solverPrefix}/${relativePath}`, relativePath] as const)
    );
    const delta = gitNameStatus(index.workspace, index.actualBaseCommit, head);
    if (delta.some((entry) => entry.status !== 'M' || !allowed.has(entry.relativePath))) {
      throw new Error('Lean-Eval solver commit contains a deletion or a change outside receipt-authorized files');
    }

    const promoted: Array<{
      absolutePath: string;
      repositoryPath: string;
      original: Buffer;
      merged: Buffer;
    }> = [];
    for (const entry of delta) {
      const solverOwnedPath = allowed.get(entry.relativePath)!;
      const absolutePath = path.resolve(canonicalProjectRoot, solverOwnedPath);
      if (!isWithin(canonicalProjectRoot, absolutePath) || !fs.existsSync(absolutePath)) {
        throw new Error(`Canonical solver-owned file is missing: ${solverOwnedPath}`);
      }
      const stat = fs.lstatSync(absolutePath);
      if (stat.isSymbolicLink() || !stat.isFile()) {
        throw new Error(`Canonical solver-owned file is unsafe: ${solverOwnedPath}`);
      }
      const repositoryPath = path.relative(canonicalRepositoryRoot, absolutePath).replaceAll(path.sep, '/');
      const base = gitBlob(index.workspace, index.actualBaseCommit, entry.relativePath);
      const candidate = gitBlob(index.workspace, head, entry.relativePath);
      const current = gitBlob(canonicalRepositoryRoot, canonicalHead, repositoryPath);
      if (!base || !candidate || !current) {
        throw new Error(`Lean-Eval integration cannot resolve all versions of ${solverOwnedPath}`);
      }
      const merged = mergeLeanSource(current, base, candidate);
      if (!merged.equals(current)) promoted.push({ absolutePath, repositoryPath, original: current, merged });
    }

    if (
      git(canonicalRepositoryRoot, ['rev-parse', 'HEAD']).toLowerCase() !== canonicalHead ||
      porcelainOutsideRuntimeMetadata(canonicalRepositoryRoot, metadataRoot)
    ) {
      throw new Error('Canonical Project Git changed while preparing Lean-Eval integration');
    }
    let mergedCommit = canonicalHead;
    if (promoted.length) {
      try {
        for (const file of promoted) writeFileAtomic(file.absolutePath, file.merged);
        git(canonicalRepositoryRoot, ['add', '--', ...promoted.map((file) => file.repositoryPath)]);
        const subject = (request.summary?.trim() || request.assignmentId).replace(/[\r\n]+/gu, ' ').slice(0, 160);
        const committed = spawnSync(
          'git',
          [
            '-C',
            canonicalRepositoryRoot,
            '-c',
            'user.name=DeepScientist Lean-Eval Integration',
            '-c',
            'user.email=lean-eval-integration@deepscientist.invalid',
            'commit',
            '--no-gpg-sign',
            '-m',
            `Lean-Eval integrate: ${subject}`,
          ],
          { encoding: 'utf8', maxBuffer: 8 * 1024 * 1024 }
        );
        if (committed.status !== 0) {
          throw new Error(committed.stderr?.trim() || 'Unable to commit the canonical Lean-Eval integration');
        }
        mergedCommit = git(canonicalRepositoryRoot, ['rev-parse', 'HEAD']).toLowerCase();
      } catch (error) {
        for (const file of promoted) writeFileAtomic(file.absolutePath, file.original);
        try {
          git(canonicalRepositoryRoot, [
            'reset',
            '--quiet',
            canonicalHead,
            '--',
            ...promoted.map((file) => file.repositoryPath),
          ]);
        } catch {
          // Preserve the integration error; the restored worktree remains reviewable.
        }
        throw error;
      }
    }

    const completedIndex = Object.freeze({
      ...index,
      integrated: true,
      integratedAt: Date.now(),
      deliveredHead: head,
      mergedCommit,
    });
    writeIndex(completedIndex);
    return Object.freeze({
      ok: true,
      alreadyIntegrated: false,
      mergedCommit,
      branch: branchDescriptor(completedIndex, head, 'clean'),
    });
  } catch (error) {
    return Object.freeze({ ok: false, error: error instanceof Error ? error.message : String(error) });
  }
}

export function integrateLeanEvalTeamWorkspace(
  request: Readonly<{
    projectRoot: string;
    assignmentId: string;
    branch: string;
    expectedHead?: string;
    summary?: string;
  }>
): LeanEvalTeamWorkspaceIntegration {
  try {
    const canonicalRepositoryRoot = fs.realpathSync(
      git(fs.realpathSync(path.resolve(request.projectRoot)), ['rev-parse', '--show-toplevel'])
    );
    return runProjectGitRepositoryMutation(canonicalRepositoryRoot, () =>
      integrateLeanEvalTeamWorkspaceUnlocked(request)
    );
  } catch (error) {
    return Object.freeze({ ok: false, error: error instanceof Error ? error.message : String(error) });
  }
}

/** Remove a per-assignment solver repository and its detached verifier/source worktrees. */
export function discardLeanEvalTeamWorkspace(request: Readonly<{ projectRoot: string; assignmentId: string }>): void {
  let file: string;
  try {
    file = indexPath(request.projectRoot, request.assignmentId);
  } catch {
    return;
  }
  if (!fs.existsSync(file)) return;
  let index: WorkspaceIndex;
  try {
    index = readIndex(file);
  } catch {
    fs.rmSync(file, { force: true });
    return;
  }
  // Continuation indexes are lightweight aliases. Removing one must preserve
  // the source assignment's solver repository so a later recovery can resume
  // the same candidate and compiler cache.
  if (index.sharedFromAssignmentId) {
    fs.rmSync(file, { force: true });
    return;
  }
  for (const worktree of [index.verifierProjectRoot, index.sourceProjectRoot, index.workspace]) {
    if (!isWithin(os.tmpdir(), worktree)) continue;
    let worktreeStat: fs.Stats;
    try {
      worktreeStat = fs.lstatSync(worktree);
    } catch {
      continue;
    }
    if (worktreeStat.isSymbolicLink()) {
      // Never pass a symlink to `git worktree remove`; remove only the link
      // itself and leave any target outside the runtime-owned directory.
      fs.rmSync(worktree, { force: true });
      continue;
    }
    if (worktree === index.verifierProjectRoot || worktree === index.sourceProjectRoot) {
      try {
        git(index.repositoryRoot, ['worktree', 'remove', '--force', worktree]);
      } catch {
        fs.rmSync(worktree, { recursive: true, force: true });
      }
    } else {
      fs.rmSync(worktree, { recursive: true, force: true });
    }
  }
  if (index.repositoryRoot && fs.existsSync(index.repositoryRoot)) {
    try {
      git(index.repositoryRoot, ['worktree', 'prune']);
    } catch {
      // Maintenance reaper handles stale worktree records.
    }
  }
  fs.rmSync(file, { force: true });
  reapLeanEvalArtifacts({ repositoryRoot: index.repositoryRoot, projectRoots: [index.projectRoot] });
}

/** Remove every durable Lean-Eval workspace owned by one deleted Team. */
export function discardLeanEvalTeamWorkspacesForTeam(
  request: Readonly<{ projectRoot: string; teamId: string }>
): readonly string[] {
  const teamId = request.teamId.trim();
  if (!teamId) throw new Error('Lean-Eval Team cleanup requires teamId');
  const directory = indexDirectory(request.projectRoot);
  if (!fs.existsSync(directory)) return Object.freeze([]);

  const matches: Array<Readonly<{ assignmentId: string; alias: boolean }>> = [];
  for (const entry of fs.readdirSync(directory)) {
    if (!entry.endsWith('.json')) continue;
    try {
      const index = readIndex(path.join(directory, entry));
      if (index.teamId !== teamId) continue;
      matches.push(Object.freeze({ assignmentId: index.assignmentId, alias: Boolean(index.sharedFromAssignmentId) }));
    } catch {
      // A malformed index has no trustworthy Team owner and is left for the
      // age-based maintenance reaper.
    }
  }

  // Remove lightweight continuation aliases before their physical owner.
  matches.sort((left, right) => Number(right.alias) - Number(left.alias));
  const discarded: string[] = [];
  for (const match of matches) {
    discardLeanEvalTeamWorkspace({ projectRoot: request.projectRoot, assignmentId: match.assignmentId });
    if (!fs.existsSync(indexPath(request.projectRoot, match.assignmentId))) discarded.push(match.assignmentId);
  }
  return Object.freeze(discarded);
}

export function findLeanEvalTeamReceipt(projectRoot: string, problemId: string): string | undefined {
  const directory = indexDirectory(projectRoot);
  if (!fs.existsSync(directory)) return undefined;
  const matches = new Set<string>();
  for (const entry of fs.readdirSync(directory)) {
    if (!entry.endsWith('.json')) continue;
    try {
      const index = readIndex(path.join(directory, entry));
      if (index.problemId !== problemId || !fs.existsSync(index.receiptPath)) continue;
      // Discovery is used by a caller that may not have an assignment id. Do
      // not return a path merely because its index is syntactically valid;
      // require the durable receipt to prove the same workspace identity.
      const receipt = loadReceipt(index.receiptPath);
      assertLeanEvalTeamWorkspaceReceiptBinding(receipt, index);
      matches.add(index.receiptPath);
    } catch {
      // Ignore malformed stale indexes; the next maintenance pass can remove them.
    }
  }
  // A problem can have several concurrent Team assignments.  Never select a
  // receipt by directory order; callers must provide an explicit path when
  // more than one durable workspace matches the problem.
  return matches.size === 1 ? matches.values().next().value : undefined;
}

export function hasLeanEvalTeamWorkspace(projectRoot: string, assignmentId: string): boolean {
  try {
    const index = readIndex(indexPath(projectRoot, assignmentId));
    const receipt = loadReceipt(index.receiptPath);
    assertLeanEvalTeamWorkspaceReceiptBinding(receipt, index);
    return [index.workspace, index.verifierProjectRoot, index.sourceProjectRoot].every((candidate) => {
      const stat = fs.lstatSync(candidate);
      return stat.isDirectory() && !stat.isSymbolicLink();
    });
  } catch {
    return false;
  }
}

export function readLeanEvalTeamWorkspaceReceipt(
  projectRoot: string,
  assignmentId: string
): Readonly<{ index: WorkspaceIndex; receipt: LeanEvalBootstrapReceipt }> {
  const index = readIndex(indexPath(projectRoot, assignmentId));
  const receipt = loadReceipt(index.receiptPath);
  assertLeanEvalTeamWorkspaceReceiptBinding(receipt, index);
  return Object.freeze({ index, receipt });
}
