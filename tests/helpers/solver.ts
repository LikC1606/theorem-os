import path from 'node:path';
import { bootstrapLocalExample, type LocalExampleReceipt } from '../../src/math/localExample';
import type { SolverRunState } from '../../src/solver/archive';
import type { ResearchWorker } from '../../src/solver/modules/organization';
import { git, readSolverProblem, type SolverProblem } from '../../src/solver/problem';
import { temporaryDirectory } from './files';

export type LocalExample = { directory: string; workspace: string; receipt: LocalExampleReceipt; problem: SolverProblem };

/** Bootstraps the local example into `<fresh temporary directory>/<name>` and reads its solver problem. */
export function localExample(prefix: string, name = 'workspace'): LocalExample {
  const directory = temporaryDirectory(prefix);
  const workspace = path.join(directory, name);
  const receipt = bootstrapLocalExample(workspace);
  return { directory, workspace, receipt, problem: readSolverProblem(workspace, receipt.activeProblemPath) };
}

export function leadWorker(problem: SolverProblem, worktree: string, id = 'solver'): ResearchWorker {
  return { id, role: 'lead', worktree, ownedFiles: problem.ownedFiles };
}

/** Adds a detached worktree `<directory>/<name ?? id>` at `commit` (default: the base commit) for a peer. */
export function peerWorker(example: LocalExample, id: string, { role = 'researcher', name = id, commit = example.problem.baseCommit }:
  { role?: ResearchWorker['role']; name?: string; commit?: string } = {}): ResearchWorker {
  const worktree = path.join(example.directory, name);
  git(example.workspace, ['worktree', 'add', '--quiet', '--detach', worktree, commit]);
  return { id, role, worktree, ownedFiles: example.problem.ownedFiles };
}

type StateFields = Pick<SolverRunState, 'runId' | 'phase'> & Partial<SolverRunState>;

/** Solver state with placeholder digests and unused model settings; `fields` adds or overrides keys. */
export function solverState(problem: SolverProblem, worktree: string, fields: StateFields): SolverRunState {
  const { runId, ...rest } = fields;
  return { schema: 'deepscientist.math.solver.v1', runId, problem,
    taskDigest: 'task', buildDigest: 'build', environmentDigest: 'environment', evaluatorDigest: 'evaluator',
    model: 'unused', effort: 'unused', worktree, turns: 0, ...rest };
}
