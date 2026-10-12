import { readMathJson, writeMathJsonDurable } from '../math/mathRuntimeIo';
import type { SolverProblem } from './problem';
import type { ProofCheck } from './modules/evidence';
import type { SolverFailure } from './feedback';
import type { ResearchCandidate } from './modules/execution';
import type { LemmaResearch } from './lemma';
import type { ResearchRole } from './modules/organization';
import type { CooperationState } from './cooperation';

export type SolverWorkerState = Pick<SolverRunState, 'worktree' | 'threadId' | 'previousThreadIds' |
  'lastInputTokens' | 'phase' | 'turns' | 'usage' | 'usageBeforeThread' | 'check' | 'candidate' | 'lemmaResearch' | 'failures'> & {
  id: string;
  role: ResearchRole;
  sessionRole?: ResearchRole;
  sessionGroupId?: string;
  error?: string;
};

/** S1: resumable records; storing a candidate never grants proof acceptance. */
export type SolverRunState = {
  schema: 'deepscientist.math.solver.v1';
  runId: string;
  problem: SolverProblem;
  taskDigest: string;
  buildDigest: string;
  environmentDigest: string;
  evaluatorDigest: string;
  methodDigest?: string;
  retrievalDigest?: string;
  model: string;
  effort: string;
  worktree: string;
  threadId?: string;
  previousThreadIds?: string[];
  lastInputTokens?: number;
  phase: 'prepared' | 'running' | 'checking' | 'evaluating' | 'finished';
  turns: number;
  usage?: Record<string, unknown>;
  usageBeforeThread?: Record<string, unknown>;
  check?: ProofCheck;
  candidate?: ResearchCandidate;
  lemmaResearch?: LemmaResearch;
  failures?: SolverFailure[];
  workerCount?: number;
  workers?: SolverWorkerState[];
  cooperation?: CooperationState;
  winningWorker?: string;
};

export const readSolverRunState = (file: string): SolverRunState => readMathJson(file) as SolverRunState;
export const writeSolverRunState = (file: string, state: SolverRunState): void => writeMathJsonDurable(file, state);
