import { readMathJson, writeMathJsonDurable } from '../math/mathRuntimeIo';
import type { SolverProblem } from './problem';
import type { ProofCheck } from './modules/evidence';
import type { SolverFailure } from './feedback';
import type { ResearchCandidate } from './modules/execution';
import type { LemmaResearch } from './lemma';
import type { ResearchRole } from './modules/organization';
import type { CooperationState } from './cooperation';
import type { MathAgentActivity } from '../runtime/codexSession';
import type { TokenBudget, UsageAccounting } from './usageBudget';
import { z } from 'zod';

export type SolverWorkerState = Pick<SolverRunState, 'worktree' | 'threadId' | 'previousThreadIds' |
  'lastInputTokens' | 'lastActivity' | 'lastFailure' | 'phase' | 'turns' | 'dispatchCounts' | 'usage' | 'usageBeforeThread' | 'usageAccounting' | 'check' | 'candidate' | 'lemmaResearch' | 'failures' | 'error'> & {
  id: string;
  role: ResearchRole;
  sessionRole?: ResearchRole;
  sessionGroupId?: string;
  sessionTaskId?: string;
  sessionTaskVersion?: string;
  sessionStatementReview?: boolean;
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
  coordination?: 'cooperative' | 'independent';
  moduleConfiguration?: { id: string; versions: Record<string, string> };
  retrievalDigest?: string;
  model: string;
  effort: string;
  worktree: string;
  threadId?: string;
  previousThreadIds?: string[];
  lastInputTokens?: number;
  lastActivity?: MathAgentActivity & { at: number };
  lastFailure?: { at: number; reason: string; taskId?: string };
  phase: 'prepared' | 'running' | 'checking' | 'evaluating' | 'finished';
  turns: number;
  /** Dispatches are scheduling events, not equal units of computation. */
  dispatchCounts?: Partial<Record<'planning' | 'research' | 'proof' | 'review', number>>;
  solveStartedAt?: number;
  solveFinishedAt?: number;
  usage?: Record<string, unknown>;
  usageBeforeThread?: Record<string, unknown>;
  usageAccounting?: UsageAccounting;
  tokenBudget?: TokenBudget;
  check?: ProofCheck;
  candidate?: ResearchCandidate;
  lemmaResearch?: LemmaResearch;
  failures?: SolverFailure[];
  error?: string;
  workerCount?: number;
  workers?: SolverWorkerState[];
  cooperation?: CooperationState;
  winningWorker?: string;
};

const phase = z.enum(['prepared', 'running', 'checking', 'evaluating', 'finished']);
const count = z.number().int().nonnegative();
const record = z.record(z.unknown());
const safeCount = count.max(Number.MAX_SAFE_INTEGER);
const usageAccounting = z.object({ startedTurns: safeCount, reportedTurns: safeCount,
  pending: z.boolean(), incomplete: z.boolean() }).refine(value => value.reportedTurns <= value.startedTurns);
const tokenBudget = z.object({ maxTotalTokens: safeCount, enforcement: z.literal('provider-observed-dispatch-limit'),
  status: z.enum(['unlimited', 'available', 'exhausted', 'usage-unavailable']), reportedTotalTokens: safeCount.nullable(),
  usageComplete: z.boolean(), overrunTokens: safeCount.nullable(),
  reason: z.enum(['math_total_token_limit', 'math_model_usage_unavailable']).optional() });
const check = z.object({ commit: z.string().min(1), sourceDigest: z.string().min(1), passed: z.boolean(),
  verification: z.object({ status: z.enum(['kernel_verified', 'failed', 'blocked', 'unavailable']),
    targetCommit: z.string().optional(), results: z.array(record) }).passthrough() }).passthrough();
const research = z.object({ worktree: z.string().min(1), phase, turns: count, threadId: z.string().optional(),
  dispatchCounts: z.object({ planning: count.optional(), research: count.optional(), proof: count.optional(), review: count.optional() }).optional(),
  solveStartedAt: count.optional(), solveFinishedAt: count.optional(),
  previousThreadIds: z.array(z.string()).optional(), lastInputTokens: count.optional(), check: check.optional(),
  lastActivity: z.object({ at: count, event: z.string().min(1).max(64), itemType: z.string().max(64).optional() }).optional(),
  lastFailure: z.object({ at: count, reason: z.string(), taskId: z.string().optional() }).optional(),
  usage: record.optional(), usageBeforeThread: record.optional(), usageAccounting: usageAccounting.optional(),
  tokenBudget: tokenBudget.optional(), candidate: record.optional(),
  lemmaResearch: record.optional(), failures: z.array(record).optional(), error: z.string().optional() }).passthrough();
const role = z.enum(['lead', 'researcher', 'engineer', 'reviewer']);
const task = z.object({ id: z.string().min(1), kind: z.enum(['research', 'sketch', 'lemma', 'goal']),
  objective: z.string(), dependsOn: z.array(z.string()), revision: count }).passthrough();
const taskRecord = z.object({ task, status: z.enum(['pending', 'running', 'blocked', 'conditional', 'delivered', 'integrated', 'completed']),
  attempts: count, proof: check.optional(), integratedCheck: check.optional(), assignment: z.object({ taskId: z.string(),
    taskDigest: z.string(), workerId: z.string(), seedCommit: z.string() }).passthrough().optional() }).passthrough();
const runState = research.extend({ schema: z.literal('deepscientist.math.solver.v1'), runId: z.string().min(1),
  problem: z.object({ workspace: z.string(), receiptDigest: z.string() }).passthrough(),
  taskDigest: z.string(), buildDigest: z.string(), environmentDigest: z.string(), evaluatorDigest: z.string(),
  model: z.string(), effort: z.string(), workerCount: z.number().int().positive().optional(),
  coordination: z.enum(['cooperative', 'independent']).optional(),
  workers: z.array(research.extend({ id: z.string(), role, sessionRole: role.optional() })).optional(),
  cooperation: z.object({ tasks: z.array(taskRecord), groups: z.array(z.object({ group: z.object({ id: z.string(),
    status: z.enum(['active', 'paused', 'stopped']), revision: count }).passthrough(), turns: count }).passthrough()).optional(),
    history: z.array(z.object({ task, proof: check.optional(), integratedCheck: check.optional() }).passthrough()).optional(),
    deliveries: z.array(record).optional() }).passthrough().optional(),
});

/** Parse persisted control state once; optional advisory fields and older extra fields remain readable. */
export const readSolverRunState = (file: string): SolverRunState => {
  const parsed = runState.safeParse(readMathJson(file));
  if (!parsed.success) throw new Error(`math_resume_state_invalid:${parsed.error.issues[0]?.path.join('.')}`);
  return parsed.data as unknown as SolverRunState;
};
export const writeSolverRunState = (file: string, state: SolverRunState): void => writeMathJsonDurable(file, state);
