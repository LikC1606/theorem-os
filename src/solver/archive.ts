import { readMathJson, writeMathJsonDurable } from '../math/mathRuntimeIo';
import type { SolverProblem } from './problem';
import type { ProofCheck } from './modules/evidence';
import type { SolverFailure } from './feedback';
import type { ResearchCandidate } from './modules/execution';
import type { LemmaResearch } from './lemma';
import type { ResearchRole } from './modules/organization';
import type { CooperationState } from './cooperation';
import type { MathAgentActivity } from '../runtime/codexSession';
import type { TokenBudget, UsageAccounting, RequestUsageAccounting } from './usageBudget';
import type { ContextManifest } from './contextCompiler';
import type { ModelTurnLedger } from './turnLedger';
import { z } from 'zod';

export type SolverWorkerState = Pick<SolverRunState, 'worktree' | 'threadId' | 'previousThreadIds' |
  'lastInputTokens' | 'lastActivity' | 'lastFailure' | 'recovery' | 'contextOverflow' | 'lastContextManifest' | 'phase' | 'turns' | 'dispatchCounts' | 'usage' | 'usageBeforeThread' | 'usageAccounting' | 'requestUsageAccounting' | 'check' | 'candidate' | 'lemmaResearch' | 'failures' | 'error'> & {
  id: string;
  role: ResearchRole;
  sessionRole?: ResearchRole;
  sessionGroupId?: string;
  sessionTaskId?: string;
  sessionTaskVersion?: string;
  sessionAssignmentId?: string;
  sessionStatementReview?: boolean;
};

export type ResearchRecovery = {
  phase: 'cooling-down' | 'retrying' | 'recovered'; reason: string; cycles: number;
  startedAt: number; nextRetryAt: number; waitedMs: number; recoveredAt?: number;
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
  providerProfile?: string;
  providerProfileDigest?: string;
  methodDigest?: string;
  coordination?: 'cooperative' | 'independent';
  moduleConfiguration?: { id: string; versions: Record<string, string> };
  retrievalDigest?: string;
  knowledgeDigest?: string;
  model: string;
  effort: string;
  worktree: string;
  threadId?: string;
  previousThreadIds?: string[];
  lastInputTokens?: number;
  lastActivity?: MathAgentActivity & { at: number };
  lastFailure?: { at: number; reason: string; taskId?: string };
  recovery?: ResearchRecovery;
  contextOverflow?: { maxOptionalContextBytes: number; failedFreshContextDigests: string[] };
  lastContextManifest?: ContextManifest;
  phase: 'prepared' | 'running' | 'checking' | 'evaluating' | 'finished';
  turns: number;
  /** Dispatches are scheduling events, not equal units of computation. */
  dispatchCounts?: Partial<Record<'planning' | 'research' | 'proof' | 'review', number>>;
  solveStartedAt?: number;
  solveFinishedAt?: number;
  usage?: Record<string, unknown>;
  usageBeforeThread?: Record<string, unknown>;
  usageAccounting?: UsageAccounting;
  requestUsageAccounting?: RequestUsageAccounting;
  tokenBudget?: TokenBudget;
  turnLedger?: ModelTurnLedger;
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
const requestUsageAccounting = z.object({ startedRequests: safeCount, reportedRequests: safeCount,
  pendingRequests: safeCount, incomplete: z.boolean() }).refine(value =>
    value.reportedRequests <= value.startedRequests && value.pendingRequests <= value.startedRequests - value.reportedRequests);
const tokenBudget = z.object({ maxTotalTokens: safeCount,
  enforcement: z.enum(['provider-observed-dispatch-limit', 'provider-observed-upstream-request-limit']),
  status: z.enum(['unlimited', 'available', 'exhausted', 'usage-unavailable']), reportedTotalTokens: safeCount.nullable(),
  usageComplete: z.boolean(), overrunTokens: safeCount.nullable(),
  reason: z.enum(['math_total_token_limit', 'math_model_usage_unavailable']).optional() });
const turnOutcome = z.object({ evidence: z.literal('recorded-not-replayed'), acceptance: z.literal('not-assessed'),
  attribution: z.literal('observed-not-causal'), observedProgress: z.object({ scope: z.enum(['assignment-cone', 'run']),
    taskVersionMatches: z.boolean(), beforeDigest: z.string(), afterDigest: z.string(),
    obligations: z.object({ closed: z.array(z.string()), reopened: z.array(z.string()), changed: z.array(z.string()) }),
    frontierChangedGoalIds: z.array(z.string()), advisoryChangedTaskIds: z.array(z.string()) }),
  retainedWork: z.object({ value: z.literal('not-assessed'), deliveries: z.array(z.object({ id: z.string(), kind: z.string(), status: z.string(),
    taskId: z.string().optional(), taskDigest: z.string().optional(), commit: z.string().optional(), findingDigest: z.string().optional(),
    evidenceRefs: z.array(z.string()), artifacts: z.object({ scope: z.string(), digest: z.string() }).optional() })),
  drafts: z.array(z.object({ taskId: z.string(), taskDigest: z.string(), assignmentId: z.string().optional(), commit: z.string(),
    outputDigest: z.string(), artifactDigest: z.string(), evidenceStatus: z.literal('advisory-unverified') })),
  blockers: z.array(z.object({ id: z.string(), taskId: z.string(), taskDigest: z.string(), status: z.string(), mechanism: z.string(),
    scope: z.string(), evidenceRefs: z.array(z.string()), count: safeCount, evidenceStatus: z.literal('advisory') })),
  failedInputs: z.array(z.object({ id: z.string(), taskId: z.string(), taskDigest: z.string(), attemptFingerprint: z.string().optional(),
    relatedFailureIds: z.array(z.string()).optional(), feedbackDigest: z.string(), evidenceStatus: z.literal('recorded-failure') })),
  checkpoint: z.object({ taskDigest: z.string(), inputDigest: z.string(), outputDigest: z.string(), count: safeCount, paused: z.boolean(),
    evidenceStatus: z.literal('candidate-not-scored') }).passthrough().optional(),
  check: z.object({ commit: z.string(), sourceDigest: z.string(), passed: z.boolean(), status: z.string(), receiptIds: z.array(z.string()) }).optional(),
}) });
const modelTurnReceipt = z.object({ schema: z.literal('theoremos.model-turn.v1'), id: z.string(), workerId: z.string(),
  sessionId: z.string().optional(), threadId: z.string().optional(), turnId: z.string().optional(),
  workerTurn: safeCount, runTurn: safeCount, startedAt: safeCount,
  modelFinishedAt: safeCount.optional(), settledAt: safeCount.optional(),
  scope: z.object({ actionKind: z.string(), operation: z.string(), taskId: z.string().optional(), taskDigest: z.string().optional(),
    assignmentId: z.string().optional(), groupId: z.string().optional(), routeId: z.string().optional(),
    seedCommit: z.string().optional(), reviewId: z.string().optional(), planVersion: z.string().optional() }),
  execution: z.enum(['running', 'completed', 'interrupted', 'failed', 'recovered']),
  usage: z.object({ basis: z.literal('provider-thread-window'), attribution: z.literal('unverified'),
    coverage: z.enum(['pending', 'reported', 'partial', 'unknown']), beforeTotalTokens: safeCount.nullable(),
    afterTotalTokens: safeCount.nullable(), observedDeltaTokens: safeCount.nullable(), reportedUpdates: safeCount,
    uncertainReasons: z.array(z.string()) }),
  outcomeStatus: z.enum(['pending', 'recorded', 'unavailable-after-restart']), outcome: turnOutcome.optional() });
const taskReference = z.object({ taskId: z.string(), taskDigest: z.string() });
const handoffDecision = z.object({ id: z.string(), deliveryId: z.string(), status: z.enum(['adopted', 'rejected', 'deferred']),
  taskId: z.string().optional(), taskDigest: z.string().optional(), reason: z.string().optional(),
  waitsOn: z.array(z.object({ taskId: z.string().regex(/^[a-zA-Z0-9_-]{1,64}$/u),
    taskDigest: z.string().regex(/^[a-f0-9]{64}$/u) }).strict()).nonempty()
    .refine(values => new Set(values.map(value => value.taskId)).size === values.length).optional(),
}).passthrough().refine(value => value.waitsOn === undefined || value.status === 'deferred');
const declarationReference = z.object({ name: z.string(), file: z.string() });
const proofReferences = z.object({ sourceCommit: z.string(), environmentDigest: z.string(), contextDigest: z.string(),
  scope: z.literal('statement').optional(), root: declarationReference,
  inputs: z.array(z.object({ file: z.string(), name: z.string().optional(), digest: z.string() })),
  tasks: z.array(taskReference).optional(), statement: z.array(declarationReference), proof: z.array(declarationReference) });
const check = z.object({ commit: z.string().min(1), sourceDigest: z.string().min(1), passed: z.boolean(),
  taskDigest: z.string().optional(), conditions: z.array(taskReference).optional(), references: proofReferences.optional(),
  projection: z.object({ environmentDigest: z.string().min(1), problemReceiptDigest: z.string().min(1),
    sourceDigest: z.string().min(1) }).optional(),
  changes: z.array(z.object({ file: z.string(), name: z.string(), after: z.string() }).passthrough()).optional(),
  verification: z.object({ status: z.enum(['kernel_verified', 'failed', 'blocked', 'unavailable']),
    targetCommit: z.string().optional(), results: z.array(record) }).passthrough() }).passthrough();
const research = z.object({ worktree: z.string().min(1), phase, turns: count, threadId: z.string().optional(),
  dispatchCounts: z.object({ planning: count.optional(), research: count.optional(), proof: count.optional(), review: count.optional() }).optional(),
  solveStartedAt: count.optional(), solveFinishedAt: count.optional(),
  previousThreadIds: z.array(z.string()).optional(), lastInputTokens: count.optional(), check: check.optional(),
  lastActivity: z.object({ at: count, event: z.string().min(1).max(64), itemType: z.string().max(64).optional() }).optional(),
  lastFailure: z.object({ at: count, reason: z.string(), taskId: z.string().optional() }).optional(),
  recovery: z.object({ phase: z.enum(['cooling-down', 'retrying', 'recovered']), reason: z.string(),
    cycles: safeCount.min(1), startedAt: safeCount, nextRetryAt: safeCount, waitedMs: safeCount,
    recoveredAt: safeCount.optional() }).optional(),
  contextOverflow: z.object({ maxOptionalContextBytes: safeCount,
    failedFreshContextDigests: z.array(z.string().regex(/^[a-f0-9]{64}$/u)) }).optional(),
  usage: record.optional(), usageBeforeThread: record.optional(), usageAccounting: usageAccounting.optional(),
  requestUsageAccounting: requestUsageAccounting.optional(),
  tokenBudget: tokenBudget.optional(), candidate: record.optional(),
  lemmaResearch: record.optional(), failures: z.array(record).optional(), error: z.string().optional() }).passthrough();
const role = z.enum(['lead', 'researcher', 'engineer', 'reviewer']);
const task = z.object({ id: z.string().min(1), kind: z.enum(['research', 'sketch', 'lemma', 'goal']),
  objective: z.string(), dependsOn: z.array(z.string()), revision: count }).passthrough();
const taskRecord = z.object({ task, status: z.enum(['pending', 'running', 'blocked', 'conditional', 'delivered', 'integrated', 'completed']),
  pendingValidation: z.object({ id: z.string().min(1), taskDigest: z.string().min(1), canonicalCommit: z.string().min(1),
    environmentDigest: z.string().min(1), problemReceiptDigest: z.string().min(1), proof: z.boolean().optional() }).optional(),
  attempts: count, proof: check.optional(), integratedCheck: check.optional(), assignment: z.object({ taskId: z.string(),
    taskDigest: z.string(), workerId: z.string(), seedCommit: z.string(), assignmentId: z.string().optional() }).passthrough().optional() }).passthrough();
const routeBlocker = z.object({ id: z.string(), taskId: z.string(), groupId: z.string(), taskDigest: z.string(),
  routeId: z.string().optional(),
  mechanism: z.string(), scope: z.string(), evidenceStatus: z.literal('advisory'), evidenceRefs: z.array(z.string()),
  reopenOn: z.array(z.discriminatedUnion('kind', [z.object({ kind: z.literal('contract-changed') }),
    z.object({ kind: z.literal('environment-changed') }), z.object({ kind: z.literal('dependency-checked'), taskId: z.string() })])),
  basis: z.object({ contractDigest: z.string(), environmentDigest: z.string(), dependencies: z.record(z.object({
    contractDigest: z.string(), evidenceDigest: z.string().optional() })) }), fingerprint: z.string(), count: safeCount.min(1),
  status: z.enum(['open', 'parked', 'reopened', 'superseded']), createdAt: count, updatedAt: count,
  reopenedReason: z.string().optional() });
const recordedObligation = z.object({ taskId: z.string(), taskDigest: z.string(), kind: z.enum(['lemma', 'goal']),
  groupId: z.string(), recordedProof: z.enum(['none', 'stale', 'failed', 'unverified', 'conditional', 'checked']),
  closed: z.boolean(), conditions: z.array(taskReference), referenceCoverage: z.enum(['available', 'missing']),
  evidenceDigest: z.string().optional() });
const frontierItem = z.object({ taskId: z.string(), taskDigest: z.string().nullable() });
const goalFrontier = z.object({ taskId: z.string(), taskDigest: z.string(), closed: z.boolean(),
  frontier: z.array(frontierItem), missingDependencies: z.array(z.string()), routeCombination: z.literal('any').optional(),
  alternatives: z.array(z.object({ routeId: z.string(), frontier: z.array(frontierItem),
    missingDependencies: z.array(z.string()), parkedBy: z.array(z.string()).optional() })).optional() });
const recordedBlocker = routeBlocker.omit({ fingerprint: true, count: true, createdAt: true, updatedAt: true });
const routeStatus = z.enum(['none', 'conditional', 'checked', 'stale', 'unverified']);
const recordedRoute = z.object({ evidence: z.literal('recorded-not-replayed'), routeId: z.string(), targetTaskId: z.string(),
  prerequisiteTaskIds: z.array(z.string()), closingTaskId: z.string(), closingType: z.string().nullable(),
  prerequisiteStatuses: z.array(z.object({ taskId: z.string(), status: routeStatus })),
  remainingPrerequisiteTaskIds: z.array(z.string()), closingStatus: routeStatus, ready: z.boolean(), targetStatus: routeStatus,
  connection: z.enum(['closed-by-original-check', 'awaiting-original-check']), referenceCoverageMissing: z.array(z.string()),
  parkedBy: z.array(z.string()).optional() });
const recordedAdvisory = z.object({ taskId: z.string(), taskDigest: z.string(), kind: z.enum(['research', 'sketch']),
  completed: z.boolean(), findingDigest: z.string().optional() });
const change = <T extends z.ZodTypeAny>(item: T) => z.object({ before: item, after: item });
const progressSnapshot = z.object({ schema: z.literal('theoremos.obligation-snapshot.v1'),
  evidence: z.literal('recorded-not-replayed'), acceptance: z.literal('not-assessed'), digest: z.string(),
  environmentDigest: z.string().optional(), obligations: z.array(recordedObligation), goals: z.array(goalFrontier),
  blockers: z.array(recordedBlocker), routes: z.array(recordedRoute), advisory: z.array(recordedAdvisory) });
const progressReceipt = z.object({ schema: z.literal('theoremos.obligation-progress.v1'),
  evidence: z.literal('recorded-not-replayed'), acceptance: z.literal('not-assessed'),
  kind: z.enum(['baseline', 'transition']), at: count, beforeDigest: z.string().optional(), afterDigest: z.string(), environmentChanged: z.boolean(),
  obligations: z.object({ new: z.array(recordedObligation), closed: z.array(change(recordedObligation)),
    reopened: z.array(change(recordedObligation)), removed: z.array(recordedObligation), changed: z.array(change(recordedObligation)) }),
  goalFrontiers: z.array(z.object({ goalId: z.string(), before: goalFrontier.optional(), after: goalFrontier.optional() })),
  blockers: z.object({ new: z.array(recordedBlocker), parked: z.array(change(recordedBlocker)), reopened: z.array(change(recordedBlocker)),
    superseded: z.array(change(recordedBlocker)), removed: z.array(recordedBlocker), changed: z.array(change(recordedBlocker)) }),
  routes: z.array(z.object({ routeId: z.string(), before: recordedRoute.optional(), after: recordedRoute.optional() })),
  advisory: z.object({ proposed: z.array(recordedAdvisory), completed: z.array(change(recordedAdvisory)),
    reopened: z.array(change(recordedAdvisory)), removed: z.array(recordedAdvisory), changed: z.array(change(recordedAdvisory)) }) });
const runState = research.extend({ schema: z.literal('deepscientist.math.solver.v1'), runId: z.string().min(1),
  problem: z.object({ workspace: z.string(), receiptDigest: z.string() }).passthrough(),
  taskDigest: z.string(), buildDigest: z.string(), environmentDigest: z.string(), evaluatorDigest: z.string(),
  providerProfile: z.string().optional(), providerProfileDigest: z.string().regex(/^[a-f0-9]{64}$/u).optional(),
  model: z.string(), effort: z.string(), workerCount: z.number().int().positive().optional(),
  knowledgeDigest: z.string().regex(/^[a-f0-9]{64}$/u).optional(),
  coordination: z.enum(['cooperative', 'independent']).optional(),
  turnLedger: z.object({ retainedLimit: safeCount.min(1), dropped: safeCount, unscopedReports: safeCount,
    turns: z.array(modelTurnReceipt) }).optional(),
  workers: z.array(research.extend({ id: z.string(), role, sessionRole: role.optional(),
    sessionAssignmentId: z.string().optional() })).optional(),
  cooperation: z.object({ tasks: z.array(taskRecord), groups: z.array(z.object({ group: z.object({ id: z.string(),
    status: z.enum(['active', 'paused', 'stopped']), revision: count }).passthrough(), turns: count }).passthrough()).optional(),
    history: z.array(z.object({ task, proof: check.optional(), integratedCheck: check.optional() }).passthrough()).optional(),
    deliveries: z.array(record).optional(), blockers: z.array(routeBlocker).optional(),
    researchDecisions: z.array(handoffDecision).optional(),
    leadSeedCommit: z.string().regex(/^[a-f0-9]{40,64}$/u).optional(),
    researchDrafts: z.record(z.object({ taskDigest: z.string(), workerId: z.string(), assignmentId: z.string().optional(),
      seedCommit: z.string().regex(/^[a-f0-9]{40,64}$/u), canonicalCommit: z.string().regex(/^[a-f0-9]{40,64}$/u).optional(),
      commit: z.string().regex(/^[a-f0-9]{40,64}$/u), outputDigest: z.string(), artifacts: record,
      suspended: z.boolean().optional() }).passthrough()).optional(),
    proofRoutes: z.array(z.object({ id: z.string(), targetTaskId: z.string(), prerequisiteTaskIds: z.array(z.string()),
      closingTaskId: z.string() })).optional(), progressSnapshot: progressSnapshot.optional(),
    progressReceipts: z.array(progressReceipt).max(64).optional() }).passthrough().optional(),
});

/** Parse persisted control state once; optional advisory fields and older extra fields remain readable. */
export const readSolverRunState = (file: string): SolverRunState => {
  const parsed = runState.safeParse(readMathJson(file));
  if (!parsed.success) throw new Error(`math_resume_state_invalid:${parsed.error.issues[0]?.path.join('.')}`);
  return parsed.data as unknown as SolverRunState;
};
export const writeSolverRunState = (file: string, state: SolverRunState): void => writeMathJsonDurable(file, state);
