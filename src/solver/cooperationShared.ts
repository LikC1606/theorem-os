import { parseCooperationPlan } from './tasks';
import { limitMathOutput } from '../math/mathProcess';
import { type SolverProblem } from './problem';
import { type ProofCheck } from './modules/evidence';
import { readMathResponse as block, type DeliveryRecord } from './deliveries';
import { type TaskProof } from './cooperativeProof';
import { type StatementReview } from './statementReview';
import { type DeliveryArtifactManifest } from './deliveryArtifacts';
import { type BlockerBasis, type RouteBlocker } from './routeControl';
import { type ProofRoute } from './proofRoutes';
import { type ResearchHandoffDecision } from './researchHandoffs';
import { type ResearchChallengeDecision } from './researchChallenges';
import { type ObligationSnapshot, type ObligationProgressReceipt } from './obligationProgress';
import { type TaskConsumerProjection } from './taskConsumers';
import { type CheckpointCandidate } from './researchEvidence';
import { type ParallelQuestion } from './taskQuestions';
import { mathematicalGaps } from './mathematicalGaps';
import { taskVersion, type CooperativeTask, type RouteRecord, type TaskRecord, type CooperativeAction } from './tasks';

export const digest = taskVersion;
export const taskSourceRejections = new Set(['math_task_source_outside_scope', 'math_task_ambiguous_declaration',
  'math_task_existing_declaration_removed', 'math_task_existing_declaration_changed', 'math_task_requires_theorem',
  'math_task_helper_is_original_declaration', 'math_task_conditional_header_unsupported',
  'math_original_declaration_changed', 'math_original_context_changed', 'math_local_module_import_cycle',
  'math_trusted_source_changed', 'math_source_outside_ownership']);
export const integrationRejections = new Set([...taskSourceRejections, 'math_task_condition_version_invalid',
  'math_task_delivery_no_longer_checks', 'math_task_dependency_invalidated', 'math_task_merged_proof_failed',
  'math_task_integration_conflict', 'math_task_integration_missing_context', 'math_task_integration_missing_declaration',
  'math_task_missing_declaration', 'math_task_check_identity_changed']);
export const directDeliveryRejections = new Set([...taskSourceRejections, 'math_task_missing_declaration', 'math_task_repeated_failed_input',
  'math_task_check_identity_changed',
  'math_research_delivery_invalid', 'math_research_delivery_unchanged', 'math_research_lemma_requests_invalid',
  'math_delivery_invalid', 'math_response_invalid', 'math_math-result_missing_or_too_large', 'math_math-result_requires_one_block',
  'math_delivery_artifact_not_regular_file', 'math_delivery_artifact_too_large', 'math_delivery_artifact_invalid_commit',
  'math_delivery_artifact_path_invalid', 'math_delivery_artifact_claim_invalid', 'math_delivery_artifact_required', 'math_route_blocker_invalid']);
export const rejectionCode = (error: Error) => error.message.split(/[\n:]/u, 1)[0];

export type ReviewRecord = { commit: string; sourceDigest: string; status: 'pending' | 'running' | 'accepted' | 'changes_requested';
  workerId?: string; assignmentId?: string; summary?: string };
export type HumanEditRecord = { id: string; status: 'received' | 'applied' | 'rejected'; reason?: string;
  receivedAt?: number; appliedAt?: number; baseVersion?: string; planVersion?: string; affectedTasks?: string[]; pendingSync?: boolean;
  recheck?: { status: 'pending' | 'passed' | 'failed' | 'not-required' | 'superseded';
    tasks: { taskId: string; taskDigest: string; status: 'pending' | 'conditional' | 'passed' | 'failed' | 'removed' | 'superseded'; reason?: string;
      lastCheck?: { commit: string; sourceDigest: string; environmentDigest: string; passed: boolean; conditional: boolean; receiptIds: string[] } }[] } };
export type InitialPlanPublication = { nonce: string; file: string; offset: number; eventDigest: string;
  baseVersion: string; planVersion: string; acceptedAt: number; finalized?: boolean };
export type FailedTaskInput = { id: string; taskId: string; taskDigest: string; inputDigest: string; basis: BlockerBasis;
  attemptFingerprint?: string; relatedFailureIds?: string[];
  sourceDigest: string; targetDigest: string; seedSourceDigest: string; seedTargetDigest: string;
  canonicalSourceDigest: string; canonicalTargetDigest: string; feedback: string;
  repair?: { taskId: string; taskDigest: string; workerId: string; pending: boolean; startedAttempt?: number } };
export type CooperationState = { tasks: TaskRecord[]; groups?: RouteRecord[]; canonicalCommit?: string; leadSeedCommit?: string; review?: ReviewRecord; error?: string;
  /** Context-only reverse uses, projected from the full archive without expanding execution visibility. */
  consumerInterfaces?: TaskConsumerProjection;
  /** Scoped advisory history, derived from immutable delivery records. */
  mathematicalGaps?: ReturnType<typeof mathematicalGaps>;
  /** Context-only public in-flight metadata, without expanding task/source visibility. */
  parallelQuestions?: readonly ParallelQuestion[];
  history?: { task: CooperativeTask; producer?: string; proof?: TaskProof; integratedCheck?: ProofCheck; finding?: string }[];
  deliveries?: DeliveryRecord[]; cursors?: Record<string, number>; edits?: HumanEditRecord[];
  researchDecisions?: ResearchHandoffDecision[];
  challengeDecisions?: ResearchChallengeDecision[];
  planVersion?: string; planEdited?: boolean; statementReviews?: StatementReview[];
  initialPlanPublication?: InitialPlanPublication;
  helpRequestDigest?: string;
  planRejection?: { proposalDigest: string; inputDigest: string; error: string; stalled: boolean };
  lastLeadInputDigest?: string;
  frontierRecoveries?: { id: string; taskIds: string[]; goalIds: string[];
    status: 'requested' | 'planned' | 'awaiting-input'; taskInputDigests: string[]; readyTaskIds?: string[]; reason?: string;
    investigationTaskId?: string }[];
  frontierWaiting?: { inputDigest: string; taskIds: string[]; goalIds: string[]; reason: 'awaiting-new-mathematical-input' };
  failedTaskInputs?: FailedTaskInput[];
  blockers?: RouteBlocker[];
  proofRoutes?: ProofRoute[];
  progressSnapshot?: ObligationSnapshot;
  progressReceipts?: ObligationProgressReceipt[];
  unchangedResearch?: Record<string, { taskDigest: string; notesBlob: string; count: number }>;
  researchCheckpoints?: Record<string, { taskDigest: string; inputDigest: string; outputDigest: string; count: number;
    localInputDigest?: string; candidateOutputDigest?: string; unchangedEvidenceCount?: number; candidateStatus?: CheckpointCandidate['status'];
    paused?: boolean; blockerId?: string }>;
  researchDrafts?: Record<string, { taskDigest: string; workerId: string; assignmentId?: string; seedCommit: string; canonicalCommit?: string;
    commit: string; outputDigest: string; artifacts: DeliveryArtifactManifest; suspended?: boolean }>;
  recheck?: { canonicalCommit: string; total: number; completed: number; taskId?: string };
  initialPlanFallback?: { at: number; reason: string } };
export type TaskVersions = ReadonlyMap<string, { task: CooperativeTask; version: string }>;
export type DispatchBudget = { maxTurns: number; remainingMs: number };
export const RETRY_DISPATCH = Symbol('retry-dispatch');
export type DispatchResult = CooperativeAction | typeof RETRY_DISPATCH | undefined;

export const bounded = (text: string, bytes: number) => limitMathOutput(text, bytes, 'head');
export const deliveryInputFields = (record: DeliveryRecord) => ({
  taskId: record.taskId, taskDigest: record.taskDigest, kind: record.kind, status: record.status,
  summary: record.summary, evidenceRefs: record.evidenceRefs, dependencies: record.dependencies,
  remainingObligations: record.remainingObligations, lemmaRequests: record.lemmaRequests, findingDigest: record.findingDigest,
  mathematicalGap: record.mathematicalGap, mathematicalGapScope: record.mathematicalGapScope,
});
/** Model proposes tasks; the host validates coverage, exact targets and an acyclic dependency graph. */
export function readCooperationPlan(problem: SolverProblem, worktree: string): ReturnType<typeof parseCooperationPlan> {
  return parseCooperationPlan(problem, block(worktree, 'math-plan'));
}
