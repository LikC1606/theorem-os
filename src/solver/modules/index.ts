import { createCodexMathSession } from '../../runtime/codexSession';
import { checkSolverProof } from './evidence';
import { executeResearch } from './execution';
import { buildResearchContext, buildStatementReviewContext } from './context';
import { selectResearchAction, planResearchRetry, readyResearchTasks, criticalPathResearchTasks, continuationResearchTasks } from './search';
import { assignSharedResearchTask, researchWorkers, assignResearchReviewer } from './organization';
import { checkTaskProof } from '../cooperativeProof';
import { canonicalMathJson, mathDigest } from '../../math/mathRuntimeIo';

/** Frozen component versions compose one ordinary direct-proof program. */
export const directSolverModules = {
  id: 'direct-v1',
  M1: { version: 'bounded-codex-turn-v15/distinct-recovery-delivery-v1/provider-diagnostics-v1/saved-plan-recovery-v1/closed-writer-ownership-v1/advisory-draft-recovery-v1/session-admission-v1/closed-statement-ownership-v1/feasibility-session-v1/observed-turn-ledger-v1/session-scoped-usage-v1/persistent-provider-cooldown-v1/context-overflow-recovery-v1/initial-planning-budget-v1/trusted-local-stop-v1/initial-plan-publication-v1/observed-knowledge-use-v1/diagnostic-log-ownership-v1/turn-ledger-removed-v1/advisory-scratch-ownership-v1/durable-reasoning-checkpoint-v1/lead-thread-continuation-v1/bounded-coordination-checkpoints-v1/live-saved-context-yield-v1/published-context-checkpoint-v1/compaction-aware-checkpoints-v1', open: createCodexMathSession, execute: executeResearch },
  M2: { version: 'lean-kernel-v14/declaration-prefix-projection-v1/task-root-references-v1/conditional-child-changes-v1/scoped-conditional-projection-v1/exact-input-failure-reuse-v1/conditional-projection-identity-v1/attributed-batch-evidence-v1/fixed-candidate-references-v1/exact-projection-cache-v1/shared-source-index-v1/host-consumer-connection-v1/content-projection-reuse-v1/ready-integration-batches-v1/coded-lean-diagnostics-v1/live-exact-projection-recheck-v1/lean-diagnostic-word-classification-v1/advisory-scratch-checkout-v1', check: checkSolverProof, checkTask: checkTaskProof },
  M3: { version: 'route-budget-v12/blocker-or-routes-v1/structured-provider-failure-v1/assignable-work-v1/advisory-settlement-v3/goal-scoped-advancement-v1/early-route-checks-v1/ready-consumers-v1/evidence-ranked-routes-v2/capacity-free-ranking-v1/active-or-frontier-v1/context-overflow-recovery-v1/pending-validation-v1/trusted-local-stop-v1/host-consumer-connection-v1', select: selectResearchAction, retry: planResearchRetry, ready: readyResearchTasks },
  M4: { version: 'task-interface-context-v31/original-goal-frontier-v3/finished-objective-refs-v1/work-contract-v2/research-handoff-batches-v3/resume-drafts-v1/assignment-knowledge-hints-v1/deferred-handoff-inputs-v1/mathematical-route-planning-v1/complete-research-findings-v1/consumer-interfaces-v1/current-feedback-v1/complete-checkpoints-v1/early-feasibility-v1/parallel-questions-v2/local-attempt-feedback-v1/compact-handoff-sources-v1/exact-interface-diversity-v1/bounded-route-focus-v1/compact-inline-manifest-v1/adopted-research-use-v1/bounded-knowledge-metadata-v1/interface-idf-v1/overflow-optional-budget-v1/initial-planning-budget-v1/required-research-challenges-v1/initial-plan-publication-v1/scoped-route-findings-v1/observed-knowledge-use-v1/lean-json-diagnostics-v1/host-consumer-connection-v1/finite-boolean-evidence-v1/live-research-publication-v1/current-residual-goal-v1/continuation-attachments-v1/accepted-consumer-knowledge-v1/single-delivery-protocol-v1/route-focused-knowledge-v1/independent-goal-knowledge-batch-v1/route-finding-batch-v1/primary-led-removed-v1/assigned-proof-only-diagnostics-v1/lean-prover-v1/host-capacity-exploration-v1/explicit-handoff-publication-v1/advisory-scratch-roots-v1/exact-gap-checkpoint-context-v1/lead-continuation-context-v1/shared-new-helper-ownership-v1/compact-proof-role-context-v1/precise-gap-correction-context-v1/full-plan-adoption-context-v1/coordination-first-context-v1/explicit-research-source-context-v1/short-challenge-assessments-v1', build: buildResearchContext, statement: buildStatementReviewContext },
  M5: { version: 'route-cooperation-v33/persistent-failed-input-v1/continuous-frontier-input-v1/research-handoff-batches-v3/assignable-work-v1/resumable-lead-drafts-v1/assignment-deliveries-v1/scoped-research-drafts-v1/review-dispatches-v1/recoverable-delivery-cursors-v1/recoverable-human-edits-v1/recoverable-proof-integration-v1/deferred-handoff-reactivation-v1/concurrent-frontier-recovery-v1/complete-research-findings-v1/consumer-interface-projection-v1/independent-feasibility-v1/ranked-assignment-v1/local-checkpoint-evidence-v1/stable-handoff-inputs-v1/local-attempt-identity-v1/exact-inflight-questions-v1/description-source-recheck-v1/conditional-restore-v1/live-capacity-exploration-v1/snapshot-statement-review-reuse-v1/concurrent-merged-check-v1/adopted-research-use-v1/fixed-candidate-statement-scope-v1/semantic-dependency-review-v1/nonblocking-plan-validation-v1/exact-projection-cache-v1/required-research-challenges-v1/initial-plan-publication-v1/observed-knowledge-use-v1/host-consumer-connection-v1/live-research-publication-v1/typed-helper-preflight-v1/stale-preflight-cancellation-v1/type-projection-preflight-reuse-v1/stale-plan-recheck-stop-v1/shared-statement-preparation-v1/scoped-statement-types-v1/empty-route-list-v1/route-evidence-obligations-v1/primary-led-removed-v1/source-contract-local-repair-v1/unlimited-dispatch-recovery-v1/assignment-condition-snapshot-v1/conditional-dependency-order-v1/original-goal-capacity-coverage-v1/assigned-source-diagnostic-preflight-v1/current-batch-projection-v1/stalled-plan-continuous-recovery-v1/actual-dependency-invalidation-v1/lean-prover-v1/host-capacity-exploration-v1/explicit-handoff-publication-v1/semantic-lead-checkpoints-v1/continuation-handoff-provenance-v1/advisory-stagnation-recovery-v1/explicit-mathematical-gap-recovery-v1/shared-responsibility-assessment-v1/recorded-dispatch-waits-v1/full-plan-explicit-adoption-v1/scoped-delivery-correction-chain-v1/legacy-research-without-finding-v1/research-source-snapshots-v1/source-bound-mathematical-gap-v1/large-delivery-lines-v1/executable-work-assessment-v1', workers: researchWorkers, reviewer: assignResearchReviewer, assign: assignSharedResearchTask },
};

export type SolverModules = Omit<typeof directSolverModules, 'M2' | 'M5'> & {
  M2: Omit<typeof directSolverModules.M2, 'checkTask'> & { checkTask?: typeof checkTaskProof };
  M5: typeof directSolverModules.M5;
};

/** Named CLI policies bind search and assignment versions without changing host acceptance. */
export function configuredSolverModules(method: string, scheduler: string): SolverModules {
  if (method !== 'direct') throw new Error('invalid --method');
  if (!['plan', 'critical-path', 'continuation'].includes(scheduler)) throw new Error('invalid --scheduler');
  const base: SolverModules = directSolverModules;
  if (scheduler === 'critical-path') return { ...base,
    M3: { ...base.M3, version: `${base.M3.version}/critical-path-v1`, ready: criticalPathResearchTasks },
    M5: { ...base.M5, version: `${base.M5.version}/shared-work-v1`, assign: assignSharedResearchTask } };
  return scheduler === 'plan' ? base : { ...base,
    M3: { ...base.M3, version: `${base.M3.version}/continuation-v5/original-goal-frontier-v3/ready-consumers-v1`, ready: continuationResearchTasks },
    M5: { ...base.M5, version: `${base.M5.version}/shared-work-v1`, assign: assignSharedResearchTask } };
}

export function solverModuleConfiguration(modules: SolverModules) {
  return { id: modules.id, versions: Object.fromEntries(Object.entries(modules)
    .filter(([key]) => key !== 'id').map(([key, module]) => [key, (module as { version: string }).version])) };
}

/** Preserve the default historical identity while binding independent runs to their mode. */
export function solverMethodDigest(modules: SolverModules, coordination: 'cooperative' | 'independent') {
  const { id, versions } = solverModuleConfiguration(modules);
  return mathDigest(canonicalMathJson({ id, versions: Object.entries(versions),
    ...(coordination === 'independent' ? { coordination } : {}) }));
}
