import { createCodexMathSession } from '../../runtime/codexSession';
import { checkSolverProof } from './evidence';
import { executeResearch } from './execution';
import { buildResearchContext, buildStatementReviewContext } from './context';
import type { ResearchOperation, ValueEstimate } from './value';
import type { SolverRunState } from '../archive';
import { selectResearchAction, selectLemmaAction, planResearchRetry, readyResearchTasks, goalsFirstResearchTasks, criticalPathResearchTasks, continuationResearchTasks } from './search';
import { assignSharedResearchTask, researchWorkers, assignResearchReviewer, type organizeResearch } from './organization';
import { checkLemmaResearch } from '../lemma';
import { checkTaskProof } from '../cooperativeProof';
import { canonicalMathJson, mathDigest } from '../../math/mathRuntimeIo';

/** Frozen component versions compose one ordinary direct-proof program. */
export const directSolverModules = {
  id: 'direct-v1',
  M1: { version: 'bounded-codex-turn-v14/distinct-recovery-delivery-v1/provider-diagnostics-v1/saved-plan-recovery-v1/closed-writer-ownership-v1/advisory-draft-recovery-v1/session-admission-v1/closed-statement-ownership-v1/feasibility-session-v1/observed-turn-ledger-v1/session-scoped-usage-v1/persistent-provider-cooldown-v1/context-overflow-recovery-v1/initial-planning-budget-v1/trusted-local-stop-v1', open: createCodexMathSession, execute: executeResearch },
  M2: { version: 'lean-kernel-v14/declaration-prefix-projection-v1/task-root-references-v1/conditional-child-changes-v1/scoped-conditional-projection-v1/exact-input-failure-reuse-v1/conditional-projection-identity-v1/attributed-batch-evidence-v1/fixed-candidate-references-v1/exact-projection-cache-v1/shared-source-index-v1', check: checkSolverProof, checkTask: checkTaskProof },
  M3: { version: 'route-budget-v12/blocker-or-routes-v1/structured-provider-failure-v1/assignable-work-v1/advisory-settlement-v3/goal-scoped-advancement-v1/early-route-checks-v1/ready-consumers-v1/evidence-ranked-routes-v2/capacity-free-ranking-v1/active-or-frontier-v1/context-overflow-recovery-v1/pending-validation-v1/trusted-local-stop-v1', select: selectResearchAction, retry: planResearchRetry, ready: readyResearchTasks },
  M4: { version: 'task-interface-context-v30/original-goal-frontier-v3/finished-objective-refs-v1/work-contract-v2/research-handoff-batches-v3/resume-drafts-v1/assignment-knowledge-hints-v1/deferred-handoff-inputs-v1/mathematical-route-planning-v1/complete-research-findings-v1/consumer-interfaces-v1/current-feedback-v1/complete-checkpoints-v1/early-feasibility-v1/parallel-questions-v2/local-attempt-feedback-v1/compact-handoff-sources-v1/exact-interface-diversity-v1/bounded-route-focus-v1/compact-inline-manifest-v1/adopted-research-use-v1/bounded-knowledge-metadata-v1/interface-idf-v1/overflow-optional-budget-v1/initial-planning-budget-v1', build: buildResearchContext, statement: buildStatementReviewContext },
  M5: { version: 'route-cooperation-v32/persistent-failed-input-v1/continuous-frontier-input-v1/research-handoff-batches-v3/assignable-work-v1/resumable-lead-drafts-v1/assignment-deliveries-v1/scoped-research-drafts-v1/review-dispatches-v1/recoverable-delivery-cursors-v1/recoverable-human-edits-v1/recoverable-proof-integration-v1/deferred-handoff-reactivation-v1/concurrent-frontier-recovery-v1/complete-research-findings-v1/consumer-interface-projection-v1/independent-feasibility-v1/ranked-assignment-v1/local-checkpoint-evidence-v1/stable-handoff-inputs-v1/local-attempt-identity-v1/exact-inflight-questions-v1/description-source-recheck-v1/conditional-restore-v1/live-capacity-exploration-v1/snapshot-statement-review-reuse-v1/concurrent-merged-check-v1/adopted-research-use-v1/fixed-candidate-statement-scope-v1/semantic-dependency-review-v1/nonblocking-plan-validation-v1/exact-projection-cache-v1', workers: researchWorkers, reviewer: assignResearchReviewer, assign: assignSharedResearchTask },
};

export type SolverModules = Omit<typeof directSolverModules, 'M2' | 'M3' | 'M5'> & {
  M2: Omit<typeof directSolverModules.M2, 'checkTask'> & { checkTask?: typeof checkTaskProof; checkLemma?: typeof checkLemmaResearch };
  M3: typeof directSolverModules.M3 & {
    estimate?: (state: Readonly<SolverRunState>, options: readonly ResearchOperation[]) => readonly ValueEstimate[];
  };
  M5: typeof directSolverModules.M5 & { organize?: typeof organizeResearch; primaryLed?: boolean };
};

export const lemmaSolverModules: SolverModules = {
  ...directSolverModules, id: 'lemma-v1',
  M2: { ...directSolverModules.M2, version: 'lean-obligations-v14/declaration-prefix-projection-v1/task-root-references-v1/conditional-child-changes-v1/scoped-conditional-projection-v1/exact-input-failure-reuse-v1/conditional-projection-identity-v1/attributed-batch-evidence-v1/fixed-candidate-references-v1/exact-projection-cache-v1/shared-source-index-v1', checkLemma: checkLemmaResearch },
  M3: { ...directSolverModules.M3, version: 'lemma-route-search-v13/blocker-or-routes-v1/structured-provider-failure-v1/assignable-work-v1/advisory-settlement-v3/goal-scoped-advancement-v1/early-route-checks-v1/ready-consumers-v1/evidence-ranked-routes-v2/capacity-free-ranking-v1/active-or-frontier-v1/context-overflow-recovery-v1/pending-validation-v1/trusted-local-stop-v1', select: selectLemmaAction },
};

/** Named CLI policies bind search and assignment versions without changing host acceptance. */
export function configuredSolverModules(method: string, scheduler: string): SolverModules {
  if (!['direct', 'lemma'].includes(method)) throw new Error('invalid --method');
  if (!['plan', 'goals-first', 'critical-path', 'continuation', 'primary-led'].includes(scheduler)) throw new Error('invalid --scheduler');
  const base = method === 'lemma' ? lemmaSolverModules : directSolverModules;
  if (scheduler === 'primary-led') return { ...base,
    M4: { ...base.M4, version: `${base.M4.version}/primary-led-v1` },
    M5: { ...base.M5, version: `${base.M5.version}/primary-led-v1`, primaryLed: true, assign: assignSharedResearchTask } };
  if (scheduler === 'critical-path') return { ...base,
    M3: { ...base.M3, version: `${base.M3.version}/critical-path-v1`, ready: criticalPathResearchTasks },
    M5: { ...base.M5, version: `${base.M5.version}/shared-work-v1`, assign: assignSharedResearchTask } };
  if (scheduler === 'continuation') return { ...base,
    M3: { ...base.M3, version: `${base.M3.version}/continuation-v5/original-goal-frontier-v3/ready-consumers-v1`, ready: continuationResearchTasks },
    M5: { ...base.M5, version: `${base.M5.version}/shared-work-v1`, assign: assignSharedResearchTask } };
  return scheduler === 'plan' ? base : { ...base,
    M3: { ...base.M3, version: `${base.M3.version}/goals-first-v1`, ready: goalsFirstResearchTasks } };
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
