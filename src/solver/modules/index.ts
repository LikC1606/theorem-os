import { createCodexMathSession } from '../../runtime/codexSession';
import { checkSolverProof } from './evidence';
import { executeResearch } from './execution';
import { buildResearchContext, buildStatementReviewContext } from './context';
import type { ResearchOperation, ValueEstimate } from './value';
import type { SolverRunState } from '../archive';
import { selectResearchAction, selectLemmaAction, planResearchRetry, readyResearchTasks, goalsFirstResearchTasks, criticalPathResearchTasks, continuationResearchTasks } from './search';
import { assignResearchTask, assignSharedResearchTask, researchWorkers, assignResearchReviewer, type organizeResearch } from './organization';
import { checkLemmaResearch } from '../lemma';
import { checkTaskProof } from '../cooperativeProof';
import { canonicalMathJson, mathDigest } from '../../math/mathRuntimeIo';

/** Frozen component versions compose one ordinary direct-proof program. */
export const directSolverModules = {
  id: 'direct-v1',
  M1: { version: 'bounded-codex-turn-v10/distinct-recovery-delivery-v1/provider-diagnostics-v1', open: createCodexMathSession, execute: executeResearch },
  M2: { version: 'lean-kernel-v11/declaration-prefix-projection-v1/task-root-references-v1', check: checkSolverProof, checkTask: checkTaskProof },
  M3: { version: 'route-budget-v8/blocker-or-routes-v1/structured-provider-failure-v1/assignable-work-v1', select: selectResearchAction, retry: planResearchRetry, ready: readyResearchTasks },
  M4: { version: 'task-interface-context-v22/original-goal-frontier-v1/finished-objective-refs-v1/work-contract-v1/research-handoffs-v1', build: buildResearchContext, statement: buildStatementReviewContext },
  M5: { version: 'route-cooperation-v21/persistent-failed-input-v1/continuous-frontier-input-v1/research-handoffs-v1/assignable-work-v1', workers: researchWorkers, reviewer: assignResearchReviewer, assign: assignResearchTask },
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
  M2: { ...directSolverModules.M2, version: 'lean-obligations-v11/declaration-prefix-projection-v1/task-root-references-v1', checkLemma: checkLemmaResearch },
  M3: { ...directSolverModules.M3, version: 'lemma-route-search-v9/blocker-or-routes-v1/structured-provider-failure-v1/assignable-work-v1', select: selectLemmaAction },
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
    M3: { ...base.M3, version: `${base.M3.version}/continuation-v2/original-goal-frontier-v1`, ready: continuationResearchTasks },
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
