import { createCodexMathSession } from '../../runtime/codexSession';
import { checkSolverProof } from './evidence';
import { executeResearch } from './execution';
import { buildResearchContext, buildStatementReviewContext } from './context';
import type { ResearchOperation, ValueEstimate } from './value';
import type { SolverRunState } from '../archive';
import { selectResearchAction, selectLemmaAction, planResearchRetry, readyResearchTasks, goalsFirstResearchTasks } from './search';
import { assignResearchTask, researchWorkers, assignResearchReviewer, type organizeResearch } from './organization';
import { checkLemmaResearch } from '../lemma';
import { checkTaskProof } from '../cooperativeProof';
import { canonicalMathJson, mathDigest } from '../../math/mathRuntimeIo';

/** Frozen component versions compose one ordinary direct-proof program. */
export const directSolverModules = {
  id: 'direct-v1',
  M1: { version: 'bounded-codex-turn-v6', open: createCodexMathSession, execute: executeResearch },
  M2: { version: 'lean-kernel-v4', check: checkSolverProof, checkTask: checkTaskProof },
  M3: { version: 'route-budget-v4', select: selectResearchAction, retry: planResearchRetry, ready: readyResearchTasks },
  M4: { version: 'checkpoint-context-v7', build: buildResearchContext, statement: buildStatementReviewContext },
  M5: { version: 'route-cooperation-v6', workers: researchWorkers, reviewer: assignResearchReviewer, assign: assignResearchTask },
};

export type SolverModules = Omit<typeof directSolverModules, 'M2' | 'M3' | 'M5'> & {
  M2: Omit<typeof directSolverModules.M2, 'checkTask'> & { checkTask?: typeof checkTaskProof; checkLemma?: typeof checkLemmaResearch };
  M3: typeof directSolverModules.M3 & {
    estimate?: (state: Readonly<SolverRunState>, options: readonly ResearchOperation[]) => readonly ValueEstimate[];
  };
  M5: typeof directSolverModules.M5 & { organize?: typeof organizeResearch };
};

export const lemmaSolverModules: SolverModules = {
  ...directSolverModules, id: 'lemma-v1',
  M2: { ...directSolverModules.M2, version: 'lean-obligations-v4', checkLemma: checkLemmaResearch },
  M3: { ...directSolverModules.M3, version: 'lemma-route-search-v5', select: selectLemmaAction },
};

/** Named CLI policies replace M3 alone; host verification and ownership stay fixed. */
export function configuredSolverModules(method: string, scheduler: string): SolverModules {
  if (!['direct', 'lemma'].includes(method)) throw new Error('invalid --method');
  if (!['plan', 'goals-first'].includes(scheduler)) throw new Error('invalid --scheduler');
  const base = method === 'lemma' ? lemmaSolverModules : directSolverModules;
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
