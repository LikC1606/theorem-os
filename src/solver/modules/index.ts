import { createCodexMathSession } from '../../runtime/codexSession';
import type { MathAgentOptions } from '../../runtime/codexSession';
import { checkSolverProof } from './evidence';
import { executeResearch } from './execution';
import { buildResearchContext, buildStatementReviewContext } from './context';
import { estimateResearchValue } from './value';
import { selectResearchAction, selectLemmaAction, planResearchRetry, readyResearchTasks } from './search';
import { organizeResearch, assignResearchTask, researchWorkers, assignResearchReviewer } from './organization';
import { checkLemmaResearch } from '../lemma';
import { checkTaskProof } from '../cooperativeProof';

/** Frozen component versions compose one ordinary direct-proof program. */
export const directSolverModules = {
  id: 'direct-v1',
  M1: { version: 'bounded-codex-turn-v5', open: (options: MathAgentOptions) => createCodexMathSession(options), execute: executeResearch },
  M2: { version: 'lean-kernel-v4', check: checkSolverProof, checkTask: checkTaskProof },
  M3: { version: 'route-budget-v4', estimate: estimateResearchValue, select: selectResearchAction, retry: planResearchRetry, ready: readyResearchTasks },
  M4: { version: 'checkpoint-context-v6', build: buildResearchContext, statement: buildStatementReviewContext },
  M5: { version: 'route-cooperation-v5', workers: researchWorkers, reviewer: assignResearchReviewer, organize: organizeResearch, assign: assignResearchTask },
};

export type SolverModules = Omit<typeof directSolverModules, 'M2'> & {
  M2: Omit<typeof directSolverModules.M2, 'checkTask'> & { checkTask?: typeof checkTaskProof; checkLemma?: typeof checkLemmaResearch };
};

export const lemmaSolverModules: SolverModules = {
  ...directSolverModules, id: 'lemma-v1',
  M2: { ...directSolverModules.M2, version: 'lean-obligations-v4', checkLemma: checkLemmaResearch },
  M3: { ...directSolverModules.M3, version: 'lemma-route-search-v5', select: selectLemmaAction },
};
