import { createCodexMathSession } from '../../runtime/codexSession';
import type { MathAgentOptions } from '../../runtime/codexSession';
import { checkSolverProof } from './evidence';
import { executeResearch } from './execution';
import { buildResearchContext } from './context';
import { estimateResearchValue } from './value';
import { selectResearchAction, selectLemmaAction, planResearchRetry, readyResearchTasks } from './search';
import { organizeResearch, assignResearchTask } from './organization';
import { checkLemmaResearch } from '../lemma';

/** Frozen component versions compose one ordinary direct-proof program. */
export const directSolverModules = {
  id: 'direct-v1',
  M1: { version: 'bounded-codex-turn-v3', open: (options: MathAgentOptions) => createCodexMathSession(options), execute: executeResearch },
  M2: { version: 'lean-kernel-v1', check: checkSolverProof },
  M3: { version: 'route-budget-v3', estimate: estimateResearchValue, select: selectResearchAction, retry: planResearchRetry, ready: readyResearchTasks },
  M4: { version: 'checkpoint-context-v3', build: buildResearchContext },
  M5: { version: 'route-cooperation-v3', organize: organizeResearch, assign: assignResearchTask },
};

export type SolverModules = Omit<typeof directSolverModules, 'M2'> & {
  M2: typeof directSolverModules.M2 & { checkLemma?: typeof checkLemmaResearch };
};

export const lemmaSolverModules: SolverModules = {
  ...directSolverModules, id: 'lemma-v1',
  M2: { ...directSolverModules.M2, version: 'lean-obligations-v2', checkLemma: checkLemmaResearch },
  M3: { ...directSolverModules.M3, version: 'lemma-route-search-v4', select: selectLemmaAction },
};
