import { createCodexMathSession } from '../../runtime/codexSession';
import type { MathAgentOptions } from '../../runtime/codexSession';
import { checkSolverProof } from './evidence';
import { executeResearch } from './execution';
import { buildResearchContext } from './context';
import { estimateResearchValue } from './value';
import { selectResearchAction, selectLemmaAction, planResearchRetry } from './search';
import { organizeResearch } from './organization';
import { integrateResearch } from './integration';
import { checkLemmaResearch } from '../lemma';

/** Frozen component versions compose one ordinary direct-proof program. */
export const directSolverModules = {
  id: 'direct-v1',
  M1: { version: 'bounded-codex-turn-v2', open: (options: MathAgentOptions) => createCodexMathSession(options), execute: executeResearch },
  M2: { version: 'lean-kernel-v1', check: checkSolverProof },
  M3: { version: 'no-estimate-v1', estimate: estimateResearchValue },
  M4: { version: 'bounded-direct-v1', select: selectResearchAction, retry: planResearchRetry },
  M5: { version: 'bounded-lean-feedback-v2', build: buildResearchContext },
  M6: { version: 'single-worker-v1', organize: organizeResearch },
  M7: { version: 'complete-proof-v1', integrate: integrateResearch },
};

export type SolverModules = Omit<typeof directSolverModules, 'M2'> & {
  M2: typeof directSolverModules.M2 & { checkLemma?: typeof checkLemmaResearch };
};

export const lemmaSolverModules: SolverModules = {
  ...directSolverModules, id: 'lemma-v1',
  M2: { ...directSolverModules.M2, version: 'lean-obligations-v2', checkLemma: checkLemmaResearch },
  M4: { ...directSolverModules.M4, version: 'lemma-search-v2', select: selectLemmaAction },
};
