import { z } from 'zod';
import { configurableSolverModules } from '../../src/solver/modules/custom';
import { solverMethodDigest, solverModuleConfiguration } from '../../src/solver/modules';
import { researchModulePlanSchema, type ResearchModulePlan } from '../../src/solver/modules/policy';

export type ModuleExperiment = {
  schema: 'theorem-os.module-experiment.v1';
  baseline: string;
  variants: { id: string; label: string; plan: ResearchModulePlan }[];
};

export const moduleExperimentSchema = z.object({
  schema: z.literal('theorem-os.module-experiment.v1'),
  baseline: z.string(),
  variants: z.array(z.object({
    id: z.string().regex(/^[a-z][a-z0-9-]{0,47}$/u),
    label: z.string().trim().min(1).max(80).refine(value => !/[\r\n\0|]/u.test(value)),
    plan: researchModulePlanSchema,
  }).strict()).min(2).max(8),
}).strict().superRefine((experiment, context) => {
  const ids = experiment.variants.map(variant => variant.id);
  if (new Set(ids).size !== ids.length)
    context.addIssue({ code: z.ZodIssueCode.custom, path: ['variants'], message: 'Module experiment variant IDs must be unique.' });
  if (!ids.includes(experiment.baseline))
    context.addIssue({ code: z.ZodIssueCode.custom, path: ['baseline'], message: 'Module experiment baseline must name a variant.' });
}).transform(value => value as ModuleExperiment);

/** Compare effective implementations, including the M4 wrapper used to inject custom rules. */
export function describeModuleExperiment(experiment: ModuleExperiment, workers: number) {
  const variants = experiment.variants.map(variant => {
    const modules = configurableSolverModules(variant.plan, 'cooperative', workers);
    return { ...variant, moduleConfiguration: solverModuleConfiguration(modules),
      methodDigest: solverMethodDigest(modules, 'cooperative') };
  });
  if (new Set(variants.map(variant => variant.methodDigest)).size !== variants.length)
    throw new Error('module_experiment_duplicate_effective_configuration');
  const baseline = variants.find(variant => variant.id === experiment.baseline)!;
  return variants.map(variant => ({ ...variant, changedComponents: Object.keys(variant.moduleConfiguration.versions)
    .filter(slot => variant.moduleConfiguration.versions[slot] !== baseline.moduleConfiguration.versions[slot]) }));
}

type Outcome = { arm: string; repetition: number; status: string; accepted: boolean;
  totalTokens: number | null; solveWallMs: number | null };
const observed = (row: Outcome) => !['missing', 'invalid', 'unfinished', 'prepared'].includes(row.status);

/** Pair by problem-local repetition; missing attempts remain in the planned denominator. */
export function moduleExperimentPairs(experiment: ModuleExperiment, rows: Outcome[]) {
  return experiment.variants.filter(variant => variant.id !== experiment.baseline).map(variant => {
    const pairs = rows.filter(row => row.arm === experiment.baseline).map(baseline => {
      const treatment = rows.find(row => row.arm === variant.id && row.repetition === baseline.repetition);
      const complete = observed(baseline) && !!treatment && observed(treatment);
      const tokenDelta = complete && baseline.totalTokens !== null && treatment!.totalTokens !== null
        ? treatment!.totalTokens - baseline.totalTokens : null;
      const solveWallDeltaMs = complete && baseline.solveWallMs !== null && treatment!.solveWallMs !== null
        ? treatment!.solveWallMs - baseline.solveWallMs : null;
      return { repetition: baseline.repetition, baselineStatus: baseline.status, treatmentStatus: treatment?.status ?? 'missing',
        complete, baselineAccepted: baseline.accepted, treatmentAccepted: treatment?.accepted ?? false,
        tokenDelta, solveWallDeltaMs };
    });
    const complete = pairs.filter(pair => pair.complete);
    const tokenPairs = pairs.filter(pair => pair.tokenDelta !== null);
    const timePairs = pairs.filter(pair => pair.solveWallDeltaMs !== null);
    const wins = complete.filter(pair => !pair.baselineAccepted && pair.treatmentAccepted).length;
    const losses = complete.filter(pair => pair.baselineAccepted && !pair.treatmentAccepted).length;
    return { baseline: experiment.baseline, treatment: variant.id, plannedPairs: pairs.length,
      observedPairs: complete.length, incompletePairs: pairs.length - complete.length,
      wins, losses, bothAccepted: complete.filter(pair => pair.baselineAccepted && pair.treatmentAccepted).length,
      neitherAccepted: complete.filter(pair => !pair.baselineAccepted && !pair.treatmentAccepted).length,
      acceptanceRateDelta: pairs.length ? pairs.reduce((sum, pair) =>
        sum + Number(pair.treatmentAccepted) - Number(pair.baselineAccepted), 0) / pairs.length : null,
      tokenPairs: tokenPairs.length,
      meanTokenDelta: tokenPairs.length ? tokenPairs.reduce((sum, pair) => sum + pair.tokenDelta!, 0) / tokenPairs.length : null,
      timePairs: timePairs.length,
      meanSolveWallDeltaMs: timePairs.length ? timePairs.reduce((sum, pair) => sum + pair.solveWallDeltaMs!, 0) / timePairs.length : null,
      pairs };
  });
}
