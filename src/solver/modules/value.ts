import type { SolverRunState } from '../archive';

export type ResearchOperation = 'direct' | 'decompose' | 'bridge' | 'prove-lemma' | 'integrate-lemma';
export type ValueEstimate = Readonly<{
  operation: ResearchOperation;
  target: 'remaining-turns';
  value: number | null;
  uncertainty: number | null;
  calibration: 'uncalibrated' | 'calibrated';
}>;

/** M3 scoring: the direct baseline explicitly has no remaining-cost prediction. */
export function estimateResearchValue(_state: Readonly<SolverRunState>, options: readonly ResearchOperation[]): readonly ValueEstimate[] {
  return options.map(operation => ({ operation, target: 'remaining-turns', value: null,
    uncertainty: null, calibration: 'uncalibrated' }));
}
