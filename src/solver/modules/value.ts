export type ResearchOperation = 'direct' | 'decompose' | 'bridge' | 'prove-lemma' | 'integrate-lemma';
export type ValueEstimate = Readonly<{
  operation: ResearchOperation;
  target: 'remaining-turns';
  value: number | null;
  uncertainty: number | null;
  calibration: 'uncalibrated' | 'calibrated';
}>;
