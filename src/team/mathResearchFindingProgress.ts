import {
  assessMathResearchFindingEvidence,
  assessNovelMathResearchFindingEvidence,
  normalizeMathResearchStatement,
  type MathResearchEvidence,
  type MathResearchFinding,
  type MathResearchProblemContract,
} from "../common/types/team/mathematicsTeam";

export type MathResearchFindingProgressClass =
  | 'route_refuted'
  | 'bottleneck_resolved'
  | 'new_claim'
  | 'bottleneck_narrowed'
  | 'new_elimination'
  | 'new_conjecture'
  | 'new_evidence'
  | 'no_state_change';

function normalizedStatements(values: readonly string[]): Set<string> {
  return new Set(values.map((value) => value.normalize('NFC').replace(/\s+/gu, ' ').trim()).filter(Boolean));
}

export function hasMathResearchProgressSignal(
  finding: MathResearchFinding,
  trustedEvidence: readonly MathResearchEvidence[] = []
): boolean {
  return assessMathResearchFindingEvidence(finding, trustedEvidence).observed;
}

export function classifyMathResearchFindingProgress(
  finding: MathResearchFinding,
  impact: string,
  priorContract: MathResearchProblemContract | undefined,
  trustedEvidence: readonly MathResearchEvidence[] = []
): Readonly<{ kind: MathResearchFindingProgressClass; rank: number; novelStateCount: number }> {
  const novelCount = (values: readonly string[], priorValues: readonly string[] | undefined): number => {
    const prior = normalizedStatements(priorValues ?? []);
    return [...normalizedStatements(values)].filter((value) => !prior.has(value)).length;
  };
  const assessment = assessNovelMathResearchFindingEvidence(priorContract, finding, trustedEvidence);
  const newClaims = novelCount(assessment.establishedClaims, priorContract?.establishedClaims);
  const newEliminations = novelCount(assessment.eliminatedApproaches, priorContract?.failedApproaches);
  const newConjectures = novelCount(assessment.conjectures, [
    ...(priorContract?.conjectures ?? []),
    ...(priorContract?.establishedClaims ?? []),
  ]);
  const novelStateCount = newClaims + newEliminations + newConjectures;
  const supported = assessment.observed;
  if (newEliminations > 0 && impact === 'route_refuted')
    return Object.freeze({ kind: 'route_refuted', rank: 8, novelStateCount });
  if (
    assessment.closesBottleneck &&
    finding.bottleneckUpdate?.outcome === 'resolved' &&
    normalizeMathResearchStatement(finding.bottleneckUpdate.target) ===
      normalizeMathResearchStatement(priorContract?.activeBottleneck ?? '')
  ) {
    return Object.freeze({ kind: 'bottleneck_resolved', rank: 7, novelStateCount });
  }
  if (supported && newClaims > 0) return Object.freeze({ kind: 'new_claim', rank: 6, novelStateCount });
  if (
    assessment.narrowsBottleneck &&
    finding.bottleneckUpdate?.diagnosis &&
    normalizeMathResearchStatement(finding.bottleneckUpdate.target) ===
      normalizeMathResearchStatement(priorContract?.activeBottleneck ?? '') &&
    normalizeMathResearchStatement(finding.bottleneckUpdate.diagnosis) !==
      normalizeMathResearchStatement(priorContract?.bottleneckDiagnosis ?? '')
  ) {
    return Object.freeze({ kind: 'bottleneck_narrowed', rank: 5, novelStateCount });
  }
  if (newEliminations > 0) {
    return Object.freeze({ kind: 'new_elimination', rank: 4, novelStateCount });
  }
  // Unverified assertions remain useful hypotheses, without claiming a resolution.
  if (newConjectures > 0 || newClaims > 0 || newEliminations > 0) {
    return Object.freeze({ kind: 'new_conjecture', rank: 3, novelStateCount });
  }
  if (supported) return Object.freeze({ kind: 'new_evidence', rank: 2, novelStateCount });
  return Object.freeze({ kind: 'no_state_change', rank: 1, novelStateCount });
}

export function isMathResearchMainlineProgress(
  kind: MathResearchFindingProgressClass,
  finding: MathResearchFinding,
  trustedEvidence: readonly MathResearchEvidence[] = []
): boolean {
  const assessment = assessMathResearchFindingEvidence(finding, trustedEvidence);
  return (
    ['bottleneck_resolved', 'new_claim', 'bottleneck_narrowed', 'new_elimination'].includes(kind) &&
    (assessment.establishedClaims.length > 0 ||
      assessment.eliminatedApproaches.length > 0 ||
      assessment.closesBottleneck ||
      assessment.narrowsBottleneck)
  );
}
