/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

/** Runtime-neutral scheduling and progress contracts for Mathematics Team work. */

export type ProtocolIssue = Readonly<{
  path: string;
  code:
    | 'required'
    | 'invalid'
    | 'payload_too_large'
    | 'conflict'
    | 'not_found'
    | 'stale'
    | 'integrity'
    | 'runtime_owned_field'
    | 'unauthorized';
  message: string;
  expected?: string;
  received?: string;
}>;

export const MATH_PROOF_STAGES = [
  'audit',
  'diversify',
  'select',
  'formalize',
  'local_gate',
  'review',
  'official_gate',
  'replan',
  'done',
] as const;
export type MathProofStage = (typeof MATH_PROOF_STAGES)[number];

export const MATH_WORKFLOW_STAGES = [
  'intake',
  'exploration',
  'candidate',
  'formalization',
  'review',
  'final_verification',
  'done',
] as const;
export type MathWorkflowStage = (typeof MATH_WORKFLOW_STAGES)[number];

const LEGACY_MATH_WORKFLOW_STAGE_MAP: Readonly<Record<string, MathWorkflowStage>> = Object.freeze({
  audit: 'intake',
  diversify: 'exploration',
  select: 'candidate',
  formalize: 'formalization',
  local_gate: 'formalization',
  official_gate: 'final_verification',
  replan: 'exploration',
});

export function normalizeMathWorkflowStage(input: unknown): MathWorkflowStage {
  if (typeof input !== 'string') throw new TypeError('Mathematics workflow stage is invalid');
  const migrated = LEGACY_MATH_WORKFLOW_STAGE_MAP[input] ?? input;
  if (!MATH_WORKFLOW_STAGES.includes(migrated as MathWorkflowStage)) {
    throw new TypeError('Mathematics workflow stage is invalid');
  }
  return migrated as MathWorkflowStage;
}

/**
 * Immutable identity and acceptance contract for one mathematical problem.
 *
 * The natural-language and Lean statements are deliberately carried together:
 * a proof is never allowed to silently drift to a nearby formalization.
 */
export type MathProblemContract = Readonly<{
  problemId: string;
  informalStatement: string;
  formalStatement: string;
  /** Canonical Lean declaration for the negation, required before a formal refutation can be terminal. */
  formalNegationStatement?: string;
  assumptions: readonly string[];
  statementHash: string;
  leanStatementHash: string;
  leanNegationHash?: string;
  knownTraps: readonly string[];
  acceptanceCriteria: readonly string[];
  officialVerificationCommand: string;
  /** Optional identity of the committed official problem manifest. */
  officialManifestId?: string;
  officialManifestHash?: string;
}>;

/**
 * Mutable research identity used before a problem has a stable Lean statement.
 * It records what the researcher currently believes and what remains unknown;
 * formal verification can attach a MathProblemContract later.
 */
export type MathResearchProblemContract = Readonly<{
  problemId: string;
  objective: string;
  context?: string;
  knownResults?: readonly string[];
  establishedClaims?: readonly string[];
  conjectures?: readonly string[];
  failedApproaches?: readonly string[];
  openObligations?: readonly string[];
  /** Recent finding summaries paired with their evidence references. */
  evidenceNotes?: readonly string[];
  /** Compact reusable discoveries; Workers receive only the active-bottleneck projection. */
  insights?: readonly MathResearchInsight[];
  /** Cumulative outcomes for every probe method, independent of recent context eviction. */
  probeSummary?: readonly MathResearchProbeSummary[];
  bottleneckDiagnosis?: string;
  /** Durable runtime evidence identities, independent of the recent prompt window. */
  consumedEvidenceKeys?: readonly string[];
  /** The single bottleneck that currently determines the next useful probe. */
  activeBottleneck?: string;
  /** Project-local reference to a bounded solution sketch; the sketch itself stays out of the contract. */
  solutionSketchRef?: string;
  nextAction?: string;
}>;

export type MathResearchInsight = Readonly<{
  claim: string;
  conditions: readonly string[];
  failure?: string;
  repair?: string;
  usableWhen: string;
  evidenceRefs: readonly string[];
}>;

const uniqueMathResearchStrings = (...values: readonly (readonly string[] | undefined)[]): readonly string[] =>
  Object.freeze([...new Set(values.flatMap((value) => value ?? []))]);

const mathResearchInsightKey = (value: MathResearchInsight): string => `${value.claim}\u0000${value.usableWhen}`;

export const MATH_RESEARCH_FINDING_KINDS = [
  'literature',
  'example',
  'computation',
  'counterexample',
  'proof_step',
  'conjecture_update',
  'obstruction',
  'critique',
] as const;
export type MathResearchFindingKind = (typeof MATH_RESEARCH_FINDING_KINDS)[number];

export const MATH_RESEARCH_FINDING_IMPACTS = ['mainline_advanced', 'route_refuted', 'supporting', 'stalled'] as const;
export type MathResearchFindingImpact = (typeof MATH_RESEARCH_FINDING_IMPACTS)[number];

/** The next highest-information discovery probe selected by the Worker. */
export const MATH_RESEARCH_PROBE_KINDS = [
  'literature',
  'example',
  'computation',
  'counterexample',
  'problem_family',
  'proof_step',
  'obstruction',
  'critique',
] as const;
export type MathResearchProbeKind = (typeof MATH_RESEARCH_PROBE_KINDS)[number];

export const MATH_RESEARCH_PROBE_OUTCOMES = [
  'useful_state_change',
  'evidence_only',
  'no_state_change',
  'route_eliminated',
] as const;
export type MathResearchProbeOutcome = (typeof MATH_RESEARCH_PROBE_OUTCOMES)[number];

export type MathResearchProbeSummary = Readonly<{
  probeKind: MathResearchProbeKind;
  bottleneck?: string;
  bottleneckStats?: readonly MathResearchProbeBottleneckSummary[];
  attempts: number;
  usefulChanges: number;
  noChange: number;
  lastOutcome: MathResearchProbeOutcome;
}>;

export type MathResearchProbeBottleneckSummary = Readonly<{
  bottleneck: string;
  attempts: number;
  usefulChanges: number;
  noChange: number;
  lastOutcome: MathResearchProbeOutcome;
}>;

export const MATH_RESEARCH_BOTTLENECK_OUTCOMES = ['resolved', 'narrowed', 'unchanged', 'refuted'] as const;
export type MathResearchBottleneckOutcome = (typeof MATH_RESEARCH_BOTTLENECK_OUTCOMES)[number];

/** Compact diagnosis used to repair the current route without restarting it. */
export type MathResearchBottleneckUpdate = Readonly<{
  target: string;
  outcome: MathResearchBottleneckOutcome;
  category?: MathFailureCategory;
  diagnosis?: string;
  repair?: string;
}>;

/** One optional, bounded helper request tied to the current bottleneck. */
export type MathResearchHelperRequest = Readonly<{
  bottleneck: string;
  probeKind: MathResearchProbeKind;
  objective: string;
}>;

export const MATH_PROBLEM_FAMILY_INSTANCE_OUTCOMES = ['supports', 'counterexample', 'inconclusive'] as const;
export type MathProblemFamilyInstanceOutcome = (typeof MATH_PROBLEM_FAMILY_INSTANCE_OUTCOMES)[number];

export const MATH_PROBLEM_FAMILY_GENERALIZATION_OUTCOMES = ['supported', 'refuted', 'inconclusive'] as const;
export type MathProblemFamilyGeneralizationOutcome = (typeof MATH_PROBLEM_FAMILY_GENERALIZATION_OUTCOMES)[number];

export type MathProblemFamilyProbe = Readonly<{
  instances: readonly {
    input: string;
    outcome: MathProblemFamilyInstanceOutcome;
    observation?: string;
  }[];
  sharedMechanism?: string;
  firstCounterexample?: string;
  generalization: MathProblemFamilyGeneralizationOutcome;
}>;

export type MathResearchEvidence = Readonly<{
  grade: 'hypothesis' | 'observed' | 'runtime_checked' | 'kernel_verified';
  scope: 'claim' | 'bounded_observation' | 'approach' | 'bottleneck';
  statement: string;
  reference: string;
  fingerprint?: string;
}>;

/** One lightweight discovery result that updates the active research state. */
export type MathResearchFinding = Readonly<{
  kind: MathResearchFindingKind;
  /** Short mathematical mechanism shared by cosmetic variants of the same route. */
  mechanism?: string;
  /** Worker hint about whether this result changed the active bottleneck. */
  mainlineImpact?: MathResearchFindingImpact;
  /** Optional structured routing hint for the next discovery action. */
  nextProbeKind?: MathResearchProbeKind;
  /** Optional diagnosis of the active bottleneck and the smallest useful repair. */
  bottleneckUpdate?: MathResearchBottleneckUpdate;
  /** Optional short-lived helper request; the runtime may dispatch a fresh slot when useful. */
  helperRequest?: MathResearchHelperRequest;
  /** Bounded transfer test across nearby instances; never a proof of the general theorem. */
  problemFamilyProbe?: MathProblemFamilyProbe;
  /** Optional project-local reference to a persisted solution sketch. */
  solutionSketchRef?: string;
  summary: string;
  evidenceRefs: readonly string[];
  /** Worker declarations are observations; checked authority comes from runtime receipts. */
  evidence?: readonly MathResearchEvidence[];
  establishedClaims: readonly string[];
  conjectureUpdates: readonly string[];
  eliminatedApproaches: readonly string[];
  openObligations: readonly string[];
  nextAction: string;
}>;

export const MATH_FAST_CHECK_OUTCOMES = ['no_counterexample_found', 'counterexample_found', 'inconclusive'] as const;
export type MathFastCheckOutcome = (typeof MATH_FAST_CHECK_OUTCOMES)[number];

/** Runtime-owned bounded Lean evaluation requested alongside a FAST_CHECK. */
export type MathFastCheckRuntimeProbe = Readonly<{
  /** A function-like Lean expression applied to each bounded case. */
  expression: string;
  /** Optional function-like proposition used to filter out illegal samples. */
  precondition?: string;
  /** Concrete Lean expressions. Omit to use the runtime's small default set. */
  cases?: readonly string[];
  /** Propositions are the default; boolean predicates compare against true. */
  mode?: 'proposition' | 'boolean';
  /** Additional project imports needed by the expression. */
  imports?: readonly string[];
  /** Per-probe timeout, bounded by the runtime. */
  timeoutMs?: number;
}>;

const MATH_FAST_CHECK_MAX_PROBE_CASES = 16;
const MATH_FAST_CHECK_MAX_PROBE_CASE_CHARS = 4_000;
const MATH_FAST_CHECK_MAX_PROBE_IMPORTS = 16;

/** Lead-owned bounded falsification pass completed before proof search starts. */
export type MathFastCheck = Readonly<{
  statementHash: string;
  checkedAt: number;
  method: string;
  checkedCaseCount: number;
  outcome: MathFastCheckOutcome;
  candidateClaim: 'statement' | 'negation';
  /** Advisory routing hint retained for compatibility; the Lead owns the direct-vs-DAG decision. */
  directAttemptRecommended: boolean;
  summary: string;
  evidenceRefs: readonly string[];
  /** Optional executable probe. Its result is always runtime-owned evidence. */
  runtimeProbe?: MathFastCheckRuntimeProbe;
}>;

export function normalizeMathFastCheck(input: MathFastCheck): MathFastCheck {
  const statementHash = requiredHash(input.statementHash, 'fastCheck.statementHash');
  if (!Number.isFinite(input.checkedAt) || input.checkedAt <= 0) {
    throw new TypeError('Mathematics fast check checkedAt must be a positive timestamp');
  }
  if (!Number.isSafeInteger(input.checkedCaseCount) || input.checkedCaseCount < 1) {
    throw new TypeError('Mathematics fast check must inspect at least one bounded case');
  }
  if (!MATH_FAST_CHECK_OUTCOMES.includes(input.outcome)) {
    throw new TypeError('Mathematics fast check outcome is invalid');
  }
  if (!['statement', 'negation'].includes(input.candidateClaim)) {
    throw new TypeError('Mathematics fast check candidateClaim is invalid');
  }
  if (typeof input.directAttemptRecommended !== 'boolean') {
    throw new TypeError('Mathematics fast check directAttemptRecommended must be boolean');
  }
  if (input.outcome === 'counterexample_found' && input.candidateClaim !== 'negation') {
    throw new TypeError('A Mathematics counterexample fast check must target the formal negation');
  }
  if (input.outcome === 'no_counterexample_found' && input.candidateClaim !== 'statement') {
    throw new TypeError('A Mathematics no-counterexample fast check must target the original statement');
  }
  if (input.outcome === 'inconclusive' && input.directAttemptRecommended) {
    throw new TypeError('An inconclusive Mathematics fast check cannot recommend a direct attempt');
  }
  const evidenceRefs = textList(input.evidenceRefs, 'fastCheck.evidenceRefs');
  if (input.outcome === 'counterexample_found' && evidenceRefs.length === 0) {
    throw new TypeError('A Mathematics counterexample fast check requires evidence');
  }
  const runtimeProbe = input.runtimeProbe ? normalizeMathFastCheckRuntimeProbe(input.runtimeProbe) : undefined;
  return Object.freeze({
    statementHash,
    checkedAt: input.checkedAt,
    method: boundedRequiredText(input.method, 'fastCheck.method', 2000),
    checkedCaseCount: input.checkedCaseCount,
    outcome: input.outcome,
    candidateClaim: input.candidateClaim,
    directAttemptRecommended: input.directAttemptRecommended,
    summary: boundedRequiredText(input.summary, 'fastCheck.summary', 4000),
    evidenceRefs,
    ...(runtimeProbe ? { runtimeProbe } : {}),
  });
}

function normalizeMathFastCheckRuntimeProbe(input: MathFastCheckRuntimeProbe): MathFastCheckRuntimeProbe {
  if (!input || typeof input !== 'object') {
    throw new TypeError('Mathematics fastCheck.runtimeProbe must be an object');
  }
  const expression = boundedRequiredText(input.expression, 'fastCheck.runtimeProbe.expression', 12_000);
  if (/[\r\n]/u.test(expression) || expression.includes('\0')) {
    throw new TypeError('Mathematics fastCheck.runtimeProbe.expression must be a single-line expression');
  }
  let precondition: string | undefined;
  if (input.precondition !== undefined) {
    precondition = boundedRequiredText(input.precondition, 'fastCheck.runtimeProbe.precondition', 12_000);
    if (/[\r\n]/u.test(precondition) || precondition.includes('\0')) {
      throw new TypeError('Mathematics fastCheck.runtimeProbe.precondition must be a single-line expression');
    }
  }
  const mode = input.mode === undefined ? 'proposition' : input.mode;
  if (mode !== 'proposition' && mode !== 'boolean') {
    throw new TypeError('Mathematics fastCheck.runtimeProbe.mode is invalid');
  }
  let cases: readonly string[] | undefined;
  if (input.cases !== undefined) {
    if (!Array.isArray(input.cases) || input.cases.length < 1 || input.cases.length > MATH_FAST_CHECK_MAX_PROBE_CASES) {
      throw new TypeError(
        `Mathematics fastCheck.runtimeProbe.cases must contain 1-${MATH_FAST_CHECK_MAX_PROBE_CASES} items`
      );
    }
    cases = textList(input.cases, 'fastCheck.runtimeProbe.cases');
    if (
      cases.some(
        (value) => value.length > MATH_FAST_CHECK_MAX_PROBE_CASE_CHARS || /[\r\n]/u.test(value) || value.includes('\0')
      )
    ) {
      throw new TypeError(
        `Mathematics fastCheck.runtimeProbe.cases must be single-line values of at most ${MATH_FAST_CHECK_MAX_PROBE_CASE_CHARS} characters`
      );
    }
  }
  let imports: readonly string[] | undefined;
  if (input.imports !== undefined) {
    if (!Array.isArray(input.imports) || input.imports.length > MATH_FAST_CHECK_MAX_PROBE_IMPORTS) {
      throw new TypeError(
        `Mathematics fastCheck.runtimeProbe.imports must contain at most ${MATH_FAST_CHECK_MAX_PROBE_IMPORTS} items`
      );
    }
    imports = textList(input.imports, 'fastCheck.runtimeProbe.imports');
    if (imports.some((value) => !/^[A-Za-z][A-Za-z0-9_.]*$/u.test(value))) {
      throw new TypeError('Mathematics fastCheck.runtimeProbe.imports contains an invalid module name');
    }
  }
  let timeoutMs: number | undefined;
  if (input.timeoutMs !== undefined) {
    if (!Number.isSafeInteger(input.timeoutMs) || input.timeoutMs < 1_000 || input.timeoutMs > 60_000) {
      throw new TypeError('Mathematics fastCheck.runtimeProbe.timeoutMs must be an integer in [1000,60000]');
    }
    timeoutMs = input.timeoutMs;
  }
  return Object.freeze({
    expression,
    ...(precondition ? { precondition } : {}),
    ...(cases ? { cases } : {}),
    mode,
    ...(imports ? { imports } : {}),
    ...(timeoutMs !== undefined ? { timeoutMs } : {}),
  });
}

/**
 * Signals used to select a formal task before spending a long solver episode.
 * Counts describe the benchmark, while the remaining values are calibrated
 * availability/risk estimates in the closed interval [0, 1]. A high
 * definitionSurface or missingFoundationDepth means more new infrastructure
 * is required; the other availability values are positive signals.
 */
export type MathFeasibilitySignals = Readonly<{
  candidateId?: string;
  acceptedCreditCount: number;
  holeCount: number;
  importCoverage: number;
  literatureAvailability: number;
  relatedFormalizationAvailability: number;
  definitionSurface: number;
  missingFoundationDepth: number;
  formalDegeneracyPotential: number;
  firstMilestoneCost: number;
  toolchainCompatibility: number;
  /** Optional official-catalog gates. Omitted means legacy/non-LeanEval intake. */
  benchmarkCommit?: string;
  statementRevision?: number;
  active?: boolean;
  visible?: boolean;
  inV1?: boolean;
  evidenceSource?: string;
  evidenceFreshAt?: number;
  /** Structural features extracted from the public Lean AST/source. */
  declarationCount?: number;
  declarationSize?: number;
  quantifierDepth?: number;
  typeclassDepth?: number;
  dependencyCriticalPath?: number;
  mathlibApiCoverage?: number;
  /** Optional historical outcomes used for empirical calibration. */
  historicalAttempts?: number;
  historicalSuccesses?: number;
}>;

export const MATH_FEASIBILITY_RISK_CODES = [
  'zero_credit',
  'low_import_coverage',
  'low_literature_availability',
  'low_related_formalization',
  'wide_definition_surface',
  'deep_missing_foundations',
  'formal_degeneracy',
  'expensive_first_milestone',
  'toolchain_incompatible',
  'not_active',
  'not_visible',
  'not_in_v1',
  'stale_evidence',
  'deep_quantifier_nesting',
  'long_dependency_critical_path',
  'low_api_coverage',
  'historical_low_success',
] as const;
export type MathFeasibilityRiskCode = (typeof MATH_FEASIBILITY_RISK_CODES)[number];

/** Ranked, explainable intake result. The score is a bounded presentation value. */
export type MathFeasibilityProfile = Readonly<{
  candidateId?: string;
  candidateIndex: number;
  score: number;
  calibratedSolveProbability: number;
  /** Legacy numeric field above is a ranking heuristic, not a calibrated probability. */
  estimateInterpretation?: 'uncalibrated-structural-ranking';
  historicalSolveRate?: number;
  /** Eligibility is a hard gate; ranking never silently promotes rejected tasks. */
  eligible: boolean;
  rejectionCodes: readonly MathFeasibilityRiskCode[];
  /** Novelty is intentionally independent from solve probability. */
  noveltyScore: number;
  evidence: Readonly<{ source?: string; benchmarkCommit?: string; freshAt?: number }>;
  zeroCredit: boolean;
  majorRisks: readonly MathFeasibilityRiskCode[];
  recommendedFirstMilestone: string;
  signals: MathFeasibilitySignals;
  confidenceInterval?: Readonly<{ lower: number; upper: number; level: number }>;
}>;

const MATH_FEASIBILITY_RATIO_FIELDS = [
  'importCoverage',
  'literatureAvailability',
  'relatedFormalizationAvailability',
  'definitionSurface',
  'missingFoundationDepth',
  'formalDegeneracyPotential',
  'firstMilestoneCost',
  'toolchainCompatibility',
] as const;

function normalizeMathFeasibilityRatio(value: unknown, field: string): number {
  if (typeof value !== 'number' || !Number.isFinite(value) || value < 0 || value > 1) {
    throw new TypeError(`Mathematics feasibility ${field} must be a finite number in [0,1]`);
  }
  return value;
}

function normalizeMathFeasibilityBoolean(value: unknown, field: string): boolean {
  if (typeof value !== 'boolean') throw new TypeError(`Mathematics ${field} must be a boolean`);
  return value;
}

function normalizeOptionalNonnegative(value: unknown, field: string): number | undefined {
  if (value === undefined) return undefined;
  if (typeof value !== 'number' || !Number.isFinite(value) || value < 0) {
    throw new TypeError(`Mathematics ${field} must be a nonnegative finite number`);
  }
  return value;
}

export function normalizeMathFeasibilitySignals(input: MathFeasibilitySignals): MathFeasibilitySignals {
  if (!input || typeof input !== 'object') {
    throw new TypeError('Mathematics feasibility signals are required');
  }
  if (input.candidateId !== undefined && typeof input.candidateId !== 'string') {
    throw new TypeError('Mathematics feasibility candidateId must be a string');
  }
  const candidateId = optionalText(input.candidateId);
  const acceptedCreditCount = nonnegativeInteger(input.acceptedCreditCount, 'feasibility.acceptedCreditCount');
  const holeCount = nonnegativeInteger(input.holeCount, 'feasibility.holeCount');
  const ratios = Object.fromEntries(
    MATH_FEASIBILITY_RATIO_FIELDS.map((field) => [
      field,
      normalizeMathFeasibilityRatio(input[field], `feasibility.${field}`),
    ])
  ) as Record<(typeof MATH_FEASIBILITY_RATIO_FIELDS)[number], number>;
  const historicalAttempts =
    input.historicalAttempts === undefined
      ? undefined
      : nonnegativeInteger(input.historicalAttempts, 'feasibility.historicalAttempts');
  const historicalSuccesses =
    input.historicalSuccesses === undefined
      ? undefined
      : nonnegativeInteger(input.historicalSuccesses, 'feasibility.historicalSuccesses');
  if (historicalSuccesses !== undefined && historicalAttempts === undefined) {
    throw new TypeError('Mathematics feasibility historicalAttempts is required with historicalSuccesses');
  }
  if (
    historicalAttempts !== undefined &&
    historicalSuccesses !== undefined &&
    historicalSuccesses > historicalAttempts
  ) {
    throw new TypeError('Mathematics feasibility historicalSuccesses cannot exceed historicalAttempts');
  }
  return Object.freeze({
    ...(candidateId ? { candidateId: boundedRequiredText(candidateId, 'feasibility.candidateId', 256) } : {}),
    acceptedCreditCount,
    holeCount,
    ...ratios,
    ...(input.benchmarkCommit !== undefined
      ? { benchmarkCommit: boundedRequiredText(input.benchmarkCommit, 'feasibility.benchmarkCommit', 128) }
      : {}),
    ...(input.statementRevision !== undefined
      ? { statementRevision: nonnegativeInteger(input.statementRevision, 'feasibility.statementRevision') }
      : {}),
    ...(input.active !== undefined
      ? { active: normalizeMathFeasibilityBoolean(input.active, 'feasibility.active') }
      : {}),
    ...(input.visible !== undefined
      ? { visible: normalizeMathFeasibilityBoolean(input.visible, 'feasibility.visible') }
      : {}),
    ...(input.inV1 !== undefined ? { inV1: normalizeMathFeasibilityBoolean(input.inV1, 'feasibility.inV1') } : {}),
    ...(input.evidenceSource !== undefined
      ? { evidenceSource: boundedRequiredText(input.evidenceSource, 'feasibility.evidenceSource', 256) }
      : {}),
    ...(input.evidenceFreshAt !== undefined
      ? { evidenceFreshAt: nonnegativeInteger(input.evidenceFreshAt, 'feasibility.evidenceFreshAt') }
      : {}),
    ...(input.declarationCount !== undefined
      ? { declarationCount: normalizeOptionalNonnegative(input.declarationCount, 'feasibility.declarationCount') }
      : {}),
    ...(input.declarationSize !== undefined
      ? { declarationSize: normalizeOptionalNonnegative(input.declarationSize, 'feasibility.declarationSize') }
      : {}),
    ...(input.quantifierDepth !== undefined
      ? { quantifierDepth: normalizeOptionalNonnegative(input.quantifierDepth, 'feasibility.quantifierDepth') }
      : {}),
    ...(input.typeclassDepth !== undefined
      ? { typeclassDepth: normalizeOptionalNonnegative(input.typeclassDepth, 'feasibility.typeclassDepth') }
      : {}),
    ...(input.dependencyCriticalPath !== undefined
      ? {
          dependencyCriticalPath: normalizeOptionalNonnegative(
            input.dependencyCriticalPath,
            'feasibility.dependencyCriticalPath'
          ),
        }
      : {}),
    ...(input.mathlibApiCoverage !== undefined
      ? {
          mathlibApiCoverage: normalizeMathFeasibilityRatio(input.mathlibApiCoverage, 'feasibility.mathlibApiCoverage'),
        }
      : {}),
    ...(historicalAttempts !== undefined ? { historicalAttempts } : {}),
    ...(historicalSuccesses !== undefined ? { historicalSuccesses } : {}),
  });
}

function mathFeasibilityRiskCodes(signals: MathFeasibilitySignals): readonly MathFeasibilityRiskCode[] {
  const risks: MathFeasibilityRiskCode[] = [];
  if (signals.acceptedCreditCount === 0) risks.push('zero_credit');
  if (signals.importCoverage < 0.5) risks.push('low_import_coverage');
  if (signals.literatureAvailability < 0.35) risks.push('low_literature_availability');
  if (signals.relatedFormalizationAvailability < 0.35) risks.push('low_related_formalization');
  if (signals.definitionSurface > 0.6) risks.push('wide_definition_surface');
  if (signals.missingFoundationDepth > 0.5) risks.push('deep_missing_foundations');
  if (signals.formalDegeneracyPotential > 0.5) risks.push('formal_degeneracy');
  if (signals.firstMilestoneCost > 0.6) risks.push('expensive_first_milestone');
  if (signals.toolchainCompatibility < 0.75) risks.push('toolchain_incompatible');
  if (signals.active === false) risks.push('not_active');
  if (signals.visible === false) risks.push('not_visible');
  if (signals.inV1 === false) risks.push('not_in_v1');
  if (signals.evidenceFreshAt !== undefined && signals.evidenceFreshAt < Date.now() - 30 * 24 * 60 * 60 * 1000) {
    risks.push('stale_evidence');
  }
  if ((signals.quantifierDepth ?? 0) > 5 || (signals.typeclassDepth ?? 0) > 4) risks.push('deep_quantifier_nesting');
  if ((signals.dependencyCriticalPath ?? 0) > 6) risks.push('long_dependency_critical_path');
  if (signals.mathlibApiCoverage !== undefined && signals.mathlibApiCoverage < 0.35) risks.push('low_api_coverage');
  if (
    signals.historicalAttempts !== undefined &&
    signals.historicalAttempts >= 3 &&
    (signals.historicalSuccesses ?? 0) / Math.max(1, signals.historicalAttempts) < 0.2
  ) {
    risks.push('historical_low_success');
  }
  return Object.freeze(risks);
}

function mathFeasibilityFirstMilestone(
  signals: MathFeasibilitySignals,
  risks: readonly MathFeasibilityRiskCode[]
): string {
  if (signals.toolchainCompatibility < 0.75)
    return 'Validate the pinned Lean toolchain and compile a minimal import probe.';
  if (signals.importCoverage < 0.5)
    return 'Close the smallest import/API gap and compile one declaration using the live imports.';
  if (signals.missingFoundationDepth > 0.5 || signals.definitionSurface > 0.6) {
    return 'Implement and compile the smallest missing definition or endpoint helper.';
  }
  if (signals.relatedFormalizationAvailability < 0.35 && signals.literatureAvailability < 0.35) {
    return 'Run one bounded literature and public-formalization probe for a reusable construction.';
  }
  if (signals.firstMilestoneCost > 0.6)
    return 'Reduce the route to a cheaper typed lemma before attempting the full theorem.';
  if (signals.holeCount === 0) return 'Compile the named theorem against the frozen benchmark imports.';
  if (risks.includes('formal_degeneracy'))
    return 'Run a bounded degeneracy check and freeze the first non-degenerate formal case.';
  return 'Compile the first hole-aligned lemma and retain its exact declaration receipt.';
}

/** Build one deterministic, bounded solve-probability profile. */
export function buildMathFeasibilityProfile(input: MathFeasibilitySignals, candidateIndex = 0): MathFeasibilityProfile {
  const signals = normalizeMathFeasibilitySignals(input);
  if (!Number.isSafeInteger(candidateIndex) || candidateIndex < 0) {
    throw new TypeError('Mathematics feasibility candidateIndex must be a nonnegative integer');
  }
  // Coverage and toolchain readiness dominate the estimate. Credit and hole
  // counts are deliberately small terms so statement size does not win intake.
  const holeSignal = 1 / (1 + Math.log1p(signals.holeCount));
  const structuralReadiness =
    (signals.mathlibApiCoverage ?? signals.importCoverage) * 0.08 +
    (1 - Math.min(1, (signals.quantifierDepth ?? 0) / 8)) * 0.04 +
    (1 - Math.min(1, (signals.typeclassDepth ?? 0) / 6)) * 0.03 +
    (1 - Math.min(1, (signals.dependencyCriticalPath ?? signals.holeCount) / 12)) * 0.04;
  const historicalRate =
    signals.historicalAttempts && signals.historicalAttempts > 0
      ? (signals.historicalSuccesses ?? 0) / signals.historicalAttempts
      : undefined;
  const weightedReadiness =
    signals.importCoverage * 0.18 +
    signals.literatureAvailability * 0.12 +
    signals.relatedFormalizationAvailability * 0.16 +
    (1 - signals.definitionSurface) * 0.08 +
    (1 - signals.missingFoundationDepth) * 0.12 +
    (1 - signals.formalDegeneracyPotential) * 0.08 +
    (1 - signals.firstMilestoneCost) * 0.07 +
    signals.toolchainCompatibility * 0.14 +
    holeSignal * 0.02 +
    structuralReadiness +
    (historicalRate === undefined ? 0 : (historicalRate - 0.5) * 0.08);
  const calibratedSolveProbability =
    Math.round(Math.max(0.01, Math.min(0.99, 0.02 + weightedReadiness * 0.96)) * 10_000) / 10_000;
  const risks = mathFeasibilityRiskCodes(signals);
  const rejectionCodes = risks.filter((risk) =>
    ['not_active', 'not_visible', 'not_in_v1', 'toolchain_incompatible', 'stale_evidence'].includes(risk)
  );
  const eligible = rejectionCodes.length === 0;
  const noveltyScore = Math.round((1 / (1 + signals.acceptedCreditCount)) * 10_000) / 10_000;
  const confidenceInterval = (() => {
    const attempts = signals.historicalAttempts ?? 0;
    if (!attempts) return undefined;
    const successes = Math.min(attempts, signals.historicalSuccesses ?? 0);
    const p = successes / attempts;
    const z = 1.96;
    const denominator = 1 + (z * z) / attempts;
    const center = (p + (z * z) / (2 * attempts)) / denominator;
    const radius = (z / denominator) * Math.sqrt((p * (1 - p)) / attempts + (z * z) / (4 * attempts * attempts));
    return Object.freeze({ lower: Math.max(0, center - radius), upper: Math.min(1, center + radius), level: 0.95 });
  })();
  return Object.freeze({
    ...(signals.candidateId ? { candidateId: signals.candidateId } : {}),
    candidateIndex,
    score: Math.round(calibratedSolveProbability * 1000) / 10,
    calibratedSolveProbability,
    estimateInterpretation: 'uncalibrated-structural-ranking' as const,
    ...(historicalRate !== undefined ? { historicalSolveRate: historicalRate } : {}),
    eligible,
    rejectionCodes: Object.freeze(rejectionCodes),
    noveltyScore,
    evidence: Object.freeze({
      ...(signals.evidenceSource ? { source: signals.evidenceSource } : {}),
      ...(signals.benchmarkCommit ? { benchmarkCommit: signals.benchmarkCommit } : {}),
      ...(signals.evidenceFreshAt !== undefined ? { freshAt: signals.evidenceFreshAt } : {}),
    }),
    zeroCredit: signals.acceptedCreditCount === 0,
    majorRisks: risks,
    recommendedFirstMilestone: mathFeasibilityFirstMilestone(signals, risks),
    signals,
    ...(confidenceInterval ? { confidenceInterval } : {}),
  });
}

/** Rank formal candidates by expected solve probability, retaining stable ties. */
export function rankMathFeasibilityCandidates(
  inputs: readonly MathFeasibilitySignals[]
): readonly MathFeasibilityProfile[] {
  if (!Array.isArray(inputs)) throw new TypeError('Mathematics feasibility candidates must be an array');
  const profiles = inputs.map((input, index) => buildMathFeasibilityProfile(input, index));
  return Object.freeze(
    profiles.toSorted(
      (left, right) =>
        Number(right.eligible) - Number(left.eligible) ||
        right.calibratedSolveProbability - left.calibratedSolveProbability ||
        right.noveltyScore - left.noveltyScore ||
        left.candidateIndex - right.candidateIndex
    )
  );
}

/**
 * Problem identity published by an official benchmark repository.  The
 * verifier reads this file from the exact target commit before running the
 * comparator; worker-supplied prose is never treated as the authority.
 */
export type MathOfficialProblemManifest = Readonly<{
  schema: 'deepscientist.mathematics.official-manifest.v1';
  manifestId: string;
  manifestHash: string;
  problemId: string;
  informalStatement: string;
  formalStatement: string;
  formalNegationStatement?: string;
  assumptions: readonly string[];
  statementHash: string;
  leanStatementHash: string;
  leanNegationHash?: string;
  officialVerificationCommand: string;
  repositoryUrl: string;
  baselineCommit: string;
  benchmarkAdapterId: string;
  benchmarkAdapterVersion: string;
  trackedFiles: readonly Readonly<{ path: string; sha256: string }>[];
  targetCommit?: string;
}>;

export function normalizeMathOfficialProblemManifest(input: MathOfficialProblemManifest): MathOfficialProblemManifest {
  const manifestId = requiredText(input.manifestId, 'officialManifest.manifestId');
  const manifestHash = requiredHash(input.manifestHash, 'officialManifest.manifestHash');
  const problemId = requiredText(input.problemId, 'officialManifest.problemId');
  const informalStatement = requiredText(input.informalStatement, 'officialManifest.informalStatement');
  const formalStatement = requiredText(input.formalStatement, 'officialManifest.formalStatement');
  const formalNegationStatement = optionalText(input.formalNegationStatement);
  const assumptions = textList(input.assumptions, 'officialManifest.assumptions');
  const statementHash = requiredHash(input.statementHash, 'officialManifest.statementHash');
  const leanStatementHash = requiredHash(input.leanStatementHash, 'officialManifest.leanStatementHash');
  const leanNegationHash = optionalText(input.leanNegationHash);
  if (Boolean(formalNegationStatement) !== Boolean(leanNegationHash)) {
    throw new TypeError('officialManifest formal negation statement and hash must be supplied together');
  }
  const officialVerificationCommand = requiredText(
    input.officialVerificationCommand,
    'officialManifest.officialVerificationCommand'
  );
  const repositoryUrl = requiredText(input.repositoryUrl, 'officialManifest.repositoryUrl');
  if (!/^(?:https:\/\/[^\s]+|ssh:\/\/[^\s]+|git@[^\s:]+:[^\s]+)$/u.test(repositoryUrl)) {
    throw new TypeError('officialManifest.repositoryUrl must be an HTTPS or SSH repository URL');
  }
  const baselineCommit = input.baselineCommit?.trim().toLowerCase();
  if (!baselineCommit || !/^(?:[0-9a-f]{40}|[0-9a-f]{64})$/u.test(baselineCommit)) {
    throw new TypeError('officialManifest.baselineCommit must be a full Git object id');
  }
  const benchmarkAdapterId = requiredText(input.benchmarkAdapterId, 'officialManifest.benchmarkAdapterId');
  const benchmarkAdapterVersion = requiredText(
    input.benchmarkAdapterVersion,
    'officialManifest.benchmarkAdapterVersion'
  );
  if (!Array.isArray(input.trackedFiles) || input.trackedFiles.length < 1 || input.trackedFiles.length > 1024) {
    throw new TypeError('officialManifest.trackedFiles must contain 1-1024 official file hashes');
  }
  const trackedFilePathSet = new Set<string>();
  const trackedFiles = Object.freeze(
    input.trackedFiles.map((file, index) => {
      const filePath = requiredText(file.path, `officialManifest.trackedFiles[${index}].path`)
        .replaceAll('\\', '/')
        .replace(/^\.\//u, '');
      if (filePath.startsWith('/') || filePath.split('/').includes('..') || filePath.includes('\0')) {
        throw new TypeError(`officialManifest.trackedFiles[${index}].path must be repository-relative`);
      }
      trackedFilePathSet.add(filePath);
      return Object.freeze({
        path: filePath,
        sha256: requiredHash(file.sha256, `officialManifest.trackedFiles[${index}].sha256`),
      });
    })
  );
  if (trackedFilePathSet.size !== trackedFiles.length) {
    throw new TypeError('officialManifest.trackedFiles paths must be unique');
  }
  const targetCommit = input.targetCommit?.trim();
  if (targetCommit && !/^(?:[0-9a-f]{40}|[0-9a-f]{64})$/u.test(targetCommit)) {
    throw new TypeError('officialManifest.targetCommit must be a full Git object id');
  }
  return Object.freeze({
    schema: 'deepscientist.mathematics.official-manifest.v1',
    manifestId,
    manifestHash,
    problemId,
    informalStatement,
    formalStatement,
    ...(formalNegationStatement ? { formalNegationStatement } : {}),
    assumptions,
    statementHash,
    leanStatementHash,
    ...(leanNegationHash
      ? { leanNegationHash: requiredHash(leanNegationHash, 'officialManifest.leanNegationHash') }
      : {}),
    officialVerificationCommand,
    repositoryUrl,
    baselineCommit,
    benchmarkAdapterId,
    benchmarkAdapterVersion,
    trackedFiles,
    ...(targetCommit ? { targetCommit } : {}),
  });
}

export function assertMathProblemContractMatchesOfficialManifest(
  contract: MathProblemContract,
  manifest: MathOfficialProblemManifest
): void {
  const normalizedContract = normalizeMathProblemContract(contract);
  const normalizedManifest = normalizeMathOfficialProblemManifest(manifest);
  if (
    normalizedContract.problemId !== normalizedManifest.problemId ||
    normalizedContract.statementHash !== normalizedManifest.statementHash ||
    normalizedContract.leanStatementHash !== normalizedManifest.leanStatementHash ||
    normalizedContract.informalStatement !== normalizedManifest.informalStatement ||
    normalizedContract.formalStatement !== normalizedManifest.formalStatement ||
    normalizedContract.formalNegationStatement !== normalizedManifest.formalNegationStatement ||
    normalizedContract.leanNegationHash !== normalizedManifest.leanNegationHash ||
    JSON.stringify(normalizedContract.assumptions) !== JSON.stringify(normalizedManifest.assumptions) ||
    normalizedContract.officialVerificationCommand !== normalizedManifest.officialVerificationCommand
  ) {
    throw new TypeError('Mathematics problem contract does not match the official problem manifest');
  }
  if (
    normalizedContract.officialManifestId &&
    normalizedContract.officialManifestId !== normalizedManifest.manifestId
  ) {
    throw new TypeError('Mathematics problem contract officialManifestId does not match the official manifest');
  }
  if (
    normalizedContract.officialManifestHash &&
    normalizedContract.officialManifestHash !== normalizedManifest.manifestHash
  ) {
    throw new TypeError('Mathematics problem contract officialManifestHash does not match the official manifest');
  }
}

/** Canonical bytes hashed by trusted process boundaries for statement identity. */
export function canonicalMathProblemStatementPayloads(
  input: Pick<MathProblemContract, 'informalStatement' | 'formalStatement' | 'assumptions'>
): Readonly<{ informal: string; lean: string }> {
  const assumptions = textList(input.assumptions, 'problemContract.assumptions');
  return Object.freeze({
    informal: JSON.stringify({
      schema: 'deepscientist.mathematics.informal-statement.v1',
      statement: requiredText(input.informalStatement, 'problemContract.informalStatement'),
      assumptions,
    }),
    lean: JSON.stringify({
      schema: 'deepscientist.mathematics.lean-statement.v1',
      statement: requiredText(input.formalStatement, 'problemContract.formalStatement'),
      assumptions,
    }),
  });
}

export function canonicalMathProblemNegationPayload(
  input: Pick<MathProblemContract, 'formalNegationStatement' | 'assumptions'>
): string | undefined {
  const formalNegationStatement = optionalText(input.formalNegationStatement);
  if (!formalNegationStatement) return undefined;
  return JSON.stringify({
    schema: 'deepscientist.mathematics.lean-negation.v1',
    statement: formalNegationStatement,
    assumptions: textList(input.assumptions, 'problemContract.assumptions'),
  });
}

export const MATH_ALIGNMENT_VERDICTS = ['exact', 'stronger', 'weaker', 'mismatch', 'unknown'] as const;
export type MathAlignmentVerdict = (typeof MATH_ALIGNMENT_VERDICTS)[number];

/** Lead-owned statement quiz completed before proof-producing work starts. */
export type MathAlignmentCheck = Readonly<{
  problemId: string;
  statementHash: string;
  leanStatementHash: string;
  contractCommit: string;
  assessorSessionId: string;
  goalInOwnWords: string;
  quantifiedObjects: readonly string[];
  assumptions: readonly string[];
  forbiddenChanges: readonly string[];
  officialVerificationCommand: string;
  verdict: MathAlignmentVerdict;
  assumptionDelta: readonly string[];
  quantifierDelta: readonly string[];
  domainDelta: readonly string[];
  firstMismatch?: string;
}>;

export const MATH_PLAN_NODE_ROLES = ['goal', 'reduction', 'auxiliary', 'case_split', 'bridge'] as const;
export type MathPlanNodeRole = (typeof MATH_PLAN_NODE_ROLES)[number];

export const MATH_PLAN_NODE_KINDS = ['theorem', 'definition', 'api_bridge', 'ported_helper'] as const;
export type MathPlanNodeKind = (typeof MATH_PLAN_NODE_KINDS)[number];

export const MATH_PROOF_PLAN_SCHEMA = 'deepscientist.mathematics.proof-plan.v1' as const;
export const MATH_PROOF_STATE_SCHEMA = 'deepscientist.mathematics.proof-state.v1' as const;
export const MATH_PROOF_ACTION_SCHEMA = 'deepscientist.mathematics.proof-action.v1' as const;

export const MATH_PROOF_PLAN_MECHANISMS = [
  'invariant',
  'induction',
  'well_founded',
  'normal_form',
  'case_split',
  'finite_certificate',
  'contradiction',
  'structure_classification',
  'compactness',
  'asymptotic_estimate',
  'other',
] as const;
export type MathProofPlanMechanism = (typeof MATH_PROOF_PLAN_MECHANISMS)[number];

export const MATH_PROOF_ACTION_KINDS = [
  'tactic',
  'premise',
  'rewrite',
  'constructor',
  'cases',
  'induction',
  'helper',
  'import',
] as const;
export type MathProofActionKind = (typeof MATH_PROOF_ACTION_KINDS)[number];

export const MATH_PROOF_ACTION_OUTCOMES = ['advanced', 'unchanged', 'failed', 'inconclusive'] as const;
export type MathProofActionOutcome = (typeof MATH_PROOF_ACTION_OUTCOMES)[number];

export const MATH_PROOF_STATE_STATUSES = ['open', 'closed', 'failed', 'timeout'] as const;
export type MathProofStateStatus = (typeof MATH_PROOF_STATE_STATUSES)[number];

export const MATH_PLAN_NODE_STATUSES = [
  'proposed',
  'sourced',
  'counterexample_checked',
  'typed',
  'compiling',
  'compiled',
  'kernel_verified',
  'refuted',
] as const;
export type MathPlanNodeStatus = (typeof MATH_PLAN_NODE_STATUSES)[number];

export const MATH_SOURCE_KINDS = ['paper', 'mathlib', 'lean_package', 'local'] as const;
export type MathSourceKind = (typeof MATH_SOURCE_KINDS)[number];

export const MATH_SOURCE_COMPATIBILITY = ['exact', 'portable', 'conceptual', 'rejected'] as const;
export type MathSourceCompatibility = (typeof MATH_SOURCE_COMPATIBILITY)[number];

/** Auditable source identity for a paper argument or reusable formal dependency. */
export type MathSourceProvenance = Readonly<{
  kind: MathSourceKind;
  locator: string;
  compatibility: MathSourceCompatibility;
  commit?: string;
  license?: string;
  evidenceRef: string;
}>;

/** One locally revisable claim in a route-level lemma DAG. */
export type MathPlanNode = Readonly<{
  id: string;
  informalClaim: string;
  provisionalLeanStatement: string;
  dependsOn: readonly string[];
  role: MathPlanNodeRole;
  status: MathPlanNodeStatus;
  evidenceRefs: readonly string[];
  /** Hierarchical containment for infrastructure expanded beneath a stable route milestone. */
  parentNodeId?: string;
  kind?: MathPlanNodeKind;
  /** Relative 1-5 engineering cost used by the runtime scheduler. */
  estimatedEffort?: number;
  /** Calibrated probability in [0,1] of completing the node in its next bounded episode. */
  successProbability?: number;
  /** Relative 1-5 value independent of graph fan-out. */
  downstreamValue?: number;
  sourceProvenance?: readonly MathSourceProvenance[];
  /** Optional executable scaffold retained with the node for local repair. */
  proofSkeleton?: string;
  /** Runtime-facing description of the state change that closes this node. */
  expectedProgress?: string;
  /** Concrete conditions that the runtime can check before marking the node complete. */
  successCriteria?: readonly string[];
  /** Alternate node ids to try after a structural failure. */
  fallbackNodeIds?: readonly string[];
  /** Mathematical mechanism proposed for this local claim. */
  mechanism?: MathProofPlanMechanism;
}>;

/** Explicit explanation of how one lemma DAG dependency is consumed downstream. */
export type MathPlanBridge = Readonly<{
  dependencyNodeId: string;
  consumerNodeId: string;
  mathematicalBridge: string;
  leanUse: string;
}>;

/** Versioned executable proof plan carried alongside the route-card projection. */
export type MathProofPlan = Readonly<{
  schema: typeof MATH_PROOF_PLAN_SCHEMA;
  version: 1;
  planId: string;
  statementHash: string;
  routeFingerprint: string;
  rootNodeId: string;
  planNodes: readonly MathPlanNode[];
  bridges: readonly MathPlanBridge[];
  bottleneckNodeId?: string;
  openFrontierNodeIds: readonly string[];
}>;

/** One runtime action that was actually attempted against a Lean state. */
export type MathProofAction = Readonly<{
  schema: typeof MATH_PROOF_ACTION_SCHEMA;
  version: 1;
  actionId: string;
  kind: MathProofActionKind;
  payload: string;
  preconditionStateId: string;
  resultStateId?: string;
  runtime: Readonly<{
    durationMs: number;
    exitCode?: number;
    diagnosticHash?: string;
  }>;
  outcome: MathProofActionOutcome;
}>;

/** Persistent Lean state used to resume and deduplicate bounded proof search. */
export type MathProofState = Readonly<{
  schema: typeof MATH_PROOF_STATE_SCHEMA;
  version: 1;
  episodeId: string;
  stateId: string;
  parentStateId?: string;
  statementHash: string;
  routeFingerprint: string;
  planId?: string;
  goalFingerprint: string;
  sourceFile: string;
  sourceHash: string;
  openGoals: readonly string[];
  localContextHash: string;
  metavariableCount: number;
  declarationHashes: readonly string[];
  actionHistory: readonly MathProofAction[];
  actionHistoryOffset?: number;
  actionHistoryRef?: string;
  status: MathProofStateStatus;
}>;

export const MATH_PREMISE_STATUSES = ['proposed', 'located', 'typed', 'rejected'] as const;
export type MathPremiseStatus = (typeof MATH_PREMISE_STATUSES)[number];

export const MATH_PREMISE_SOURCE_KINDS = ['library', 'verified_local'] as const;
export type MathPremiseSourceKind = (typeof MATH_PREMISE_SOURCE_KINDS)[number];

/** One exact library or locally verified declaration used by the complete proof route. */
export type MathPremiseCandidate = Readonly<{
  declarationName: string;
  declarationType: string;
  sourceKind: MathPremiseSourceKind;
  sourceModule?: string;
  sourceCommit?: string;
  sourceFile?: string;
  proofHash?: string;
  importModules?: readonly string[];
  checkedAtCommit?: string;
  intendedUse: string;
  status: MathPremiseStatus;
  evidenceRefs: readonly string[];
}>;

/** Explicit mapping from one route-DAG node to the premises needed to formalize it. */
export type MathPremiseCoverage = Readonly<{
  planNodeId: string;
  premiseDeclarationNames: readonly string[];
  selfContained: boolean;
  unresolvedNeed?: string;
}>;

export const MATH_PREMISE_COVERAGE_STATUSES = ['covered', 'partial', 'missing'] as const;
export type MathPremiseCoverageStatus = (typeof MATH_PREMISE_COVERAGE_STATUSES)[number];

/** Runtime-derived coverage row. Workers provide the mapping, never its status. */
export type MathPremiseCoverageRow = MathPremiseCoverage &
  Readonly<{
    status: MathPremiseCoverageStatus;
    untypedPremiseDeclarationNames: readonly string[];
  }>;

/** Whole-route retrieval result shared by every Worker assigned to this route. */
export type MathPremiseBundle = Readonly<{
  strategySketch: string;
  leanSkeleton: string;
  premises: readonly MathPremiseCandidate[];
  coverage: readonly MathPremiseCoverage[];
  unresolvedNeeds: readonly string[];
}>;

export const MATH_ROUTE_CHECK_VERDICTS = ['pass', 'fail', 'unknown'] as const;
export type MathRouteCheckVerdict = (typeof MATH_ROUTE_CHECK_VERDICTS)[number];

export const MATH_ROUTE_PROBE_OUTCOMES = [
  'not_run',
  'inconclusive',
  'supported',
  'kernel_verified',
  'refuted',
] as const;
export type MathRouteProbeOutcome = (typeof MATH_ROUTE_PROBE_OUTCOMES)[number];

/** Distinguishes an axiom-backed composition probe from real dependency proof. */
export const MATH_ROUTE_PROBE_VERIFICATION_MODES = ['speculative_axiom_closure', 'verified_dependencies'] as const;
export type MathRouteProbeVerificationMode = (typeof MATH_ROUTE_PROBE_VERIFICATION_MODES)[number];

export const MATH_SEMANTIC_VIABILITY_KINDS = [
  'premise_domain',
  'state_invariant',
  'boundary_cases',
  'terminal_closure',
] as const;
export type MathSemanticViabilityKind = (typeof MATH_SEMANTIC_VIABILITY_KINDS)[number];

/** One cheap semantic obligation checked before full proof assembly starts. */
export type MathSemanticViabilityCheck = Readonly<{
  kind: MathSemanticViabilityKind;
  planNodeId: string;
  verdict: MathRouteCheckVerdict;
  summary: string;
  evidenceRefs: readonly string[];
}>;

/** Fresh Lead-owned check performed after a Strategy Explorer proposes a plan. */
export type MathRouteAssessment = Readonly<{
  assessorSessionId: string;
  probePlanNodeId: string;
  faithfulness: MathRouteCheckVerdict;
  mathematicalValidity: MathRouteCheckVerdict;
  decompositionUsefulness: MathRouteCheckVerdict;
  probeOutcome: MathRouteProbeOutcome;
  probeSummary: string;
  evidenceRefs: readonly string[];
  /** One Lead-owned probe may discharge all four checks; no extra Worker wave is implied. */
  semanticViabilityChecks?: readonly MathSemanticViabilityCheck[];
  checkedAt: number;
}>;

export type MathRouteCard = Readonly<{
  statementHash: string;
  routeFingerprint: string;
  proposerSessionId: string;
  structuralCommitment: string;
  decisiveLemma: string;
  decisiveTest: string;
  falsificationSignal: string;
  premiseBundle: MathPremiseBundle;
  planNodes: readonly MathPlanNode[];
  bridges: readonly MathPlanBridge[];
  rootNodeId: string;
  bottleneckNodeId?: string;
  openFrontierNodeIds: readonly string[];
  /** Required only for an explicitly expanded hard-problem DAG (8-128 nodes). */
  extendedPlanReason?: string;
  /** Absent on the raw Worker proposal; required before route selection. */
  assessment?: MathRouteAssessment;
  expectedInformationGain: number;
  estimatedCost: number;
  formalizationRisk: number;
}>;

/** Minimal executable context for one dependency-ready formalization node. */
export type MathActiveNodeProofPack = Readonly<{
  statementHash: string;
  routeFingerprint: string;
  activePlanNodeId: string;
  activeNode: MathPlanNode;
  /** Natural-language and Lean skeleton scaffold retained by the route card. */
  strategySketch: string;
  leanSkeleton: string;
  /** Optional project-local sketch artifact to revise after a structural failure. */
  solutionSketchRef?: string;
  dependencyNodes: readonly MathPlanNode[];
  bridges: readonly MathPlanBridge[];
  premises: readonly MathPremiseCandidate[];
  /** Small goal-aligned suggestions from the route premise slate; validate against the live Lean goal. */
  premiseHints: readonly MathPremiseCandidate[];
  /** Bounded live-goal query template; execute only after a premise-shaped Lean failure or a real stall. */
  premiseRetrieval?: Readonly<{
    tool: 'math_portfolio';
    action: 'get';
    problemId: string;
    routeFingerprint: string;
    planNodeId: string;
    premiseLimit: 4;
    goalSource: 'live_lean_goal';
    importModulesSource: 'current_lean_file';
    sourceFileSource: 'current_lean_file';
    cacheBy: 'proof_state_fingerprint';
    upstreamSources: readonly ['leansearch', 'loogle'];
    upstreamActivation: 'after_local_miss';
  }>;
  premiseCoverage: readonly MathPremiseCoverage[];
}>;

export type MathRouteSelection = Readonly<{
  statementHash: string;
  selectionCommit: string;
  primaryFingerprint: string;
  reserveFingerprint?: string;
  comparedFingerprints: readonly string[];
  rationale: string;
  selectedAt: number;
  /** Optional semantic re-materialization marker when the proof base advances. */
  rebasedFromCommit?: string;
  revalidatedAtCommit?: string;
}>;

/** Runtime-derived route cost; Workers never estimate or report these fields. */
export type MathRouteExecutionEstimate = Readonly<{
  nodeCount: number;
  kernelVerifiedNodeCount: number;
  typedOrVerifiedNodeCount: number;
  evidenceBackedNodeCount: number;
  remainingNodeCount: number;
  remainingCriticalPathLength: number;
  usefulNodeConcurrency: number;
}>;

export const MATH_LESSON_DISPOSITIONS = ['avoid_route', 'avoid_pattern', 'reuse'] as const;
export type MathLessonDisposition = (typeof MATH_LESSON_DISPOSITIONS)[number];

/** Compact, evidence-bound experience that can be injected into later waves. */
export type MathLesson = Readonly<{
  lessonId: string;
  statementHash: string;
  routeFingerprint: string;
  sourceCommit: string;
  failureCategory: MathFailureCategory;
  disposition: MathLessonDisposition;
  trigger: string;
  failedPattern: string;
  rootCause: string;
  reusableRule: string;
  evidenceRefs: readonly string[];
  createdAt: number;
}>;

/** Kernel-grounded receipt produced by LOCAL_GATE for one frozen candidate. */
export type MathLocalGateReceipt = Readonly<{
  receiptId: string;
  targetCommit: string;
  statementHash: string;
  /** Omitted only by legacy receipts, where `statement` is implied. */
  claim?: 'statement' | 'negation';
  /** Runtime-bound hash of the exact canonical Lean proposition. */
  leanStatementHash?: string;
  routeFingerprint: string;
  status: 'kernel_verified';
  verifier: 'lean-kernel';
  theoremName: string;
  proofHash: string;
  theoremDeclarationHash: string;
  sourceDeclarationHash?: string;
  goalsRemaining: 0;
  sorryCount: 0;
  admitCount: 0;
  axioms: readonly string[];
  checkedAt: number;
}>;

export const MATH_FOUNDATIONAL_LEAN_AXIOMS = Object.freeze([
  'Classical.choice',
  'Quot.sound',
  'choice',
  'propext',
] as const);

const MATH_FOUNDATIONAL_LEAN_AXIOM_SET = new Set<string>(MATH_FOUNDATIONAL_LEAN_AXIOMS);

export const isMathFoundationalLeanAxiom = (value: string): boolean =>
  MATH_FOUNDATIONAL_LEAN_AXIOM_SET.has(value.trim());

export type MathReceiptAttestation = Readonly<{
  algorithm: 'hmac-sha256';
  keyId: string;
  value: string;
}>;

/** Runtime-owned completion identity; model text is not completion evidence. */
export type MathSolverReadyReceipt = Readonly<{
  schema: 'deepscientist.mathematics.solver-ready.v1';
  receiptId: string;
  teamId: string;
  slotId: string;
  assignmentId: string;
  deliveryId: string;
  targetCommit: string;
  statementHash: string;
  routeFingerprint: string;
  checkedAt: number;
  attestation: MathReceiptAttestation;
}>;

export type MathRouteProbeBrief = Readonly<{
  routeFingerprint: string;
  structuralCommitment: string;
  decisiveLemma: string;
  decisiveTest: string;
  falsificationSignal: string;
  expectedInformationGain: number;
  estimatedCost: number;
  formalizationRisk: number;
}>;

export type MathRouteProbeReceipt = Readonly<{
  receiptId: string;
  statementHash: string;
  routeFingerprint: string;
  routeBrief: MathRouteProbeBrief;
  proposerSessionId: string;
  assessorSessionId: string;
  outcome: MathRouteProbeOutcome;
  /** Omitted only by legacy receipts; new runtime probes must state their evidence mode. */
  verificationMode?: MathRouteProbeVerificationMode;
  probeSummary: string;
  evidenceRefs: readonly string[];
  checkedAt: number;
  proposalDeliveryId: string;
  assessmentDeliveryId: string;
  /** Runtime-owned route-composition evidence bound before a Formalizer is dispatched. */
  runtimeBinding?: Readonly<{
    targetCommit: string;
    routeStructureHash: string;
    sourceHash: string;
    harnessHash: string;
    environmentFingerprint: string;
    proofStateFingerprint: string;
    durationMs: number;
    sandboxBackend?: 'unshare' | 'bwrap' | 'docker' | 'podman';
  }>;
  attestation?: MathReceiptAttestation;
}>;

export function normalizeMathRouteProbeReceipt(input: MathRouteProbeReceipt): MathRouteProbeReceipt {
  if (!input || typeof input !== 'object') throw new TypeError('Mathematics route probe receipt is required');
  if (!MATH_ROUTE_PROBE_OUTCOMES.includes(input.outcome)) {
    throw new TypeError('Mathematics route probe receipt outcome is invalid');
  }
  if (input.verificationMode !== undefined && !MATH_ROUTE_PROBE_VERIFICATION_MODES.includes(input.verificationMode)) {
    throw new TypeError('Mathematics route probe receipt verificationMode is invalid');
  }
  if (input.verificationMode === 'speculative_axiom_closure' && input.outcome === 'kernel_verified') {
    throw new TypeError('A speculative axiom-backed route probe cannot be kernel_verified');
  }
  if (input.verificationMode === 'verified_dependencies' && input.outcome !== 'kernel_verified') {
    throw new TypeError('A verified-dependencies route probe must be kernel_verified');
  }
  const routeFingerprint = normalizeMathRouteFingerprint(input.routeFingerprint);
  const routeBrief = input.routeBrief;
  if (!routeBrief || typeof routeBrief !== 'object') {
    throw new TypeError('Mathematics route probe receipt routeBrief is required');
  }
  if (normalizeMathRouteFingerprint(routeBrief.routeFingerprint) !== routeFingerprint) {
    throw new TypeError('Mathematics route probe receipt routeBrief must match routeFingerprint');
  }
  const evidenceRefs = textList(input.evidenceRefs, 'routeProbeReceipt.evidenceRefs');
  if (['supported', 'kernel_verified', 'refuted'].includes(input.outcome) && evidenceRefs.length === 0) {
    throw new TypeError('Mathematics route probe receipt decisive outcomes require evidenceRefs');
  }
  if (!Number.isFinite(input.checkedAt) || input.checkedAt <= 0) {
    throw new TypeError('Mathematics route probe receipt checkedAt must be a positive timestamp');
  }
  const runtimeBinding = input.runtimeBinding;
  if (runtimeBinding && (!Number.isFinite(runtimeBinding.durationMs) || runtimeBinding.durationMs < 0)) {
    throw new TypeError('Mathematics route probe runtimeBinding.durationMs must be nonnegative');
  }
  if (
    runtimeBinding?.sandboxBackend !== undefined &&
    !['unshare', 'bwrap', 'docker', 'podman'].includes(runtimeBinding.sandboxBackend)
  ) {
    throw new TypeError('Mathematics route probe runtimeBinding.sandboxBackend is invalid');
  }
  const normalized = Object.freeze({
    receiptId: requiredText(input.receiptId, 'routeProbeReceipt.receiptId'),
    statementHash: requiredHash(input.statementHash, 'routeProbeReceipt.statementHash'),
    routeFingerprint,
    routeBrief: Object.freeze({
      routeFingerprint,
      structuralCommitment: requiredText(
        routeBrief.structuralCommitment,
        'routeProbeReceipt.routeBrief.structuralCommitment'
      ),
      decisiveLemma: requiredText(routeBrief.decisiveLemma, 'routeProbeReceipt.routeBrief.decisiveLemma'),
      decisiveTest: requiredText(routeBrief.decisiveTest, 'routeProbeReceipt.routeBrief.decisiveTest'),
      falsificationSignal: requiredText(
        routeBrief.falsificationSignal,
        'routeProbeReceipt.routeBrief.falsificationSignal'
      ),
      expectedInformationGain: boundedRating(
        routeBrief.expectedInformationGain,
        'routeProbeReceipt.routeBrief.expectedInformationGain'
      ),
      estimatedCost: boundedRating(routeBrief.estimatedCost, 'routeProbeReceipt.routeBrief.estimatedCost'),
      formalizationRisk: boundedRating(routeBrief.formalizationRisk, 'routeProbeReceipt.routeBrief.formalizationRisk'),
    }),
    proposerSessionId: requiredText(input.proposerSessionId, 'routeProbeReceipt.proposerSessionId'),
    assessorSessionId: requiredText(input.assessorSessionId, 'routeProbeReceipt.assessorSessionId'),
    outcome: input.outcome,
    ...(input.verificationMode ? { verificationMode: input.verificationMode } : {}),
    probeSummary: boundedRequiredText(input.probeSummary, 'routeProbeReceipt.probeSummary', 4000),
    evidenceRefs,
    checkedAt: input.checkedAt,
    proposalDeliveryId: requiredText(input.proposalDeliveryId, 'routeProbeReceipt.proposalDeliveryId'),
    assessmentDeliveryId: requiredText(input.assessmentDeliveryId, 'routeProbeReceipt.assessmentDeliveryId'),
    ...(runtimeBinding
      ? {
          runtimeBinding: Object.freeze({
            targetCommit: requiredGitOid(runtimeBinding.targetCommit, 'routeProbeReceipt.runtimeBinding.targetCommit'),
            routeStructureHash: requiredHash(
              runtimeBinding.routeStructureHash,
              'routeProbeReceipt.runtimeBinding.routeStructureHash'
            ),
            sourceHash: requiredHash(runtimeBinding.sourceHash, 'routeProbeReceipt.runtimeBinding.sourceHash'),
            harnessHash: requiredHash(runtimeBinding.harnessHash, 'routeProbeReceipt.runtimeBinding.harnessHash'),
            environmentFingerprint: requiredHash(
              runtimeBinding.environmentFingerprint,
              'routeProbeReceipt.runtimeBinding.environmentFingerprint'
            ),
            proofStateFingerprint: requiredHash(
              runtimeBinding.proofStateFingerprint,
              'routeProbeReceipt.runtimeBinding.proofStateFingerprint'
            ),
            durationMs: runtimeBinding.durationMs,
            ...(runtimeBinding.sandboxBackend ? { sandboxBackend: runtimeBinding.sandboxBackend } : {}),
          }),
        }
      : {}),
    ...(input.attestation
      ? { attestation: normalizeMathReceiptAttestation(input.attestation, 'routeProbeReceipt.attestation') }
      : {}),
  });
  if (normalized.proposerSessionId === normalized.assessorSessionId) {
    throw new TypeError('Mathematics route probe receipt must have independent proposer and assessor sessions');
  }
  return normalized;
}

/** Kernel receipt for one independently formalized route-DAG node. */
export type MathNodeProofReceipt = Readonly<{
  receiptId: string;
  targetCommit: string;
  statementHash: string;
  /** Runtime-bound hash of the exact canonical Lean proposition. */
  leanStatementHash?: string;
  routeFingerprint: string;
  planNodeId: string;
  status: 'kernel_verified';
  verifier: 'lean-kernel';
  theoremName: string;
  proofHash: string;
  theoremDeclarationHash: string;
  sourceDeclarationHash?: string;
  goalsRemaining: 0;
  sorryCount: 0;
  admitCount: 0;
  axioms: readonly string[];
  checkedAt: number;
}>;

/** Kernel receipt for a helper introduced while expanding a larger route milestone. */
export type MathHelperReceipt = Readonly<{
  receiptId: string;
  targetCommit: string;
  statementHash: string;
  routeFingerprint: string;
  helperPlanNodeId: string;
  parentPlanNodeId: string;
  status: 'kernel_verified';
  verifier: 'lean-kernel';
  declarationKind: 'theorem' | 'definition';
  declarationName: string;
  declarationType: string;
  proofHash: string;
  declarationHash: string;
  sourceDeclarationHash?: string;
  sourceFile: string;
  importModules: readonly string[];
  sourceProvenance: readonly MathSourceProvenance[];
  goalsRemaining: 0;
  sorryCount: 0;
  admitCount: 0;
  axioms: readonly string[];
  checkedAt: number;
}>;

export type MathWorkflowPreflightIssue = Readonly<{
  code:
    | 'missing_contract'
    | 'missing_fast_check'
    | 'inconclusive_fast_check'
    | 'missing_alignment'
    | 'non_exact_alignment'
    | 'missing_route'
    | 'missing_plan_node'
    | 'missing_local_receipt';
  message: string;
}>;

export type MathWorkflowPreflight = Readonly<{
  ok: boolean;
  stage: MathProofStage;
  issues: readonly MathWorkflowPreflightIssue[];
}>;

/**
 * Humanize-inspired preflight for mathematical Worker waves.
 *
 * It is deliberately a pure contract check: it does not create a Goal,
 * dispatch a Worker, or mutate the portfolio. Existing validators remain the
 * authority for detailed field-level checks; this helper provides one compact,
 * reusable readiness decision for routing and tests.
 */
export function evaluateMathWorkflowPreflight(
  input: Readonly<{
    stage: MathProofStage;
    fastCheck?: MathFastCheck;
    problemContract?: MathProblemContract;
    researchContract?: MathResearchProblemContract;
    alignmentCheck?: MathAlignmentCheck;
    directAttempt?: boolean;
    routeSelection?: MathRouteSelection;
    activePlanNodeId?: string;
    localGateReceipt?: MathLocalGateReceipt;
  }>
): MathWorkflowPreflight {
  const issues: MathWorkflowPreflightIssue[] = [];
  const explorationStage = input.stage === 'diversify' || input.stage === 'replan';
  const proofStage = input.stage === 'formalize' || input.stage === 'review';

  if (explorationStage && !input.researchContract && !input.problemContract) {
    issues.push({
      code: 'missing_contract',
      message: 'Mathematics exploration preflight requires a researchContract or problemContract',
    });
  }
  if (proofStage && !input.problemContract) {
    issues.push({
      code: 'missing_contract',
      message: 'Mathematics proof and review preflight requires an immutable problemContract',
    });
  }
  if (proofStage && !input.fastCheck) {
    issues.push({
      code: 'missing_fast_check',
      message: 'Mathematics proof and review preflight requires a completed FAST_CHECK decision',
    });
  } else if (
    proofStage &&
    input.fastCheck?.outcome === 'inconclusive' &&
    !input.directAttempt &&
    !input.routeSelection
  ) {
    issues.push({
      code: 'inconclusive_fast_check',
      message:
        'Mathematics proof and review preflight requires an explicit directAttempt or selected route after an inconclusive FAST_CHECK',
    });
  }
  if (proofStage && !input.alignmentCheck) {
    issues.push({
      code: 'missing_alignment',
      message: 'Mathematics proof and review preflight requires an alignmentCheck',
    });
  } else if (proofStage && input.alignmentCheck?.verdict !== 'exact') {
    issues.push({
      code: 'non_exact_alignment',
      message: 'Mathematics proof and review preflight is blocked by non-exact alignment',
    });
  }
  if (proofStage && !input.directAttempt && !input.routeSelection) {
    issues.push({
      code: 'missing_route',
      message: 'Mathematics proof and review preflight requires a frozen routeSelection or directAttempt',
    });
  }
  if (input.stage === 'formalize' && !input.activePlanNodeId) {
    issues.push({
      code: 'missing_plan_node',
      message: 'Mathematics FORMALIZE preflight requires one activePlanNodeId',
    });
  }
  if (input.stage === 'review' && !input.localGateReceipt) {
    issues.push({
      code: 'missing_local_receipt',
      message: 'Mathematics REVIEW preflight requires a frozen LOCAL_GATE receipt',
    });
  }
  return Object.freeze({
    ok: issues.length === 0,
    stage: input.stage,
    issues: Object.freeze(issues),
  });
}

/** Official-command receipt produced by OFFICIAL_GATE for the unchanged frozen candidate. */
export type MathOfficialGateReceipt = Readonly<{
  receiptId: string;
  targetCommit: string;
  statementHash: string;
  /** Omitted only by legacy receipts, where `statement` is implied. */
  claim?: 'statement' | 'negation';
  routeFingerprint: string;
  localGateReceiptId: string;
  theoremName: string;
  proofHash: string;
  theoremDeclarationHash: string;
  /** Runtime-derived source theorem header identity mirrored from LOCAL_GATE. */
  sourceDeclarationHash?: string;
  status: 'official_verified';
  verifier: 'official-comparator';
  command: string;
  exitCode: 0;
  timedOut: false;
  stdoutSha256: string;
  stderrSha256: string;
  durationMs: number;
  checkedAt: number;
  /** Identity of the committed official manifest used by the comparator. */
  problemId?: string;
  officialManifestPath?: string;
  officialManifestId?: string;
  officialManifestHash?: string;
  leanStatementHash?: string;
  officialRepositoryUrl: string;
  officialBaselineCommit: string;
  benchmarkAdapterId: string;
  benchmarkAdapterVersion: string;
  attestation: MathReceiptAttestation;
}>;

export const MATH_CANDIDATE_REVIEW_VERDICTS = ['sound', 'gap', 'wrong'] as const;
export type MathCandidateReviewVerdict = (typeof MATH_CANDIDATE_REVIEW_VERDICTS)[number];

export type MathCandidateReviewSource = Readonly<{
  teamId: string;
  slotId: string;
  assignmentId: string;
  deliveryId: string;
  /** Runtime roster lane that authorized the signed review. */
  laneId?: string;
}>;

/**
 * Machine-readable severity for independent review findings.
 *
 * This borrows Humanize's useful property that review output can drive the
 * next action without parsing prose, while keeping mathematics-specific
 * verdicts and kernel gates authoritative.
 */
export const MATH_REVIEW_FINDING_SEVERITIES = ['blocker', 'major', 'minor', 'note'] as const;
export type MathReviewFindingSeverity = (typeof MATH_REVIEW_FINDING_SEVERITIES)[number];

export const MATH_REVIEW_FINDING_KINDS = [
  'statement_mismatch',
  'missing_assumption',
  'quantifier_error',
  'domain_error',
  'proof_gap',
  'stale_commit',
  'evidence_scope',
  'counterexample_gap',
  'axiom_violation',
  'other',
] as const;
export type MathReviewFindingKind = (typeof MATH_REVIEW_FINDING_KINDS)[number];

/** A concise, evidence-bound finding that can route the next repair. */
export type MathReviewFinding = Readonly<{
  severity: MathReviewFindingSeverity;
  kind: MathReviewFindingKind;
  message: string;
  repairTarget?: string;
  evidenceRefs: readonly string[];
}>;

/** A review is tied to a frozen commit and an independent reviewer session. */
export type MathCandidateReview = Readonly<{
  verdict: MathCandidateReviewVerdict;
  firstFault?: string;
  repairTarget?: string;
  problemId: string;
  targetCommit: string;
  statementHash: string;
  reviewerSessionId: string;
  localGateReceiptId?: string;
  /** Optional diagnostic replay; terminal execution remains the official comparator's responsibility. */
  replayReceiptId?: string;
  replayTheoremName?: string;
  replayProofHash?: string;
  replayTheoremDeclarationHash?: string;
  replaySourceDeclarationHash?: string;
  evidenceRefs: readonly string[];
  /** Optional structured findings; omitted for legacy reviews. */
  findings?: readonly MathReviewFinding[];
  /** Added and signed by research_team(deliver); never trusted from Worker input. */
  source?: MathCandidateReviewSource;
  attestation?: MathReceiptAttestation;
}>;

export type MathReviewGateStatus = 'passed' | 'changes_requested' | 'refuted' | 'inconclusive';

export type MathReviewGate = Readonly<{
  status: MathReviewGateStatus;
  canAdvance: boolean;
  problemId: string;
  targetCommit: string;
  statementHash: string;
  reviewerCount: number;
  reviewerSessionIds: readonly string[];
  localGateReceiptId?: string;
  firstFaults: readonly string[];
  repairTargets: readonly string[];
  findingSeverities: Readonly<Record<MathReviewFindingSeverity, number>>;
  blockingFindingCount: number;
}>;

/**
 * Runtime-owned continuation for a fresh semantic review.
 *
 * The reviewer only judges the frozen candidate. The Lead still owns the
 * subsequent proof/evaluator transition, so this is deliberately a small
 * control value rather than a terminal status.
 */
export const MATH_REVIEW_ACTIONS = ['advance', 'repair', 'reject'] as const;
export type MathReviewAction = (typeof MATH_REVIEW_ACTIONS)[number];

export function mathCandidateReviewAction(review: Pick<MathCandidateReview, 'verdict'>): MathReviewAction {
  switch (review.verdict) {
    case 'sound':
      return 'advance';
    case 'gap':
      return 'repair';
    case 'wrong':
      return 'reject';
  }
}

export const MATH_FAILURE_CATEGORIES = [
  'none',
  'wrong_statement',
  'counterexample',
  'lean_error',
  'stalled',
  'regression',
  'infra',
  'duplicate_route',
  'review_gap',
  'toolchain',
  'wrong_problem_id',
  'stale_benchmark_commit',
  'statement_revision_mismatch',
  'trusted_file_changed',
  'submission_namespace_mismatch',
  'missing_hole',
  'import_or_olean_mismatch',
  'toolchain_unavailable',
  'comparator_failure',
  'landrun_failure',
  'nanoda_failure',
  'actual_proof_failure',
] as const;
export type MathFailureCategory = (typeof MATH_FAILURE_CATEGORIES)[number];

/** Minimal write-ahead state needed to resume without repeating a failed route. */
export type MathFailureLedger = Readonly<{
  stage: MathProofStage;
  statementHash: string;
  activeRoute: string;
  triedRoutes: readonly string[];
  /** Complete durable structural route history; worker projections may truncate it. */
  triedRouteStructureSignatures?: readonly string[];
  /** Local repair target inside the active route-level lemma DAG. */
  activePlanNodeId?: string;
  /** Exact Lean state at the solver-episode boundary. */
  proofStateFingerprint?: string;
  /** Full proof frontier identity, including the first diagnostic and node. */
  progressFingerprint?: string;
  /** Kernel-verified nodes retained when a downstream node fails. */
  verifiedPlanNodeIds?: readonly string[];
  /** Maximal compatible verified prefix retained for the next repair attempt. */
  semiProofCheckpoint?: MathSemiProofCheckpoint;
  firstLeanError?: string;
  latestReceipt?: string;
  nextSingleObjective: string;
  failureCategory: MathFailureCategory;
  doNotRepeatRefs: readonly string[];
}>;

export type MathVerifiedLemma = Readonly<{
  planNodeId: string;
  theoremName: string;
  theoremStatement: string;
  sourceFile: string;
  proofHash: string;
  importModules: readonly string[];
  evidenceRefs: readonly string[];
}>;

/** Kernel-grounded partial proof retained after the first incompatible node. */
export type MathSemiProofCheckpoint = Readonly<{
  routeFingerprint: string;
  targetCommit: string;
  verifiedLemmas: readonly MathVerifiedLemma[];
  firstIncompatibleNodeId: string;
  repairFrontierNodeIds: readonly string[];
  discardedNodeIds: readonly string[];
  resumeObjective: string;
  checkedAt: number;
}>;

export type MathRecoveryCheckpoint = Readonly<{
  checkpointId: string;
  targetCommit: string;
  updatedAt: number;
  ledger: MathFailureLedger;
  /** Optional P0 execution state; omitted by legacy checkpoints. */
  proofPlan?: MathProofPlan;
  proofState?: MathProofState;
}>;

export const MATH_ROUTE_DISPOSITIONS = ['advance', 'reject', 'blocked', 'duplicate'] as const;
export type MathRouteDisposition = (typeof MATH_ROUTE_DISPOSITIONS)[number];

export const MATH_INFRA_STATUSES = [
  'ready',
  'api_error',
  'proxy_error',
  'rate_limited',
  'tool_unavailable',
  'runtime_error',
] as const;
export type MathInfraStatus = (typeof MATH_INFRA_STATUSES)[number];

export const MATH_EVIDENCE_DELTA_KINDS = [
  'kernel_declaration',
  'helper_declaration',
  'mathlib_declaration',
  'plan_expansion',
  'upstream_source',
  'counterexample_probe',
  'route_refutation',
  ...MATH_RESEARCH_FINDING_KINDS,
] as const;
export type MathEvidenceDeltaKind = (typeof MATH_EVIDENCE_DELTA_KINDS)[number];

export type MathEvidenceDelta = Readonly<{
  kind: MathEvidenceDeltaKind;
  ref: string;
  summary: string;
}>;

export const MATH_WHOLE_PROOF_PROBE_OUTCOMES = ['lean_failed', 'kernel_verified'] as const;
export type MathWholeProofProbeOutcome = (typeof MATH_WHOLE_PROOF_PROBE_OUTCOMES)[number];

export const MATH_LEAN_FAILURE_KINDS = [
  'unknown_identifier',
  'type_mismatch',
  'unsolved_goals',
  'tactic_failed',
  'instance_synthesis_failed',
  'declaration_rejected',
  'termination_failed',
  'timeout_or_resource',
  'unknown',
] as const;
export type MathLeanFailureKind = (typeof MATH_LEAN_FAILURE_KINDS)[number];

/** One runtime-selected tactic rung. The Worker may explain a choice, but the
 * runtime owns the order and budget so retries cannot silently repeat blind
 * automation. */
export type MathExecutionTacticStep = Readonly<{
  tactic: string;
  budgetMs: number;
  when: string;
}>;

export const MATH_EXECUTION_MODEL_STATUSES = ['selected', 'fallback', 'unavailable'] as const;
export type MathExecutionModelStatus = (typeof MATH_EXECUTION_MODEL_STATUSES)[number];

/** Receipt for the model slot actually selected for an assignment. */
export type MathExecutionModelReceipt = Readonly<{
  status: MathExecutionModelStatus;
  requested?: string;
  selected?: string;
  reason?: string;
}>;

/** Durable route policy carried from Lean-Eval routing into each assignment. */
export type MathExecutionPolicy = Readonly<{
  modelPriority: readonly string[];
  tacticLadder: readonly MathExecutionTacticStep[];
  premiseQueries: readonly string[];
  tacticIndex: number;
  premiseQueryIndex: number;
  attemptedModels: readonly string[];
  attemptedTactics: readonly string[];
  attemptedPremiseQueries: readonly string[];
  lastProofStateFingerprint?: string;
  modelReceipt?: MathExecutionModelReceipt;
}>;

export function normalizeMathExecutionPolicy(input: MathExecutionPolicy): MathExecutionPolicy {
  if (!input || typeof input !== 'object') throw new TypeError('Mathematics executionPolicy must be an object');
  const normalizeList = (values: readonly string[], field: string, maximum: number): readonly string[] => {
    if (!Array.isArray(values) || values.length > maximum) {
      throw new TypeError(`Mathematics executionPolicy.${field} must be an array of at most ${maximum} items`);
    }
    const normalized = values.map((value, index) => {
      if (typeof value !== 'string' || !value.trim()) {
        throw new TypeError(`Mathematics executionPolicy.${field}[${index}] is required`);
      }
      return value.trim();
    });
    if (new Set(normalized).size !== normalized.length) {
      throw new TypeError(`Mathematics executionPolicy.${field} must be unique`);
    }
    return Object.freeze(normalized);
  };
  const modelPriority = normalizeList(input.modelPriority, 'modelPriority', 32);
  const premiseQueries = normalizeList(input.premiseQueries, 'premiseQueries', 32);
  if (!Array.isArray(input.tacticLadder) || input.tacticLadder.length > 32) {
    throw new TypeError('Mathematics executionPolicy.tacticLadder must be an array of at most 32 items');
  }
  const tacticLadder = Object.freeze(
    input.tacticLadder.map((step, index) => {
      if (!step || typeof step !== 'object') {
        throw new TypeError(`Mathematics executionPolicy.tacticLadder[${index}] must be an object`);
      }
      const budgetMs = step.budgetMs;
      if (!Number.isSafeInteger(budgetMs) || budgetMs < 1 || budgetMs > 300_000) {
        throw new TypeError(`Mathematics executionPolicy.tacticLadder[${index}].budgetMs is invalid`);
      }
      return Object.freeze({
        tactic: boundedRequiredText(step.tactic, `executionPolicy.tacticLadder[${index}].tactic`, 128),
        budgetMs,
        when: boundedRequiredText(step.when, `executionPolicy.tacticLadder[${index}].when`, 512),
      });
    })
  );
  const index = (value: unknown, field: string, length: number): number => {
    if (!Number.isSafeInteger(value) || Number(value) < 0 || Number(value) > length) {
      throw new TypeError(`Mathematics executionPolicy.${field} is outside its policy range`);
    }
    return Number(value);
  };
  const tacticIndex = index(input.tacticIndex ?? 0, 'tacticIndex', tacticLadder.length);
  const premiseQueryIndex = index(input.premiseQueryIndex ?? 0, 'premiseQueryIndex', premiseQueries.length);
  const attemptedTactics = normalizeList(input.attemptedTactics ?? [], 'attemptedTactics', 64);
  const attemptedPremiseQueries = normalizeList(input.attemptedPremiseQueries ?? [], 'attemptedPremiseQueries', 64);
  const attemptedModels = normalizeList(input.attemptedModels ?? [], 'attemptedModels', 64);
  const modelReceipt = input.modelReceipt
    ? (() => {
        if (!MATH_EXECUTION_MODEL_STATUSES.includes(input.modelReceipt!.status)) {
          throw new TypeError('Mathematics executionPolicy.modelReceipt.status is invalid');
        }
        return Object.freeze({
          status: input.modelReceipt!.status,
          ...(input.modelReceipt!.requested
            ? {
                requested: boundedRequiredText(
                  input.modelReceipt!.requested,
                  'executionPolicy.modelReceipt.requested',
                  128
                ),
              }
            : {}),
          ...(input.modelReceipt!.selected
            ? {
                selected: boundedRequiredText(
                  input.modelReceipt!.selected,
                  'executionPolicy.modelReceipt.selected',
                  128
                ),
              }
            : {}),
          ...(input.modelReceipt!.reason
            ? { reason: boundedRequiredText(input.modelReceipt!.reason, 'executionPolicy.modelReceipt.reason', 512) }
            : {}),
        });
      })()
    : undefined;
  const lastProofStateFingerprint = input.lastProofStateFingerprint
    ? requiredHash(input.lastProofStateFingerprint, 'executionPolicy.lastProofStateFingerprint')
    : undefined;
  return Object.freeze({
    modelPriority,
    tacticLadder,
    premiseQueries,
    tacticIndex,
    premiseQueryIndex,
    attemptedModels,
    attemptedTactics,
    attemptedPremiseQueries,
    ...(lastProofStateFingerprint ? { lastProofStateFingerprint } : {}),
    ...(modelReceipt ? { modelReceipt } : {}),
  });
}

/** One bounded whole-proof execution used to localize the next DAG repair. */
export type MathWholeProofProbe = Readonly<{
  candidateProofHash: string;
  sourceFile: string;
  outcome: MathWholeProofProbeOutcome;
  firstIncompatibleNodeId?: string;
  firstLeanError?: string;
  errorStartOffset?: number;
  errorEndOffset?: number;
  repairObjective?: string;
  /** Deterministically derived from firstLeanError; Worker-provided values are checked, not trusted. */
  failureKind?: MathLeanFailureKind;
  evidenceRefs: readonly string[];
}>;

/** Runtime-validated in-place expansion of one actionable milestone. */
export type MathPlanExpansion = Readonly<{
  expandedNodeId: string;
  addedNodes: readonly MathPlanNode[];
  reason: string;
  evidenceRefs: readonly string[];
}>;

/**
 * Runtime-owned source progress for a committed Lean artifact.
 *
 * This is deliberately weaker than a kernel receipt: it proves that one or
 * more declaration bodies changed between the assignment base and candidate,
 * but says nothing about whether the resulting file compiles or solves the
 * theorem.  The runtime computes and validates every field; Workers must not
 * self-report it.
 */
export type MathSourceProgress = Readonly<{
  artifactPath: string;
  changedDeclarationNames: readonly string[];
  baseSourceHash: string;
  candidateSourceHash: string;
}>;

export type MathProgressDelta = Readonly<{
  statementHash: string;
  routeFingerprint: string;
  /** Runtime-owned tactic/query/model cursor after this proof episode. */
  executionPolicy?: MathExecutionPolicy;
  /** Deterministic identity of the proof state at this episode boundary. */
  progressFingerprint?: string;
  /** Runtime-derived failure category used to select a recovery route. */
  failureCategory?: MathFailureCategory;
  activePlanNodeId?: string;
  planBefore?: MathPlanSnapshot;
  planAfter?: MathPlanSnapshot;
  planExpansion?: MathPlanExpansion;
  verifiedPlanNodeIdsAdded?: readonly string[];
  /** Runtime-owned declaration-level source change; never a kernel claim. */
  sourceProgress?: MathSourceProgress;
  checkedDeclarationsAdded: number;
  openGoalFingerprintBefore?: string;
  openGoalFingerprintAfter?: string;
  openGoalCountBefore: number;
  openGoalCountAfter: number;
  /** Bounded live Lean goal retained only when the next repair may need premise retrieval. */
  openGoalAfter?: string;
  firstLeanErrorBefore?: string;
  firstLeanErrorAfter?: string;
  /** Monotone byte/character offset in the same target file, when available. */
  firstLeanErrorOffsetBefore?: number;
  firstLeanErrorOffsetAfter?: number;
  wholeProofProbe?: MathWholeProofProbe;
  evidenceDelta: readonly MathEvidenceDelta[];
  routeDisposition: MathRouteDisposition;
  /** Runtime-owned continuation emitted after an independent candidate review. */
  reviewAction?: MathReviewAction;
  nextSingleObjective: string;
  infraStatus: MathInfraStatus;
}>;

/** Full proof-plan state before or after one formalization assignment. */
export type MathPlanSnapshot = Readonly<{
  rootNodeId: string;
  planNodes: readonly MathPlanNode[];
  bottleneckNodeId?: string;
  openFrontierNodeIds: readonly string[];
}>;

export type MathProgressOutcome = 'advanced' | 'stalled' | 'regressed' | 'infra_failed';

/** Finer-grained progress semantics used by the runtime scheduler. */
export type MathProgressKind =
  | 'kernel_progress'
  | 'foundation_progress'
  | 'goal_progress'
  | 'route_information'
  | 'research_information'
  | 'library_discovery'
  | 'infra_progress'
  | 'none';

export const MATH_PROGRESS_KINDS = [
  'kernel_progress',
  'foundation_progress',
  'goal_progress',
  'route_information',
  'research_information',
  'library_discovery',
  'infra_progress',
  'none',
] as const satisfies readonly MathProgressKind[];

export const MATH_PROGRESS_DIRECTIVES = [
  'continue_node',
  'switch_node',
  'expand_node',
  'promote_helper',
  'port_upstream',
  're_decompose',
  'retry_infrastructure',
  'solver_complete',
] as const;
export type MathProgressDirective = (typeof MATH_PROGRESS_DIRECTIVES)[number];

export const MATH_COST_PRESSURES = ['low', 'meaningful', 'high'] as const;
export type MathCostPressure = (typeof MATH_COST_PRESSURES)[number];

/** Runtime-owned cost signals. Missing telemetry never becomes a Worker-reported fact. */
export type MathProgressCost = Readonly<{
  assignmentElapsedMs?: number;
  tokensUsed?: number;
  leanExecutionCount?: number;
}>;

/** Compact route history used by deterministic schedule replay. */
export type MathRoutePerformanceRecord = Readonly<{
  routeFingerprint: string;
  planNodeId: string;
  attempts: number;
  goalProgressCount: number;
  frontierProgressCount: number;
  scaffoldOnlyCount: number;
  lastFailureCategory?: string;
  bestProofStateFingerprint?: string;
  researchContextFingerprint?: string;
  /** Runtime-observed verified gain and work, used only for route scheduling. */
  verifiedMarginalGain?: number;
  totalLeanCalls?: number;
  totalWallClockMs?: number;
}>;

/** Runtime evidence binding used when classifying untrusted Worker deltas. */
export type MathProgressEvidenceContext = Readonly<{
  /** Whether declaration/node kernel claims are backed by a stored receipt. */
  kernelReceiptBound?: boolean;
  /** Scheduler-only guard: a DAG expansion is not progress without a kernel receipt. */
  requireKernelReceiptForPlanExpansion?: boolean;
  /** Previous runtime-only scaffold streak, restored from the durable checkpoint. */
  previousScaffoldOnlyStreak?: number;
}>;

export type MathProgressState = Readonly<{
  outcome: MathProgressOutcome;
  consecutiveStalls: number;
  directive: MathProgressDirective;
  costPressure: MathCostPressure;
  nextStage: MathProofStage;
  /** Fine-grained semantic kind retained for scheduler decisions. */
  progressKind?: MathProgressKind;
  /** Consecutive helper/plan-only results that did not move the main goal. */
  scaffoldOnlyStreak?: number;
}>;

/** Durable checkpoint written after every integrated Mathematics result. */
export type MathDurableProgressCheckpoint = Readonly<{
  statementHash: string;
  routeFingerprint: string;
  executionPolicy?: MathExecutionPolicy;
  /** Stable identity used to detect a repeated episode after a Lead restart. */
  progressFingerprint?: string;
  failureCategory?: MathFailureCategory;
  outcome: MathProgressOutcome;
  consecutiveStalls: number;
  directive: MathProgressDirective;
  nextStage: MathProofStage;
  progressKind?: MathProgressKind;
  scaffoldOnlyStreak?: number;
  routePerformance?: readonly MathRoutePerformanceRecord[];
  /** Bounded exact-attempt identities recovered across Workers and Lead restarts. */
  routeAttemptDigests?: readonly string[];
  activePlanNodeId?: string;
  proofStateFingerprint?: string;
  updatedAt: number;
}>;

export function normalizeMathDurableProgressCheckpoint(
  input: MathDurableProgressCheckpoint
): MathDurableProgressCheckpoint {
  if (!['advanced', 'stalled', 'regressed', 'infra_failed'].includes(input.outcome)) {
    throw new TypeError('Mathematics durable progress outcome is invalid');
  }
  if (!MATH_PROGRESS_DIRECTIVES.includes(input.directive)) {
    throw new TypeError('Mathematics durable progress directive is invalid');
  }
  if (!MATH_PROOF_STAGES.includes(input.nextStage)) {
    throw new TypeError('Mathematics durable progress nextStage is invalid');
  }
  if (!Number.isSafeInteger(input.consecutiveStalls) || input.consecutiveStalls < 0) {
    throw new TypeError('Mathematics durable progress consecutiveStalls must be a nonnegative integer');
  }
  if (input.progressKind !== undefined && !MATH_PROGRESS_KINDS.includes(input.progressKind)) {
    throw new TypeError('Mathematics durable progress progressKind is invalid');
  }
  if (
    input.scaffoldOnlyStreak !== undefined &&
    (!Number.isSafeInteger(input.scaffoldOnlyStreak) || input.scaffoldOnlyStreak < 0)
  ) {
    throw new TypeError('Mathematics durable progress scaffoldOnlyStreak must be a nonnegative integer');
  }
  if (input.routePerformance !== undefined) {
    if (!Array.isArray(input.routePerformance) || input.routePerformance.length > 512) {
      throw new TypeError('Mathematics durable progress routePerformance must contain at most 512 records');
    }
    for (const [index, record] of input.routePerformance.entries()) {
      if (
        !record ||
        !record.routeFingerprint.trim() ||
        !record.planNodeId.trim() ||
        (record.researchContextFingerprint !== undefined &&
          !/^[a-f0-9]{64}$/u.test(record.researchContextFingerprint)) ||
        (record.verifiedMarginalGain !== undefined &&
          (!Number.isFinite(record.verifiedMarginalGain) || record.verifiedMarginalGain < 0)) ||
        (record.totalLeanCalls !== undefined &&
          (!Number.isSafeInteger(record.totalLeanCalls) || record.totalLeanCalls < 0)) ||
        (record.totalWallClockMs !== undefined &&
          (!Number.isFinite(record.totalWallClockMs) || record.totalWallClockMs < 0)) ||
        ![record.attempts, record.goalProgressCount, record.frontierProgressCount, record.scaffoldOnlyCount].every(
          (value) => Number.isSafeInteger(value) && value >= 0
        )
      ) {
        throw new TypeError(`Mathematics durable progress routePerformance[${index}] is invalid`);
      }
    }
  }
  if (
    input.routeAttemptDigests !== undefined &&
    (!Array.isArray(input.routeAttemptDigests) ||
      input.routeAttemptDigests.length > 512 ||
      new Set(input.routeAttemptDigests).size !== input.routeAttemptDigests.length ||
      input.routeAttemptDigests.some((digest) => !/^[a-f0-9]{64}$/u.test(digest)))
  ) {
    throw new TypeError(
      'Mathematics durable progress routeAttemptDigests must contain at most 512 unique SHA-256 values'
    );
  }
  if (!Number.isFinite(input.updatedAt) || input.updatedAt <= 0) {
    throw new TypeError('Mathematics durable progress updatedAt must be positive');
  }
  return Object.freeze({
    statementHash: requiredHash(input.statementHash, 'mathProgress.statementHash'),
    routeFingerprint: normalizeMathRouteFingerprint(input.routeFingerprint),
    ...(input.executionPolicy ? { executionPolicy: normalizeMathExecutionPolicy(input.executionPolicy) } : {}),
    ...(input.progressFingerprint
      ? { progressFingerprint: requiredHash(input.progressFingerprint, 'mathProgress.progressFingerprint') }
      : {}),
    ...(input.failureCategory
      ? MATH_FAILURE_CATEGORIES.includes(input.failureCategory)
        ? { failureCategory: input.failureCategory }
        : (() => {
            throw new TypeError('Mathematics progress failureCategory is invalid');
          })()
      : {}),
    outcome: input.outcome,
    consecutiveStalls: input.consecutiveStalls,
    directive: input.directive,
    nextStage: input.nextStage,
    ...(input.progressKind ? { progressKind: input.progressKind } : {}),
    ...(input.scaffoldOnlyStreak !== undefined ? { scaffoldOnlyStreak: input.scaffoldOnlyStreak } : {}),
    ...(input.routePerformance
      ? {
          routePerformance: Object.freeze(
            input.routePerformance.map((record) =>
              Object.freeze({
                ...record,
                ...(record.verifiedMarginalGain !== undefined
                  ? { verifiedMarginalGain: record.verifiedMarginalGain }
                  : {}),
                ...(record.totalLeanCalls !== undefined ? { totalLeanCalls: record.totalLeanCalls } : {}),
                ...(record.totalWallClockMs !== undefined ? { totalWallClockMs: record.totalWallClockMs } : {}),
              })
            )
          ),
        }
      : {}),
    ...(input.routeAttemptDigests ? { routeAttemptDigests: Object.freeze([...input.routeAttemptDigests]) } : {}),
    ...(input.activePlanNodeId
      ? { activePlanNodeId: normalizeMathPlanNodeId(input.activePlanNodeId, 'mathProgress.activePlanNodeId') }
      : {}),
    ...(input.proofStateFingerprint
      ? { proofStateFingerprint: requiredText(input.proofStateFingerprint, 'mathProgress.proofStateFingerprint') }
      : {}),
    updatedAt: input.updatedAt,
  });
}

export function normalizeMathProblemContract(input: MathProblemContract): MathProblemContract {
  const assumptions = textList(input.assumptions, 'problemContract.assumptions');
  const knownTraps = textList(input.knownTraps, 'problemContract.knownTraps');
  const acceptanceCriteria = requiredTextList(input.acceptanceCriteria, 'problemContract.acceptanceCriteria');
  const officialManifestId = input.officialManifestId?.trim();
  const officialManifestHash = input.officialManifestHash?.trim();
  const formalNegationStatement = optionalText(input.formalNegationStatement);
  const leanNegationHash = optionalText(input.leanNegationHash);
  if (Boolean(formalNegationStatement) !== Boolean(leanNegationHash)) {
    throw new TypeError('Mathematics problemContract formal negation statement and hash must be supplied together');
  }
  if (Boolean(officialManifestId) !== Boolean(officialManifestHash)) {
    throw new TypeError('Mathematics problemContract official manifest id and hash must be supplied together');
  }
  return Object.freeze({
    problemId: requiredText(input.problemId, 'problemContract.problemId'),
    informalStatement: requiredText(input.informalStatement, 'problemContract.informalStatement'),
    formalStatement: requiredText(input.formalStatement, 'problemContract.formalStatement'),
    ...(formalNegationStatement ? { formalNegationStatement } : {}),
    assumptions,
    statementHash: requiredHash(input.statementHash, 'problemContract.statementHash'),
    leanStatementHash: requiredHash(input.leanStatementHash, 'problemContract.leanStatementHash'),
    ...(leanNegationHash
      ? { leanNegationHash: requiredHash(leanNegationHash, 'problemContract.leanNegationHash') }
      : {}),
    knownTraps,
    acceptanceCriteria,
    officialVerificationCommand: requiredText(
      input.officialVerificationCommand,
      'problemContract.officialVerificationCommand'
    ),
    ...(officialManifestId ? { officialManifestId } : {}),
    ...(officialManifestHash
      ? { officialManifestHash: requiredHash(officialManifestHash, 'problemContract.officialManifestHash') }
      : {}),
  });
}

export function normalizeMathResearchProblemContract(input: MathResearchProblemContract): MathResearchProblemContract {
  const optionalList = (value: readonly string[] | undefined, field: string): readonly string[] | undefined =>
    value === undefined ? undefined : textList(value, field);
  const context = optionalText(input.context);
  const knownResults = optionalList(input.knownResults, 'researchContract.knownResults');
  const establishedClaims = optionalList(input.establishedClaims, 'researchContract.establishedClaims');
  const conjectures = optionalList(input.conjectures, 'researchContract.conjectures');
  const failedApproaches = optionalList(input.failedApproaches, 'researchContract.failedApproaches');
  const openObligations = optionalList(input.openObligations, 'researchContract.openObligations');
  const evidenceNotes = optionalList(input.evidenceNotes, 'researchContract.evidenceNotes');
  if (evidenceNotes && evidenceNotes.length > 8) {
    throw new TypeError('Mathematics researchContract.evidenceNotes must contain at most 8 entries');
  }
  evidenceNotes?.forEach((note, index) => boundedRequiredText(note, `researchContract.evidenceNotes[${index}]`, 800));
  if (input.insights !== undefined && (!Array.isArray(input.insights) || input.insights.length > 8)) {
    throw new TypeError('Mathematics researchContract.insights must contain at most 8 entries');
  }
  const insights = input.insights
    ? Object.freeze(
        input.insights.map((insight, index): MathResearchInsight => {
          const conditions = textList(insight.conditions, `researchContract.insights[${index}].conditions`);
          const evidenceRefs = textList(insight.evidenceRefs, `researchContract.insights[${index}].evidenceRefs`);
          if (conditions.length > 4 || evidenceRefs.length > 8) {
            throw new TypeError(`Mathematics researchContract.insights[${index}] exceeds its compact list bounds`);
          }
          const failure = optionalText(insight.failure);
          const repair = optionalText(insight.repair);
          return Object.freeze({
            claim: boundedRequiredText(insight.claim, `researchContract.insights[${index}].claim`, 800),
            conditions: Object.freeze(
              conditions.map((condition, conditionIndex) =>
                boundedRequiredText(condition, `researchContract.insights[${index}].conditions[${conditionIndex}]`, 500)
              )
            ),
            ...(failure
              ? { failure: boundedRequiredText(failure, `researchContract.insights[${index}].failure`, 800) }
              : {}),
            ...(repair
              ? { repair: boundedRequiredText(repair, `researchContract.insights[${index}].repair`, 800) }
              : {}),
            usableWhen: boundedRequiredText(insight.usableWhen, `researchContract.insights[${index}].usableWhen`, 800),
            evidenceRefs,
          });
        })
      )
    : undefined;
  if (
    input.probeSummary !== undefined &&
    (!Array.isArray(input.probeSummary) || input.probeSummary.length > MATH_RESEARCH_PROBE_KINDS.length)
  ) {
    throw new TypeError('Mathematics researchContract.probeSummary must contain at most one entry per probe method');
  }
  const probeSummary = input.probeSummary
    ? Object.freeze(
        input.probeSummary.map((entry, index): MathResearchProbeSummary => {
          if (!MATH_RESEARCH_PROBE_KINDS.includes(entry.probeKind)) {
            throw new TypeError(`researchContract.probeSummary[${index}].probeKind is invalid`);
          }
          if (!MATH_RESEARCH_PROBE_OUTCOMES.includes(entry.lastOutcome)) {
            throw new TypeError(`researchContract.probeSummary[${index}].lastOutcome is invalid`);
          }
          return Object.freeze({
            probeKind: entry.probeKind,
            ...(entry.bottleneck
              ? {
                  bottleneck: boundedRequiredText(
                    entry.bottleneck,
                    `researchContract.probeSummary[${index}].bottleneck`,
                    800
                  ),
                }
              : {}),
            ...(entry.bottleneckStats
              ? {
                  bottleneckStats: Object.freeze(
                    entry.bottleneckStats.map((bucket, bucketIndex) => {
                      const prefix = `researchContract.probeSummary[${index}].bottleneckStats[${bucketIndex}]`;
                      if (!bucket.bottleneck?.trim()) throw new TypeError(`${prefix}.bottleneck is required`);
                      if (!MATH_RESEARCH_PROBE_OUTCOMES.includes(bucket.lastOutcome))
                        throw new TypeError(`${prefix}.lastOutcome is invalid`);
                      return Object.freeze({
                        bottleneck: boundedRequiredText(bucket.bottleneck, `${prefix}.bottleneck`, 800),
                        attempts: nonnegativeInteger(bucket.attempts, `${prefix}.attempts`),
                        usefulChanges: nonnegativeInteger(bucket.usefulChanges, `${prefix}.usefulChanges`),
                        noChange: nonnegativeInteger(bucket.noChange, `${prefix}.noChange`),
                        lastOutcome: bucket.lastOutcome,
                      });
                    })
                  ),
                }
              : {}),
            attempts: nonnegativeInteger(entry.attempts, `researchContract.probeSummary[${index}].attempts`),
            usefulChanges: nonnegativeInteger(
              entry.usefulChanges,
              `researchContract.probeSummary[${index}].usefulChanges`
            ),
            noChange: nonnegativeInteger(entry.noChange, `researchContract.probeSummary[${index}].noChange`),
            lastOutcome: entry.lastOutcome,
          });
        })
      )
    : undefined;
  for (const [index, entry] of (probeSummary ?? []).entries()) {
    if (
      entry.bottleneckStats &&
      new Set(entry.bottleneckStats.map((bucket) => normalizeMathResearchStatement(bucket.bottleneck))).size !==
        entry.bottleneckStats.length
    )
      throw new TypeError(`researchContract.probeSummary[${index}].bottleneckStats bottlenecks must be unique`);
  }
  if (probeSummary && new Set(probeSummary.map((entry) => entry.probeKind)).size !== probeSummary.length) {
    throw new TypeError('Mathematics researchContract.probeSummary probeKind values must be unique');
  }
  const activeBottleneck = input.activeBottleneck
    ? boundedRequiredText(input.activeBottleneck, 'researchContract.activeBottleneck', 800)
    : undefined;
  const solutionSketchRef = input.solutionSketchRef
    ? boundedRequiredText(input.solutionSketchRef, 'researchContract.solutionSketchRef', 512)
    : undefined;
  const nextAction = optionalText(input.nextAction);
  return Object.freeze({
    problemId: requiredText(input.problemId, 'researchContract.problemId'),
    objective: requiredText(input.objective, 'researchContract.objective'),
    ...(context ? { context } : {}),
    ...(knownResults ? { knownResults } : {}),
    ...(establishedClaims ? { establishedClaims } : {}),
    ...(conjectures ? { conjectures } : {}),
    ...(failedApproaches ? { failedApproaches } : {}),
    ...(openObligations ? { openObligations } : {}),
    ...(evidenceNotes ? { evidenceNotes } : {}),
    ...(insights ? { insights } : {}),
    ...(probeSummary ? { probeSummary } : {}),
    ...(input.consumedEvidenceKeys
      ? {
          consumedEvidenceKeys: Object.freeze([
            ...new Set(
              input.consumedEvidenceKeys.map((key) => requiredText(key, 'researchContract.consumedEvidenceKeys'))
            ),
          ]),
        }
      : {}),
    ...(input.bottleneckDiagnosis
      ? {
          bottleneckDiagnosis: boundedRequiredText(
            input.bottleneckDiagnosis,
            'researchContract.bottleneckDiagnosis',
            800
          ),
        }
      : {}),
    ...(activeBottleneck ? { activeBottleneck } : {}),
    ...(solutionSketchRef ? { solutionSketchRef } : {}),
    ...(nextAction ? { nextAction } : {}),
  });
}

export function normalizeMathResearchFinding(input: MathResearchFinding): MathResearchFinding {
  const evidence = input.evidence?.map((entry) => {
    if (
      !entry ||
      !['hypothesis', 'observed', 'runtime_checked', 'kernel_verified'].includes(entry.grade) ||
      !['claim', 'bounded_observation', 'approach', 'bottleneck'].includes(entry.scope)
    ) {
      throw new TypeError('Mathematics researchFinding evidence grade or scope is invalid');
    }
    return Object.freeze({
      grade: entry.grade,
      scope: entry.scope,
      statement: boundedRequiredText(entry.statement, 'researchFinding.evidence.statement', 4000),
      reference: boundedRequiredText(entry.reference, 'researchFinding.evidence.reference', 1000),
    });
  });
  if (!MATH_RESEARCH_FINDING_KINDS.includes(input.kind)) {
    throw new TypeError('Mathematics researchFinding kind is invalid');
  }
  if (input.mainlineImpact && !MATH_RESEARCH_FINDING_IMPACTS.includes(input.mainlineImpact)) {
    throw new TypeError('Mathematics researchFinding mainlineImpact is invalid');
  }
  if (input.nextProbeKind && !MATH_RESEARCH_PROBE_KINDS.includes(input.nextProbeKind)) {
    throw new TypeError('Mathematics researchFinding nextProbeKind is invalid');
  }
  const mechanism = input.mechanism
    ? boundedRequiredText(input.mechanism, 'researchFinding.mechanism', 512)
    : undefined;
  let bottleneckUpdate: MathResearchBottleneckUpdate | undefined;
  if (input.bottleneckUpdate !== undefined) {
    const update = input.bottleneckUpdate;
    if (!update || typeof update !== 'object') {
      throw new TypeError('Mathematics researchFinding bottleneckUpdate must be an object');
    }
    if (!MATH_RESEARCH_BOTTLENECK_OUTCOMES.includes(update.outcome)) {
      throw new TypeError('Mathematics researchFinding bottleneckUpdate outcome is invalid');
    }
    if (update.category !== undefined && !MATH_FAILURE_CATEGORIES.includes(update.category)) {
      throw new TypeError('Mathematics researchFinding bottleneckUpdate category is invalid');
    }
    const target = boundedRequiredText(update.target, 'researchFinding.bottleneckUpdate.target', 800);
    const diagnosis = update.diagnosis
      ? boundedRequiredText(update.diagnosis, 'researchFinding.bottleneckUpdate.diagnosis', 1200)
      : undefined;
    const repair = update.repair
      ? boundedRequiredText(update.repair, 'researchFinding.bottleneckUpdate.repair', 1200)
      : undefined;
    if (update.category && update.category !== 'none' && (!diagnosis || !repair)) {
      throw new TypeError('Mathematics non-empty bottleneckUpdate category requires diagnosis and repair');
    }
    bottleneckUpdate = Object.freeze({
      target,
      outcome: update.outcome,
      ...(update.category ? { category: update.category } : {}),
      ...(diagnosis ? { diagnosis } : {}),
      ...(repair ? { repair } : {}),
    });
  }
  let helperRequest: MathResearchHelperRequest | undefined;
  if (input.helperRequest !== undefined) {
    const helper = input.helperRequest;
    if (!helper || typeof helper !== 'object') {
      throw new TypeError('Mathematics researchFinding helperRequest must be an object');
    }
    if (!MATH_RESEARCH_PROBE_KINDS.includes(helper.probeKind)) {
      throw new TypeError('Mathematics researchFinding helperRequest probeKind is invalid');
    }
    helperRequest = Object.freeze({
      bottleneck: boundedRequiredText(helper.bottleneck, 'researchFinding.helperRequest.bottleneck', 800),
      probeKind: helper.probeKind,
      objective: boundedRequiredText(helper.objective, 'researchFinding.helperRequest.objective', 1200),
    });
  }
  let problemFamilyProbe: MathProblemFamilyProbe | undefined;
  if (input.problemFamilyProbe !== undefined) {
    const probe = input.problemFamilyProbe;
    if (
      !probe ||
      typeof probe !== 'object' ||
      !Array.isArray(probe.instances) ||
      probe.instances.length < 1 ||
      probe.instances.length > 5
    ) {
      throw new TypeError('Mathematics researchFinding problemFamilyProbe requires 1 to 5 instances');
    }
    if (!MATH_PROBLEM_FAMILY_GENERALIZATION_OUTCOMES.includes(probe.generalization)) {
      throw new TypeError('Mathematics researchFinding problemFamilyProbe generalization is invalid');
    }
    const instances = probe.instances.map((instance, index) => {
      if (
        !instance ||
        typeof instance !== 'object' ||
        !MATH_PROBLEM_FAMILY_INSTANCE_OUTCOMES.includes(instance.outcome)
      ) {
        throw new TypeError(`Mathematics problemFamilyProbe.instances[${index}] outcome is invalid`);
      }
      const observation = instance.observation
        ? boundedRequiredText(instance.observation, `problemFamilyProbe.instances[${index}].observation`, 800)
        : undefined;
      return Object.freeze({
        input: boundedRequiredText(instance.input, `problemFamilyProbe.instances[${index}].input`, 800),
        outcome: instance.outcome,
        ...(observation ? { observation } : {}),
      });
    });
    const counterexampleCount = instances.filter((instance) => instance.outcome === 'counterexample').length;
    const sharedMechanism = probe.sharedMechanism
      ? boundedRequiredText(probe.sharedMechanism, 'researchFinding.problemFamilyProbe.sharedMechanism', 1000)
      : undefined;
    const firstCounterexample = probe.firstCounterexample
      ? boundedRequiredText(probe.firstCounterexample, 'researchFinding.problemFamilyProbe.firstCounterexample', 1200)
      : undefined;
    if (probe.generalization === 'supported' && !sharedMechanism) {
      throw new TypeError('A supported problemFamilyProbe requires sharedMechanism');
    }
    if ((probe.generalization === 'refuted' || firstCounterexample) && counterexampleCount === 0) {
      throw new TypeError('A refuted problemFamilyProbe requires a counterexample instance');
    }
    problemFamilyProbe = Object.freeze({
      instances: Object.freeze(instances),
      ...(sharedMechanism ? { sharedMechanism } : {}),
      ...(firstCounterexample ? { firstCounterexample } : {}),
      generalization: probe.generalization,
    });
  }
  const solutionSketchRef = input.solutionSketchRef
    ? boundedRequiredText(input.solutionSketchRef, 'researchFinding.solutionSketchRef', 512)
    : undefined;
  const evidenceRefs = textList(input.evidenceRefs, 'researchFinding.evidenceRefs');
  const establishedClaims = textList(input.establishedClaims, 'researchFinding.establishedClaims');
  const conjectureUpdates = textList(input.conjectureUpdates, 'researchFinding.conjectureUpdates');
  const eliminatedApproaches = textList(input.eliminatedApproaches, 'researchFinding.eliminatedApproaches');
  const openObligations = textList(input.openObligations, 'researchFinding.openObligations');
  if (problemFamilyProbe && evidenceRefs.length === 0) {
    throw new TypeError('Mathematics problemFamilyProbe requires evidenceRefs for its bounded instances');
  }
  if (input.mainlineImpact === 'mainline_advanced' && !establishedClaims.length && !eliminatedApproaches.length) {
    throw new TypeError(
      'Mathematics mainline_advanced researchFinding requires an established claim or eliminated approach'
    );
  }
  if (input.mainlineImpact === 'route_refuted' && (!evidenceRefs.length || !eliminatedApproaches.length)) {
    throw new TypeError(
      'Mathematics route_refuted researchFinding requires evidence and an eliminated active approach'
    );
  }
  return Object.freeze({
    kind: input.kind,
    ...(mechanism ? { mechanism } : {}),
    ...(input.mainlineImpact ? { mainlineImpact: input.mainlineImpact } : {}),
    ...(input.nextProbeKind ? { nextProbeKind: input.nextProbeKind } : {}),
    ...(bottleneckUpdate ? { bottleneckUpdate } : {}),
    ...(helperRequest ? { helperRequest } : {}),
    ...(problemFamilyProbe ? { problemFamilyProbe } : {}),
    ...(solutionSketchRef ? { solutionSketchRef } : {}),
    summary: boundedRequiredText(input.summary, 'researchFinding.summary', 4000),
    evidenceRefs,
    ...(evidence ? { evidence: Object.freeze(evidence) } : {}),
    establishedClaims,
    conjectureUpdates,
    eliminatedApproaches,
    openObligations,
    nextAction: boundedRequiredText(input.nextAction, 'researchFinding.nextAction', 2000),
  });
}

export function normalizeMathResearchStatement(value: string): string {
  return value.normalize('NFC').replace(/\s+/gu, ' ').trim();
}

export function isMathResearchEvidenceReference(reference: string): boolean {
  return Boolean(reference.trim()) && !/^(?:none|null|undefined|n\/?a|todo|pending|unknown)$/i.test(reference.trim());
}

/** trustedEvidence must be resolved by the runtime, never copied from worker declarations. */
export function assessMathResearchFindingEvidence(
  finding: MathResearchFinding,
  trustedEvidence: readonly MathResearchEvidence[] = []
) {
  const checked = trustedEvidence.filter(
    (entry) =>
      ['runtime_checked', 'kernel_verified'].includes(entry.grade) && isMathResearchEvidenceReference(entry.reference)
  );
  const matches = (scope: MathResearchEvidence['scope'], statement: string, kernel = false) =>
    checked.some(
      (entry) =>
        entry.scope === scope &&
        (!kernel || entry.grade === 'kernel_verified') &&
        normalizeMathResearchStatement(entry.statement) === normalizeMathResearchStatement(statement)
    );
  const establishedClaims = finding.establishedClaims.filter((claim) => matches('claim', claim, true));
  const boundedObservations = checked
    .filter((entry) => entry.scope === 'bounded_observation')
    .map((entry) => `Bounded observation: ${entry.statement}`);
  const eliminatedApproaches = finding.eliminatedApproaches.filter((approach) => matches('approach', approach));
  const family = deriveMathProblemFamilyState(finding.problemFamilyProbe);
  const conjectures = uniqueMathResearchStrings(
    finding.conjectureUpdates,
    finding.establishedClaims.filter((claim) => !establishedClaims.includes(claim)),
    finding.eliminatedApproaches
      .filter((approach) => !eliminatedApproaches.includes(approach))
      .map((approach) => `Unverified elimination: ${approach}`),
    family.establishedClaims,
    family.failedApproaches
  );
  const observed =
    finding.evidenceRefs.some(isMathResearchEvidenceReference) ||
    Boolean(
      finding.evidence?.some(
        (entry) => entry.grade !== 'hypothesis' && isMathResearchEvidenceReference(entry.reference)
      )
    ) ||
    checked.length > 0;
  const bottleneck = finding.bottleneckUpdate;
  const supportedBottleneck = Boolean(bottleneck && matches('bottleneck', bottleneck.target));
  const grade: MathResearchEvidence['grade'] = checked.some((entry) => entry.grade === 'kernel_verified')
    ? 'kernel_verified'
    : checked.length
      ? 'runtime_checked'
      : observed
        ? 'observed'
        : 'hypothesis';
  return Object.freeze({
    grade,
    observed,
    establishedClaims: uniqueMathResearchStrings(establishedClaims, boundedObservations),
    eliminatedApproaches,
    conjectures,
    closesBottleneck: supportedBottleneck && ['resolved', 'refuted'].includes(bottleneck!.outcome),
    narrowsBottleneck: supportedBottleneck && bottleneck!.outcome === 'narrowed',
  });
}

/** Keep the evidence identity stable when a finding paraphrases its diagnosis. */
export function mathResearchEvidenceKey(
  contract: MathResearchProblemContract | undefined,
  evidence: MathResearchEvidence
): string {
  return JSON.stringify([
    normalizeMathResearchStatement(contract?.activeBottleneck ?? ''),
    evidence.grade,
    evidence.scope,
    normalizeMathResearchStatement(evidence.statement),
    evidence.fingerprint ?? evidence.reference,
  ]);
}

/** Shared novelty decision for durable method statistics and Lead progress. */
export function assessNovelMathResearchFindingEvidence(
  contract: MathResearchProblemContract | undefined,
  finding: MathResearchFinding,
  trustedEvidence: readonly MathResearchEvidence[] = []
) {
  const assessment = assessMathResearchFindingEvidence(finding, trustedEvidence);
  const consumed = new Set(contract?.consumedEvidenceKeys ?? []);
  const fresh = assessMathResearchFindingEvidence(
    finding,
    trustedEvidence.filter((entry) => !consumed.has(mathResearchEvidenceKey(contract, entry)))
  );
  const sameTarget =
    Boolean(contract?.activeBottleneck) &&
    normalizeMathResearchStatement(finding.bottleneckUpdate?.target ?? '') ===
      normalizeMathResearchStatement(contract.activeBottleneck);
  const isNew = (value: string, prior: readonly string[] | undefined) =>
    !prior?.some((entry) => normalizeMathResearchStatement(entry) === normalizeMathResearchStatement(value));
  return Object.freeze({
    ...assessment,
    establishedClaims: fresh.establishedClaims.filter((claim) => isNew(claim, contract?.establishedClaims)),
    eliminatedApproaches: fresh.eliminatedApproaches.filter((claim) => isNew(claim, contract?.failedApproaches)),
    closesBottleneck: sameTarget && fresh.closesBottleneck,
    narrowsBottleneck:
      sameTarget &&
      fresh.narrowsBottleneck &&
      Boolean(finding.bottleneckUpdate?.diagnosis) &&
      normalizeMathResearchStatement(finding.bottleneckUpdate?.diagnosis ?? '') !==
        normalizeMathResearchStatement(contract?.bottleneckDiagnosis ?? ''),
  });
}

/** Merge one accepted discovery result into the durable pre-formal research state. */
export function applyMathResearchFinding(
  contractInput: MathResearchProblemContract,
  findingInput: MathResearchFinding,
  trustedEvidence: readonly MathResearchEvidence[] = []
): MathResearchProblemContract {
  const contract = normalizeMathResearchProblemContract(contractInput);
  const finding = normalizeMathResearchFinding(findingInput);
  const assessment = assessMathResearchFindingEvidence(finding, trustedEvidence);
  const novelAssessment = assessNovelMathResearchFindingEvidence(contract, finding, trustedEvidence);
  const establishedClaims = uniqueMathResearchStrings(contract.establishedClaims, assessment.establishedClaims);
  const establishedClaimSet = new Set(establishedClaims.map(normalizeMathResearchStatement));
  const conjectures = uniqueMathResearchStrings(contract.conjectures, assessment.conjectures).filter(
    (conjecture) => !establishedClaimSet.has(normalizeMathResearchStatement(conjecture))
  );
  // Finite observations may accumulate knowledge, but cannot discharge proof obligations.
  const discharged = new Set(
    [
      ...(contract.establishedClaims ?? []).filter((claim) => !claim.startsWith('Bounded observation: ')),
      ...assessment.establishedClaims.filter((claim) => !claim.startsWith('Bounded observation: ')),
    ].map(normalizeMathResearchStatement)
  );
  const openObligations = uniqueMathResearchStrings(contract.openObligations, finding.openObligations).filter(
    (obligation) => !discharged.has(normalizeMathResearchStatement(obligation))
  );
  const evidenceNote = mathResearchEvidenceNote(finding, assessment.grade);
  const evidenceNotes = evidenceNote
    ? [...(contract.evidenceNotes ?? []).filter((note) => note !== evidenceNote), evidenceNote].slice(-8)
    : contract.evidenceNotes;
  const bottleneckUpdate = finding.bottleneckUpdate;
  const activeBottleneck =
    novelAssessment.closesBottleneck &&
    normalizeMathResearchStatement(bottleneckUpdate!.target) ===
      normalizeMathResearchStatement(contract.activeBottleneck ?? '')
      ? undefined
      : (contract.activeBottleneck ?? bottleneckUpdate?.target);
  const nextAction = bottleneckUpdate?.repair ?? finding.nextAction;
  const solutionSketchRef = finding.solutionSketchRef ?? contract.solutionSketchRef;
  const insight = mathResearchInsight(contract, finding);
  const insights = insight
    ? [
        ...(contract.insights ?? []).filter(
          (value) => mathResearchInsightKey(value) !== mathResearchInsightKey(insight)
        ),
        insight,
      ].slice(-8)
    : contract.insights;
  const probeSummary = updateMathResearchProbeSummary(contract, finding, evidenceNote, novelAssessment);
  return normalizeMathResearchProblemContract({
    ...contract,
    consumedEvidenceKeys: [
      ...new Set([
        ...(contract.consumedEvidenceKeys ?? []),
        ...trustedEvidence
          .filter(
            (entry) =>
              ['runtime_checked', 'kernel_verified'].includes(entry.grade) &&
              isMathResearchEvidenceReference(entry.reference)
          )
          .map((entry) => mathResearchEvidenceKey(contract, entry)),
      ]),
    ],
    ...(establishedClaims.length ? { establishedClaims } : {}),
    conjectures,
    failedApproaches: uniqueMathResearchStrings(contract.failedApproaches, assessment.eliminatedApproaches),
    openObligations,
    ...(evidenceNotes?.length ? { evidenceNotes } : {}),
    ...(insights?.length ? { insights } : {}),
    ...(probeSummary?.length ? { probeSummary } : {}),
    activeBottleneck,
    bottleneckDiagnosis:
      activeBottleneck &&
      normalizeMathResearchStatement(bottleneckUpdate?.target ?? '') ===
        normalizeMathResearchStatement(activeBottleneck) &&
      assessment.narrowsBottleneck
        ? bottleneckUpdate.diagnosis
        : activeBottleneck === contract.activeBottleneck
          ? contract.bottleneckDiagnosis
          : undefined,
    ...(solutionSketchRef ? { solutionSketchRef } : {}),
    nextAction,
  });
}

function updateMathResearchProbeSummary(
  contract: MathResearchProblemContract,
  finding: MathResearchFinding,
  evidenceNote: string | undefined,
  assessment: ReturnType<typeof assessMathResearchFindingEvidence>
): readonly MathResearchProbeSummary[] | undefined {
  if (
    evidenceNote &&
    contract.evidenceNotes?.includes(evidenceNote) &&
    !assessment.establishedClaims.length &&
    !assessment.eliminatedApproaches.length &&
    !assessment.closesBottleneck &&
    !assessment.narrowsBottleneck
  )
    return contract.probeSummary;
  const probeKind = researchProbeKindForFinding(finding);
  const outcome = researchProbeOutcomeForFinding(finding, assessment);
  const current = contract.probeSummary?.find((entry) => entry.probeKind === probeKind);
  const bottleneck = finding.bottleneckUpdate?.target ?? contract.activeBottleneck;
  const currentForBottleneck = bottleneck
    ? (current?.bottleneckStats?.find((entry) => entry.bottleneck === bottleneck) ??
      (current?.bottleneck === bottleneck ? current : undefined))
    : undefined;
  const bucket = bottleneck
    ? {
        bottleneck,
        attempts: (currentForBottleneck?.attempts ?? 0) + 1,
        usefulChanges:
          (currentForBottleneck?.usefulChanges ?? 0) +
          (outcome === 'useful_state_change' || outcome === 'route_eliminated' ? 1 : 0),
        noChange: (currentForBottleneck?.noChange ?? 0) + (outcome === 'no_state_change' ? 1 : 0),
        lastOutcome: outcome,
      }
    : undefined;
  const updated: MathResearchProbeSummary = Object.freeze({
    probeKind,
    attempts: (current?.attempts ?? 0) + 1,
    usefulChanges:
      (current?.usefulChanges ?? 0) + (outcome === 'useful_state_change' || outcome === 'route_eliminated' ? 1 : 0),
    noChange: (current?.noChange ?? 0) + (outcome === 'no_state_change' ? 1 : 0),
    lastOutcome: outcome,
    ...(bottleneck
      ? {
          bottleneckStats: [
            ...(current?.bottleneckStats ?? []).filter((entry) => entry.bottleneck !== bottleneck),
            bucket!,
          ],
        }
      : current?.bottleneckStats
        ? { bottleneckStats: current.bottleneckStats }
        : {}),
  });
  return Object.freeze([...(contract.probeSummary ?? []).filter((entry) => entry.probeKind !== probeKind), updated]);
}

export function researchProbeKindForFinding(finding: MathResearchFinding): MathResearchProbeKind {
  switch (finding.kind) {
    case 'literature':
      return 'literature';
    case 'example':
      return 'example';
    case 'computation':
      return 'computation';
    case 'counterexample':
      return 'counterexample';
    case 'obstruction':
      return 'obstruction';
    case 'proof_step':
      return 'proof_step';
    case 'critique':
      return 'critique';
    case 'conjecture_update':
      return finding.openObligations.length ? 'proof_step' : 'critique';
  }
}

function researchProbeOutcomeForFinding(
  finding: MathResearchFinding,
  assessment: ReturnType<typeof assessMathResearchFindingEvidence>
): MathResearchProbeOutcome {
  if (finding.mainlineImpact === 'route_refuted' && assessment.eliminatedApproaches.length) return 'route_eliminated';
  if (
    assessment.establishedClaims.length ||
    assessment.eliminatedApproaches.length ||
    assessment.closesBottleneck ||
    assessment.narrowsBottleneck
  ) {
    return 'useful_state_change';
  }
  if (assessment.observed) return 'evidence_only';
  return 'no_state_change';
}

function deriveMathProblemFamilyState(
  probe: MathProblemFamilyProbe | undefined
): Readonly<{ establishedClaims: readonly string[]; failedApproaches: readonly string[] }> {
  if (!probe) return Object.freeze({ establishedClaims: [], failedApproaches: [] });
  if (probe.generalization === 'supported' && probe.sharedMechanism) {
    const inputs = probe.instances.map((instance) => instance.input).join(', ');
    return Object.freeze({
      establishedClaims: Object.freeze([`Bounded family support on [${inputs}]: ${probe.sharedMechanism}`]),
      failedApproaches: Object.freeze([]),
    });
  }
  if (probe.generalization === 'refuted' && probe.firstCounterexample) {
    return Object.freeze({
      establishedClaims: Object.freeze([]),
      failedApproaches: Object.freeze([`Bounded family generalization refuted by ${probe.firstCounterexample}`]),
    });
  }
  return Object.freeze({ establishedClaims: [], failedApproaches: [] });
}

function mathResearchInsight(
  contract: MathResearchProblemContract,
  finding: MathResearchFinding
): MathResearchInsight | undefined {
  if (!finding.evidenceRefs.length && !finding.establishedClaims.length && !finding.eliminatedApproaches.length) {
    return undefined;
  }
  const failure =
    finding.bottleneckUpdate?.diagnosis ??
    finding.problemFamilyProbe?.firstCounterexample ??
    finding.eliminatedApproaches[0];
  const repair = finding.bottleneckUpdate?.repair ?? finding.nextAction;
  const conditions = [finding.mechanism, finding.problemFamilyProbe?.sharedMechanism, ...finding.conjectureUpdates]
    .filter(Boolean)
    .slice(0, 4) as string[];
  return Object.freeze({
    claim: (finding.establishedClaims[0] ?? finding.summary).slice(0, 800),
    conditions: Object.freeze(conditions.map((value) => value.slice(0, 500))),
    ...(failure ? { failure: failure.slice(0, 800) } : {}),
    ...(repair ? { repair: repair.slice(0, 800) } : {}),
    usableWhen: (finding.bottleneckUpdate?.target ?? contract.activeBottleneck ?? finding.nextAction).slice(0, 800),
    evidenceRefs: finding.evidenceRefs.slice(-8),
  });
}

function mathResearchEvidenceNote(
  finding: MathResearchFinding,
  grade: MathResearchEvidence['grade']
): string | undefined {
  if (!finding.evidenceRefs.length && !finding.evidence?.length) return undefined;
  const summary = finding.summary.length > 500 ? `${finding.summary.slice(0, 497)}...` : finding.summary;
  const family = finding.problemFamilyProbe
    ? ` Family generalization=${finding.problemFamilyProbe.generalization}.` +
      (finding.problemFamilyProbe.sharedMechanism
        ? ` Shared mechanism: ${finding.problemFamilyProbe.sharedMechanism.slice(0, 240)}.`
        : '') +
      (finding.problemFamilyProbe.firstCounterexample
        ? ` First counterexample: ${finding.problemFamilyProbe.firstCounterexample.slice(0, 240)}.`
        : '')
    : '';
  const prefix = `[${grade}] ${summary}${family} Evidence: `.slice(0, 797);
  const maximumRefsLength = 800 - prefix.length;
  const refs = uniqueMathResearchStrings(
    finding.evidenceRefs,
    finding.evidence?.map((entry) => `${entry.scope}: ${entry.statement} (${entry.reference})`)
  ).join('; ');
  const boundedRefs =
    refs.length > maximumRefsLength ? `${refs.slice(0, Math.max(0, maximumRefsLength - 3))}...` : refs;
  return `${prefix}${boundedRefs}`;
}

export function normalizeMathAlignmentCheck(
  input: MathAlignmentCheck,
  contract?: MathProblemContract
): MathAlignmentCheck {
  if (!MATH_ALIGNMENT_VERDICTS.includes(input.verdict)) {
    throw new TypeError('Mathematics alignment verdict is invalid');
  }
  const assumptionDelta = textList(input.assumptionDelta, 'alignmentCheck.assumptionDelta');
  const quantifierDelta = textList(input.quantifierDelta, 'alignmentCheck.quantifierDelta');
  const domainDelta = textList(input.domainDelta, 'alignmentCheck.domainDelta');
  const firstMismatch = optionalText(input.firstMismatch);
  if (input.verdict === 'exact' && (assumptionDelta.length || quantifierDelta.length || domainDelta.length)) {
    throw new TypeError('Mathematics exact alignment cannot contain statement deltas');
  }
  if (input.verdict !== 'exact' && !firstMismatch) {
    throw new TypeError('Mathematics non-exact alignment requires firstMismatch');
  }
  const normalized = Object.freeze({
    problemId: requiredText(input.problemId, 'alignmentCheck.problemId'),
    statementHash: requiredHash(input.statementHash, 'alignmentCheck.statementHash'),
    leanStatementHash: requiredHash(input.leanStatementHash, 'alignmentCheck.leanStatementHash'),
    contractCommit: requiredGitOid(input.contractCommit, 'alignmentCheck.contractCommit'),
    assessorSessionId: requiredText(input.assessorSessionId, 'alignmentCheck.assessorSessionId'),
    goalInOwnWords: requiredText(input.goalInOwnWords, 'alignmentCheck.goalInOwnWords'),
    quantifiedObjects: requiredTextList(input.quantifiedObjects, 'alignmentCheck.quantifiedObjects'),
    assumptions: textList(input.assumptions, 'alignmentCheck.assumptions'),
    forbiddenChanges: requiredTextList(input.forbiddenChanges, 'alignmentCheck.forbiddenChanges'),
    officialVerificationCommand: requiredText(
      input.officialVerificationCommand,
      'alignmentCheck.officialVerificationCommand'
    ),
    verdict: input.verdict,
    assumptionDelta,
    quantifierDelta,
    domainDelta,
    ...(firstMismatch ? { firstMismatch } : {}),
  });
  if (contract) assertAlignmentMatchesContract(normalized, normalizeMathProblemContract(contract));
  return normalized;
}

const normalizedMathPlanSnapshots = new WeakSet<MathPlanSnapshot>();
const normalizedMathRouteCards = new WeakSet<MathRouteCard>();
const normalizedMathProofPlans = new WeakSet<MathProofPlan>();
const normalizedMathProofStates = new WeakSet<MathProofState>();
const normalizedMathProofActions = new WeakSet<MathProofAction>();

export function normalizeMathRouteCard(input: MathRouteCard): MathRouteCard {
  if (normalizedMathRouteCards.has(input)) return input;
  const planSnapshot = normalizeMathPlanSnapshot(input);
  const { planNodes, rootNodeId, bottleneckNodeId, openFrontierNodeIds } = planSnapshot;
  const extendedPlanReason = optionalText(input.extendedPlanReason);
  if (planNodes.length > 7 && !extendedPlanReason) {
    throw new TypeError('Mathematics route plans above 7 nodes require extendedPlanReason');
  }
  const bridges = normalizeMathPlanBridges(input.bridges, planNodes);
  const proposerSessionId = requiredText(input.proposerSessionId, 'routeCard.proposerSessionId');
  const assessment = input.assessment ? normalizeMathRouteAssessment(input.assessment) : undefined;
  if (assessment?.assessorSessionId === proposerSessionId) {
    throw new TypeError('Mathematics route assessment must be independent from the route proposer');
  }
  const probeNode = assessment ? planNodes.find((node) => node.id === assessment.probePlanNodeId) : undefined;
  if (assessment && !probeNode) {
    throw new TypeError('Mathematics route assessment probePlanNodeId must reference a plan node');
  }
  if (
    assessment &&
    ['supported', 'kernel_verified'].includes(assessment.probeOutcome) &&
    probeNode?.status === 'proposed'
  ) {
    throw new TypeError('Mathematics supported route probe requires evidence on the probed plan node');
  }
  if (assessment?.probeOutcome === 'kernel_verified' && probeNode?.status !== 'kernel_verified') {
    throw new TypeError('Mathematics kernel-verified route probe requires a kernel-verified probed node');
  }
  const probeEvidenceRefs = new Set(probeNode?.evidenceRefs ?? []);
  if (
    assessment &&
    ['supported', 'kernel_verified'].includes(assessment.probeOutcome) &&
    !assessment.evidenceRefs.some((ref) => probeEvidenceRefs.has(ref))
  ) {
    throw new TypeError('Mathematics supported route probe must share evidence with the probed plan node');
  }
  for (const check of assessment?.semanticViabilityChecks ?? []) {
    const checkedNode = planNodes.find((node) => node.id === check.planNodeId);
    if (!checkedNode) {
      throw new TypeError('Mathematics semantic viability check planNodeId must reference a plan node');
    }
    if (check.verdict === 'pass' && checkedNode.status === 'proposed') {
      throw new TypeError('Mathematics passing semantic viability check requires evidence on its plan node');
    }
    const checkedEvidence = new Set(checkedNode.evidenceRefs);
    if (check.verdict === 'pass' && !check.evidenceRefs.some((ref) => checkedEvidence.has(ref))) {
      throw new TypeError('Mathematics passing semantic viability check must share evidence with its plan node');
    }
  }
  const premiseBundle = normalizeMathPremiseBundle(input.premiseBundle, planNodes);
  const normalized = Object.freeze({
    statementHash: requiredHash(input.statementHash, 'routeCard.statementHash'),
    routeFingerprint: normalizeMathRouteFingerprint(input.routeFingerprint),
    proposerSessionId,
    structuralCommitment: requiredText(input.structuralCommitment, 'routeCard.structuralCommitment'),
    decisiveLemma: requiredText(input.decisiveLemma, 'routeCard.decisiveLemma'),
    decisiveTest: requiredText(input.decisiveTest, 'routeCard.decisiveTest'),
    falsificationSignal: requiredText(input.falsificationSignal, 'routeCard.falsificationSignal'),
    premiseBundle,
    planNodes,
    bridges,
    rootNodeId,
    ...(bottleneckNodeId ? { bottleneckNodeId } : {}),
    openFrontierNodeIds,
    ...(extendedPlanReason ? { extendedPlanReason } : {}),
    ...(assessment ? { assessment } : {}),
    expectedInformationGain: boundedRating(input.expectedInformationGain, 'routeCard.expectedInformationGain'),
    estimatedCost: boundedRating(input.estimatedCost, 'routeCard.estimatedCost'),
    formalizationRisk: boundedRating(input.formalizationRisk, 'routeCard.formalizationRisk'),
  });
  normalizedMathRouteCards.add(normalized);
  normalizedMathPlanSnapshots.add(normalized);
  return normalized;
}

export function normalizeMathPlanSnapshot(input: MathPlanSnapshot): MathPlanSnapshot {
  if (normalizedMathPlanSnapshots.has(input)) return input;
  const planNodes = normalizeMathPlanNodes(input.planNodes);
  const nodeById = new Map<string, MathPlanNode>();
  let goalNodeId: string | undefined;
  let hasMultipleGoalNodes = false;
  for (const node of planNodes) {
    nodeById.set(node.id, node);
    if (node.role !== 'goal') continue;
    if (goalNodeId) hasMultipleGoalNodes = true;
    else goalNodeId = node.id;
  }
  const rootNodeId = normalizeMathPlanNodeId(input.rootNodeId, 'planSnapshot.rootNodeId');
  const bottleneckNodeId = input.bottleneckNodeId
    ? normalizeMathPlanNodeId(input.bottleneckNodeId, 'planSnapshot.bottleneckNodeId')
    : undefined;
  if (!nodeById.has(rootNodeId)) throw new TypeError('Mathematics planSnapshot.rootNodeId must reference a plan node');
  if (bottleneckNodeId && !nodeById.has(bottleneckNodeId)) {
    throw new TypeError('Mathematics planSnapshot.bottleneckNodeId must reference a plan node');
  }
  if (hasMultipleGoalNodes || goalNodeId !== rootNodeId) {
    throw new TypeError('Mathematics route plan must have exactly one goal node matching rootNodeId');
  }
  assertMathPlanDag(planNodes, rootNodeId, nodeById);
  const openFrontierNodeIds = normalizeMathPlanNodeIds(input.openFrontierNodeIds, 'planSnapshot.openFrontierNodeIds');
  if (openFrontierNodeIds.some((nodeId) => !nodeById.has(nodeId))) {
    throw new TypeError('Mathematics planSnapshot.openFrontierNodeIds must reference plan nodes');
  }
  const expectedFrontier = computeMathActionableFrontierNodeIds(planNodes);
  const expectedFrontierSet = new Set(expectedFrontier);
  if (
    openFrontierNodeIds.length !== expectedFrontierSet.size ||
    openFrontierNodeIds.some((nodeId) => !expectedFrontierSet.has(nodeId))
  ) {
    throw new TypeError('Mathematics planSnapshot.openFrontierNodeIds must equal the actionable plan nodes');
  }
  const scheduledBottleneckNodeId = rankMathActionablePlanNodeIdsFromNormalized(planNodes, expectedFrontier)[0];
  if (bottleneckNodeId !== scheduledBottleneckNodeId) {
    throw new TypeError(
      scheduledBottleneckNodeId
        ? 'Mathematics planSnapshot.bottleneckNodeId must equal the highest-impact actionable node'
        : 'Mathematics completed plan snapshot must omit bottleneckNodeId'
    );
  }
  const normalized = Object.freeze({
    rootNodeId,
    planNodes,
    ...(bottleneckNodeId ? { bottleneckNodeId } : {}),
    openFrontierNodeIds,
  });
  normalizedMathPlanSnapshots.add(normalized);
  return normalized;
}

/** Normalize the versioned executable plan without changing the legacy route-card contract. */
export function normalizeMathProofPlan(input: MathProofPlan): MathProofPlan {
  if (normalizedMathProofPlans.has(input)) return input;
  if (!input || input.schema !== MATH_PROOF_PLAN_SCHEMA || input.version !== 1) {
    throw new TypeError('Mathematics proof plan schema or version is invalid');
  }
  const planNodes = normalizeMathPlanNodes(input.planNodes);
  const rootNodeId = normalizeMathPlanNodeId(input.rootNodeId, 'proofPlan.rootNodeId');
  const bottleneckNodeId = input.bottleneckNodeId
    ? normalizeMathPlanNodeId(input.bottleneckNodeId, 'proofPlan.bottleneckNodeId')
    : undefined;
  const openFrontierNodeIds = normalizeMathPlanNodeIds(input.openFrontierNodeIds, 'proofPlan.openFrontierNodeIds');
  const snapshot = normalizeMathPlanSnapshot({
    rootNodeId,
    planNodes,
    ...(bottleneckNodeId ? { bottleneckNodeId } : {}),
    openFrontierNodeIds,
  });
  const bridges = normalizeMathPlanBridges(input.bridges, snapshot.planNodes);
  const normalized = Object.freeze({
    schema: MATH_PROOF_PLAN_SCHEMA,
    version: 1 as const,
    planId: boundedRequiredText(input.planId, 'proofPlan.planId', 256),
    statementHash: requiredHash(input.statementHash, 'proofPlan.statementHash'),
    routeFingerprint: normalizeMathRouteFingerprint(input.routeFingerprint),
    rootNodeId: snapshot.rootNodeId,
    planNodes: snapshot.planNodes,
    bridges,
    ...(snapshot.bottleneckNodeId ? { bottleneckNodeId: snapshot.bottleneckNodeId } : {}),
    openFrontierNodeIds: snapshot.openFrontierNodeIds,
  });
  normalizedMathProofPlans.add(normalized);
  return normalized;
}

/** Normalize one action independently so action histories can be streamed or replayed. */
export function normalizeMathProofAction(input: MathProofAction): MathProofAction {
  if (normalizedMathProofActions.has(input)) return input;
  if (!input || input.schema !== MATH_PROOF_ACTION_SCHEMA || input.version !== 1) {
    throw new TypeError('Mathematics proof action schema or version is invalid');
  }
  if (!MATH_PROOF_ACTION_KINDS.includes(input.kind)) {
    throw new TypeError('Mathematics proof action kind is invalid');
  }
  if (!MATH_PROOF_ACTION_OUTCOMES.includes(input.outcome)) {
    throw new TypeError('Mathematics proof action outcome is invalid');
  }
  if (!input.runtime || typeof input.runtime !== 'object') {
    throw new TypeError('Mathematics proof action runtime is required');
  }
  if (
    !Number.isSafeInteger(input.runtime.durationMs) ||
    input.runtime.durationMs < 0 ||
    input.runtime.durationMs > 900_000
  ) {
    throw new TypeError('Mathematics proof action runtime.durationMs is invalid');
  }
  if (
    input.runtime.exitCode !== undefined &&
    (!Number.isSafeInteger(input.runtime.exitCode) || input.runtime.exitCode < 0 || input.runtime.exitCode > 255)
  ) {
    throw new TypeError('Mathematics proof action runtime.exitCode is invalid');
  }
  const diagnosticHash = input.runtime.diagnosticHash
    ? requiredHash(input.runtime.diagnosticHash, 'proofAction.runtime.diagnosticHash')
    : undefined;
  const normalized = Object.freeze({
    schema: MATH_PROOF_ACTION_SCHEMA,
    version: 1 as const,
    actionId: boundedRequiredText(input.actionId, 'proofAction.actionId', 256),
    kind: input.kind,
    payload: boundedRequiredText(input.payload, 'proofAction.payload', 16_000),
    preconditionStateId: boundedRequiredText(input.preconditionStateId, 'proofAction.preconditionStateId', 256),
    ...(input.resultStateId
      ? { resultStateId: boundedRequiredText(input.resultStateId, 'proofAction.resultStateId', 256) }
      : {}),
    runtime: Object.freeze({
      durationMs: input.runtime.durationMs,
      ...(input.runtime.exitCode !== undefined ? { exitCode: input.runtime.exitCode } : {}),
      ...(diagnosticHash ? { diagnosticHash } : {}),
    }),
    outcome: input.outcome,
  });
  if (normalized.resultStateId === normalized.preconditionStateId) {
    throw new TypeError('Mathematics proof action cannot return the same state it consumed');
  }
  normalizedMathProofActions.add(normalized);
  return normalized;
}

/** Normalize a persistent Lean state and its replayable action history. */
export function normalizeMathProofState(input: MathProofState): MathProofState {
  if (normalizedMathProofStates.has(input)) return input;
  if (!input || input.schema !== MATH_PROOF_STATE_SCHEMA || input.version !== 1) {
    throw new TypeError('Mathematics proof state schema or version is invalid');
  }
  if (!MATH_PROOF_STATE_STATUSES.includes(input.status)) {
    throw new TypeError('Mathematics proof state status is invalid');
  }
  if (!Number.isSafeInteger(input.metavariableCount) || input.metavariableCount < 0) {
    throw new TypeError('Mathematics proof state metavariableCount must be a nonnegative integer');
  }
  if (!Array.isArray(input.openGoals) || input.openGoals.length > 128) {
    throw new TypeError('Mathematics proof state openGoals must contain at most 128 items');
  }
  if (!Array.isArray(input.declarationHashes) || input.declarationHashes.length > 128) {
    throw new TypeError('Mathematics proof state declarationHashes must contain at most 128 items');
  }
  if (!Array.isArray(input.actionHistory) || input.actionHistory.length > 512) {
    throw new TypeError('Mathematics proof state actionHistory must contain at most 512 items');
  }
  if (
    input.actionHistoryOffset !== undefined &&
    (!Number.isSafeInteger(input.actionHistoryOffset) || input.actionHistoryOffset < 0)
  ) {
    throw new TypeError('Mathematics proof state actionHistoryOffset must be a nonnegative integer');
  }
  const actionHistory = input.actionHistory.map(normalizeMathProofAction);
  const actionHistoryOffset = input.actionHistoryOffset ?? 0;
  if (
    !Number.isSafeInteger(actionHistoryOffset) ||
    actionHistoryOffset < 0 ||
    !Number.isSafeInteger(actionHistoryOffset + actionHistory.length)
  ) {
    throw new TypeError('Mathematics proof state actionHistoryOffset must be a nonnegative safe integer');
  }
  const actionHistoryRef = input.actionHistoryRef?.replaceAll('\\', '/');
  if (
    (actionHistoryOffset > 0 && !actionHistoryRef) ||
    (actionHistoryRef &&
      (actionHistoryRef.startsWith('/') ||
        /^[A-Za-z]:/u.test(actionHistoryRef) ||
        actionHistoryRef.split('/').some((part) => !part || part === '.' || part === '..') ||
        !actionHistoryRef.endsWith('.jsonl')))
  ) {
    throw new TypeError('Mathematics proof state actionHistoryRef must reference a project-relative JSONL archive');
  }
  if (new Set(actionHistory.map((action) => action.actionId)).size !== actionHistory.length) {
    throw new TypeError('Mathematics proof state actionHistory action ids must be unique');
  }
  const sourceFile = requiredText(input.sourceFile, 'proofState.sourceFile').replaceAll('\\', '/');
  if (
    sourceFile.startsWith('/') ||
    sourceFile.split('/').includes('..') ||
    !sourceFile.toLowerCase().endsWith('.lean')
  ) {
    throw new TypeError('Mathematics proofState.sourceFile must be a project-relative Lean path');
  }
  const normalized = Object.freeze({
    schema: MATH_PROOF_STATE_SCHEMA,
    version: 1 as const,
    episodeId: boundedRequiredText(input.episodeId, 'proofState.episodeId', 256),
    stateId: boundedRequiredText(input.stateId, 'proofState.stateId', 256),
    ...(input.parentStateId
      ? { parentStateId: boundedRequiredText(input.parentStateId, 'proofState.parentStateId', 256) }
      : {}),
    statementHash: requiredHash(input.statementHash, 'proofState.statementHash'),
    routeFingerprint: normalizeMathRouteFingerprint(input.routeFingerprint),
    ...(input.planId ? { planId: boundedRequiredText(input.planId, 'proofState.planId', 256) } : {}),
    goalFingerprint: requiredHash(input.goalFingerprint, 'proofState.goalFingerprint'),
    sourceFile,
    sourceHash: requiredHash(input.sourceHash, 'proofState.sourceHash'),
    openGoals: Object.freeze(
      input.openGoals.map((goal, index) => boundedRequiredText(goal, `proofState.openGoals[${index}]`, 4_000))
    ),
    localContextHash: requiredHash(input.localContextHash, 'proofState.localContextHash'),
    metavariableCount: input.metavariableCount,
    declarationHashes: Object.freeze(
      input.declarationHashes.map((hash, index) => requiredHash(hash, `proofState.declarationHashes[${index}]`))
    ),
    actionHistory: Object.freeze(actionHistory),
    ...(input.actionHistoryOffset !== undefined ? { actionHistoryOffset: input.actionHistoryOffset } : {}),
    ...(input.actionHistoryRef
      ? { actionHistoryRef: boundedRequiredText(input.actionHistoryRef, 'proofState.actionHistoryRef', 512) }
      : {}),
    status: input.status,
  });
  if (normalized.parentStateId === normalized.stateId) {
    throw new TypeError('Mathematics proof state cannot be its own parent');
  }
  if (normalized.status === 'closed' && normalized.openGoals.length > 0) {
    throw new TypeError('A closed Mathematics proof state cannot retain open goals');
  }
  normalizedMathProofStates.add(normalized);
  return normalized;
}

export function mathActionablePlanSchedule(nodes: readonly MathPlanNode[]): Readonly<{
  rootNodeId: string;
  openFrontierNodeIds: readonly string[];
  rankedNodeIds: readonly string[];
}> {
  const normalized = normalizeMathActionablePlanNodes(nodes);
  return mathActionablePlanScheduleFromNormalized(normalized);
}

export function mathActionablePlanScheduleFromNormalized(normalized: readonly MathPlanNode[]): Readonly<{
  rootNodeId: string;
  openFrontierNodeIds: readonly string[];
  rankedNodeIds: readonly string[];
}> {
  const rootNodeId = normalized.find((node) => node.role === 'goal')!.id;
  const openFrontierNodeIds = computeMathActionableFrontierNodeIds(normalized);
  const rankedNodeIds = rankMathActionablePlanNodeIdsFromNormalized(normalized, openFrontierNodeIds);
  return Object.freeze({
    rootNodeId,
    openFrontierNodeIds: Object.freeze(openFrontierNodeIds),
    rankedNodeIds: Object.freeze(rankedNodeIds),
  });
}

function normalizeMathActionablePlanNodes(nodes: readonly MathPlanNode[]): readonly MathPlanNode[] {
  const normalized = normalizeMathPlanNodes(nodes);
  const nodeById = new Map<string, MathPlanNode>();
  let goalNode: MathPlanNode | undefined;
  for (const node of normalized) {
    nodeById.set(node.id, node);
    if (node.role !== 'goal') continue;
    if (goalNode) throw new TypeError('Mathematics route plan must have exactly one goal node');
    goalNode = node;
  }
  if (!goalNode) throw new TypeError('Mathematics route plan must have exactly one goal node');
  assertMathPlanDag(normalized, goalNode.id, nodeById);
  return normalized;
}

function computeMathDownstreamImpactByNodeId(normalized: readonly MathPlanNode[]): ReadonlyMap<string, number> {
  const nodeById = new Map<string, MathPlanNode>();
  for (const node of normalized) nodeById.set(node.id, node);
  const dependentsByNodeId = new Map<string, string[]>();
  for (const node of normalized) {
    for (const dependencyId of node.dependsOn) {
      const dependents = dependentsByNodeId.get(dependencyId);
      if (dependents) dependents.push(node.id);
      else dependentsByNodeId.set(dependencyId, [node.id]);
    }
    if (node.parentNodeId) {
      const dependents = dependentsByNodeId.get(node.id);
      if (dependents) dependents.push(node.parentNodeId);
      else dependentsByNodeId.set(node.id, [node.parentNodeId]);
    }
  }

  const descendantsByNodeId = new Map<string, ReadonlySet<string>>();
  const descendantsFor = (nodeId: string): ReadonlySet<string> => {
    const cached = descendantsByNodeId.get(nodeId);
    if (cached) return cached;
    const descendants = new Set<string>();
    for (const dependentId of dependentsByNodeId.get(nodeId) ?? []) {
      descendants.add(dependentId);
      for (const descendantId of descendantsFor(dependentId)) descendants.add(descendantId);
    }
    descendantsByNodeId.set(nodeId, descendants);
    return descendants;
  };
  const impactByNodeId = new Map<string, number>();
  for (const node of normalized) {
    let impact = 0;
    for (const descendantId of descendantsFor(node.id)) {
      if (nodeById.get(descendantId)?.status !== 'kernel_verified') impact += 1;
    }
    impactByNodeId.set(node.id, impact);
  }
  return impactByNodeId;
}

function rankMathActionablePlanNodeIdsFromNormalized(
  normalized: readonly MathPlanNode[],
  frontier = computeMathActionableFrontierNodeIds(normalized),
  downstreamImpactByNodeId = computeMathDownstreamImpactByNodeId(normalized)
): string[] {
  const statusRank: Readonly<Record<MathPlanNodeStatus, number>> = {
    proposed: 0,
    sourced: 1,
    counterexample_checked: 2,
    typed: 3,
    compiling: 4,
    compiled: 5,
    kernel_verified: 6,
    refuted: -1,
  };
  const nodeById = new Map<string, MathPlanNode>();
  for (const node of normalized) nodeById.set(node.id, node);
  return frontier.toSorted((leftId, rightId) => {
    const left = nodeById.get(leftId)!;
    const right = nodeById.get(rightId)!;
    const priority = (node: MathPlanNode): number => {
      const unlockValue = (downstreamImpactByNodeId.get(node.id) ?? 0) + (node.downstreamValue ?? 1);
      return (unlockValue * (node.successProbability ?? 0.5)) / (node.estimatedEffort ?? 3);
    };
    return (
      priority(right) - priority(left) ||
      statusRank[right.status] - statusRank[left.status] ||
      downstreamImpactByNodeId.get(rightId)! - downstreamImpactByNodeId.get(leftId)! ||
      leftId.localeCompare(rightId)
    );
  });
}

function isNormalizedMathPremiseBundleReady(bundle: MathPremiseBundle): boolean {
  return (
    bundle.unresolvedNeeds.length === 0 &&
    deriveMathPremiseCoverageRows(bundle).every((row) => row.status === 'covered')
  );
}

export function mathPremiseRouteSchedule(card: MathRouteCard): Readonly<{
  coverage: readonly MathPremiseCoverageRow[];
  gapNodeIds: readonly string[];
}> {
  const normalized = normalizeMathRouteCard(card);
  const coverage = deriveMathPremiseCoverageRows(normalized.premiseBundle);
  const gapNodeIds = rankMathPremiseGapNodeIdsFromNormalized(normalized, coverage);
  return Object.freeze({ coverage, gapNodeIds });
}

function rankMathPremiseGapNodeIdsFromNormalized(
  normalized: MathRouteCard,
  coverage = deriveMathPremiseCoverageRows(normalized.premiseBundle)
): readonly string[] {
  const rowByNodeId = new Map<string, MathPremiseCoverageRow>();
  for (const row of coverage) rowByNodeId.set(row.planNodeId, row);
  const downstreamImpactByNodeId = computeMathDownstreamImpactByNodeId(normalized.planNodes);
  const statusRank: Readonly<Record<MathPremiseCoverageStatus, number>> = { covered: 0, partial: 1, missing: 2 };
  const gapNodeIds: string[] = [];
  for (const node of normalized.planNodes) {
    if (rowByNodeId.get(node.id)?.status !== 'covered') gapNodeIds.push(node.id);
  }
  gapNodeIds.sort((leftId, rightId) => {
    const leftRow = rowByNodeId.get(leftId)!;
    const rightRow = rowByNodeId.get(rightId)!;
    return (
      downstreamImpactByNodeId.get(rightId)! - downstreamImpactByNodeId.get(leftId)! ||
      statusRank[rightRow.status] - statusRank[leftRow.status] ||
      leftId.localeCompare(rightId)
    );
  });
  return Object.freeze(gapNodeIds);
}

export function mathRouteStructureSignatureFromNormalized(card: MathRouteCard): string {
  return deriveMathRouteStructureSignature(card);
}

export function assertNormalizedMathRouteCardsStructurallyDistinct(cards: readonly MathRouteCard[]): void {
  const seen = new Map<string, string>();
  for (const card of cards) {
    const signature = deriveMathRouteStructureSignature(card);
    const priorFingerprint = seen.get(signature);
    if (priorFingerprint) {
      throw new TypeError(
        `Mathematics route cards must be structurally distinct: ${priorFingerprint} and ${card.routeFingerprint}`
      );
    }
    seen.set(signature, card.routeFingerprint);
  }
}

export function isMathRouteSelectable(card: MathRouteCard): boolean {
  const normalized = normalizeMathRouteCard(card);
  return isNormalizedMathRouteSelectable(normalized);
}

function isNormalizedMathRouteSelectable(card: MathRouteCard): boolean {
  const assessment = card.assessment;
  const viabilityChecks = assessment?.semanticViabilityChecks ?? [];
  const viabilityKinds = new Set(viabilityChecks.map((check) => check.kind));
  const semanticViabilityPassed =
    viabilityChecks.length === MATH_SEMANTIC_VIABILITY_KINDS.length &&
    MATH_SEMANTIC_VIABILITY_KINDS.every((kind) => viabilityKinds.has(kind)) &&
    viabilityChecks.every((check) => check.verdict === 'pass');
  return Boolean(
    assessment &&
    semanticViabilityPassed &&
    isNormalizedMathPremiseBundleReady(card.premiseBundle) &&
    assessment.faithfulness === 'pass' &&
    assessment.mathematicalValidity === 'pass' &&
    assessment.decompositionUsefulness === 'pass' &&
    ['supported', 'kernel_verified'].includes(assessment.probeOutcome)
  );
}

export function normalizeMathRouteSelectionFromNormalized(
  input: MathRouteSelection,
  normalizedCards: readonly MathRouteCard[]
): MathRouteSelection {
  if (normalizedCards.length < 1) {
    throw new TypeError('Mathematics route selection requires at least one route card');
  }
  const cardByFingerprint = new Map<string, MathRouteCard>();
  const cardFingerprints: string[] = [];
  for (const card of normalizedCards) {
    if (cardByFingerprint.has(card.routeFingerprint)) {
      throw new TypeError('Mathematics route cards must use distinct fingerprints');
    }
    cardByFingerprint.set(card.routeFingerprint, card);
    cardFingerprints.push(card.routeFingerprint);
  }
  assertNormalizedMathRouteCardsStructurallyDistinct(normalizedCards);
  const statementHash = requiredHash(input.statementHash, 'routeSelection.statementHash');
  const selectionCommit = requiredGitOid(input.selectionCommit, 'routeSelection.selectionCommit');
  if (normalizedCards.some((card) => card.statementHash !== statementHash)) {
    throw new TypeError('Mathematics route cards must match routeSelection.statementHash');
  }
  const primaryFingerprint = normalizeMathRouteFingerprint(input.primaryFingerprint);
  const reserveFingerprint = input.reserveFingerprint
    ? normalizeMathRouteFingerprint(input.reserveFingerprint)
    : undefined;
  if (!cardByFingerprint.has(primaryFingerprint)) {
    throw new TypeError('Mathematics primary route must reference a route card');
  }
  const selectableByCard = new Map<MathRouteCard, boolean>();
  const executionEstimates = new Map<MathRouteCard, MathRouteExecutionEstimate>();
  for (const card of normalizedCards) {
    selectableByCard.set(card, isNormalizedMathRouteSelectable(card));
    executionEstimates.set(card, deriveMathRouteExecutionEstimate(card));
  }
  if (!selectableByCard.get(cardByFingerprint.get(primaryFingerprint)!)) {
    throw new TypeError('Mathematics primary route must pass independent checks and a decisive probe');
  }
  let highestEvidenceRoute: MathRouteCard | undefined;
  for (const card of normalizedCards) {
    if (!selectableByCard.get(card)) continue;
    if (!highestEvidenceRoute) {
      highestEvidenceRoute = card;
      continue;
    }
    const comparison = compareMathRouteEvidence(card, highestEvidenceRoute, executionEstimates, selectableByCard);
    if (
      comparison > 0 ||
      (comparison === 0 && card.routeFingerprint.localeCompare(highestEvidenceRoute.routeFingerprint) < 0)
    ) {
      highestEvidenceRoute = card;
    }
  }
  if (highestEvidenceRoute?.routeFingerprint !== primaryFingerprint) {
    throw new TypeError('Mathematics primary route must be the highest evidence-ranked selectable route');
  }
  if (reserveFingerprint && (!cardByFingerprint.has(reserveFingerprint) || reserveFingerprint === primaryFingerprint)) {
    throw new TypeError('Mathematics reserve route must reference a different route card');
  }
  if (reserveFingerprint && !selectableByCard.get(cardByFingerprint.get(reserveFingerprint)!)) {
    throw new TypeError('Mathematics reserve route must pass independent checks and a decisive probe');
  }
  const hasReMaterialization = Boolean(input.rebasedFromCommit && input.revalidatedAtCommit);
  if (input.rebasedFromCommit && input.rebasedFromCommit !== selectionCommit) {
    throw new TypeError('Mathematics routeSelection rebasedFromCommit must equal selectionCommit');
  }
  if (input.rebasedFromCommit && !hasReMaterialization) {
    throw new TypeError('Mathematics routeSelection re-materialization must name the old and current commit');
  }
  if (input.revalidatedAtCommit && !input.rebasedFromCommit) {
    throw new TypeError('Mathematics routeSelection revalidatedAtCommit requires rebasedFromCommit');
  }
  for (const fingerprint of [primaryFingerprint, reserveFingerprint].filter(Boolean) as string[]) {
    const selectedPremises = cardByFingerprint.get(fingerprint)!.premiseBundle.premises;
    if (!hasReMaterialization && selectedPremises.some((premise) => premise.checkedAtCommit !== selectionCommit)) {
      throw new TypeError(
        'Mathematics routeSelection must target the assignment base commit recorded by every selected premise checkedAtCommit'
      );
    }
  }
  const comparedFingerprints = uniqueMathRouteFingerprints(input.comparedFingerprints);
  const comparedFingerprintSet = new Set(comparedFingerprints);
  if (comparedFingerprints.some((fingerprint) => !cardByFingerprint.has(fingerprint))) {
    throw new TypeError('Mathematics route selection cannot compare an unknown route card');
  }
  if (cardFingerprints.some((fingerprint) => !comparedFingerprintSet.has(fingerprint))) {
    throw new TypeError('Mathematics route selection must compare every route card');
  }
  if (!Number.isFinite(input.selectedAt) || input.selectedAt <= 0) {
    throw new TypeError('Mathematics route selection selectedAt must be a positive timestamp');
  }
  return Object.freeze({
    statementHash,
    selectionCommit,
    primaryFingerprint,
    ...(reserveFingerprint ? { reserveFingerprint } : {}),
    comparedFingerprints,
    rationale: requiredText(input.rationale, 'routeSelection.rationale'),
    selectedAt: input.selectedAt,
    ...(input.rebasedFromCommit
      ? { rebasedFromCommit: requiredGitOid(input.rebasedFromCommit, 'routeSelection.rebasedFromCommit') }
      : {}),
    ...(input.revalidatedAtCommit
      ? { revalidatedAtCommit: requiredGitOid(input.revalidatedAtCommit, 'routeSelection.revalidatedAtCommit') }
      : {}),
  });
}

export function normalizeMathLesson(input: MathLesson): MathLesson {
  if (!MATH_FAILURE_CATEGORIES.includes(input.failureCategory) || input.failureCategory === 'none') {
    throw new TypeError('Mathematics lesson requires a non-none failure category');
  }
  if (!MATH_LESSON_DISPOSITIONS.includes(input.disposition)) {
    throw new TypeError('Mathematics lesson disposition is invalid');
  }
  if (!Number.isFinite(input.createdAt) || input.createdAt <= 0) {
    throw new TypeError('Mathematics lesson createdAt must be a positive timestamp');
  }
  return Object.freeze({
    lessonId: requiredText(input.lessonId, 'lesson.lessonId'),
    statementHash: requiredHash(input.statementHash, 'lesson.statementHash'),
    routeFingerprint: normalizeMathRouteFingerprint(input.routeFingerprint),
    sourceCommit: requiredGitOid(input.sourceCommit, 'lesson.sourceCommit'),
    failureCategory: input.failureCategory,
    disposition: input.disposition,
    trigger: requiredText(input.trigger, 'lesson.trigger'),
    failedPattern: requiredText(input.failedPattern, 'lesson.failedPattern'),
    rootCause: requiredText(input.rootCause, 'lesson.rootCause'),
    reusableRule: requiredText(input.reusableRule, 'lesson.reusableRule'),
    evidenceRefs: requiredTextList(input.evidenceRefs, 'lesson.evidenceRefs'),
    createdAt: input.createdAt,
  });
}

export function assertMathLessonsApplied(
  routeFingerprint: string,
  applicableLessons: readonly MathLesson[],
  doNotRepeatRefs: readonly string[],
  routePattern?: string
): void {
  const route = normalizeMathRouteFingerprint(routeFingerprint);
  const pattern = routePattern ? normalizeMathLessonPattern(routePattern) : undefined;
  const lessons = applicableLessons.map(normalizeMathLesson);
  const refs = new Set(textList(doNotRepeatRefs, 'doNotRepeatRefs'));
  for (const lesson of lessons) {
    if (!refs.has(`lesson:${lesson.lessonId}`)) {
      throw new TypeError(`Mathematics assignment must acknowledge lesson:${lesson.lessonId}`);
    }
    if (lesson.disposition === 'avoid_route' && lesson.routeFingerprint === route) {
      throw new TypeError(`Mathematics route is forbidden by lesson:${lesson.lessonId}`);
    }
    if (lesson.disposition === 'avoid_pattern') {
      if (!pattern) {
        throw new TypeError(`Mathematics assignment must declare routePattern for lesson:${lesson.lessonId}`);
      }
      if (pattern === normalizeMathLessonPattern(lesson.failedPattern)) {
        throw new TypeError(`Mathematics route pattern is forbidden by lesson:${lesson.lessonId}`);
      }
    }
  }
}

export function normalizeMathCandidateReview(input: MathCandidateReview): MathCandidateReview {
  if (!MATH_CANDIDATE_REVIEW_VERDICTS.includes(input.verdict)) {
    throw new TypeError('Mathematics candidate review verdict is invalid');
  }
  const firstFault = optionalText(input.firstFault);
  if ((input.verdict === 'gap' || input.verdict === 'wrong') && !firstFault) {
    throw new TypeError('Mathematics non-sound review requires firstFault');
  }
  const source = input.source
    ? Object.freeze({
        teamId: requiredText(input.source.teamId, 'candidateReview.source.teamId'),
        slotId: requiredText(input.source.slotId, 'candidateReview.source.slotId'),
        assignmentId: requiredText(input.source.assignmentId, 'candidateReview.source.assignmentId'),
        deliveryId: requiredText(input.source.deliveryId, 'candidateReview.source.deliveryId'),
        ...(input.source.laneId ? { laneId: requiredText(input.source.laneId, 'candidateReview.source.laneId') } : {}),
      })
    : undefined;
  const attestation = input.attestation
    ? normalizeMathReceiptAttestation(input.attestation, 'candidateReview.attestation')
    : undefined;
  let findings: readonly MathReviewFinding[] | undefined;
  if (input.findings !== undefined) {
    if (!Array.isArray(input.findings) || input.findings.length > 12) {
      throw new TypeError('Mathematics candidate review findings must contain at most 12 entries');
    }
    findings = Object.freeze(
      input.findings.map((finding, index) => {
        if (!finding || typeof finding !== 'object') {
          throw new TypeError(`candidateReview.findings[${index}] must be an object`);
        }
        if (!MATH_REVIEW_FINDING_SEVERITIES.includes(finding.severity)) {
          throw new TypeError(`candidateReview.findings[${index}].severity is invalid`);
        }
        if (!MATH_REVIEW_FINDING_KINDS.includes(finding.kind)) {
          throw new TypeError(`candidateReview.findings[${index}].kind is invalid`);
        }
        const evidenceRefs = textList(finding.evidenceRefs, `candidateReview.findings[${index}].evidenceRefs`);
        if (evidenceRefs.length === 0) {
          throw new TypeError(`candidateReview.findings[${index}] requires at least one evidenceRef`);
        }
        return Object.freeze({
          severity: finding.severity,
          kind: finding.kind,
          message: boundedRequiredText(finding.message, `candidateReview.findings[${index}].message`, 1200),
          ...(optionalText(finding.repairTarget)
            ? {
                repairTarget: boundedRequiredText(
                  finding.repairTarget,
                  `candidateReview.findings[${index}].repairTarget`,
                  800
                ),
              }
            : {}),
          evidenceRefs,
        });
      })
    );
    if (
      input.verdict === 'sound' &&
      findings.some((finding) => finding.severity === 'blocker' || finding.severity === 'major')
    ) {
      throw new TypeError('Mathematics sound review cannot contain blocker or major findings');
    }
  }
  if (Boolean(source) !== Boolean(attestation)) {
    throw new TypeError('Mathematics candidate review source and attestation must be supplied together');
  }
  return Object.freeze({
    verdict: input.verdict,
    ...(firstFault ? { firstFault } : {}),
    ...(optionalText(input.repairTarget) ? { repairTarget: optionalText(input.repairTarget) } : {}),
    problemId: requiredText(input.problemId, 'candidateReview.problemId'),
    targetCommit: requiredGitOid(input.targetCommit, 'candidateReview.targetCommit'),
    statementHash: requiredHash(input.statementHash, 'candidateReview.statementHash'),
    reviewerSessionId: requiredText(input.reviewerSessionId, 'candidateReview.reviewerSessionId'),
    ...(input.localGateReceiptId
      ? { localGateReceiptId: requiredText(input.localGateReceiptId, 'candidateReview.localGateReceiptId') }
      : {}),
    ...(input.replayReceiptId
      ? { replayReceiptId: requiredText(input.replayReceiptId, 'candidateReview.replayReceiptId') }
      : {}),
    ...(input.replayTheoremName
      ? { replayTheoremName: requiredText(input.replayTheoremName, 'candidateReview.replayTheoremName') }
      : {}),
    ...(input.replayProofHash
      ? { replayProofHash: requiredHash(input.replayProofHash, 'candidateReview.replayProofHash') }
      : {}),
    ...(input.replayTheoremDeclarationHash
      ? {
          replayTheoremDeclarationHash: requiredHash(
            input.replayTheoremDeclarationHash,
            'candidateReview.replayTheoremDeclarationHash'
          ),
        }
      : {}),
    ...(input.replaySourceDeclarationHash
      ? {
          replaySourceDeclarationHash: requiredHash(
            input.replaySourceDeclarationHash,
            'candidateReview.replaySourceDeclarationHash'
          ),
        }
      : {}),
    evidenceRefs: requiredTextList(input.evidenceRefs, 'candidateReview.evidenceRefs'),
    ...(findings ? { findings } : {}),
    ...(source ? { source } : {}),
    ...(attestation ? { attestation } : {}),
  });
}

export function normalizeMathLocalGateReceipt(input: MathLocalGateReceipt): MathLocalGateReceipt {
  if (input.status !== 'kernel_verified' || input.verifier !== 'lean-kernel') {
    throw new TypeError('Mathematics local gate receipt must be Lean kernel verified');
  }
  if (input.goalsRemaining !== 0 || input.sorryCount !== 0 || input.admitCount !== 0) {
    throw new TypeError('Mathematics local gate receipt must have no goals, sorry, or admit');
  }
  const axioms = textList(input.axioms, 'localGateReceipt.axioms');
  const unsupportedAxioms = axioms.filter((axiom) => !isMathFoundationalLeanAxiom(axiom));
  if (unsupportedAxioms.length) {
    throw new TypeError(
      `Mathematics local gate receipt uses non-foundational Lean axioms: ${unsupportedAxioms.join(', ')}`
    );
  }
  if (!Number.isFinite(input.checkedAt) || input.checkedAt <= 0) {
    throw new TypeError('Mathematics local gate receipt checkedAt must be a positive timestamp');
  }
  return Object.freeze({
    receiptId: requiredText(input.receiptId, 'localGateReceipt.receiptId'),
    targetCommit: requiredGitOid(input.targetCommit, 'localGateReceipt.targetCommit'),
    statementHash: requiredHash(input.statementHash, 'localGateReceipt.statementHash'),
    ...(input.claim ? { claim: input.claim === 'negation' ? 'negation' : 'statement' } : {}),
    ...(optionalText(input.leanStatementHash)
      ? { leanStatementHash: requiredHash(input.leanStatementHash, 'localGateReceipt.leanStatementHash') }
      : {}),
    routeFingerprint: normalizeMathRouteFingerprint(input.routeFingerprint),
    status: 'kernel_verified',
    verifier: 'lean-kernel',
    theoremName: requiredText(input.theoremName, 'localGateReceipt.theoremName'),
    proofHash: requiredHash(input.proofHash, 'localGateReceipt.proofHash'),
    theoremDeclarationHash: requiredHash(input.theoremDeclarationHash, 'localGateReceipt.theoremDeclarationHash'),
    ...(optionalText(input.sourceDeclarationHash)
      ? { sourceDeclarationHash: requiredHash(input.sourceDeclarationHash, 'localGateReceipt.sourceDeclarationHash') }
      : {}),
    goalsRemaining: 0,
    sorryCount: 0,
    admitCount: 0,
    axioms,
    checkedAt: input.checkedAt,
  });
}

export function normalizeMathNodeProofReceipt(input: MathNodeProofReceipt): MathNodeProofReceipt {
  if (input.status !== 'kernel_verified' || input.verifier !== 'lean-kernel') {
    throw new TypeError('Mathematics node proof receipt must be Lean kernel verified');
  }
  if (input.goalsRemaining !== 0 || input.sorryCount !== 0 || input.admitCount !== 0) {
    throw new TypeError('Mathematics node proof receipt must have no goals, sorry, or admit');
  }
  const axioms = textList(input.axioms, 'nodeProofReceipt.axioms');
  const unsupportedAxioms = axioms.filter((axiom) => !isMathFoundationalLeanAxiom(axiom));
  if (unsupportedAxioms.length) {
    throw new TypeError(
      `Mathematics node proof receipt uses non-foundational Lean axioms: ${unsupportedAxioms.join(', ')}`
    );
  }
  if (!Number.isFinite(input.checkedAt) || input.checkedAt <= 0) {
    throw new TypeError('Mathematics node proof receipt checkedAt must be a positive timestamp');
  }
  return Object.freeze({
    receiptId: requiredText(input.receiptId, 'nodeProofReceipt.receiptId'),
    targetCommit: requiredGitOid(input.targetCommit, 'nodeProofReceipt.targetCommit'),
    statementHash: requiredHash(input.statementHash, 'nodeProofReceipt.statementHash'),
    ...(optionalText(input.leanStatementHash)
      ? { leanStatementHash: requiredHash(input.leanStatementHash, 'nodeProofReceipt.leanStatementHash') }
      : {}),
    routeFingerprint: normalizeMathRouteFingerprint(input.routeFingerprint),
    planNodeId: normalizeMathPlanNodeId(input.planNodeId, 'nodeProofReceipt.planNodeId'),
    status: 'kernel_verified',
    verifier: 'lean-kernel',
    theoremName: requiredText(input.theoremName, 'nodeProofReceipt.theoremName'),
    proofHash: requiredHash(input.proofHash, 'nodeProofReceipt.proofHash'),
    theoremDeclarationHash: requiredHash(input.theoremDeclarationHash, 'nodeProofReceipt.theoremDeclarationHash'),
    ...(optionalText(input.sourceDeclarationHash)
      ? { sourceDeclarationHash: requiredHash(input.sourceDeclarationHash, 'nodeProofReceipt.sourceDeclarationHash') }
      : {}),
    goalsRemaining: 0,
    sorryCount: 0,
    admitCount: 0,
    axioms,
    checkedAt: input.checkedAt,
  });
}

export function normalizeMathHelperReceipt(input: MathHelperReceipt): MathHelperReceipt {
  if (input.status !== 'kernel_verified' || input.verifier !== 'lean-kernel') {
    throw new TypeError('Mathematics helper receipt must be Lean kernel verified');
  }
  if (input.goalsRemaining !== 0 || input.sorryCount !== 0 || input.admitCount !== 0) {
    throw new TypeError('Mathematics helper receipt must have no goals, sorry, or admit');
  }
  if (input.declarationKind !== 'theorem' && input.declarationKind !== 'definition') {
    throw new TypeError('Mathematics helper receipt declarationKind is invalid');
  }
  const axioms = textList(input.axioms, 'helperReceipt.axioms');
  const unsupportedAxioms = axioms.filter((axiom) => !isMathFoundationalLeanAxiom(axiom));
  if (unsupportedAxioms.length) {
    throw new TypeError(
      `Mathematics helper receipt uses non-foundational Lean axioms: ${unsupportedAxioms.join(', ')}`
    );
  }
  if (!Number.isFinite(input.checkedAt) || input.checkedAt <= 0) {
    throw new TypeError('Mathematics helper receipt checkedAt must be a positive timestamp');
  }
  return Object.freeze({
    receiptId: requiredText(input.receiptId, 'helperReceipt.receiptId'),
    targetCommit: requiredGitOid(input.targetCommit, 'helperReceipt.targetCommit'),
    statementHash: requiredHash(input.statementHash, 'helperReceipt.statementHash'),
    routeFingerprint: normalizeMathRouteFingerprint(input.routeFingerprint),
    helperPlanNodeId: normalizeMathPlanNodeId(input.helperPlanNodeId, 'helperReceipt.helperPlanNodeId'),
    parentPlanNodeId: normalizeMathPlanNodeId(input.parentPlanNodeId, 'helperReceipt.parentPlanNodeId'),
    status: 'kernel_verified',
    verifier: 'lean-kernel',
    declarationKind: input.declarationKind,
    declarationName: requiredText(input.declarationName, 'helperReceipt.declarationName'),
    declarationType: requiredText(input.declarationType, 'helperReceipt.declarationType'),
    proofHash: requiredHash(input.proofHash, 'helperReceipt.proofHash'),
    declarationHash: requiredHash(input.declarationHash, 'helperReceipt.declarationHash'),
    ...(optionalText(input.sourceDeclarationHash)
      ? { sourceDeclarationHash: requiredHash(input.sourceDeclarationHash, 'helperReceipt.sourceDeclarationHash') }
      : {}),
    sourceFile: requiredText(input.sourceFile, 'helperReceipt.sourceFile'),
    importModules: requiredTextList(input.importModules, 'helperReceipt.importModules'),
    sourceProvenance: normalizeMathSourceProvenance(input.sourceProvenance, 'helperReceipt.sourceProvenance'),
    goalsRemaining: 0,
    sorryCount: 0,
    admitCount: 0,
    axioms,
    checkedAt: input.checkedAt,
  });
}

export function normalizeMathOfficialGateReceipt(input: MathOfficialGateReceipt): MathOfficialGateReceipt {
  if (input.status !== 'official_verified' || input.verifier !== 'official-comparator') {
    throw new TypeError('Mathematics official gate receipt must be verified by the official comparator');
  }
  if (input.exitCode !== 0 || input.timedOut !== false) {
    throw new TypeError('Mathematics official gate receipt requires exitCode=0 and timedOut=false');
  }
  if (!Number.isFinite(input.durationMs) || input.durationMs < 0) {
    throw new TypeError('Mathematics official gate receipt durationMs must be nonnegative');
  }
  if (!Number.isFinite(input.checkedAt) || input.checkedAt <= 0) {
    throw new TypeError('Mathematics official gate receipt checkedAt must be a positive timestamp');
  }
  const problemId = optionalText(input.problemId);
  const officialManifestPath = optionalText(input.officialManifestPath);
  const officialManifestId = optionalText(input.officialManifestId);
  const officialManifestHash = optionalText(input.officialManifestHash);
  const leanStatementHash = optionalText(input.leanStatementHash);
  return Object.freeze({
    receiptId: requiredText(input.receiptId, 'officialGateReceipt.receiptId'),
    targetCommit: requiredGitOid(input.targetCommit, 'officialGateReceipt.targetCommit'),
    statementHash: requiredHash(input.statementHash, 'officialGateReceipt.statementHash'),
    ...(input.claim ? { claim: input.claim === 'negation' ? 'negation' : 'statement' } : {}),
    routeFingerprint: normalizeMathRouteFingerprint(input.routeFingerprint),
    localGateReceiptId: requiredText(input.localGateReceiptId, 'officialGateReceipt.localGateReceiptId'),
    theoremName: requiredText(input.theoremName, 'officialGateReceipt.theoremName'),
    proofHash: requiredHash(input.proofHash, 'officialGateReceipt.proofHash'),
    theoremDeclarationHash: requiredHash(input.theoremDeclarationHash, 'officialGateReceipt.theoremDeclarationHash'),
    ...(optionalText(input.sourceDeclarationHash)
      ? {
          sourceDeclarationHash: requiredHash(input.sourceDeclarationHash, 'officialGateReceipt.sourceDeclarationHash'),
        }
      : {}),
    status: 'official_verified',
    verifier: 'official-comparator',
    command: requiredText(input.command, 'officialGateReceipt.command'),
    exitCode: 0,
    timedOut: false,
    stdoutSha256: requiredHash(input.stdoutSha256, 'officialGateReceipt.stdoutSha256'),
    stderrSha256: requiredHash(input.stderrSha256, 'officialGateReceipt.stderrSha256'),
    durationMs: input.durationMs,
    checkedAt: input.checkedAt,
    ...(problemId ? { problemId } : {}),
    ...(officialManifestPath ? { officialManifestPath } : {}),
    ...(officialManifestId ? { officialManifestId } : {}),
    ...(officialManifestHash
      ? { officialManifestHash: requiredHash(officialManifestHash, 'officialGateReceipt.officialManifestHash') }
      : {}),
    ...(leanStatementHash
      ? { leanStatementHash: requiredHash(leanStatementHash, 'officialGateReceipt.leanStatementHash') }
      : {}),
    officialRepositoryUrl: requiredText(input.officialRepositoryUrl, 'officialGateReceipt.officialRepositoryUrl'),
    officialBaselineCommit: requiredGitOid(input.officialBaselineCommit, 'officialGateReceipt.officialBaselineCommit'),
    benchmarkAdapterId: requiredText(input.benchmarkAdapterId, 'officialGateReceipt.benchmarkAdapterId'),
    benchmarkAdapterVersion: requiredText(input.benchmarkAdapterVersion, 'officialGateReceipt.benchmarkAdapterVersion'),
    attestation: normalizeMathReceiptAttestation(input.attestation, 'officialGateReceipt.attestation'),
  });
}

/** One fresh semantic review guards statement alignment before the comparator. */
export function aggregateMathCandidateReviews(inputs: readonly MathCandidateReview[]): MathReviewGate {
  if (!Array.isArray(inputs) || inputs.length < 1) {
    throw new TypeError('Mathematics review gate requires one independent review');
  }
  const first = normalizeMathCandidateReview(inputs[0]);
  let statementHashMismatch = false;
  let targetCommitMismatch = false;
  let hasWrong = false;
  let hasGap = false;
  let allSound = true;
  const reviewerSessionIds: string[] = [];
  const localGateReceiptIds: string[] = [];
  const firstFaults: string[] = [];
  const repairTargets: string[] = [];
  const findingSeverities: Record<MathReviewFindingSeverity, number> = {
    blocker: 0,
    major: 0,
    minor: 0,
    note: 0,
  };
  let blockingFindingCount = 0;
  for (let index = 0; index < inputs.length; index += 1) {
    const review = index === 0 ? first : normalizeMathCandidateReview(inputs[index]);
    if (review.problemId !== first.problemId) {
      throw new TypeError('Mathematics reviews must target the same problem');
    }
    if (review.statementHash !== first.statementHash) statementHashMismatch = true;
    if (review.targetCommit !== first.targetCommit) targetCommitMismatch = true;
    reviewerSessionIds.push(review.reviewerSessionId);
    if (review.localGateReceiptId) localGateReceiptIds.push(review.localGateReceiptId);
    if (review.verdict === 'wrong') hasWrong = true;
    if (review.verdict === 'gap') hasGap = true;
    if (review.verdict !== 'sound') allSound = false;
    if (review.firstFault) firstFaults.push(review.firstFault);
    if (review.repairTarget) repairTargets.push(review.repairTarget);
    for (const finding of review.findings ?? []) {
      findingSeverities[finding.severity] += 1;
      if (finding.severity === 'blocker' || finding.severity === 'major') blockingFindingCount += 1;
    }
  }
  if (statementHashMismatch) {
    throw new TypeError('Mathematics reviews must use the same statementHash');
  }
  if (targetCommitMismatch) {
    throw new TypeError('Mathematics reviews must target the same commit');
  }
  if (new Set(reviewerSessionIds).size !== reviewerSessionIds.length) {
    throw new TypeError('Mathematics reviews must come from independent reviewer sessions');
  }
  if (localGateReceiptIds.length > 0 && localGateReceiptIds.length !== inputs.length) {
    throw new TypeError('Mathematics reviews must either all reference a local gate receipt or all omit it');
  }
  if (new Set(localGateReceiptIds).size > 1) {
    throw new TypeError('Mathematics reviews must reference the same local gate receipt');
  }
  const localGateReceiptId = localGateReceiptIds.length === inputs.length ? localGateReceiptIds[0] : undefined;
  const status: MathReviewGateStatus = hasWrong
    ? 'refuted'
    : hasGap
      ? 'changes_requested'
      : allSound
        ? 'passed'
        : 'inconclusive';
  return Object.freeze({
    status,
    canAdvance: status === 'passed' && blockingFindingCount === 0,
    problemId: first.problemId,
    targetCommit: first.targetCommit,
    statementHash: first.statementHash,
    reviewerCount: inputs.length,
    reviewerSessionIds: Object.freeze(reviewerSessionIds),
    ...(localGateReceiptId ? { localGateReceiptId } : {}),
    firstFaults: Object.freeze(firstFaults),
    repairTargets: Object.freeze(repairTargets),
    findingSeverities: Object.freeze(findingSeverities),
    blockingFindingCount,
  });
}

export function normalizeMathFailureLedger(input: MathFailureLedger): MathFailureLedger {
  if (!MATH_PROOF_STAGES.includes(input.stage)) throw new TypeError('Mathematics failure ledger stage is invalid');
  if (!MATH_FAILURE_CATEGORIES.includes(input.failureCategory)) {
    throw new TypeError('Mathematics failure ledger category is invalid');
  }
  const activeRoute = normalizeMathRouteFingerprint(input.activeRoute);
  const triedRoutes = uniqueMathRouteFingerprints(input.triedRoutes);
  if (!triedRoutes.includes(activeRoute)) {
    throw new TypeError('Mathematics failure ledger triedRoutes must include activeRoute');
  }
  let triedRouteStructureSignatures: readonly string[] | undefined;
  if (input.triedRouteStructureSignatures) {
    const signatures: string[] = [];
    const seenSignatures = new Set<string>();
    for (let index = 0; index < input.triedRouteStructureSignatures.length; index += 1) {
      const signature = boundedRequiredText(
        input.triedRouteStructureSignatures[index],
        `failureLedger.triedRouteStructureSignatures[${index}]`,
        4000
      );
      if (seenSignatures.has(signature)) continue;
      seenSignatures.add(signature);
      signatures.push(signature);
    }
    triedRouteStructureSignatures = Object.freeze(signatures);
  }
  const activePlanNodeId = input.activePlanNodeId
    ? normalizeMathPlanNodeId(input.activePlanNodeId, 'failureLedger.activePlanNodeId')
    : undefined;
  const proofStateFingerprint = optionalText(input.proofStateFingerprint);
  const progressFingerprint = optionalText(input.progressFingerprint);
  const verifiedPlanNodeIds = input.verifiedPlanNodeIds
    ? normalizeMathPlanNodeIds(input.verifiedPlanNodeIds, 'failureLedger.verifiedPlanNodeIds')
    : undefined;
  const semiProofCheckpoint = input.semiProofCheckpoint
    ? normalizeMathSemiProofCheckpoint(input.semiProofCheckpoint)
    : undefined;
  if (semiProofCheckpoint && semiProofCheckpoint.routeFingerprint !== activeRoute) {
    throw new TypeError('Mathematics semi-proof checkpoint must match failureLedger.activeRoute');
  }
  if (semiProofCheckpoint) {
    const verifiedPlanNodeIdSet = new Set(verifiedPlanNodeIds ?? []);
    if (
      verifiedPlanNodeIdSet.size !== semiProofCheckpoint.verifiedLemmas.length ||
      semiProofCheckpoint.verifiedLemmas.some((lemma) => !verifiedPlanNodeIdSet.has(lemma.planNodeId))
    ) {
      throw new TypeError('Mathematics semi-proof checkpoint must record every verifiedPlanNodeId');
    }
    if (!activePlanNodeId || !semiProofCheckpoint.repairFrontierNodeIds.includes(activePlanNodeId)) {
      throw new TypeError('Mathematics activePlanNodeId must belong to the semi-proof repair frontier');
    }
  }
  return Object.freeze({
    stage: input.stage,
    statementHash: requiredHash(input.statementHash, 'failureLedger.statementHash'),
    activeRoute,
    triedRoutes,
    ...(triedRouteStructureSignatures ? { triedRouteStructureSignatures } : {}),
    ...(activePlanNodeId ? { activePlanNodeId } : {}),
    ...(proofStateFingerprint ? { proofStateFingerprint } : {}),
    ...(progressFingerprint
      ? { progressFingerprint: requiredHash(progressFingerprint, 'failureLedger.progressFingerprint') }
      : {}),
    ...(verifiedPlanNodeIds ? { verifiedPlanNodeIds } : {}),
    ...(semiProofCheckpoint ? { semiProofCheckpoint } : {}),
    ...(optionalText(input.firstLeanError) ? { firstLeanError: optionalText(input.firstLeanError) } : {}),
    ...(optionalText(input.latestReceipt) ? { latestReceipt: optionalText(input.latestReceipt) } : {}),
    nextSingleObjective: requiredText(input.nextSingleObjective, 'failureLedger.nextSingleObjective'),
    failureCategory: input.failureCategory,
    doNotRepeatRefs: textList(input.doNotRepeatRefs, 'failureLedger.doNotRepeatRefs'),
  });
}

export function normalizeMathRecoveryCheckpoint(input: MathRecoveryCheckpoint): MathRecoveryCheckpoint {
  if (!Number.isFinite(input.updatedAt) || input.updatedAt <= 0) {
    throw new TypeError('Mathematics recovery checkpoint updatedAt must be a positive timestamp');
  }
  const ledger = normalizeMathFailureLedger(input.ledger);
  const targetCommit = requiredGitOid(input.targetCommit, 'recoveryCheckpoint.targetCommit');
  if (ledger.semiProofCheckpoint && ledger.semiProofCheckpoint.targetCommit !== targetCommit) {
    throw new TypeError('Mathematics semi-proof checkpoint must match recoveryCheckpoint.targetCommit');
  }
  const proofPlan = input.proofPlan ? normalizeMathProofPlan(input.proofPlan) : undefined;
  const proofState = input.proofState ? normalizeMathProofState(input.proofState) : undefined;
  if (
    proofPlan &&
    (proofPlan.statementHash !== ledger.statementHash || proofPlan.routeFingerprint !== ledger.activeRoute)
  ) {
    throw new TypeError('Mathematics recovery proofPlan must match the failure ledger identity');
  }
  if (
    proofState &&
    (proofState.statementHash !== ledger.statementHash || proofState.routeFingerprint !== ledger.activeRoute)
  ) {
    throw new TypeError('Mathematics recovery proofState must match the failure ledger identity');
  }
  if (proofPlan && proofState?.planId && proofState.planId !== proofPlan.planId) {
    throw new TypeError('Mathematics recovery proofState.planId must match proofPlan.planId');
  }
  return Object.freeze({
    checkpointId: requiredText(input.checkpointId, 'recoveryCheckpoint.checkpointId'),
    targetCommit,
    updatedAt: input.updatedAt,
    ledger,
    ...(proofPlan ? { proofPlan } : {}),
    ...(proofState ? { proofState } : {}),
  });
}

export function normalizeMathSemiProofCheckpoint(input: MathSemiProofCheckpoint): MathSemiProofCheckpoint {
  if (!Array.isArray(input.verifiedLemmas) || input.verifiedLemmas.length < 1 || input.verifiedLemmas.length > 128) {
    throw new TypeError('Mathematics semi-proof checkpoint must retain between 1 and 128 verified lemmas');
  }
  const verifiedNodeIdSet = new Set<string>();
  const theoremNameSet = new Set<string>();
  const verifiedLemmas = input.verifiedLemmas.map((lemma, index) => {
    const normalized = normalizeMathVerifiedLemma(lemma, `semiProofCheckpoint.verifiedLemmas[${index}]`);
    verifiedNodeIdSet.add(normalized.planNodeId);
    theoremNameSet.add(normalized.theoremName);
    return normalized;
  });
  if (verifiedNodeIdSet.size !== verifiedLemmas.length) {
    throw new TypeError('Mathematics semi-proof checkpoint verified plan nodes must be unique');
  }
  if (theoremNameSet.size !== verifiedLemmas.length) {
    throw new TypeError('Mathematics semi-proof checkpoint theorem names must be unique');
  }
  const firstIncompatibleNodeId = normalizeMathPlanNodeId(
    input.firstIncompatibleNodeId,
    'semiProofCheckpoint.firstIncompatibleNodeId'
  );
  const repairFrontierNodeIds = normalizeMathPlanNodeIds(
    input.repairFrontierNodeIds,
    'semiProofCheckpoint.repairFrontierNodeIds'
  );
  if (repairFrontierNodeIds.length === 0 || !repairFrontierNodeIds.includes(firstIncompatibleNodeId)) {
    throw new TypeError('Mathematics semi-proof repair frontier must include the first incompatible node');
  }
  const discardedNodeIds = normalizeMathPlanNodeIds(input.discardedNodeIds, 'semiProofCheckpoint.discardedNodeIds');
  if (!discardedNodeIds.includes(firstIncompatibleNodeId)) {
    throw new TypeError('Mathematics semi-proof discarded nodes must include the first incompatible node');
  }
  if (discardedNodeIds.some((nodeId) => verifiedNodeIdSet.has(nodeId))) {
    throw new TypeError('Mathematics semi-proof verified and discarded nodes must be disjoint');
  }
  if (!Number.isFinite(input.checkedAt) || input.checkedAt <= 0) {
    throw new TypeError('Mathematics semi-proof checkpoint checkedAt must be a positive timestamp');
  }
  return Object.freeze({
    routeFingerprint: normalizeMathRouteFingerprint(input.routeFingerprint),
    targetCommit: requiredGitOid(input.targetCommit, 'semiProofCheckpoint.targetCommit'),
    verifiedLemmas: Object.freeze(verifiedLemmas),
    firstIncompatibleNodeId,
    repairFrontierNodeIds,
    discardedNodeIds,
    resumeObjective: requiredText(input.resumeObjective, 'semiProofCheckpoint.resumeObjective'),
    checkedAt: input.checkedAt,
  });
}

export function mathVerifiedLemmaToPremiseCandidate(
  lemma: MathVerifiedLemma,
  sourceCommit: string,
  intendedUse: string
): MathPremiseCandidate {
  const normalized = normalizeMathVerifiedLemma(lemma, 'verifiedLemma');
  const normalizedSourceCommit = requiredGitOid(sourceCommit, 'verifiedLemma.sourceCommit');
  return Object.freeze({
    declarationName: normalized.theoremName,
    declarationType: normalized.theoremStatement,
    sourceKind: 'verified_local',
    sourceCommit: normalizedSourceCommit,
    sourceFile: normalized.sourceFile,
    proofHash: normalized.proofHash,
    importModules: normalized.importModules,
    checkedAtCommit: normalizedSourceCommit,
    intendedUse: requiredText(intendedUse, 'verifiedLemma.intendedUse'),
    status: 'typed',
    evidenceRefs: normalized.evidenceRefs,
  });
}

const normalizedMathProgressDeltas = new WeakSet<MathProgressDelta>();

export function normalizeMathProgressDelta(input: MathProgressDelta): MathProgressDelta {
  if (normalizedMathProgressDeltas.has(input)) return input;
  const statementHash = requiredHash(input.statementHash, 'statementHash');
  const routeFingerprint = normalizeMathRouteFingerprint(input.routeFingerprint);
  const executionPolicy = input.executionPolicy ? normalizeMathExecutionPolicy(input.executionPolicy) : undefined;
  const activePlanNodeId = input.activePlanNodeId
    ? normalizeMathPlanNodeId(input.activePlanNodeId, 'activePlanNodeId')
    : undefined;
  const planBefore = input.planBefore ? normalizeMathPlanSnapshot(input.planBefore) : undefined;
  const planAfter = input.planAfter ? normalizeMathPlanSnapshot(input.planAfter) : undefined;
  const planExpansion = input.planExpansion ? normalizeMathPlanExpansion(input.planExpansion) : undefined;
  if (Boolean(planBefore) !== Boolean(planAfter)) {
    throw new TypeError('Mathematics progress must provide both planBefore and planAfter');
  }
  if (planExpansion && (!planBefore || !planAfter)) {
    throw new TypeError('Mathematics planExpansion requires planBefore and planAfter');
  }
  const verifiedPlanNodeIdsAdded = input.verifiedPlanNodeIdsAdded
    ? normalizeMathPlanNodeIds(input.verifiedPlanNodeIdsAdded, 'verifiedPlanNodeIdsAdded')
    : undefined;
  const sourceProgress = input.sourceProgress ? normalizeMathSourceProgress(input.sourceProgress) : undefined;
  if (planBefore && planAfter) {
    const verifiedNodeIdsAdded = assertMathPlanSnapshotTransition(planBefore, planAfter, planExpansion);
    const verifiedPlanNodeIdsAddedSet = new Set(verifiedPlanNodeIdsAdded ?? []);
    if (
      verifiedPlanNodeIdsAddedSet.size !== verifiedNodeIdsAdded.length ||
      verifiedNodeIdsAdded.some((nodeId) => !verifiedPlanNodeIdsAddedSet.has(nodeId))
    ) {
      throw new TypeError('Mathematics verifiedPlanNodeIdsAdded must equal the plan snapshot delta');
    }
    if (
      activePlanNodeId &&
      !planBefore.openFrontierNodeIds.includes(activePlanNodeId) &&
      !planAfter.openFrontierNodeIds.includes(activePlanNodeId)
    ) {
      throw new TypeError('Mathematics activePlanNodeId must be actionable in planBefore or planAfter');
    }
  }
  const checkedDeclarationsAdded = nonnegativeInteger(input.checkedDeclarationsAdded, 'checkedDeclarationsAdded');
  const openGoalCountBefore = nonnegativeInteger(input.openGoalCountBefore, 'openGoalCountBefore');
  const openGoalCountAfter = nonnegativeInteger(input.openGoalCountAfter, 'openGoalCountAfter');
  const firstLeanErrorOffsetBefore = optionalNonnegativeInteger(
    input.firstLeanErrorOffsetBefore,
    'firstLeanErrorOffsetBefore'
  );
  const firstLeanErrorOffsetAfter = optionalNonnegativeInteger(
    input.firstLeanErrorOffsetAfter,
    'firstLeanErrorOffsetAfter'
  );
  const firstLeanErrorBefore = optionalText(input.firstLeanErrorBefore);
  const firstLeanErrorAfter = optionalText(input.firstLeanErrorAfter);
  const openGoalFingerprintBefore = optionalText(input.openGoalFingerprintBefore);
  const openGoalFingerprintAfter = optionalText(input.openGoalFingerprintAfter);
  const openGoalAfter = optionalText(input.openGoalAfter);
  if (openGoalAfter && openGoalCountAfter === 0) {
    throw new TypeError('Mathematics openGoalAfter requires at least one remaining goal');
  }
  const wholeProofProbe = input.wholeProofProbe
    ? normalizeMathWholeProofProbe(
        input.wholeProofProbe,
        planBefore,
        planAfter,
        openGoalCountAfter,
        firstLeanErrorAfter,
        firstLeanErrorOffsetAfter
      )
    : undefined;
  const evidenceDelta = Object.freeze(
    (input.evidenceDelta || []).map((item, index) => freezeEvidenceDelta(item, index))
  );
  if (!MATH_ROUTE_DISPOSITIONS.includes(input.routeDisposition)) {
    throw new TypeError('Mathematics routeDisposition is invalid');
  }
  if (!MATH_INFRA_STATUSES.includes(input.infraStatus)) {
    throw new TypeError('Mathematics infraStatus is invalid');
  }
  if (input.reviewAction !== undefined && !MATH_REVIEW_ACTIONS.includes(input.reviewAction)) {
    throw new TypeError('Mathematics reviewAction is invalid');
  }

  const normalized = Object.freeze({
    statementHash,
    routeFingerprint,
    ...(executionPolicy ? { executionPolicy } : {}),
    ...(input.progressFingerprint
      ? { progressFingerprint: requiredHash(input.progressFingerprint, 'mathProgress.progressFingerprint') }
      : {}),
    ...(input.failureCategory
      ? MATH_FAILURE_CATEGORIES.includes(input.failureCategory)
        ? { failureCategory: input.failureCategory }
        : (() => {
            throw new TypeError('Mathematics progress failureCategory is invalid');
          })()
      : {}),
    ...(activePlanNodeId ? { activePlanNodeId } : {}),
    ...(planBefore ? { planBefore } : {}),
    ...(planAfter ? { planAfter } : {}),
    ...(planExpansion ? { planExpansion } : {}),
    ...(verifiedPlanNodeIdsAdded ? { verifiedPlanNodeIdsAdded } : {}),
    ...(sourceProgress ? { sourceProgress } : {}),
    checkedDeclarationsAdded,
    ...(openGoalFingerprintBefore ? { openGoalFingerprintBefore } : {}),
    ...(openGoalFingerprintAfter ? { openGoalFingerprintAfter } : {}),
    openGoalCountBefore,
    openGoalCountAfter,
    ...(openGoalAfter ? { openGoalAfter: boundedRequiredText(openGoalAfter, 'openGoalAfter', 4000) } : {}),
    ...(firstLeanErrorBefore ? { firstLeanErrorBefore } : {}),
    ...(firstLeanErrorAfter ? { firstLeanErrorAfter } : {}),
    ...(firstLeanErrorOffsetBefore !== undefined ? { firstLeanErrorOffsetBefore } : {}),
    ...(firstLeanErrorOffsetAfter !== undefined ? { firstLeanErrorOffsetAfter } : {}),
    ...(wholeProofProbe ? { wholeProofProbe } : {}),
    evidenceDelta,
    routeDisposition: input.routeDisposition,
    ...(input.reviewAction ? { reviewAction: input.reviewAction } : {}),
    nextSingleObjective: requiredText(input.nextSingleObjective, 'nextSingleObjective'),
    infraStatus: input.infraStatus,
  });
  normalizedMathProgressDeltas.add(normalized);
  return normalized;
}

function normalizeMathSourceProgress(input: MathSourceProgress): MathSourceProgress {
  if (!input || typeof input !== 'object') {
    throw new TypeError('Mathematics sourceProgress is invalid');
  }
  const artifactPath = requiredText(input.artifactPath, 'sourceProgress.artifactPath').replaceAll('\\', '/');
  const pathWithoutSelector = artifactPath.split('#', 1)[0]!.trim();
  if (
    !pathWithoutSelector ||
    pathWithoutSelector.startsWith('/') ||
    pathWithoutSelector.split('/').includes('..') ||
    !pathWithoutSelector.toLowerCase().endsWith('.lean')
  ) {
    throw new TypeError('Mathematics sourceProgress.artifactPath must be a project-relative Lean path');
  }
  if (!Array.isArray(input.changedDeclarationNames) || input.changedDeclarationNames.length < 1) {
    throw new TypeError('Mathematics sourceProgress.changedDeclarationNames must be non-empty');
  }
  if (input.changedDeclarationNames.length > 128) {
    throw new TypeError('Mathematics sourceProgress.changedDeclarationNames is too large');
  }
  const names = input.changedDeclarationNames.map((name, index) => {
    const normalized = requiredText(name, `sourceProgress.changedDeclarationNames[${index}]`);
    if (!/^[A-Za-z_][A-Za-z0-9_'.]*$/u.test(normalized)) {
      throw new TypeError('Mathematics sourceProgress declaration name is invalid');
    }
    return normalized;
  });
  if (new Set(names).size !== names.length) {
    throw new TypeError('Mathematics sourceProgress declaration names must be unique');
  }
  const baseSourceHash = requiredHash(input.baseSourceHash, 'sourceProgress.baseSourceHash');
  const candidateSourceHash = requiredHash(input.candidateSourceHash, 'sourceProgress.candidateSourceHash');
  if (baseSourceHash === candidateSourceHash) {
    throw new TypeError('Mathematics sourceProgress requires a changed source hash');
  }
  return Object.freeze({
    artifactPath,
    changedDeclarationNames: Object.freeze(names),
    baseSourceHash,
    candidateSourceHash,
  });
}

export function normalizeMathPlanExpansion(input: MathPlanExpansion): MathPlanExpansion {
  const addedNodes = normalizeMathPlanNodes(input.addedNodes);
  if (addedNodes.length < 1 || addedNodes.length > 16) {
    throw new TypeError('Mathematics planExpansion must add between 1 and 16 nodes');
  }
  return Object.freeze({
    expandedNodeId: normalizeMathPlanNodeId(input.expandedNodeId, 'planExpansion.expandedNodeId'),
    addedNodes,
    reason: requiredText(input.reason, 'planExpansion.reason'),
    evidenceRefs: requiredTextList(input.evidenceRefs, 'planExpansion.evidenceRefs'),
  });
}

export function classifyMathProgress(
  input: MathProgressDelta,
  evidence: MathProgressEvidenceContext = {}
): MathProgressOutcome {
  const delta = normalizeMathProgressDelta(input);
  if (delta.infraStatus !== 'ready') return 'infra_failed';
  if (delta.openGoalCountAfter > delta.openGoalCountBefore) return 'regressed';

  const firstErrorAdvanced =
    delta.firstLeanErrorBefore !== undefined &&
    delta.firstLeanErrorAfter === undefined &&
    delta.openGoalCountAfter <= delta.openGoalCountBefore;
  const evidenceKinds = summarizeMathEvidenceDeltaKinds(delta.evidenceDelta);
  const strictRouteRefutation = delta.routeDisposition === 'reject' && evidenceKinds.routeRefutation;
  const boundedCounterexampleEvidence = delta.routeDisposition === 'reject' && evidenceKinds.counterexampleProbe;
  const verifiedLibraryFact = evidenceKinds.mathlibDeclaration;
  const kernelClaim =
    delta.checkedDeclarationsAdded > 0 ||
    Boolean(delta.verifiedPlanNodeIdsAdded?.length) ||
    evidenceKinds.kernelDeclaration ||
    evidenceKinds.helperDeclaration;
  const sourceProgress = Boolean(delta.sourceProgress?.changedDeclarationNames.length);
  // The standalone classifier retains its historical semantic behavior for
  // trusted callers. Runtime Team validation passes kernelReceiptBound=false
  // for an untrusted Lean Worker, so self-reported declaration counts cannot
  // advance the frontier without a receipt.
  const kernelProgress = kernelClaim && evidence.kernelReceiptBound !== false;

  const proofStateChanged =
    delta.openGoalFingerprintBefore !== undefined &&
    delta.openGoalFingerprintAfter !== undefined &&
    delta.openGoalFingerprintBefore !== delta.openGoalFingerprintAfter;

  return kernelProgress ||
    delta.openGoalCountAfter < delta.openGoalCountBefore ||
    firstErrorAdvanced ||
    proofStateChanged ||
    Boolean(delta.planExpansion) ||
    strictRouteRefutation ||
    boundedCounterexampleEvidence ||
    evidenceKinds.researchInformation ||
    verifiedLibraryFact ||
    sourceProgress
    ? 'advanced'
    : 'stalled';
}

/**
 * Do not let a discovered mathlib declaration reset FORMALIZE stall counters.
 * The legacy classifier remains available for compatibility; scheduling uses
 * this stricter semantic classification.
 */
export function classifyMathProgressKind(
  input: MathProgressDelta,
  evidence: MathProgressEvidenceContext = {}
): MathProgressKind {
  const delta = normalizeMathProgressDelta(input);
  return classifyMathProgressKindNormalized(delta, evidence);
}

function classifyMathProgressKindNormalized(
  delta: MathProgressDelta,
  evidence: MathProgressEvidenceContext
): MathProgressKind {
  if (delta.infraStatus !== 'ready') return 'infra_progress';
  const evidenceKinds = summarizeMathEvidenceDeltaKinds(delta.evidenceDelta);
  if (
    delta.checkedDeclarationsAdded > 0 ||
    Boolean(delta.verifiedPlanNodeIdsAdded?.length) ||
    evidenceKinds.kernelDeclaration ||
    evidenceKinds.helperDeclaration
  ) {
    if (evidence.kernelReceiptBound === false) return 'none';
    return evidenceKinds.helperDeclaration ? 'foundation_progress' : 'kernel_progress';
  }
  // Runtime source comparison can establish that a declaration body changed
  // even when the global proof-state count is unchanged. This is useful for
  // accumulating disjoint declaration work, but it is intentionally not a
  // kernel-progress claim.
  if (delta.sourceProgress?.changedDeclarationNames.length) return 'goal_progress';
  const planExpansion = delta.planExpansion || evidenceKinds.planExpansion;
  if (planExpansion) {
    // A Worker can add arbitrary DAG prose without executing Lean.  The public
    // classifier keeps its historical behavior, but the runtime scheduler opts
    // into this stricter gate so a plan-only loop cannot reset FORMALIZE stalls.
    const hasKernelReceipt =
      Boolean(delta.verifiedPlanNodeIdsAdded?.length) ||
      evidenceKinds.kernelDeclaration ||
      evidenceKinds.helperDeclaration;
    if (evidence.requireKernelReceiptForPlanExpansion && !hasKernelReceipt) return 'none';
    return 'foundation_progress';
  }
  if (
    delta.openGoalCountAfter < delta.openGoalCountBefore ||
    (delta.firstLeanErrorBefore !== undefined &&
      (delta.firstLeanErrorAfter === undefined ||
        (delta.firstLeanErrorOffsetBefore !== undefined &&
          delta.firstLeanErrorOffsetAfter !== undefined &&
          delta.firstLeanErrorOffsetAfter > delta.firstLeanErrorOffsetBefore))) ||
    (delta.openGoalFingerprintBefore !== undefined &&
      delta.openGoalFingerprintAfter !== undefined &&
      delta.openGoalFingerprintBefore !== delta.openGoalFingerprintAfter)
  ) {
    return 'goal_progress';
  }
  if (delta.routeDisposition === 'reject' && evidenceKinds.routeRefutation) {
    return 'route_information';
  }
  if (delta.routeDisposition === 'reject' && evidenceKinds.counterexampleProbe) {
    return 'route_information';
  }
  if (evidenceKinds.researchInformation) return 'research_information';
  if (evidenceKinds.mathlibDeclaration) return 'library_discovery';
  return 'none';
}

function summarizeMathEvidenceDeltaKinds(evidenceDelta: readonly MathEvidenceDelta[]): Readonly<{
  kernelDeclaration: boolean;
  helperDeclaration: boolean;
  mathlibDeclaration: boolean;
  planExpansion: boolean;
  upstreamSource: boolean;
  routeRefutation: boolean;
  counterexampleProbe: boolean;
  researchInformation: boolean;
}> {
  let kernelDeclaration = false;
  let helperDeclaration = false;
  let mathlibDeclaration = false;
  let planExpansion = false;
  let upstreamSource = false;
  let routeRefutation = false;
  let counterexampleProbe = false;
  let researchInformation = false;
  for (const item of evidenceDelta) {
    if (item.kind === 'kernel_declaration') kernelDeclaration = true;
    else if (item.kind === 'helper_declaration') helperDeclaration = true;
    else if (item.kind === 'mathlib_declaration') mathlibDeclaration = true;
    else if (item.kind === 'plan_expansion') planExpansion = true;
    else if (item.kind === 'upstream_source') upstreamSource = true;
    else if (item.kind === 'route_refutation') routeRefutation = true;
    else if (item.kind === 'counterexample_probe') counterexampleProbe = true;
    else researchInformation = true;
  }
  return {
    kernelDeclaration,
    helperDeclaration,
    mathlibDeclaration,
    planExpansion,
    upstreamSource,
    routeRefutation,
    counterexampleProbe,
    researchInformation,
  };
}

function hasMainlineFrontierProgress(delta: MathProgressDelta): boolean {
  if (delta.openGoalCountAfter < delta.openGoalCountBefore) return true;
  if (
    delta.firstLeanErrorBefore !== undefined &&
    (delta.firstLeanErrorAfter === undefined ||
      (delta.firstLeanErrorOffsetBefore !== undefined &&
        delta.firstLeanErrorOffsetAfter !== undefined &&
        delta.firstLeanErrorOffsetAfter > delta.firstLeanErrorOffsetBefore))
  ) {
    return true;
  }
  if (
    delta.openGoalFingerprintBefore !== undefined &&
    delta.openGoalFingerprintAfter !== undefined &&
    delta.openGoalFingerprintBefore !== delta.openGoalFingerprintAfter
  ) {
    return true;
  }
  return Boolean(delta.activePlanNodeId && delta.verifiedPlanNodeIdsAdded?.includes(delta.activePlanNodeId));
}

export function updateMathProgressState(
  stage: MathProofStage,
  previousConsecutiveStalls: number,
  input: MathProgressDelta,
  cost: MathProgressCost = {},
  evidence: MathProgressEvidenceContext = {}
): MathProgressState {
  if (!MATH_PROOF_STAGES.includes(stage)) throw new TypeError('Mathematics proof stage is invalid');
  const priorStalls = nonnegativeInteger(previousConsecutiveStalls, 'previousConsecutiveStalls');
  const delta = normalizeMathProgressDelta(input);
  const semanticKind = classifyMathProgressKindNormalized(delta, evidence);
  const evidenceKinds = summarizeMathEvidenceDeltaKinds(delta.evidenceDelta);
  const scaffoldOnly =
    semanticKind === 'foundation_progress' && evidenceKinds.helperDeclaration && !hasMainlineFrontierProgress(delta);
  const priorScaffoldOnlyStreak = nonnegativeInteger(
    evidence.previousScaffoldOnlyStreak ?? 0,
    'previousScaffoldOnlyStreak'
  );
  const scaffoldOnlyStreak = scaffoldOnly ? priorScaffoldOnlyStreak + 1 : 0;
  const outcome: MathProgressOutcome =
    semanticKind === 'infra_progress'
      ? 'infra_failed'
      : !scaffoldOnly &&
          (semanticKind === 'kernel_progress' ||
            semanticKind === 'foundation_progress' ||
            semanticKind === 'goal_progress' ||
            semanticKind === 'route_information' ||
            semanticKind === 'research_information')
        ? 'advanced'
        : delta.openGoalCountAfter > delta.openGoalCountBefore
          ? 'regressed'
          : 'stalled';
  const consecutiveStalls = outcome === 'stalled' ? priorStalls + 1 : outcome === 'infra_failed' ? priorStalls : 0;
  const costPressure = classifyMathCostPressure(cost, delta);
  const directive = deriveMathProgressDirective(delta, outcome, consecutiveStalls, costPressure, scaffoldOnlyStreak);
  return Object.freeze({
    outcome,
    consecutiveStalls,
    directive,
    costPressure,
    nextStage: directive === 're_decompose' ? 'replan' : stage,
    // Preserve the legacy state shape for ordinary progress. Scaffold is the
    // scheduler-significant case that must survive into the next assignment.
    ...(scaffoldOnly || scaffoldOnlyStreak > 0 ? { progressKind: semanticKind } : {}),
    ...(scaffoldOnlyStreak > 0 ? { scaffoldOnlyStreak } : {}),
  });
}

function classifyMathCostPressure(cost: MathProgressCost, delta: MathProgressDelta): MathCostPressure {
  const assignmentElapsedMs = optionalNonnegativeInteger(cost.assignmentElapsedMs, 'assignmentElapsedMs') ?? 0;
  const tokensUsed = optionalNonnegativeInteger(cost.tokensUsed, 'tokensUsed') ?? 0;
  optionalNonnegativeInteger(cost.leanExecutionCount, 'leanExecutionCount');
  const madeProgress =
    delta.openGoalCountAfter < delta.openGoalCountBefore ||
    Boolean(delta.verifiedPlanNodeIdsAdded?.length) ||
    delta.checkedDeclarationsAdded > 0 ||
    Boolean(delta.sourceProgress?.changedDeclarationNames.length);
  if (!madeProgress && (tokensUsed >= 15_000 || assignmentElapsedMs >= 15 * 60_000)) return 'high';
  if (!madeProgress && (tokensUsed >= 8_000 || assignmentElapsedMs >= 5 * 60_000)) return 'meaningful';
  return 'low';
}

function deriveMathProgressDirective(
  delta: MathProgressDelta,
  outcome: MathProgressOutcome,
  consecutiveStalls: number,
  costPressure: MathCostPressure,
  scaffoldOnlyStreak = 0
): MathProgressDirective {
  if (outcome === 'infra_failed') return 'retry_infrastructure';
  if (delta.routeDisposition === 'reject' || delta.routeDisposition === 'duplicate') return 're_decompose';

  const leanFailureKind =
    delta.wholeProofProbe?.failureKind ??
    (delta.firstLeanErrorAfter ? classifyMathLeanFailure(delta.firstLeanErrorAfter) : undefined);
  const structuralFailure =
    ['declaration_rejected', 'termination_failed'].includes(leanFailureKind ?? '') ||
    ['actual_proof_failure', 'missing_hole', 'wrong_statement', 'counterexample'].includes(delta.failureCategory ?? '');
  if (structuralFailure) return 're_decompose';
  // Lean executed successfully here: heartbeat, recursion-depth, and memory
  // diagnostics describe an over-expensive candidate, not unavailable
  // infrastructure. Keep the candidate local so its proof term or tactic
  // family can be simplified before opening another route.
  if (leanFailureKind === 'timeout_or_resource') return 'continue_node';
  if (scaffoldOnlyStreak >= 2) return 're_decompose';

  const activeNodeCompleted = Boolean(
    delta.activePlanNodeId && delta.verifiedPlanNodeIdsAdded?.includes(delta.activePlanNodeId)
  );
  const evidenceKinds = summarizeMathEvidenceDeltaKinds(delta.evidenceDelta);
  if (evidenceKinds.helperDeclaration) return 'promote_helper';
  if (evidenceKinds.upstreamSource) return 'port_upstream';
  if (delta.planExpansion || evidenceKinds.planExpansion) return 'expand_node';
  const alternateFrontierCount = delta.planAfter
    ? delta.planAfter.openFrontierNodeIds.filter((nodeId) => nodeId !== delta.activePlanNodeId).length
    : 0;
  if (outcome === 'advanced') {
    return activeNodeCompleted && alternateFrontierCount > 0 ? 'switch_node' : 'continue_node';
  }
  if (outcome === 'regressed') return alternateFrontierCount > 0 ? 'switch_node' : 're_decompose';

  if (consecutiveStalls >= 2 || costPressure === 'high') return 'expand_node';
  return 'continue_node';
}

export function normalizeMathRouteFingerprint(value: string): string {
  const normalized = requiredText(value, 'routeFingerprint').toLowerCase().replace(/\s+/gu, ' ');
  if (normalized.length > 512) throw new TypeError('Mathematics routeFingerprint is too long');
  return normalized;
}

export function uniqueMathRouteFingerprints(values: readonly string[]): readonly string[] {
  if (!Array.isArray(values)) throw new TypeError('Mathematics route fingerprints must be an array');
  const unique = new Set<string>();
  for (const value of values) unique.add(normalizeMathRouteFingerprint(value));
  return Object.freeze([...unique]);
}

function normalizeMathPlanNodes(values: readonly MathPlanNode[]): readonly MathPlanNode[] {
  if (!Array.isArray(values) || values.length < 1 || values.length > 128) {
    throw new TypeError('Mathematics routeCard.planNodes must contain between 1 and 128 nodes');
  }
  const nodeIds = new Set<string>();
  const normalized = values.map((node, index) => {
    if (!MATH_PLAN_NODE_ROLES.includes(node.role)) {
      throw new TypeError(`Mathematics routeCard.planNodes[${index}].role is invalid`);
    }
    if (!MATH_PLAN_NODE_STATUSES.includes(node.status)) {
      throw new TypeError(`Mathematics routeCard.planNodes[${index}].status is invalid`);
    }
    if (node.kind !== undefined && !MATH_PLAN_NODE_KINDS.includes(node.kind)) {
      throw new TypeError(`Mathematics routeCard.planNodes[${index}].kind is invalid`);
    }
    const evidenceRefs = textList(node.evidenceRefs, `routeCard.planNodes[${index}].evidenceRefs`);
    if (node.status !== 'proposed' && evidenceRefs.length === 0) {
      throw new TypeError(`Mathematics routeCard.planNodes[${index}] checked status requires evidenceRefs`);
    }
    const id = normalizeMathPlanNodeId(node.id, `routeCard.planNodes[${index}].id`);
    if (nodeIds.has(id)) {
      throw new TypeError('Mathematics routeCard.planNodes must use unique ids');
    }
    nodeIds.add(id);
    const parentNodeId = node.parentNodeId
      ? normalizeMathPlanNodeId(node.parentNodeId, `routeCard.planNodes[${index}].parentNodeId`)
      : undefined;
    const estimatedEffort =
      node.estimatedEffort === undefined
        ? undefined
        : boundedRating(node.estimatedEffort, `routeCard.planNodes[${index}].estimatedEffort`);
    const downstreamValue =
      node.downstreamValue === undefined
        ? undefined
        : boundedRating(node.downstreamValue, `routeCard.planNodes[${index}].downstreamValue`);
    const successProbability = node.successProbability;
    if (
      successProbability !== undefined &&
      (!Number.isFinite(successProbability) || successProbability < 0 || successProbability > 1)
    ) {
      throw new TypeError(`Mathematics routeCard.planNodes[${index}].successProbability must be in [0,1]`);
    }
    const sourceProvenance = node.sourceProvenance
      ? normalizeMathSourceProvenance(node.sourceProvenance, `routeCard.planNodes[${index}].sourceProvenance`)
      : undefined;
    const proofSkeleton = optionalText(node.proofSkeleton);
    const expectedProgress = optionalText(node.expectedProgress);
    const successCriteria = node.successCriteria
      ? requiredTextList(node.successCriteria, `routeCard.planNodes[${index}].successCriteria`)
      : undefined;
    const fallbackNodeIds = node.fallbackNodeIds
      ? normalizeMathPlanNodeIds(node.fallbackNodeIds, `routeCard.planNodes[${index}].fallbackNodeIds`)
      : undefined;
    const mechanism = node.mechanism;
    if (mechanism !== undefined && !MATH_PROOF_PLAN_MECHANISMS.includes(mechanism)) {
      throw new TypeError(`Mathematics routeCard.planNodes[${index}].mechanism is invalid`);
    }
    return Object.freeze({
      id,
      informalClaim: requiredText(node.informalClaim, `routeCard.planNodes[${index}].informalClaim`),
      provisionalLeanStatement: requiredText(
        node.provisionalLeanStatement,
        `routeCard.planNodes[${index}].provisionalLeanStatement`
      ),
      dependsOn: normalizeMathPlanNodeIds(node.dependsOn, `routeCard.planNodes[${index}].dependsOn`),
      role: node.role,
      status: node.status,
      evidenceRefs,
      ...(parentNodeId ? { parentNodeId } : {}),
      ...(node.kind ? { kind: node.kind } : {}),
      ...(estimatedEffort !== undefined ? { estimatedEffort } : {}),
      ...(successProbability !== undefined ? { successProbability } : {}),
      ...(downstreamValue !== undefined ? { downstreamValue } : {}),
      ...(sourceProvenance ? { sourceProvenance } : {}),
      ...(proofSkeleton
        ? { proofSkeleton: boundedRequiredText(proofSkeleton, `routeCard.planNodes[${index}].proofSkeleton`, 16_000) }
        : {}),
      ...(expectedProgress
        ? {
            expectedProgress: boundedRequiredText(
              expectedProgress,
              `routeCard.planNodes[${index}].expectedProgress`,
              4_000
            ),
          }
        : {}),
      ...(successCriteria ? { successCriteria } : {}),
      ...(fallbackNodeIds ? { fallbackNodeIds } : {}),
      ...(mechanism ? { mechanism } : {}),
    });
  });
  const normalizedNodeIds = new Set(normalized.map((node) => node.id));
  for (const node of normalized) {
    if (node.fallbackNodeIds?.some((fallbackNodeId) => !normalizedNodeIds.has(fallbackNodeId))) {
      throw new TypeError(`Mathematics route plan node ${node.id} has an unknown fallback node`);
    }
    if (node.fallbackNodeIds?.includes(node.id)) {
      throw new TypeError(`Mathematics route plan node ${node.id} cannot fall back to itself`);
    }
  }
  return Object.freeze(normalized);
}

function normalizeMathSourceProvenance(
  values: readonly MathSourceProvenance[],
  field: string
): readonly MathSourceProvenance[] {
  if (!Array.isArray(values) || values.length < 1 || values.length > 8) {
    throw new TypeError(`Mathematics ${field} must contain 1-8 sources`);
  }
  return Object.freeze(
    values.map((source, index) => {
      if (!MATH_SOURCE_KINDS.includes(source.kind)) {
        throw new TypeError(`Mathematics ${field}[${index}].kind is invalid`);
      }
      if (!MATH_SOURCE_COMPATIBILITY.includes(source.compatibility)) {
        throw new TypeError(`Mathematics ${field}[${index}].compatibility is invalid`);
      }
      const commit = optionalText(source.commit);
      const license = optionalText(source.license);
      return Object.freeze({
        kind: source.kind,
        locator: requiredText(source.locator, `${field}[${index}].locator`),
        compatibility: source.compatibility,
        ...(commit ? { commit: requiredGitOid(commit, `${field}[${index}].commit`) } : {}),
        ...(license ? { license } : {}),
        evidenceRef: requiredText(source.evidenceRef, `${field}[${index}].evidenceRef`),
      });
    })
  );
}

const mathPlanEdgeKey = (dependencyNodeId: string, consumerNodeId: string): string =>
  `${dependencyNodeId}\u0000${consumerNodeId}`;

function normalizeMathPlanBridges(
  values: readonly MathPlanBridge[],
  planNodes: readonly MathPlanNode[]
): readonly MathPlanBridge[] {
  if (!Array.isArray(values)) throw new TypeError('Mathematics routeCard.bridges must be an array');
  const nodeIds = new Set<string>();
  for (const node of planNodes) nodeIds.add(node.id);
  const expectedEdges = new Set<string>();
  for (const node of planNodes) {
    for (const dependencyNodeId of node.dependsOn) {
      expectedEdges.add(mathPlanEdgeKey(dependencyNodeId, node.id));
    }
  }
  const actualEdges = new Set<string>();
  const normalized = values.map((bridge, index) => {
    const dependencyNodeId = normalizeMathPlanNodeId(
      bridge.dependencyNodeId,
      `routeCard.bridges[${index}].dependencyNodeId`
    );
    const consumerNodeId = normalizeMathPlanNodeId(bridge.consumerNodeId, `routeCard.bridges[${index}].consumerNodeId`);
    if (!nodeIds.has(dependencyNodeId) || !nodeIds.has(consumerNodeId)) {
      throw new TypeError(`Mathematics routeCard.bridges[${index}] must reference plan nodes`);
    }
    const edge = mathPlanEdgeKey(dependencyNodeId, consumerNodeId);
    if (actualEdges.has(edge)) {
      throw new TypeError('Mathematics routeCard.bridges must not duplicate a dependency edge');
    }
    actualEdges.add(edge);
    return Object.freeze({
      dependencyNodeId,
      consumerNodeId,
      mathematicalBridge: requiredText(bridge.mathematicalBridge, `routeCard.bridges[${index}].mathematicalBridge`),
      leanUse: requiredText(bridge.leanUse, `routeCard.bridges[${index}].leanUse`),
    });
  });
  let coversExpectedEdges = actualEdges.size === expectedEdges.size;
  if (coversExpectedEdges) {
    for (const edge of actualEdges) {
      if (expectedEdges.has(edge)) continue;
      coversExpectedEdges = false;
      break;
    }
  }
  if (!coversExpectedEdges) {
    throw new TypeError('Mathematics routeCard.bridges must cover every dependency edge exactly once');
  }
  return Object.freeze(normalized);
}

function normalizeMathVerifiedLemma(lemma: MathVerifiedLemma, field: string): MathVerifiedLemma {
  return Object.freeze({
    planNodeId: normalizeMathPlanNodeId(lemma.planNodeId, `${field}.planNodeId`),
    theoremName: requiredText(lemma.theoremName, `${field}.theoremName`),
    theoremStatement: requiredText(lemma.theoremStatement, `${field}.theoremStatement`),
    sourceFile: requiredText(lemma.sourceFile, `${field}.sourceFile`),
    proofHash: requiredHash(lemma.proofHash, `${field}.proofHash`),
    importModules: textList(lemma.importModules, `${field}.importModules`),
    evidenceRefs: requiredTextList(lemma.evidenceRefs, `${field}.evidenceRefs`),
  });
}

function normalizeMathPremiseBundle(input: MathPremiseBundle, planNodes?: readonly MathPlanNode[]): MathPremiseBundle {
  if (!input || typeof input !== 'object') {
    throw new TypeError('Mathematics routeCard.premiseBundle is required');
  }
  if (!Array.isArray(input.premises) || input.premises.length > 16) {
    throw new TypeError('Mathematics routeCard.premiseBundle.premises must contain at most 16 declarations');
  }
  const declarationNames = new Set<string>();
  const premises = input.premises.map((premise, index) => {
    if (!MATH_PREMISE_STATUSES.includes(premise.status)) {
      throw new TypeError(`Mathematics routeCard.premiseBundle.premises[${index}].status is invalid`);
    }
    if (!MATH_PREMISE_SOURCE_KINDS.includes(premise.sourceKind)) {
      throw new TypeError(`Mathematics routeCard.premiseBundle.premises[${index}].sourceKind is invalid`);
    }
    const evidenceRefs = textList(premise.evidenceRefs, `routeCard.premiseBundle.premises[${index}].evidenceRefs`);
    const sourceModule = optionalText(premise.sourceModule);
    const sourceCommit = premise.sourceCommit
      ? requiredGitOid(premise.sourceCommit, `routeCard.premiseBundle.premises[${index}].sourceCommit`)
      : undefined;
    const sourceFile = optionalText(premise.sourceFile);
    const proofHash = premise.proofHash
      ? requiredHash(premise.proofHash, `routeCard.premiseBundle.premises[${index}].proofHash`)
      : undefined;
    const importModules = premise.importModules
      ? textList(premise.importModules, `routeCard.premiseBundle.premises[${index}].importModules`)
      : undefined;
    const checkedAtCommit = premise.checkedAtCommit
      ? requiredGitOid(premise.checkedAtCommit, `routeCard.premiseBundle.premises[${index}].checkedAtCommit`)
      : undefined;
    if (premise.status !== 'proposed' && evidenceRefs.length === 0) {
      throw new TypeError(
        `Mathematics routeCard.premiseBundle.premises[${index}] checked status requires evidenceRefs`
      );
    }
    if (premise.sourceKind === 'library' && ['located', 'typed'].includes(premise.status) && !sourceModule) {
      throw new TypeError(
        `Mathematics routeCard.premiseBundle.premises[${index}] located status requires sourceModule`
      );
    }
    if (premise.status === 'typed' && !checkedAtCommit) {
      throw new TypeError(
        `Mathematics routeCard.premiseBundle.premises[${index}] typed status requires checkedAtCommit`
      );
    }
    if (premise.status !== 'typed' && checkedAtCommit) {
      throw new TypeError(
        `Mathematics routeCard.premiseBundle.premises[${index}] unchecked status cannot use checkedAtCommit`
      );
    }
    if (premise.sourceKind === 'library' && (sourceCommit || sourceFile || proofHash || importModules)) {
      throw new TypeError(
        `Mathematics routeCard.premiseBundle.premises[${index}] library source cannot use local proof provenance`
      );
    }
    if (
      premise.sourceKind === 'verified_local' &&
      (premise.status !== 'typed' || !sourceCommit || !sourceFile || !proofHash || !importModules)
    ) {
      throw new TypeError(
        `Mathematics routeCard.premiseBundle.premises[${index}] verified_local source requires typed commit, file, and proof hash`
      );
    }
    const declarationName = requiredText(
      premise.declarationName,
      `routeCard.premiseBundle.premises[${index}].declarationName`
    );
    if (declarationNames.has(declarationName)) {
      throw new TypeError('Mathematics routeCard.premiseBundle declarations must be unique');
    }
    declarationNames.add(declarationName);
    return Object.freeze({
      declarationName,
      declarationType: requiredText(
        premise.declarationType,
        `routeCard.premiseBundle.premises[${index}].declarationType`
      ),
      sourceKind: premise.sourceKind,
      ...(sourceModule ? { sourceModule } : {}),
      ...(sourceCommit ? { sourceCommit } : {}),
      ...(sourceFile ? { sourceFile } : {}),
      ...(proofHash ? { proofHash } : {}),
      ...(importModules ? { importModules } : {}),
      ...(checkedAtCommit ? { checkedAtCommit } : {}),
      intendedUse: requiredText(premise.intendedUse, `routeCard.premiseBundle.premises[${index}].intendedUse`),
      status: premise.status,
      evidenceRefs,
    });
  });
  const rawCoverage = (input as Partial<MathPremiseBundle>).coverage;
  const legacyCoverage = rawCoverage === undefined && planNodes !== undefined;
  const coverageInput = legacyCoverage
    ? planNodes.map(
        (node): MathPremiseCoverage => ({
          planNodeId: node.id,
          premiseDeclarationNames: [],
          selfContained: false,
          unresolvedNeed: `Map exact premises for plan node ${node.id}.`,
        })
      )
    : rawCoverage;
  if (!Array.isArray(coverageInput) || coverageInput.length === 0 || coverageInput.length > 128) {
    throw new TypeError('Mathematics routeCard.premiseBundle.coverage must contain 1-128 node mappings');
  }
  const coveragePlanNodeIds = new Set<string>();
  const coverage = coverageInput.map((entry, index): MathPremiseCoverage => {
    const planNodeId = normalizeMathPlanNodeId(
      entry.planNodeId,
      `routeCard.premiseBundle.coverage[${index}].planNodeId`
    );
    coveragePlanNodeIds.add(planNodeId);
    const premiseDeclarationNames = textList(
      entry.premiseDeclarationNames,
      `routeCard.premiseBundle.coverage[${index}].premiseDeclarationNames`
    );
    const unresolvedNeed = optionalText(entry.unresolvedNeed);
    if (typeof entry.selfContained !== 'boolean') {
      throw new TypeError(`Mathematics routeCard.premiseBundle.coverage[${index}].selfContained must be boolean`);
    }
    if (premiseDeclarationNames.some((name) => !declarationNames.has(name))) {
      throw new TypeError(
        `Mathematics routeCard.premiseBundle.coverage[${index}] must reference retained premise declarations`
      );
    }
    if (entry.selfContained && (premiseDeclarationNames.length > 0 || unresolvedNeed)) {
      throw new TypeError(
        `Mathematics routeCard.premiseBundle.coverage[${index}] self-contained node cannot require premises`
      );
    }
    if (!entry.selfContained && premiseDeclarationNames.length === 0 && !unresolvedNeed) {
      throw new TypeError(
        `Mathematics routeCard.premiseBundle.coverage[${index}] must map a premise or unresolved need`
      );
    }
    return Object.freeze({
      planNodeId,
      premiseDeclarationNames,
      selfContained: entry.selfContained,
      ...(unresolvedNeed ? { unresolvedNeed } : {}),
    });
  });
  if (coveragePlanNodeIds.size !== coverage.length) {
    throw new TypeError('Mathematics routeCard.premiseBundle.coverage must map each plan node once');
  }
  if (
    planNodes &&
    (planNodes.length !== coveragePlanNodeIds.size || planNodes.some((node) => !coveragePlanNodeIds.has(node.id)))
  ) {
    throw new TypeError('Mathematics routeCard.premiseBundle.coverage must map every plan node exactly once');
  }
  const unresolvedNeedsFromCoverage: string[] = [];
  for (const entry of coverage) {
    if (entry.unresolvedNeed) unresolvedNeedsFromCoverage.push(entry.unresolvedNeed);
  }
  const unresolvedNeeds = legacyCoverage
    ? unresolvedNeedsFromCoverage
    : textList(input.unresolvedNeeds, 'routeCard.premiseBundle.unresolvedNeeds');
  const unresolvedNeedCounts = new Map<string, number>();
  for (const value of unresolvedNeedsFromCoverage) {
    unresolvedNeedCounts.set(value, (unresolvedNeedCounts.get(value) ?? 0) + 1);
  }
  const unresolvedNeedsMatch =
    unresolvedNeeds.length === unresolvedNeedsFromCoverage.length &&
    unresolvedNeeds.every((value) => {
      const count = unresolvedNeedCounts.get(value) ?? 0;
      if (count === 0) return false;
      if (count === 1) unresolvedNeedCounts.delete(value);
      else unresolvedNeedCounts.set(value, count - 1);
      return true;
    });
  if (!unresolvedNeedsMatch) {
    throw new TypeError('Mathematics routeCard.premiseBundle.unresolvedNeeds must equal node coverage gaps');
  }
  return Object.freeze({
    strategySketch: requiredText(input.strategySketch, 'routeCard.premiseBundle.strategySketch'),
    leanSkeleton: requiredText(input.leanSkeleton, 'routeCard.premiseBundle.leanSkeleton'),
    premises: Object.freeze(premises),
    coverage: Object.freeze(coverage),
    unresolvedNeeds,
  });
}

function deriveMathPremiseCoverageRows(bundle: MathPremiseBundle): readonly MathPremiseCoverageRow[] {
  const premiseByName = new Map<string, MathPremiseCandidate>();
  for (const premise of bundle.premises) premiseByName.set(premise.declarationName, premise);
  return Object.freeze(
    bundle.coverage.map((entry): MathPremiseCoverageRow => {
      const untypedPremiseDeclarationNames = entry.premiseDeclarationNames.filter(
        (name) => premiseByName.get(name)?.status !== 'typed'
      );
      const typedCount = entry.premiseDeclarationNames.length - untypedPremiseDeclarationNames.length;
      const status: MathPremiseCoverageStatus = entry.selfContained
        ? 'covered'
        : entry.unresolvedNeed
          ? typedCount > 0
            ? 'partial'
            : 'missing'
          : untypedPremiseDeclarationNames.length > 0
            ? 'partial'
            : 'covered';
      return Object.freeze({
        ...entry,
        status,
        untypedPremiseDeclarationNames: Object.freeze(untypedPremiseDeclarationNames),
      });
    })
  );
}

function normalizeMathRouteAssessment(input: MathRouteAssessment): MathRouteAssessment {
  if (!MATH_ROUTE_CHECK_VERDICTS.includes(input.faithfulness)) {
    throw new TypeError('Mathematics route assessment faithfulness verdict is invalid');
  }
  if (!MATH_ROUTE_CHECK_VERDICTS.includes(input.mathematicalValidity)) {
    throw new TypeError('Mathematics route assessment mathematicalValidity verdict is invalid');
  }
  if (!MATH_ROUTE_CHECK_VERDICTS.includes(input.decompositionUsefulness)) {
    throw new TypeError('Mathematics route assessment decompositionUsefulness verdict is invalid');
  }
  if (!MATH_ROUTE_PROBE_OUTCOMES.includes(input.probeOutcome)) {
    throw new TypeError('Mathematics route assessment probeOutcome is invalid');
  }
  if (!Number.isFinite(input.checkedAt) || input.checkedAt <= 0) {
    throw new TypeError('Mathematics route assessment checkedAt must be a positive timestamp');
  }
  if (input.semanticViabilityChecks !== undefined && !Array.isArray(input.semanticViabilityChecks)) {
    throw new TypeError('Mathematics route assessment semanticViabilityChecks must be an array');
  }
  const semanticViabilityChecks = input.semanticViabilityChecks
    ? input.semanticViabilityChecks.map((check, index): MathSemanticViabilityCheck => {
        if (!MATH_SEMANTIC_VIABILITY_KINDS.includes(check.kind)) {
          throw new TypeError(`routeCard.assessment.semanticViabilityChecks[${index}].kind is invalid`);
        }
        if (!MATH_ROUTE_CHECK_VERDICTS.includes(check.verdict)) {
          throw new TypeError(`routeCard.assessment.semanticViabilityChecks[${index}].verdict is invalid`);
        }
        return Object.freeze({
          kind: check.kind,
          planNodeId: normalizeMathPlanNodeId(
            check.planNodeId,
            `routeCard.assessment.semanticViabilityChecks[${index}].planNodeId`
          ),
          verdict: check.verdict,
          summary: boundedRequiredText(
            check.summary,
            `routeCard.assessment.semanticViabilityChecks[${index}].summary`,
            1200
          ),
          evidenceRefs: requiredTextList(
            check.evidenceRefs,
            `routeCard.assessment.semanticViabilityChecks[${index}].evidenceRefs`
          ),
        });
      })
    : undefined;
  if (
    semanticViabilityChecks &&
    new Set(semanticViabilityChecks.map((check) => check.kind)).size !== semanticViabilityChecks.length
  ) {
    throw new TypeError('Mathematics route assessment semantic viability kinds must be unique');
  }
  if (semanticViabilityChecks?.some((check) => check.verdict === 'fail') && input.mathematicalValidity === 'pass') {
    throw new TypeError('Mathematics route with a failed semantic viability check cannot pass mathematicalValidity');
  }
  return Object.freeze({
    assessorSessionId: requiredText(input.assessorSessionId, 'routeCard.assessment.assessorSessionId'),
    probePlanNodeId: normalizeMathPlanNodeId(input.probePlanNodeId, 'routeCard.assessment.probePlanNodeId'),
    faithfulness: input.faithfulness,
    mathematicalValidity: input.mathematicalValidity,
    decompositionUsefulness: input.decompositionUsefulness,
    probeOutcome: input.probeOutcome,
    probeSummary: requiredText(input.probeSummary, 'routeCard.assessment.probeSummary'),
    evidenceRefs: requiredTextList(input.evidenceRefs, 'routeCard.assessment.evidenceRefs'),
    ...(semanticViabilityChecks ? { semanticViabilityChecks: Object.freeze(semanticViabilityChecks) } : {}),
    checkedAt: input.checkedAt,
  });
}

function computeMathActionableFrontierNodeIds(nodes: readonly MathPlanNode[]): string[] {
  const nodeById = new Map<string, MathPlanNode>();
  for (const node of nodes) nodeById.set(node.id, node);
  const childrenByParentId = new Map<string, MathPlanNode[]>();
  for (const node of nodes) {
    if (!node.parentNodeId) continue;
    const children = childrenByParentId.get(node.parentNodeId);
    if (children) children.push(node);
    else childrenByParentId.set(node.parentNodeId, [node]);
  }
  const frontier: string[] = [];
  for (const node of nodes) {
    if (
      node.status !== 'kernel_verified' &&
      node.status !== 'refuted' &&
      node.dependsOn.every((dependencyId) => nodeById.get(dependencyId)?.status === 'kernel_verified') &&
      (childrenByParentId.get(node.id) ?? []).every((child) => child.status === 'kernel_verified')
    ) {
      frontier.push(node.id);
    }
  }
  return frontier.toSorted();
}

function assertMathPlanSnapshotTransition(
  before: MathPlanSnapshot,
  after: MathPlanSnapshot,
  expansion?: MathPlanExpansion
): string[] {
  if (before.rootNodeId !== after.rootNodeId || after.planNodes.length < before.planNodes.length) {
    throw new TypeError('Mathematics plan snapshots cannot replace or remove the existing DAG');
  }
  if (!expansion && before.planNodes.length !== after.planNodes.length) {
    throw new TypeError('Mathematics plan growth requires an explicit planExpansion');
  }
  const afterById = new Map<string, MathPlanNode>();
  for (const node of after.planNodes) afterById.set(node.id, node);
  const newlyVerifiedNodeIds: string[] = [];
  const beforeNodeIds = new Set(before.planNodes.map((node) => node.id));
  const addedNodes = after.planNodes.filter((node) => !beforeNodeIds.has(node.id));
  if (expansion) {
    if (!before.openFrontierNodeIds.includes(expansion.expandedNodeId)) {
      throw new TypeError('Mathematics planExpansion must expand an actionable frontier node');
    }
    const expectedAddedIds = new Set(expansion.addedNodes.map((node) => node.id));
    if (addedNodes.length !== expectedAddedIds.size || addedNodes.some((node) => !expectedAddedIds.has(node.id))) {
      throw new TypeError('Mathematics planExpansion addedNodeIds must equal the plan snapshot additions');
    }
    const expansionNodeById = new Map(expansion.addedNodes.map((node) => [node.id, node]));
    for (const addedNode of addedNodes) {
      const expansionNode = expansionNodeById.get(addedNode.id);
      if (!expansionNode) {
        throw new TypeError('Mathematics planExpansion addedNodeIds must equal the plan snapshot additions');
      }
      if (expansionNode.dependsOn.length > 0 || addedNode.dependsOn.length > 0) {
        throw new TypeError(
          'Mathematics planExpansion uses hierarchical children; added nodes cannot rewrite DAG edges'
        );
      }
      if (
        expansionNode.informalClaim !== addedNode.informalClaim ||
        expansionNode.provisionalLeanStatement !== addedNode.provisionalLeanStatement ||
        expansionNode.role !== addedNode.role ||
        expansionNode.parentNodeId !== addedNode.parentNodeId ||
        expansionNode.kind !== addedNode.kind ||
        expansionNode.estimatedEffort !== addedNode.estimatedEffort ||
        expansionNode.successProbability !== addedNode.successProbability ||
        expansionNode.downstreamValue !== addedNode.downstreamValue ||
        JSON.stringify(expansionNode.sourceProvenance ?? []) !== JSON.stringify(addedNode.sourceProvenance ?? []) ||
        expansionNode.dependsOn.length !== addedNode.dependsOn.length ||
        expansionNode.dependsOn.some((dependencyId) => !addedNode.dependsOn.includes(dependencyId))
      ) {
        throw new TypeError('Mathematics planExpansion must preserve added node claims and topology');
      }
      let parentNodeId = addedNode.parentNodeId;
      const seenParents = new Set<string>();
      while (parentNodeId && parentNodeId !== expansion.expandedNodeId) {
        if (seenParents.has(parentNodeId)) break;
        seenParents.add(parentNodeId);
        parentNodeId = afterById.get(parentNodeId)?.parentNodeId;
      }
      if (parentNodeId !== expansion.expandedNodeId) {
        throw new TypeError('Mathematics planExpansion nodes must be contained by the expanded node');
      }
      if (addedNode.status === 'kernel_verified') newlyVerifiedNodeIds.push(addedNode.id);
    }
  }
  for (const beforeNode of before.planNodes) {
    const afterNode = afterById.get(beforeNode.id);
    if (!afterNode) {
      throw new TypeError('Mathematics plan snapshots must preserve the same DAG topology and claims');
    }
    const afterEvidenceRefs = new Set(afterNode.evidenceRefs);
    if (
      beforeNode.informalClaim !== afterNode.informalClaim ||
      beforeNode.provisionalLeanStatement !== afterNode.provisionalLeanStatement ||
      beforeNode.role !== afterNode.role ||
      beforeNode.parentNodeId !== afterNode.parentNodeId ||
      beforeNode.kind !== afterNode.kind ||
      beforeNode.estimatedEffort !== afterNode.estimatedEffort ||
      beforeNode.successProbability !== afterNode.successProbability ||
      beforeNode.downstreamValue !== afterNode.downstreamValue ||
      JSON.stringify(beforeNode.sourceProvenance ?? []) !== JSON.stringify(afterNode.sourceProvenance ?? []) ||
      beforeNode.proofSkeleton !== afterNode.proofSkeleton ||
      beforeNode.expectedProgress !== afterNode.expectedProgress ||
      beforeNode.mechanism !== afterNode.mechanism ||
      JSON.stringify(beforeNode.successCriteria ?? []) !== JSON.stringify(afterNode.successCriteria ?? []) ||
      JSON.stringify(beforeNode.fallbackNodeIds ?? []) !== JSON.stringify(afterNode.fallbackNodeIds ?? []) ||
      beforeNode.dependsOn.length !== afterNode.dependsOn.length ||
      beforeNode.dependsOn.some((dependencyId) => !afterNode.dependsOn.includes(dependencyId))
    ) {
      throw new TypeError('Mathematics plan snapshots must preserve the same DAG topology and claims');
    }
    if (beforeNode.status === 'kernel_verified' && afterNode.status !== 'kernel_verified') {
      throw new TypeError('Mathematics plan snapshots cannot regress a kernel-verified node');
    }
    if (beforeNode.evidenceRefs.some((evidenceRef) => !afterEvidenceRefs.has(evidenceRef))) {
      throw new TypeError('Mathematics plan snapshots cannot discard existing node evidence');
    }
    if (beforeNode.status !== 'kernel_verified' && afterNode.status === 'kernel_verified') {
      newlyVerifiedNodeIds.push(beforeNode.id);
    }
  }
  return newlyVerifiedNodeIds.toSorted();
}

function assertMathPlanDag(
  nodes: readonly MathPlanNode[],
  rootNodeId: string,
  nodeById: ReadonlyMap<string, MathPlanNode>
): void {
  const childrenByParentId = new Map<string, string[]>();
  for (const node of nodes) {
    if (node.dependsOn.includes(node.id)) {
      throw new TypeError(`Mathematics route plan node ${node.id} cannot depend on itself`);
    }
    if (node.dependsOn.some((dependency) => !nodeById.has(dependency))) {
      throw new TypeError(`Mathematics route plan node ${node.id} has an unknown dependency`);
    }
    if (node.parentNodeId) {
      if (node.id === rootNodeId || node.role === 'goal') {
        throw new TypeError('Mathematics route goal cannot be an expanded child node');
      }
      if (node.parentNodeId === node.id || !nodeById.has(node.parentNodeId)) {
        throw new TypeError(`Mathematics route plan node ${node.id} has an invalid parent`);
      }
      const children = childrenByParentId.get(node.parentNodeId);
      if (children) children.push(node.id);
      else childrenByParentId.set(node.parentNodeId, [node.id]);
    }
  }

  const visiting = new Set<string>();
  const visited = new Set<string>();
  const visit = (nodeId: string): void => {
    if (visiting.has(nodeId)) throw new TypeError('Mathematics route plan must be acyclic');
    if (visited.has(nodeId)) return;
    visiting.add(nodeId);
    const node = nodeById.get(nodeId)!;
    for (const dependency of node.dependsOn) visit(dependency);
    for (const child of childrenByParentId.get(nodeId) ?? []) visit(child);
    visiting.delete(nodeId);
    visited.add(nodeId);
  };
  visit(rootNodeId);
  if (visited.size !== nodes.length) {
    throw new TypeError('Mathematics route plan nodes must all contribute to the root goal');
  }
}

export function normalizeMathPlanNodeId(value: string, field: string): string {
  const normalized = requiredText(value, field);
  if (!/^[A-Za-z0-9][A-Za-z0-9._:-]{0,127}$/u.test(normalized)) {
    throw new TypeError(`Mathematics ${field} is invalid`);
  }
  return normalized;
}

export function classifyMathLeanFailure(error: string): MathLeanFailureKind {
  const message = requiredText(error, 'Lean error').toLowerCase();
  if (
    /(?:timed?\s*out|timeout|maximum (?:heartbeats|recursion depth)|heartbeat limit|out of memory|memory exhausted|resource exhausted)/u.test(
      message
    )
  ) {
    return 'timeout_or_resource';
  }
  if (
    /(?:fail(?:ed)? to (?:show|prove) termination|termination[_ ]by|cannot use structural recursion|fail(?:ed)? to decrease|decreasing argument)/u.test(
      message
    )
  ) {
    return 'termination_failed';
  }
  if (/(?:failed to synthesize|typeclass instance problem is stuck|synth(?:esis|esize).*instance)/u.test(message)) {
    return 'instance_synthesis_failed';
  }
  if (/(?:unknown (?:identifier|constant|namespace)|invalid field notation)/u.test(message)) {
    return 'unknown_identifier';
  }
  if (/(?:declaration has metavariables|invalid declaration|declaration uses ['`]sorry['`])/u.test(message)) {
    return 'declaration_rejected';
  }
  if (/(?:application type mismatch|type mismatch|has type[\s\S]*but is expected to have type)/u.test(message)) {
    return 'type_mismatch';
  }
  if (/(?:unsolved goals?|goals? remain(?:ing)?)/u.test(message)) return 'unsolved_goals';
  if (/(?:tactic[\s\S]*failed|tactic made no progress|made no progress|no goals to be solved)/u.test(message)) {
    return 'tactic_failed';
  }
  return 'unknown';
}

function normalizeMathWholeProofProbe(
  input: MathWholeProofProbe,
  planBefore: MathPlanSnapshot | undefined,
  planAfter: MathPlanSnapshot | undefined,
  openGoalCountAfter: number,
  firstLeanErrorAfter: string | undefined,
  firstLeanErrorOffsetAfter: number | undefined
): MathWholeProofProbe {
  if (!planBefore || !planAfter) {
    throw new TypeError('Mathematics wholeProofProbe requires planBefore and planAfter');
  }
  if (!MATH_WHOLE_PROOF_PROBE_OUTCOMES.includes(input.outcome)) {
    throw new TypeError('Mathematics wholeProofProbe.outcome is invalid');
  }
  const firstIncompatibleNodeId = input.firstIncompatibleNodeId
    ? normalizeMathPlanNodeId(input.firstIncompatibleNodeId, 'wholeProofProbe.firstIncompatibleNodeId')
    : undefined;
  const firstLeanError = optionalText(input.firstLeanError);
  const errorStartOffset = optionalNonnegativeInteger(input.errorStartOffset, 'wholeProofProbe.errorStartOffset');
  const errorEndOffset = optionalNonnegativeInteger(input.errorEndOffset, 'wholeProofProbe.errorEndOffset');
  const repairObjective = optionalText(input.repairObjective);
  let failureKind: MathLeanFailureKind | undefined;
  const rootVerified = planAfter.planNodes.some(
    (node) => node.id === planAfter.rootNodeId && node.status === 'kernel_verified'
  );
  if (input.outcome === 'kernel_verified') {
    if (
      !rootVerified ||
      openGoalCountAfter !== 0 ||
      firstIncompatibleNodeId ||
      firstLeanError ||
      errorStartOffset !== undefined ||
      errorEndOffset !== undefined ||
      repairObjective ||
      input.failureKind !== undefined
    ) {
      throw new TypeError('Mathematics successful wholeProofProbe must close the root without failure fields');
    }
  } else {
    if (
      !firstIncompatibleNodeId ||
      !firstLeanError ||
      errorStartOffset === undefined ||
      errorEndOffset === undefined ||
      !repairObjective
    ) {
      throw new TypeError('Mathematics failed wholeProofProbe requires one exact localized repair target');
    }
    if (!planBefore.planNodes.some((node) => node.id === firstIncompatibleNodeId)) {
      throw new TypeError('Mathematics wholeProofProbe failure node must belong to planBefore');
    }
    if (errorEndOffset < errorStartOffset) {
      throw new TypeError('Mathematics wholeProofProbe error range is invalid');
    }
    if (firstLeanErrorAfter !== firstLeanError || firstLeanErrorOffsetAfter !== errorStartOffset) {
      throw new TypeError('Mathematics wholeProofProbe failure must match the reported Lean error and offset');
    }
    if (rootVerified) {
      throw new TypeError('Mathematics failed wholeProofProbe cannot report a kernel-verified root');
    }
    failureKind = classifyMathLeanFailure(firstLeanError);
    if (input.failureKind !== undefined && input.failureKind !== failureKind) {
      throw new TypeError('Mathematics wholeProofProbe failureKind must match the deterministic Lean classifier');
    }
  }
  return Object.freeze({
    candidateProofHash: requiredHash(input.candidateProofHash, 'wholeProofProbe.candidateProofHash'),
    sourceFile: boundedRequiredText(input.sourceFile, 'wholeProofProbe.sourceFile', 1024),
    outcome: input.outcome,
    ...(firstIncompatibleNodeId ? { firstIncompatibleNodeId } : {}),
    ...(firstLeanError ? { firstLeanError } : {}),
    ...(errorStartOffset !== undefined ? { errorStartOffset } : {}),
    ...(errorEndOffset !== undefined ? { errorEndOffset } : {}),
    ...(repairObjective
      ? { repairObjective: boundedRequiredText(repairObjective, 'wholeProofProbe.repairObjective', 500) }
      : {}),
    ...(failureKind ? { failureKind } : {}),
    evidenceRefs: requiredTextList(input.evidenceRefs, 'wholeProofProbe.evidenceRefs'),
  });
}

function normalizeMathPlanNodeIds(values: readonly string[], field: string): readonly string[] {
  if (!Array.isArray(values)) throw new TypeError(`Mathematics ${field} must be an array`);
  const normalizedSet = new Set<string>();
  const normalized = values.map((value, index) => {
    const nodeId = normalizeMathPlanNodeId(value, `${field}[${index}]`);
    normalizedSet.add(nodeId);
    return nodeId;
  });
  if (normalizedSet.size !== normalized.length) {
    throw new TypeError(`Mathematics ${field} must be unique`);
  }
  return Object.freeze(normalized);
}

function compareMathRouteEvidence(
  left: MathRouteCard,
  right: MathRouteCard,
  executionEstimates: ReadonlyMap<MathRouteCard, MathRouteExecutionEstimate>,
  selectableByCard: ReadonlyMap<MathRouteCard, boolean>
): number {
  const probeRank: Readonly<Record<MathRouteProbeOutcome, number>> = {
    refuted: -1,
    not_run: 0,
    inconclusive: 1,
    supported: 2,
    kernel_verified: 3,
  };
  const leftAssessment = left.assessment;
  const rightAssessment = right.assessment;
  const leftExecution = executionEstimates.get(left)!;
  const rightExecution = executionEstimates.get(right)!;
  // Worker-estimated information gain, cost, and formalization risk are
  // advisory metadata only. Runtime evidence decides otherwise-tied routes.
  return (
    Number(selectableByCard.get(left)) - Number(selectableByCard.get(right)) ||
    probeRank[leftAssessment?.probeOutcome ?? 'not_run'] - probeRank[rightAssessment?.probeOutcome ?? 'not_run'] ||
    compareMathRouteCoverage(
      leftExecution.kernelVerifiedNodeCount,
      leftExecution.nodeCount,
      rightExecution.kernelVerifiedNodeCount,
      rightExecution.nodeCount
    ) ||
    compareMathRouteCoverage(
      leftExecution.typedOrVerifiedNodeCount,
      leftExecution.nodeCount,
      rightExecution.typedOrVerifiedNodeCount,
      rightExecution.nodeCount
    ) ||
    compareMathRouteCoverage(
      leftExecution.evidenceBackedNodeCount,
      leftExecution.nodeCount,
      rightExecution.evidenceBackedNodeCount,
      rightExecution.nodeCount
    ) ||
    rightExecution.remainingCriticalPathLength - leftExecution.remainingCriticalPathLength ||
    rightExecution.remainingNodeCount - leftExecution.remainingNodeCount ||
    leftExecution.usefulNodeConcurrency - rightExecution.usefulNodeConcurrency
  );
}

function deriveMathRouteExecutionEstimate(card: MathRouteCard): MathRouteExecutionEstimate {
  const nodeById = new Map<string, MathPlanNode>();
  const childrenByParentId = new Map<string, string[]>();
  for (const node of card.planNodes) nodeById.set(node.id, node);
  for (const node of card.planNodes) {
    if (!node.parentNodeId) continue;
    const children = childrenByParentId.get(node.parentNodeId);
    if (children) children.push(node.id);
    else childrenByParentId.set(node.parentNodeId, [node.id]);
  }
  const depthMemo = new Map<string, number>();
  const remainingDepth = (nodeId: string): number => {
    const cached = depthMemo.get(nodeId);
    if (cached !== undefined) return cached;
    const node = nodeById.get(nodeId)!;
    if (node.status === 'kernel_verified') {
      depthMemo.set(nodeId, 0);
      return 0;
    }
    let depth = 0;
    for (const dependencyId of node.dependsOn) depth = Math.max(depth, remainingDepth(dependencyId));
    for (const childId of childrenByParentId.get(node.id) ?? []) depth = Math.max(depth, remainingDepth(childId));
    depth += 1;
    depthMemo.set(nodeId, depth);
    return depth;
  };
  let remainingNodeCount = 0;
  let remainingCriticalPathLength = 0;
  let typedOrVerifiedNodeCount = 0;
  let evidenceBackedNodeCount = 0;
  for (const node of card.planNodes) {
    if (node.status !== 'kernel_verified') {
      remainingNodeCount += 1;
      remainingCriticalPathLength = Math.max(remainingCriticalPathLength, remainingDepth(node.id));
    }
    if (node.status === 'typed' || node.status === 'kernel_verified') typedOrVerifiedNodeCount += 1;
    if (node.status !== 'proposed') evidenceBackedNodeCount += 1;
  }
  return Object.freeze({
    nodeCount: card.planNodes.length,
    kernelVerifiedNodeCount: card.planNodes.length - remainingNodeCount,
    typedOrVerifiedNodeCount,
    evidenceBackedNodeCount,
    remainingNodeCount,
    remainingCriticalPathLength,
    usefulNodeConcurrency: card.openFrontierNodeIds.length,
  });
}

function deriveMathRouteStructureSignature(card: MathRouteCard): string {
  const nodeById = new Map<string, MathPlanNode>();
  const childrenByParentId = new Map<string, string[]>();
  for (const node of card.planNodes) nodeById.set(node.id, node);
  for (const node of card.planNodes) {
    if (!node.parentNodeId) continue;
    const children = childrenByParentId.get(node.parentNodeId);
    if (children) children.push(node.id);
    else childrenByParentId.set(node.parentNodeId, [node.id]);
  }
  const signatureMemo = new Map<string, string>();
  const nodeSignature = (nodeId: string): string => {
    const cached = signatureMemo.get(nodeId);
    if (cached) return cached;
    const node = nodeById.get(nodeId)!;
    const dependencies = node.dependsOn.map(nodeSignature).toSorted();
    const children = (childrenByParentId.get(nodeId) ?? []).map(nodeSignature).toSorted();
    const signature = `${node.role}:${node.kind ?? 'theorem'}:${normalizeMathLeanStatementShape(
      node.provisionalLeanStatement
    )}(${dependencies.join(',')})[${children.join(',')}]`;
    signatureMemo.set(nodeId, signature);
    return signature;
  };
  const premises = card.premiseBundle.premises
    .map((premise) => normalizeMathStructureLabel(premise.declarationName))
    .toSorted();
  return [
    `decisive:${normalizeMathStructureLabel(card.decisiveLemma)}`,
    `premises:${premises.join(',')}`,
    `dag:${nodeSignature(card.rootNodeId)}`,
  ].join('|');
}

function normalizeMathStructureLabel(value: string): string {
  return value.normalize('NFKC').trim().replace(/^`|`$/gu, '').replace(/\s+/gu, ' ');
}

function normalizeMathLeanStatementShape(value: string): string {
  return normalizeMathStructureLabel(value).replace(
    /^(?:(?:private|protected)\s+)?(?:theorem|lemma|example)\s+[^\s:(]+/u,
    'declaration'
  );
}

function compareMathRouteCoverage(
  leftCount: number,
  leftTotal: number,
  rightCount: number,
  rightTotal: number
): number {
  return leftCount * rightTotal - rightCount * leftTotal;
}

function freezeEvidenceDelta(value: MathEvidenceDelta, index: number): MathEvidenceDelta {
  if (!MATH_EVIDENCE_DELTA_KINDS.includes(value.kind)) {
    throw new TypeError(`Mathematics evidenceDelta[${index}].kind is invalid`);
  }
  return Object.freeze({
    kind: value.kind,
    ref: requiredText(value.ref, `evidenceDelta[${index}].ref`),
    summary: requiredText(value.summary, `evidenceDelta[${index}].summary`),
  });
}

function requiredHash(value: unknown, field: string): string {
  const normalized = requiredText(value, field).toLowerCase();
  if (!/^[0-9a-f]{64}$/u.test(normalized)) throw new TypeError(`Mathematics ${field} must be SHA-256`);
  return normalized;
}

function normalizeMathReceiptAttestation(value: MathReceiptAttestation, field: string): MathReceiptAttestation {
  if (!value || value.algorithm !== 'hmac-sha256') {
    throw new TypeError(`Mathematics ${field} must use hmac-sha256`);
  }
  const keyId = requiredText(value.keyId, `${field}.keyId`).toLowerCase();
  if (!/^[0-9a-f]{16}$/u.test(keyId)) {
    throw new TypeError(`Mathematics ${field}.keyId must be a 16-character hexadecimal key id`);
  }
  return Object.freeze({
    algorithm: 'hmac-sha256',
    keyId,
    value: requiredHash(value.value, `${field}.value`),
  });
}

function requiredText(value: unknown, field: string): string {
  if (typeof value !== 'string') throw new TypeError(`Mathematics ${field} is required`);
  const normalized = value.trim();
  if (!normalized) throw new TypeError(`Mathematics ${field} is required`);
  return normalized;
}

function boundedRequiredText(value: unknown, field: string, maximumLength: number): string {
  const normalized = requiredText(value, field);
  if (normalized.length > maximumLength) {
    throw new TypeError(`Mathematics ${field} must contain at most ${maximumLength} characters`);
  }
  return normalized;
}

function textList(values: readonly string[], field: string): readonly string[] {
  if (!Array.isArray(values)) throw new TypeError(`Mathematics ${field} must be an array`);
  const normalized: string[] = [];
  const seen = new Set<string>();
  for (let index = 0; index < values.length; index += 1) {
    const value = requiredText(values[index], `${field}[${index}]`);
    normalized.push(value);
    seen.add(value);
  }
  if (seen.size !== normalized.length) throw new TypeError(`Mathematics ${field} must be unique`);
  return Object.freeze(normalized);
}

function requiredTextList(values: readonly string[], field: string): readonly string[] {
  const normalized = textList(values, field);
  if (!normalized.length) throw new TypeError(`Mathematics ${field} must not be empty`);
  return normalized;
}

function optionalText(value: unknown): string | undefined {
  if (typeof value !== 'string') return undefined;
  return value.trim() || undefined;
}

function nonnegativeInteger(value: unknown, field: string): number {
  if (!Number.isSafeInteger(value) || Number(value) < 0) {
    throw new TypeError(`Mathematics ${field} must be a nonnegative integer`);
  }
  return Number(value);
}

function optionalNonnegativeInteger(value: unknown, field: string): number | undefined {
  return value === undefined ? undefined : nonnegativeInteger(value, field);
}

function boundedRating(value: unknown, field: string): number {
  if (!Number.isSafeInteger(value) || Number(value) < 1 || Number(value) > 5) {
    throw new TypeError(`Mathematics ${field} must be an integer from 1 to 5`);
  }
  return Number(value);
}

function requiredGitOid(value: unknown, field: string): string {
  const normalized = requiredText(value, field).toLowerCase();
  if (!/^(?:[0-9a-f]{40}|[0-9a-f]{64})$/u.test(normalized)) {
    throw new TypeError(`Mathematics ${field} must be a full Git object id`);
  }
  return normalized;
}

function normalizeMathLessonPattern(value: string): string {
  const normalized = requiredText(value, 'routePattern').toLowerCase().replace(/\s+/gu, ' ');
  if (normalized.length > 512) throw new TypeError('Mathematics routePattern is too long');
  return normalized;
}

function assertAlignmentMatchesContract(check: MathAlignmentCheck, contract: MathProblemContract): void {
  if (
    check.problemId !== contract.problemId ||
    check.statementHash !== contract.statementHash ||
    check.leanStatementHash !== contract.leanStatementHash
  ) {
    throw new TypeError('Mathematics alignment check identity must match problem contract');
  }
  if (check.officialVerificationCommand !== contract.officialVerificationCommand) {
    throw new TypeError('Mathematics alignment check must preserve the official verification command');
  }
  if (
    check.assumptions.length !== contract.assumptions.length ||
    check.assumptions.some((assumption, index) => assumption !== contract.assumptions[index])
  ) {
    throw new TypeError('Mathematics alignment check assumptions must match problem contract');
  }
  const forbiddenChanges = new Set(check.forbiddenChanges);
  if (contract.knownTraps.some((trap) => !forbiddenChanges.has(trap))) {
    throw new TypeError('Mathematics alignment check must preserve every known trap as a forbidden change');
  }
}
