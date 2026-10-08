/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

/**
 * Host-owned proof-search projection.  Models may suggest routes and actions,
 * but this module derives fingerprints, diagnosis, and completion state from
 * bounded evidence supplied by the runtime.
 */

import { z } from 'zod';
import { canonicalMathJson, mathDigest } from "./mathRuntimeIo";

const identity = z.string().trim().min(1).max(512);
const hash = z.string().regex(/^[a-f0-9]{64}$/u);
const nonNegativeInt = z.number().int().nonnegative();

export const MATH_SEARCH_SCHEMA = 'deepscientist.math-search.v1' as const;
export const DEFAULT_MATH_ROUTE_PIVOT_THRESHOLD = 2 as const;

export const mathNextStepSchema = z.enum([
  'completed',
  'respect_cancel',
  'repair_runtime',
  'verify_original',
  'wait',
  'repair_local',
  'retrieve',
  'continue_branch',
  'review_structure',
  'avoid_exact_repeat',
  'continue_local',
]);
export type MathNextStep = z.infer<typeof mathNextStepSchema>;

export const mathRouteSpecSchema = z
  .object({
    tacticFamily: identity,
    keyLemmas: z.array(identity).max(64),
    normalizationStrategy: identity,
    automationSettings: z.record(z.union([z.string(), z.number(), z.boolean()])).default({}),
    targetFragment: identity,
  })
  .strict();
export type MathRouteSpec = z.infer<typeof mathRouteSpecSchema>;

export const mathRouteSchema = z
  .object({
    fingerprint: identity,
    revision: nonNegativeInt,
    objective: identity,
    spec: mathRouteSpecSchema.optional(),
  })
  .strict();
export type MathSearchRoute = z.infer<typeof mathRouteSchema>;

const mathCompilerEvidenceSchema = z
  .object({
    status: z.enum(['passed', 'failed', 'timeout', 'unavailable']),
    exitCode: z.number().int().nullable().optional(),
    diagnostic: z.string().max(12_000).optional(),
    errorLocation: identity.optional(),
  })
  .strict();

const mathRecentDeltaSchema = z
  .object({
    goalCountBefore: nonNegativeInt.optional(),
    goalCountAfter: nonNegativeInt.optional(),
    errorBefore: z.string().max(4_000).optional(),
    errorAfter: z.string().max(4_000).optional(),
  })
  .strict();

const mathTheoremCardSchema = z
  .object({
    name: identity,
    statement: z.string().max(4_000),
    source: identity,
    version: identity.optional(),
    importPath: identity.optional(),
    verificationStatus: z.enum(['verified', 'source-reported', 'inferred', 'experimental']),
    applicableFragment: identity.optional(),
    failureConditions: z.array(z.string().max(1_000)).max(8).optional(),
  })
  .strict();
export type MathTheoremCard = z.infer<typeof mathTheoremCardSchema>;

export const mathEvidencePacketSchema = z
  .object({
    statementHash: hash,
    openGoals: z.array(z.string().max(4_000)).max(128),
    proofStateFingerprint: identity,
    routeFingerprint: identity,
    routeRevision: nonNegativeInt,
    compiler: mathCompilerEvidenceSchema,
    localLemmas: z.array(identity).max(64),
    unresolvedBridge: z.enum(['none', 'local', 'structural', 'dependency', 'unknown']),
    counterexample: z.enum(['absent', 'found', 'unknown']),
    elapsedMs: z.number().finite().nonnegative(),
    attempts: nonNegativeInt,
    recentDelta: mathRecentDeltaSchema,
    /** Bounded retrieval context; unverified cards can guide search only. */
    theoremCards: z.array(mathTheoremCardSchema).max(8).optional(),
    retrievalQuality: z.enum(['verified', 'plausible', 'stale', 'missing']),
    independentEvaluator: z.enum(['passed', 'failed', 'missing', 'unavailable']),
    closedProof: z.boolean(),
    verifierReceipt: z.unknown().nullable(),
    evidenceRefs: z.array(identity).max(32),
  })
  .strict();
export type MathEvidencePacket = z.infer<typeof mathEvidencePacketSchema>;

export const mathDiagnosisSchema = z
  .object({
    goal_progress: z.enum(['advanced', 'unchanged', 'regressed', 'unknown']),
    unresolved_bridge: z.enum(['none', 'local', 'structural', 'dependency', 'unknown']),
    compiler_status: z.enum(['passed', 'failed', 'timeout', 'unavailable']),
    counterexample: z.enum(['absent', 'found', 'unknown']),
    route_novelty: z.enum(['new', 'equivalent', 'repeated', 'unknown']),
    retrieval_quality: z.enum(['verified', 'plausible', 'stale', 'missing']),
    proof_receipt: z.enum(['closed_and_verified', 'partial', 'missing', 'failed']),
    plateau: z.boolean(),
  })
  .strict();
export type MathDiagnosis = z.infer<typeof mathDiagnosisSchema>;

const mathPendingProposalSchema = z
  .object({
    fingerprint: identity,
    objective: identity,
    baseRouteRevision: nonNegativeInt,
    routeSpec: mathRouteSpecSchema.optional(),
  })
  .strict();

export const mathSearchStateSchema = z
  .object({
    schema: z.literal(MATH_SEARCH_SCHEMA),
    problemId: identity,
    statementHash: hash,
    assignmentId: identity,
    route: mathRouteSchema,
    attemptsOnRoute: nonNegativeInt,
    proofStateFingerprint: identity,
    unresolvedGoals: z.array(z.string().max(4_000)).max(128),
    evidencePacket: mathEvidencePacketSchema,
    diagnosis: mathDiagnosisSchema,
    pendingRouteProposal: mathPendingProposalSchema.nullable(),
    decision: z.enum(['continue', 'pivot', 'stop', 'complete']),
    /** Host advice only. It never rejects a legal mathematical action. */
    nextStep: mathNextStepSchema.optional(),
    /** Observation counters only; these never terminate an unbounded run. */
    budget: z
      .object({
        observedAttempts: nonNegativeInt,
        compilerCalls: nonNegativeInt,
        elapsedMs: z.number().finite().nonnegative(),
      })
      .strict(),
    verifierReceipt: z.unknown().nullable(),
  })
  .strict();
export type MathSearchState = z.infer<typeof mathSearchStateSchema>;

/**
 * Select one evidence-backed next-step suggestion. The caller remains free to
 * perform another legal action; this function does not create a scheduler or a
 * proof-completion authority.
 */
export function chooseMathNextStep(
  input: Readonly<{
    hasMatchingFinalReceipt?: boolean;
    cancelled?: boolean;
    runtimeFailure?: 'none' | 'runtime_error' | 'timeout';
    finalVerification?: 'none' | 'pending' | 'running';
    hasLocalCompilerError?: boolean;
    missingPremise?: Readonly<{ goalRef: string }>;
    selectedBranch?: boolean;
    structureReviewRequested?: boolean;
    decisiveHelperRefuted?: boolean;
    sameActionRepeated?: boolean;
    hasNewEvidence?: boolean;
  }>
): MathNextStep {
  if (input.hasMatchingFinalReceipt) return 'completed';
  if (input.cancelled) return 'respect_cancel';
  if (input.runtimeFailure && input.runtimeFailure !== 'none') return 'repair_runtime';
  if (input.finalVerification === 'running') return 'wait';
  if (input.finalVerification === 'pending') return 'verify_original';
  if (input.hasLocalCompilerError) return 'repair_local';
  if (input.missingPremise?.goalRef.trim()) return 'retrieve';
  if (input.selectedBranch) return 'continue_branch';
  if (input.structureReviewRequested || input.decisiveHelperRefuted) return 'review_structure';
  if (input.sameActionRepeated && !input.hasNewEvidence) return 'avoid_exact_repeat';
  return 'continue_local';
}

const canonicalRoutePayload = (route: MathRouteSpec): MathRouteSpec => ({
  tacticFamily: route.tacticFamily.trim(),
  keyLemmas: [...new Set(route.keyLemmas.map((lemma) => lemma.trim()))].toSorted(),
  normalizationStrategy: route.normalizationStrategy.trim(),
  automationSettings: Object.fromEntries(
    Object.entries(route.automationSettings).toSorted(([left], [right]) => left.localeCompare(right))
  ),
  targetFragment: route.targetFragment.trim(),
});

/** Generate the route identity from semantic route inputs, not a model label. */
export function computeMathRouteFingerprint(route: MathRouteSpec): string {
  return mathDigest(canonicalMathJson(canonicalRoutePayload(mathRouteSpecSchema.parse(route))));
}

const initialEvidence = (statementHash: string, route: MathSearchRoute): MathEvidencePacket => ({
  statementHash,
  openGoals: [],
  proofStateFingerprint: 'unknown',
  routeFingerprint: route.fingerprint,
  routeRevision: route.revision,
  compiler: { status: 'unavailable' },
  localLemmas: [],
  unresolvedBridge: 'unknown',
  counterexample: 'unknown',
  elapsedMs: 0,
  attempts: 0,
  recentDelta: {},
  retrievalQuality: 'missing',
  independentEvaluator: 'missing',
  closedProof: false,
  verifierReceipt: null,
  evidenceRefs: [],
});

const initialDiagnosis = (): MathDiagnosis => ({
  goal_progress: 'unknown',
  unresolved_bridge: 'unknown',
  compiler_status: 'unavailable',
  counterexample: 'unknown',
  route_novelty: 'new',
  retrieval_quality: 'missing',
  proof_receipt: 'missing',
  plateau: false,
});

export function createMathSearchState(input: {
  problemId: string;
  statementHash: string;
  assignmentId: string;
  route: MathSearchRoute;
}): MathSearchState {
  const problemId = identity.parse(input.problemId);
  const statementHash = hash.parse(input.statementHash);
  const assignmentId = identity.parse(input.assignmentId);
  const route = mathRouteSchema.parse(input.route);
  return mathSearchStateSchema.parse({
    schema: MATH_SEARCH_SCHEMA,
    problemId,
    statementHash,
    assignmentId,
    route,
    attemptsOnRoute: 0,
    proofStateFingerprint: 'unknown',
    unresolvedGoals: [],
    evidencePacket: initialEvidence(statementHash, route),
    diagnosis: initialDiagnosis(),
    pendingRouteProposal: null,
    decision: 'continue',
    nextStep: 'continue_local',
    budget: { observedAttempts: 0, compilerCalls: 0, elapsedMs: 0 },
    verifierReceipt: null,
  });
}

/** Build a bounded packet from a compiler/probe boundary before it enters a prompt or ledger. */
export function createMathEvidencePacket(input: {
  statementHash: string;
  routeFingerprint: string;
  routeRevision: number;
  proofStateFingerprint?: string;
  openGoals?: readonly string[];
  compiler: MathEvidencePacket['compiler'];
  localLemmas?: readonly string[];
  unresolvedBridge?: MathEvidencePacket['unresolvedBridge'];
  counterexample?: MathEvidencePacket['counterexample'];
  elapsedMs?: number;
  attempts?: number;
  recentDelta?: MathEvidencePacket['recentDelta'];
  theoremCards?: MathTheoremCard[];
  retrievalQuality?: MathEvidencePacket['retrievalQuality'];
  independentEvaluator?: MathEvidencePacket['independentEvaluator'];
  closedProof?: boolean;
  verifierReceipt?: unknown;
  evidenceRefs?: readonly string[];
}): MathEvidencePacket {
  return mathEvidencePacketSchema.parse({
    statementHash: input.statementHash,
    openGoals: [...(input.openGoals ?? [])].slice(0, 128),
    proofStateFingerprint: input.proofStateFingerprint?.trim() || 'unknown',
    routeFingerprint: input.routeFingerprint,
    routeRevision: input.routeRevision,
    compiler: input.compiler,
    localLemmas: [...(input.localLemmas ?? [])].slice(0, 64),
    unresolvedBridge: input.unresolvedBridge ?? 'unknown',
    counterexample: input.counterexample ?? 'unknown',
    elapsedMs: input.elapsedMs ?? 0,
    attempts: input.attempts ?? 0,
    recentDelta: input.recentDelta ?? {},
    ...(input.theoremCards ? { theoremCards: input.theoremCards.slice(0, 8) } : {}),
    retrievalQuality: input.retrievalQuality ?? 'missing',
    independentEvaluator: input.independentEvaluator ?? 'missing',
    closedProof: input.closedProof ?? false,
    verifierReceipt: input.verifierReceipt ?? null,
    evidenceRefs: [...(input.evidenceRefs ?? [])].slice(0, 32),
  });
}

function goalProgress(packet: MathEvidencePacket): MathDiagnosis['goal_progress'] {
  const before = packet.recentDelta.goalCountBefore;
  const after = packet.recentDelta.goalCountAfter;
  if (before === undefined || after === undefined) return 'unknown';
  if (after < before) return 'advanced';
  if (after > before) return 'regressed';
  return 'unchanged';
}

export function deriveMathDiagnosis(input: {
  packet: MathEvidencePacket;
  routeNovelty?: MathDiagnosis['route_novelty'];
  repeatedAttempts?: number;
  plateauThreshold?: number;
}): MathDiagnosis {
  const packet = mathEvidencePacketSchema.parse(input.packet);
  const threshold = Math.max(1, Math.floor(input.plateauThreshold ?? DEFAULT_MATH_ROUTE_PIVOT_THRESHOLD));
  const receipt =
    packet.closedProof && packet.independentEvaluator === 'passed' && packet.verifierReceipt !== null
      ? 'closed_and_verified'
      : packet.compiler.status === 'failed' && !packet.closedProof
        ? 'failed'
        : packet.closedProof || packet.verifierReceipt !== null || packet.independentEvaluator === 'passed'
          ? 'partial'
          : 'missing';
  const attempts = input.repeatedAttempts ?? packet.attempts;
  const progress = goalProgress(packet);
  return mathDiagnosisSchema.parse({
    goal_progress: progress,
    unresolved_bridge: packet.unresolvedBridge,
    compiler_status: packet.compiler.status,
    counterexample: packet.counterexample,
    route_novelty: input.routeNovelty ?? 'unknown',
    retrieval_quality: packet.retrievalQuality,
    proof_receipt: receipt,
    plateau:
      attempts >= threshold &&
      (progress === 'unchanged' || progress === 'regressed' || packet.compiler.status === 'failed'),
  });
}

export function isMathRouteStalled(input: {
  routeFingerprint: string;
  proofStateFingerprint: string;
  recentEvidence: readonly MathEvidencePacket[];
  threshold?: number;
}): boolean {
  const threshold = Math.max(2, Math.floor(input.threshold ?? DEFAULT_MATH_ROUTE_PIVOT_THRESHOLD));
  const recent = input.recentEvidence.slice(-threshold);
  if (recent.length < threshold) return false;
  return recent.every(
    (packet) =>
      packet.routeFingerprint === input.routeFingerprint &&
      packet.proofStateFingerprint === input.proofStateFingerprint &&
      deriveMathDiagnosis({ packet }).goal_progress !== 'advanced' &&
      packet.compiler.status !== 'passed'
  );
}

/** @deprecated A repeated-state threshold is an observation, not a mandatory route pivot. */
export function shouldPivotMathRoute(input: Parameters<typeof isMathRouteStalled>[0]): boolean {
  return isMathRouteStalled(input);
}

export function advanceMathSearchState(
  state: MathSearchState,
  packet: MathEvidencePacket,
  options: {
    routeNovelty?: MathDiagnosis['route_novelty'];
    route?: MathSearchRoute;
    pivotThreshold?: number;
  } = {}
): MathSearchState {
  const current = mathSearchStateSchema.parse(state);
  const evidence = mathEvidencePacketSchema.parse(packet);
  if (evidence.statementHash !== current.statementHash) throw new Error('math_search_statement_hash_mismatch');
  // A matching independent final receipt is authoritative. Later organization
  // or construction feedback may be retained elsewhere, but cannot reopen it.
  if (isMathSearchCompletionValid(current)) return current;
  const route = options.route ? mathRouteSchema.parse(options.route) : current.route;
  const routeChanged = route.fingerprint !== current.route.fingerprint || route.revision !== current.route.revision;
  const attemptsOnRoute = routeChanged ? 1 : current.attemptsOnRoute + 1;
  const history =
    routeChanged || current.budget.observedAttempts === 0 ? [evidence] : [current.evidencePacket, evidence];
  const diagnosis = deriveMathDiagnosis({
    packet: evidence,
    routeNovelty: options.routeNovelty ?? (routeChanged ? 'new' : 'equivalent'),
    repeatedAttempts: attemptsOnRoute,
    plateauThreshold: options.pivotThreshold,
  });
  const stalled = isMathRouteStalled({
    routeFingerprint: route.fingerprint,
    proofStateFingerprint: evidence.proofStateFingerprint,
    recentEvidence: history,
    threshold: options.pivotThreshold,
  });
  const complete = diagnosis.proof_receipt === 'closed_and_verified';
  const progress = diagnosis.goal_progress;
  const nextStep = chooseMathNextStep({
    hasMatchingFinalReceipt: complete,
    runtimeFailure:
      evidence.compiler.status === 'timeout'
        ? 'timeout'
        : evidence.compiler.status === 'unavailable' || evidence.independentEvaluator === 'unavailable'
          ? 'runtime_error'
          : 'none',
    finalVerification:
      evidence.closedProof && evidence.independentEvaluator === 'missing' && !complete ? 'pending' : 'none',
    hasLocalCompilerError:
      evidence.independentEvaluator === 'failed' ||
      (evidence.compiler.status === 'failed' &&
        progress !== 'advanced' &&
        evidence.unresolvedBridge !== 'dependency' &&
        evidence.unresolvedBridge !== 'structural'),
    ...(evidence.unresolvedBridge === 'dependency' && evidence.openGoals[0] && evidence.evidenceRefs.length
      ? { missingPremise: { goalRef: evidence.openGoals[0] } }
      : {}),
    selectedBranch: progress === 'advanced' && evidence.openGoals.length > 0,
    structureReviewRequested:
      evidence.counterexample === 'found' ||
      (evidence.unresolvedBridge === 'structural' && evidence.evidenceRefs.length > 0),
  });
  const decision: MathSearchState['decision'] = complete ? 'complete' : 'continue';
  return mathSearchStateSchema.parse({
    ...current,
    route,
    attemptsOnRoute,
    proofStateFingerprint: evidence.proofStateFingerprint,
    unresolvedGoals: evidence.openGoals,
    evidencePacket: evidence,
    diagnosis: { ...diagnosis, plateau: diagnosis.plateau || stalled },
    decision,
    nextStep,
    budget: {
      observedAttempts: current.budget.observedAttempts + 1,
      compilerCalls: current.budget.compilerCalls + (evidence.compiler.status === 'unavailable' ? 0 : 1),
      elapsedMs: current.budget.elapsedMs + evidence.elapsedMs,
    },
    verifierReceipt: complete ? evidence.verifierReceipt : current.verifierReceipt,
  });
}

export function isMathSearchCompletionValid(state: MathSearchState): boolean {
  const parsed = mathSearchStateSchema.parse(state);
  return (
    parsed.decision === 'complete' &&
    parsed.statementHash === parsed.evidencePacket.statementHash &&
    parsed.evidencePacket.closedProof &&
    parsed.evidencePacket.compiler.status === 'passed' &&
    parsed.evidencePacket.independentEvaluator === 'passed' &&
    parsed.evidencePacket.verifierReceipt !== null
  );
}
