/**
 * Deterministic scheduling primitives for mathematical proof agents.
 *
 * This module deliberately has no model, filesystem, or transport dependency.
 * The runtime owns the inputs and can therefore replay every scheduling choice.
 */
import crypto from 'node:crypto';
import type { MathPlanNode, MathPlanSnapshot, MathProgressKind } from "../common/types/team/mathematicsTeam";

export const MATH_SCHEDULE_TOPOLOGIES = [
  'mainline',
  'mainline_support',
  'mainline_counterexample',
  'mainline_review',
] as const;
export type MathScheduleTopology = (typeof MATH_SCHEDULE_TOPOLOGIES)[number];

export const MATH_SCHEDULE_EVIDENCE_KINDS = [
  'unknown_api',
  'goal_unchanged',
  'counterexample',
  'independent_frontier',
  'scaffold_only',
] as const;
export type MathScheduleEvidenceKind = (typeof MATH_SCHEDULE_EVIDENCE_KINDS)[number];

export const MATH_ROUTE_PROGRESS_CLASSES = [
  'goal_progress',
  'frontier_progress',
  'scaffold_progress',
  'stalled',
  'infra_failed',
] as const;
export type MathRouteProgressClass = (typeof MATH_ROUTE_PROGRESS_CLASSES)[number];

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
  /** Sum of verified marginal progress units observed for this route. */
  verifiedMarginalGain?: number;
  /** Runtime work used by this route; these are observations, never admission limits. */
  totalLeanCalls?: number;
  totalWallClockMs?: number;
}>;

export type MathRoutePerformanceUpdate = Readonly<{
  routeFingerprint: string;
  planNodeId: string;
  progressClass: MathRouteProgressClass;
  proofStateFingerprint?: string;
  failureCategory?: string;
  researchContextFingerprint?: string;
  /** Measured progress from the integrated result, if available. */
  verifiedMarginalGain?: number;
  leanCalls?: number;
  wallClockMs?: number;
}>;

/** Update route history without mutating the persisted ledger. */
export function updateMathRoutePerformanceLedger(
  ledger: readonly MathRoutePerformanceRecord[],
  update: MathRoutePerformanceUpdate
): readonly MathRoutePerformanceRecord[] {
  if (!Array.isArray(ledger)) throw new TypeError('route performance ledger must be an array');
  if (!MATH_ROUTE_PROGRESS_CLASSES.includes(update.progressClass)) {
    throw new TypeError('route performance progressClass is invalid');
  }
  const routeFingerprint = update.routeFingerprint.trim();
  const planNodeId = update.planNodeId.trim();
  if (!routeFingerprint || !planNodeId) throw new TypeError('route performance identity is required');
  for (const [name, value] of [
    ['verifiedMarginalGain', update.verifiedMarginalGain],
    ['leanCalls', update.leanCalls],
    ['wallClockMs', update.wallClockMs],
  ] as const) {
    if (value !== undefined && (!Number.isFinite(value) || value < 0)) {
      throw new TypeError(`route performance ${name} must be a nonnegative finite number`);
    }
  }
  const current = ledger.find(
    (record) => record.routeFingerprint === routeFingerprint && record.planNodeId === planNodeId
  );
  const next: MathRoutePerformanceRecord = Object.freeze({
    routeFingerprint,
    planNodeId,
    attempts: (current?.attempts ?? 0) + 1,
    goalProgressCount: (current?.goalProgressCount ?? 0) + (update.progressClass === 'goal_progress' ? 1 : 0),
    frontierProgressCount:
      (current?.frontierProgressCount ?? 0) + (update.progressClass === 'frontier_progress' ? 1 : 0),
    scaffoldOnlyCount: (current?.scaffoldOnlyCount ?? 0) + (update.progressClass === 'scaffold_progress' ? 1 : 0),
    ...(update.researchContextFingerprint ? { researchContextFingerprint: update.researchContextFingerprint } : {}),
    ...(update.failureCategory
      ? { lastFailureCategory: update.failureCategory }
      : current?.lastFailureCategory
        ? { lastFailureCategory: current.lastFailureCategory }
        : {}),
    ...(update.proofStateFingerprint
      ? { bestProofStateFingerprint: update.proofStateFingerprint }
      : current?.bestProofStateFingerprint
        ? { bestProofStateFingerprint: current.bestProofStateFingerprint }
        : {}),
    ...(current?.verifiedMarginalGain !== undefined || update.verifiedMarginalGain !== undefined
      ? {
          verifiedMarginalGain: (current?.verifiedMarginalGain ?? 0) + (update.verifiedMarginalGain ?? 0),
        }
      : {}),
    ...(current?.totalLeanCalls !== undefined || update.leanCalls !== undefined
      ? { totalLeanCalls: (current?.totalLeanCalls ?? 0) + (update.leanCalls ?? 0) }
      : {}),
    ...(current?.totalWallClockMs !== undefined || update.wallClockMs !== undefined
      ? { totalWallClockMs: (current?.totalWallClockMs ?? 0) + (update.wallClockMs ?? 0) }
      : {}),
  });
  return Object.freeze(
    [
      ...ledger.filter((record) => !(record.routeFingerprint === routeFingerprint && record.planNodeId === planNodeId)),
      next,
    ].sort((left, right) =>
      `${left.routeFingerprint}\u0000${left.planNodeId}`.localeCompare(
        `${right.routeFingerprint}\u0000${right.planNodeId}`
      )
    )
  );
}

export type MathSchedulePlanNode = MathPlanNode &
  Readonly<{
    /** Files this node may write; used only to prevent unsafe parallel writes. */
    exclusiveFiles?: readonly string[];
  }>;

export type MathScheduleAssignment = Readonly<{
  planNodeId: string;
  statementHash: string;
  sourceHash?: string;
  goalFingerprint?: string;
  researchContextFingerprint?: string;
  status?: 'queued' | 'running' | 'completed';
  exclusiveFiles?: readonly string[];
}>;

export type MathScheduleProgress = Readonly<{
  progressKind?: MathProgressKind;
  scaffoldOnlyStreak?: number;
  goalProgressCount?: number;
}>;

export type MathScheduleInput = Readonly<{
  plan: MathPlanSnapshot | Readonly<{ planNodes: readonly MathSchedulePlanNode[] }>;
  statementHash: string;
  routeFingerprint?: string;
  sourceHash?: string;
  goalFingerprint?: string;
  activeAssignments?: readonly MathScheduleAssignment[];
  /** Runtime identity of available dependencies, evidence, source and environment. */
  researchContextFingerprint?: string;
  /** Idempotency keys already integrated in this episode. */
  completedAssignmentKeys?: readonly string[];
  /** Durable hashes of exact attempts integrated by any Worker in this run. */
  completedAssignmentDigests?: readonly string[];
  routePerformance?: readonly MathRoutePerformanceRecord[];
  progress?: MathScheduleProgress;
  lastEvidence?: MathScheduleEvidenceKind;
  availableSlots: number;
}>;

export type MathScheduleDecision = Readonly<{
  topology: MathScheduleTopology;
  selectedPlanNodeIds: readonly string[];
  reason: string;
  expectedInformationGain: number;
  readyPlanNodeIds: readonly string[];
  duplicateKeys: readonly string[];
  replaySuppressedPlanNodeIds: readonly string[];
}>;

export type MathScheduleNodeScore = Readonly<{
  /** Posterior probability of useful (goal or frontier) progress. */
  progressProbability: number;
  /** Expected downstream value, including currently unlockable dependants. */
  expectedValue: number;
  /** Relative observed/planned effort used as a divisor, never a hard cap. */
  estimatedCost: number;
  /** Deterministic exploration bonus for routes with sparse history. */
  uncertaintyBonus: number;
  /** Final cost-aware utility used for ordering. */
  utility: number;
}>;

const boundedNumber = (value: number | undefined, fallback: number, minimum: number, maximum: number): number => {
  if (value === undefined || !Number.isFinite(value)) return fallback;
  return Math.min(maximum, Math.max(minimum, value));
};

/**
 * Compute a replayable, cost-aware score for one ready node.
 *
 * Node metadata is treated as a prior. Once a route has observations, the
 * posterior blends its measured useful-progress rate with that prior. This
 * keeps early schedules from starving unexplored routes while allowing routes
 * that repeatedly produce verified gain per unit effort to move ahead.
 */
export function scoreMathScheduleNode(
  node: MathSchedulePlanNode,
  record: MathRoutePerformanceRecord | undefined,
  unlockedDependants: number,
  observedAttempts: number
): MathScheduleNodeScore {
  const attempts = Math.max(0, record?.attempts ?? 0);
  const useful = Math.max(0, (record?.goalProgressCount ?? 0) + (record?.frontierProgressCount ?? 0));
  const empiricalProbability = (useful + 1) / (attempts + 2);
  const priorProbability = boundedNumber(node.successProbability, 0.5, 0, 1);
  const empiricalWeight = attempts / (attempts + 4);
  const progressProbability = priorProbability * (1 - empiricalWeight) + empiricalProbability * empiricalWeight;
  const measuredGain =
    record?.verifiedMarginalGain !== undefined && attempts > 0
      ? Math.max(0, record.verifiedMarginalGain / attempts)
      : 1;
  const expectedValue =
    Math.max(0.1, boundedNumber(node.downstreamValue, 1, 0, 5) + Math.max(0, unlockedDependants)) *
    progressProbability *
    Math.max(0.25, Math.min(2, measuredGain));
  const plannedEffort = boundedNumber(node.estimatedEffort, 3, 1, 5);
  const observedLeanCalls = record?.totalLeanCalls !== undefined && attempts > 0 ? record.totalLeanCalls / attempts : 0;
  const observedWallClock =
    record?.totalWallClockMs !== undefined && attempts > 0 ? record.totalWallClockMs / attempts : 0;
  // Keep telemetry dimensionless and bounded; effort metadata remains the dominant prior.
  const telemetryCost = Math.min(2, observedLeanCalls / 24 + observedWallClock / 30_000);
  const estimatedCost = Math.max(1, plannedEffort + telemetryCost);
  const uncertaintyBonus = 0.35 * Math.sqrt(Math.log(2 + Math.max(0, observedAttempts)) / (attempts + 1));
  const utility = expectedValue / estimatedCost + uncertaintyBonus;
  return Object.freeze({
    progressProbability,
    expectedValue,
    estimatedCost,
    uncertaintyBonus,
    utility,
  });
}

export function mathAssignmentDuplicateKey(
  input: Readonly<{
    statementHash: string;
    planNodeId: string;
    sourceHash?: string;
    goalFingerprint?: string;
    researchContextFingerprint?: string;
  }>
): string {
  return [
    input.statementHash.trim(),
    input.planNodeId.trim(),
    input.sourceHash?.trim() ?? '',
    input.goalFingerprint?.trim() ?? '',
    ...(input.researchContextFingerprint ? [input.researchContextFingerprint.trim()] : []),
  ].join('|');
}

export function mathAssignmentDuplicateDigest(input: Parameters<typeof mathAssignmentDuplicateKey>[0]): string {
  return crypto.createHash('sha256').update(mathAssignmentDuplicateKey(input)).digest('hex');
}

function normalizedFiles(files: readonly string[] | undefined): readonly string[] {
  return Object.freeze(
    [...new Set((files ?? []).map((file) => file.trim()).filter(Boolean))].sort((left, right) =>
      left.localeCompare(right)
    )
  );
}

function hasFileConflict(left: readonly string[] | undefined, right: readonly string[] | undefined): boolean {
  const rightFiles = new Set(normalizedFiles(right));
  return normalizedFiles(left).some((file) => rightFiles.has(file));
}

function topologyFor(
  input: MathScheduleInput,
  readyCount: number
): Readonly<{
  topology: MathScheduleTopology;
  reason: string;
}> {
  const evidence = input.lastEvidence;
  if (evidence === 'counterexample') {
    return {
      topology: 'mainline_counterexample',
      reason: 'A counterexample was found; test the route boundary before spending another repair episode.',
    };
  }
  if (
    evidence === 'unknown_api' ||
    evidence === 'goal_unchanged' ||
    evidence === 'scaffold_only' ||
    (input.progress?.scaffoldOnlyStreak ?? 0) >= 2
  ) {
    return {
      topology: readyCount > 1 ? 'mainline_support' : 'mainline_review',
      reason:
        readyCount > 1
          ? 'The mainline did not move; reserve one independent support lane and keep one mainline lane.'
          : 'The mainline did not move; review the proof state before another same-route repair.',
    };
  }
  if (evidence === 'independent_frontier' || (input.progress?.goalProgressCount ?? 0) > 0) {
    return {
      topology: 'mainline_support',
      reason: 'An independent frontier is ready and can progress without duplicating the active node.',
    };
  }
  return {
    topology: 'mainline',
    reason: 'Continue the dependency-ready mainline node.',
  };
}

/**
 * Selects dependency-ready, non-duplicate, non-conflicting proof nodes.
 * Selection is stable by cost-aware utility, expected value, posterior
 * progress probability, effort, then id.
 */
export function selectMathSchedule(input: MathScheduleInput): MathScheduleDecision {
  if (!Number.isSafeInteger(input.availableSlots) || input.availableSlots < 0) {
    throw new TypeError('availableSlots must be a nonnegative integer');
  }
  const nodes = input.plan.planNodes as readonly MathSchedulePlanNode[];
  const byId = new Map(nodes.map((node) => [node.id, node]));
  const active = (input.activeAssignments ?? []).filter((assignment) => assignment.status !== 'completed');
  const activeNodeIds = new Set(active.map((assignment) => assignment.planNodeId));
  const activeDuplicateKeys = active.map((assignment) =>
    mathAssignmentDuplicateKey({
      statementHash: assignment.statementHash,
      planNodeId: assignment.planNodeId,
      sourceHash: assignment.sourceHash,
      goalFingerprint: assignment.goalFingerprint,
      researchContextFingerprint: assignment.researchContextFingerprint,
    })
  );
  const duplicateKeys = [...new Set([...activeDuplicateKeys, ...(input.completedAssignmentKeys ?? [])])];
  const duplicateKeySet = new Set(duplicateKeys);
  const completedAssignmentDigests = new Set(input.completedAssignmentDigests ?? []);
  const routePerformance = new Map(
    (input.routePerformance ?? [])
      .filter((record) => !input.routeFingerprint || record.routeFingerprint === input.routeFingerprint)
      .map((record) => [record.planNodeId, record])
  );
  const replaySuppressedPlanNodeIds = nodes
    .filter((node) => {
      const record = routePerformance.get(node.id);
      return Boolean(
        record &&
        input.goalFingerprint &&
        record.bestProofStateFingerprint === input.goalFingerprint &&
        record.researchContextFingerprint === input.researchContextFingerprint &&
        record.goalProgressCount === 0 &&
        record.attempts > 0
      );
    })
    .map((node) => node.id);
  const replaySuppressed = new Set(replaySuppressedPlanNodeIds);
  const observedAttempts = [...routePerformance.values()].reduce((sum, item) => sum + item.attempts, 0);
  const unlockedDependants = new Map<string, number>();
  // Count only dependants whose other prerequisites are already verified. This
  // is O(V*E), whereas recomputing a full node scan for each dependency makes
  // large proof plans unnecessarily quadratic in the hot scheduling path.
  for (const candidate of nodes) {
    for (const dependencyId of candidate.dependsOn) {
      const dependency = byId.get(dependencyId);
      if (!dependency || dependency.status === 'kernel_verified' || dependency.status === 'refuted') continue;
      if (candidate.dependsOn.every((id) => id === dependencyId || byId.get(id)?.status === 'kernel_verified')) {
        unlockedDependants.set(dependencyId, (unlockedDependants.get(dependencyId) ?? 0) + 1);
      }
    }
  }
  const activeFiles = active.flatMap((assignment) => normalizedFiles(assignment.exclusiveFiles));
  const ready = nodes
    .filter((node) => node.status !== 'kernel_verified' && node.status !== 'refuted')
    .filter((node) => !activeNodeIds.has(node.id))
    .filter((node) => {
      const identity = {
        statementHash: input.statementHash,
        planNodeId: node.id,
        sourceHash: input.sourceHash,
        goalFingerprint: input.goalFingerprint,
        researchContextFingerprint: input.researchContextFingerprint,
      };
      return (
        !duplicateKeySet.has(mathAssignmentDuplicateKey(identity)) &&
        !completedAssignmentDigests.has(mathAssignmentDuplicateDigest(identity))
      );
    })
    .filter((node) => !replaySuppressed.has(node.id))
    .filter((node) => node.dependsOn.every((dependencyId) => byId.get(dependencyId)?.status === 'kernel_verified'))
    .sort((left, right) => {
      const score = (node: MathSchedulePlanNode): readonly number[] => {
        const scored = scoreMathScheduleNode(
          node,
          routePerformance.get(node.id),
          unlockedDependants.get(node.id) ?? 0,
          observedAttempts
        );
        return [scored.utility, scored.expectedValue, scored.progressProbability, -scored.estimatedCost];
      };
      const leftScore = score(left);
      const rightScore = score(right);
      for (let index = 0; index < leftScore.length; index += 1) {
        if (leftScore[index] !== rightScore[index]) return rightScore[index] - leftScore[index];
      }
      return left.id.localeCompare(right.id);
    });
  const { topology, reason } = topologyFor(input, ready.length);
  const selected: MathSchedulePlanNode[] = [];
  for (const node of ready) {
    if (selected.length >= input.availableSlots) break;
    const files = normalizedFiles(node.exclusiveFiles);
    if (hasFileConflict(files, activeFiles) || selected.some((item) => hasFileConflict(files, item.exclusiveFiles)))
      continue;
    selected.push(node);
  }
  return Object.freeze({
    topology,
    selectedPlanNodeIds: Object.freeze(selected.map((node) => node.id)),
    reason,
    expectedInformationGain: selected.reduce((sum, node) => {
      return (
        sum +
        scoreMathScheduleNode(
          node,
          routePerformance.get(node.id),
          unlockedDependants.get(node.id) ?? 0,
          observedAttempts
        ).expectedValue
      );
    }, 0),
    readyPlanNodeIds: Object.freeze(ready.map((node) => node.id)),
    duplicateKeys: Object.freeze(duplicateKeys),
    replaySuppressedPlanNodeIds: Object.freeze(replaySuppressedPlanNodeIds),
  });
}
