/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

import crypto from 'node:crypto';
import {
  mathActionablePlanScheduleFromNormalized,
  normalizeMathPlanSnapshot,
  type MathPlanSnapshot,
  type MathProofState,
} from "../common/types/team/mathematicsTeam";

export type LeanProofFrontier = Readonly<{
  revision: number;
  rootNodeId: string;
  openNodeIds: readonly string[];
  verifiedNodeIds: readonly string[];
  bottleneckNodeId?: string;
  activeStateId?: string;
  openGoalCount: number | null;
  progressFingerprint: string;
}>;

const sha256 = (value: string): string => crypto.createHash('sha256').update(value, 'utf8').digest('hex');

/** Derive actionable proof state from trusted plan/receipt inputs only. */
export function deriveLeanProofFrontier(
  input: Readonly<{
    plan: MathPlanSnapshot;
    verifiedNodeIds?: readonly string[];
    proofState?: MathProofState;
    revision?: number;
  }>
): LeanProofFrontier {
  const plan = normalizeMathPlanSnapshot(input.plan);
  const verified = new Set(plan.planNodes.filter((node) => node.status === 'kernel_verified').map((node) => node.id));
  for (const nodeId of input.verifiedNodeIds ?? []) {
    if (plan.planNodes.some((node) => node.id === nodeId)) verified.add(nodeId);
  }
  // Receipt-derived verification is an overlay; do not invent plan evidence references.
  const schedule = mathActionablePlanScheduleFromNormalized(
    plan.planNodes.map((node) => (verified.has(node.id) ? { ...node, status: 'kernel_verified' as const } : node))
  );
  const verifiedNodeIds = plan.planNodes.filter((node) => verified.has(node.id)).map((node) => node.id);
  const openGoalCount = input.proofState?.openGoals.length ?? null;
  const progressFingerprint = sha256(
    JSON.stringify({
      rootNodeId: plan.rootNodeId,
      openNodeIds: schedule.openFrontierNodeIds,
      verifiedNodeIds,
      goalFingerprint: input.proofState?.goalFingerprint ?? null,
      openGoalCount,
    })
  );
  return Object.freeze({
    revision: Math.max(0, Math.floor(input.revision ?? 0)),
    rootNodeId: plan.rootNodeId,
    openNodeIds: schedule.openFrontierNodeIds,
    verifiedNodeIds: Object.freeze(verifiedNodeIds),
    ...(schedule.rankedNodeIds[0] ? { bottleneckNodeId: schedule.rankedNodeIds[0] } : {}),
    ...(input.proofState?.stateId ? { activeStateId: input.proofState.stateId } : {}),
    openGoalCount,
    progressFingerprint,
  });
}
