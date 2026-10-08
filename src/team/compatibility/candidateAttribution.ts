/**
 * @license
 * Copyright 2026 DeepScientist (deepscientist.cc)
 * SPDX-License-Identifier: Apache-2.0
 */

import { isRecord } from "../competition-runtime/protocol";

export const LEGACY_COMPETITION_CANDIDATE_ATTRIBUTION_SCHEMA =
  'deepscientist.ioai.competition.candidate-attribution.v1' as const;
export const COMPETITION_CANDIDATE_ATTRIBUTION_SCHEMA =
  'deepscientist.ioai.competition.candidate-attribution.v2' as const;

export type CompetitionCandidateAttribution = {
  schema: typeof LEGACY_COMPETITION_CANDIDATE_ATTRIBUTION_SCHEMA | typeof COMPETITION_CANDIDATE_ATTRIBUTION_SCHEMA;
  team_id: string;
  slot_id: string;
  team_run_id: string;
  turn_id?: string;
  role_id: `ioai-subagent-${CompetitionCandidateStrategyLane}`;
  strategy_lane: CompetitionCandidateStrategyLane;
};

export type CompetitionCandidateStrategyLane = 'exploit' | 'explore' | 'debug' | 'audit' | 'fusion';

export type CompetitionCandidateIdentity = {
  candidate_id: string;
  candidate_content_hash: string;
  candidate_spec_hash: string;
  candidate_attribution: CompetitionCandidateAttribution | null;
};

type Invalid = (message: string) => never;

const LEGACY_ATTRIBUTION_FIELDS = ['schema', 'team_id', 'slot_id', 'team_run_id', 'role_id', 'strategy_lane'] as const;
const ATTRIBUTION_FIELDS = [...LEGACY_ATTRIBUTION_FIELDS, 'turn_id'] as const;
const STRATEGY_LANES = new Set<CompetitionCandidateStrategyLane>(['exploit', 'explore', 'debug', 'audit', 'fusion']);
const OPERATOR_BY_LANE: Record<CompetitionCandidateStrategyLane, string> = {
  exploit: 'improve',
  explore: 'draft',
  debug: 'debug',
  audit: 'audit',
  fusion: 'ensemble',
};

export function parseCompetitionCandidateIdentity(
  source: Record<string, unknown>,
  field: string,
  invalid: Invalid
): CompetitionCandidateIdentity {
  const candidateId = requiredCandidateId(source.candidate_id, `${field}.candidate_id`, invalid);
  const attribution = parseCompetitionCandidateAttribution(
    source.candidate_attribution,
    `${field}.candidate_attribution`,
    invalid
  );
  if (attribution !== null && !isStableId(candidateId)) {
    invalid(`${field}.candidate_id must be a stable 1-128 character identifier`);
  }
  return {
    candidate_id: candidateId,
    candidate_content_hash: requiredHash(source.candidate_content_hash, `${field}.candidate_content_hash`, invalid),
    candidate_spec_hash: requiredHash(source.candidate_spec_hash, `${field}.candidate_spec_hash`, invalid),
    candidate_attribution: attribution,
  };
}

export function assertUniqueCompetitionCandidateIdentities(
  identities: readonly CompetitionCandidateIdentity[],
  field: string,
  invalid: Invalid
): void {
  const ids = new Map<string, string>();
  const contentHashes = new Map<string, string>();
  const assignments = new Map<string, string>();
  for (const identity of identities) {
    const existingContent = ids.get(identity.candidate_id);
    if (existingContent !== undefined) {
      invalid(
        existingContent === identity.candidate_content_hash
          ? `${field} contains duplicate candidate_id values`
          : `${field} rebinds a candidate_id to different content`
      );
    }
    const contentOwner = contentHashes.get(identity.candidate_content_hash);
    if (contentOwner !== undefined) invalid(`${field} contains duplicate candidate content hashes`);
    ids.set(identity.candidate_id, identity.candidate_content_hash);
    contentHashes.set(identity.candidate_content_hash, identity.candidate_id);
    if (identity.candidate_attribution !== null) {
      const assignment = attributionAssignmentKey(identity.candidate_attribution);
      if (assignments.has(assignment)) invalid(`${field} contains duplicate candidate attribution assignments`);
      assignments.set(assignment, identity.candidate_id);
    }
  }
}

export function assertCompetitionCandidateLane(
  identity: CompetitionCandidateIdentity,
  lane: string,
  operator: string,
  field: string,
  invalid: Invalid
): void {
  const attribution = identity.candidate_attribution;
  if (attribution === null) return;
  if (attribution.strategy_lane !== lane) invalid(`${field}.lane does not match candidate attribution`);
  if (OPERATOR_BY_LANE[attribution.strategy_lane] !== operator) {
    invalid(`${field}.operator does not match candidate attribution`);
  }
}

export function parseCompetitionCandidateAttribution(
  value: unknown,
  field: string,
  invalid: Invalid
): CompetitionCandidateAttribution | null {
  if (value === null) return null;
  if (!isRecord(value)) invalid(`${field} must be an object or null`);
  const schema = value.schema;
  if (
    schema !== COMPETITION_CANDIDATE_ATTRIBUTION_SCHEMA &&
    schema !== LEGACY_COMPETITION_CANDIDATE_ATTRIBUTION_SCHEMA
  ) {
    invalid(`${field}.schema is unsupported`);
  }
  const keys = Object.keys(value).toSorted();
  const expected = [
    ...(schema === COMPETITION_CANDIDATE_ATTRIBUTION_SCHEMA ? ATTRIBUTION_FIELDS : LEGACY_ATTRIBUTION_FIELDS),
  ].toSorted();
  if (keys.length !== expected.length || keys.some((key, index) => key !== expected[index])) {
    invalid(`${field} fields are invalid`);
  }
  const lane = stableId(value.strategy_lane, `${field}.strategy_lane`, invalid);
  if (!STRATEGY_LANES.has(lane as CompetitionCandidateStrategyLane)) {
    invalid(`${field}.strategy_lane is unsupported`);
  }
  const strategyLane = lane as CompetitionCandidateStrategyLane;
  const roleId = stableId(value.role_id, `${field}.role_id`, invalid);
  if (roleId !== `ioai-subagent-${strategyLane}`) invalid(`${field}.role_id does not match strategy_lane`);
  return {
    schema,
    team_id: stableId(value.team_id, `${field}.team_id`, invalid),
    slot_id: stableId(value.slot_id, `${field}.slot_id`, invalid),
    team_run_id: stableId(value.team_run_id, `${field}.team_run_id`, invalid),
    ...(schema === COMPETITION_CANDIDATE_ATTRIBUTION_SCHEMA
      ? { turn_id: stableId(value.turn_id, `${field}.turn_id`, invalid) }
      : {}),
    role_id: roleId as CompetitionCandidateAttribution['role_id'],
    strategy_lane: strategyLane,
  };
}

function requiredCandidateId(value: unknown, field: string, invalid: Invalid): string {
  if (
    typeof value !== 'string' ||
    value.length === 0 ||
    value.length > 256 ||
    value.trim() !== value ||
    value.includes('\0')
  ) {
    invalid(`${field} must be a stable non-empty string`);
  }
  return value;
}

function stableId(value: unknown, field: string, invalid: Invalid): string {
  if (typeof value !== 'string' || !isStableId(value)) {
    invalid(`${field} must be a stable 1-128 character identifier`);
  }
  return value;
}

function isStableId(value: string): boolean {
  return /^[A-Za-z0-9][A-Za-z0-9._:-]{0,127}$/u.test(value);
}

function requiredHash(value: unknown, field: string, invalid: Invalid): string {
  if (typeof value !== 'string' || !/^[0-9a-f]{64}$/u.test(value)) invalid(`${field} must be a SHA-256 hash`);
  return value;
}

function attributionAssignmentKey(attribution: CompetitionCandidateAttribution): string {
  return `${attribution.team_id}\0${attribution.slot_id}\0${attribution.team_run_id}\0${attribution.turn_id ?? 'legacy-v1'}`;
}
