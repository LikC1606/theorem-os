/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

export const DEEPSCIENTIST_TEAM_SKILL_NAME = 'deepscientist-team' as const;
export const DEEPSCIENTIST_TEAM_CONFIG_SCHEMA = 'deepscientist.team.config.v1' as const;
export const DEEPSCIENTIST_TEAM_CONVERSATION_SCHEMA = 'deepscientist.team.conversation.v1' as const;

export const DEEPSCIENTIST_TEAM_MIN_AGENT_LIMIT = 4 as const;
export const DEEPSCIENTIST_TEAM_DEFAULT_AGENT_LIMIT = 8 as const;
export const DEEPSCIENTIST_TEAM_MAX_AGENT_LIMIT = 50 as const;
export const DEEPSCIENTIST_TEAM_MIN_REASONING_CONCURRENCY = 1 as const;
export const DEEPSCIENTIST_TEAM_DEFAULT_REASONING_CONCURRENCY = 4 as const;
export const DEEPSCIENTIST_TEAM_MAX_REASONING_CONCURRENCY = 10 as const;
export const DEEPSCIENTIST_TEAM_DEFAULT_THOUGHT_LEVEL = 'xhigh' as const;

const DEEPSCIENTIST_TEAM_BACKENDS = new Set(['claude', 'codex']);

export type DeepScientistTeamConfig = Readonly<{
  agentLimit: number;
  reasoningConcurrency: number;
  /**
   * Keep one advisory Strategy Worker available for bound IMO runs whose
   * FAST_CHECK requires route discovery before formalization.  Ordinary
   * mathematics Teams retain the single persistent Formalizer by default.
   */
  mathematicsRouteDiscovery?: boolean;
  /**
   * Replace one Strategy Worker with a second Lean Engineer that owns the
   * complete original theorem through a structurally different decomposition.
   * The Team size is unchanged; the first host-verified integration wins.
   */
  mathematicsSecondProofOwner?: boolean;
}>;

export type DeepScientistTeamConversationExtra = Readonly<{
  schema: typeof DEEPSCIENTIST_TEAM_CONVERSATION_SCHEMA;
  enabled: true;
  profileId: string;
  agentLimit: number;
  reasoningConcurrency: number;
  requestedThoughtLevel: string;
  managedThoughtLevel: string;
  orchestration: 'deepscientist-managed';
  workerIsolation: 'git-worktree';
  delivery: 'event-driven';
}>;

export function normalizeDeepScientistTeamConfig(value?: Partial<DeepScientistTeamConfig>): DeepScientistTeamConfig {
  const agentLimit = normalizeInteger(
    value?.agentLimit,
    DEEPSCIENTIST_TEAM_DEFAULT_AGENT_LIMIT,
    DEEPSCIENTIST_TEAM_MIN_AGENT_LIMIT,
    DEEPSCIENTIST_TEAM_MAX_AGENT_LIMIT
  );
  const reasoningConcurrency = normalizeInteger(
    value?.reasoningConcurrency,
    DEEPSCIENTIST_TEAM_DEFAULT_REASONING_CONCURRENCY,
    DEEPSCIENTIST_TEAM_MIN_REASONING_CONCURRENCY,
    Math.min(DEEPSCIENTIST_TEAM_MAX_REASONING_CONCURRENCY, agentLimit)
  );
  return Object.freeze({
    agentLimit,
    reasoningConcurrency,
    ...(value?.mathematicsRouteDiscovery === true ? { mathematicsRouteDiscovery: true } : {}),
  });
}

/**
 * DeepScientist Team is the only proactive orchestrator when enabled. Codex
 * Ultra already injects its own proactive delegation policy, so managed Team
 * sessions use XHigh instead of nesting two independent schedulers.
 */
export function resolveDeepScientistTeamThoughtLevel(value?: string | null): string {
  const normalized = value?.trim().toLowerCase();
  if (!normalized || normalized === 'ultra') return DEEPSCIENTIST_TEAM_DEFAULT_THOUGHT_LEVEL;
  return normalized;
}

export function createDeepScientistTeamConversationExtra(input: {
  profileId: string;
  config: DeepScientistTeamConfig;
  requestedThoughtLevel?: string | null;
}): DeepScientistTeamConversationExtra {
  const requestedThoughtLevel =
    input.requestedThoughtLevel?.trim().toLowerCase() || DEEPSCIENTIST_TEAM_DEFAULT_THOUGHT_LEVEL;
  const mathematicsMainline =
    input.profileId === 'mathematics-research-team' && input.config.mathematicsRouteDiscovery !== true;
  const mathematicsRouteDiscovery =
    input.profileId === 'mathematics-research-team' && input.config.mathematicsRouteDiscovery === true;
  return Object.freeze({
    schema: DEEPSCIENTIST_TEAM_CONVERSATION_SCHEMA,
    enabled: true,
    profileId: requiredText(input.profileId, 'profileId'),
    // The mathematics profile deliberately collapses to one persistent
    // Formalizer even when the general Team setting requests a larger pool.
    agentLimit: mathematicsMainline
      ? 1
      : mathematicsRouteDiscovery
        ? Math.min(2, input.config.agentLimit)
        : input.config.agentLimit,
    reasoningConcurrency: mathematicsMainline
      ? 1
      : mathematicsRouteDiscovery
        ? Math.min(2, input.config.reasoningConcurrency)
        : input.config.reasoningConcurrency,
    requestedThoughtLevel,
    managedThoughtLevel: resolveDeepScientistTeamThoughtLevel(requestedThoughtLevel),
    orchestration: 'deepscientist-managed',
    workerIsolation: 'git-worktree',
    delivery: 'event-driven',
  });
}

export function canUseDeepScientistTeam(backend?: string): boolean {
  return DEEPSCIENTIST_TEAM_BACKENDS.has(backend?.trim().toLowerCase() ?? '');
}

function normalizeInteger(value: number | undefined, fallback: number, minimum: number, maximum: number): number {
  return Number.isSafeInteger(value) ? Math.min(maximum, Math.max(minimum, Number(value))) : fallback;
}

function requiredText(value: string, field: string): string {
  const normalized = value.trim();
  if (!normalized) throw new TypeError(`DeepScientist Team ${field} is required`);
  return normalized;
}
