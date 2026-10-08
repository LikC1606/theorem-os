/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

/**
 * Team status observation is intentionally a Lead-only, bounded wait. Worker
 * completion is delivered by Core events, so Workers do not need this policy.
 */
export const TEAM_WAIT_LEVEL_SECONDS = Object.freeze({
  '1m': 60,
  '5m': 5 * 60,
  '10m': 10 * 60,
} as const);

export const TEAM_WAIT_LEVELS = Object.freeze(['1m', '5m', '10m'] as const);
export const TEAM_WAIT_MAX_SECONDS = TEAM_WAIT_LEVEL_SECONDS['10m'];

export type TeamWaitLevel = keyof typeof TEAM_WAIT_LEVEL_SECONDS;

/**
 * Convert the user-facing tier to seconds. A separate helper keeps the MCP
 * schemas and the runtime normalizer on exactly the same contract.
 */
export function teamWaitSecondsForLevel(level: unknown): number | undefined {
  if (level === undefined) return undefined;
  if (typeof level !== 'string' || !Object.hasOwn(TEAM_WAIT_LEVEL_SECONDS, level)) {
    throw new Error(`wait_level must be one of: ${TEAM_WAIT_LEVELS.join(', ')}`);
  }
  return TEAM_WAIT_LEVEL_SECONDS[level as TeamWaitLevel];
}

/**
 * Keep the old short wait_seconds form working for existing prompts/tests.
 * New callers should use wait_level; direct values are accepted only for the
 * three public tiers or the historic 0-30 second diagnostic window.
 */
export function normalizeTeamWaitSeconds(value: unknown, level?: unknown): number {
  const levelSeconds = teamWaitSecondsForLevel(level);
  if (levelSeconds !== undefined) {
    if (value !== undefined && value !== levelSeconds) {
      throw new Error(`wait_seconds conflicts with wait_level=${String(level)}`);
    }
    return levelSeconds;
  }
  if (value === undefined) return 0;
  if (!Number.isSafeInteger(value) || Number(value) < 0 || Number(value) > TEAM_WAIT_MAX_SECONDS) {
    throw new Error(
      `wait_seconds must be 0-30 for a short diagnostic check, or one of ${TEAM_WAIT_LEVELS.map((item) => TEAM_WAIT_LEVEL_SECONDS[item]).join(', ')} seconds`
    );
  }
  const seconds = Number(value);
  if (seconds <= 30 || TEAM_WAIT_LEVELS.some((level) => TEAM_WAIT_LEVEL_SECONDS[level] === seconds)) {
    return seconds;
  }
  throw new Error(
    `wait_seconds must be 0-30 for a short diagnostic check, or one of ${TEAM_WAIT_LEVELS.map((item) => TEAM_WAIT_LEVEL_SECONDS[item]).join(', ')} seconds`
  );
}

export function teamWaitLevelForSeconds(seconds: number): TeamWaitLevel | undefined {
  for (const level of TEAM_WAIT_LEVELS) {
    if (TEAM_WAIT_LEVEL_SECONDS[level] === seconds) return level;
  }
  return undefined;
}
