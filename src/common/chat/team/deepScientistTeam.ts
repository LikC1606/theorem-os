/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

const DEEPSCIENTIST_TEAM_BACKENDS = new Set(['claude', 'codex']);

export function canUseDeepScientistTeam(backend?: string): boolean {
  return DEEPSCIENTIST_TEAM_BACKENDS.has(backend?.trim().toLowerCase() ?? '');
}
