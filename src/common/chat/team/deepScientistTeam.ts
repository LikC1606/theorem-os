/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

export const DEEPSCIENTIST_TEAM_CONVERSATION_SCHEMA = 'deepscientist.team.conversation.v1' as const;

const DEEPSCIENTIST_TEAM_BACKENDS = new Set(['claude', 'codex']);

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

export function canUseDeepScientistTeam(backend?: string): boolean {
  return DEEPSCIENTIST_TEAM_BACKENDS.has(backend?.trim().toLowerCase() ?? '');
}
