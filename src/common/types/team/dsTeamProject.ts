/**
 * @license
 * Copyright 2026 DeepScientist (deepscientist.cc)
 * SPDX-License-Identifier: Apache-2.0
 */

/** Stable MCP identity for project-scoped DeepScientist Team coordination. */
export const DS_TEAM_PROJECT_MCP_NAME = 'ds-team-project' as const;

/** Frozen conversations may still contain these names. Do not use them for new runtimes. */
export const DS_TEAM_PROJECT_MCP_LEGACY_NAMES = ['deepscientist-lark-project-agent'] as const;

export const DS_TEAM_PROJECT_RUNTIME_PREFIX = 'ds-team-project-runtime' as const;
export const DS_TEAM_PROJECT_RUNTIME_LEGACY_PREFIXES = ['deepscientist-project-runtime'] as const;

export const DS_TEAM_PROJECT_TOOL = 'ds_team' as const;
export const DS_TEAM_PROJECT_TOOL_SURFACE = 'ds-team' as const;

export type DsTeamProjectRole = 'leader' | 'worker';

export type DsTeamProjectAction =
  | 'describe'
  | 'inspect'
  | 'dispatch'
  | 'status'
  | 'message'
  | 'request_decision'
  | 'decide_request'
  | 'review'
  | 'submit'
  | 'block'
  | 'graph';

export type DsTeamProjectTargetKind = 'local_slot' | 'remote_device' | 'lark_user';

export type DsTeamProjectRuntimeState =
  | 'queued'
  | 'starting'
  | 'running'
  | 'waiting_input'
  | 'needs_approval'
  | 'needs_review'
  | 'blocked'
  | 'completed'
  | 'failed'
  | 'offline';

export function isDsTeamProjectMcpName(name: string | undefined): boolean {
  if (!name) return false;
  return name === DS_TEAM_PROJECT_MCP_NAME || DS_TEAM_PROJECT_MCP_LEGACY_NAMES.some((legacy) => legacy === name);
}

export function isDsTeamProjectRuntimeName(name: string | undefined): boolean {
  if (!name) return false;
  if (name.startsWith(`${DS_TEAM_PROJECT_RUNTIME_PREFIX}-`)) return true;
  return DS_TEAM_PROJECT_RUNTIME_LEGACY_PREFIXES.some((prefix) => name.startsWith(`${prefix}-`));
}

export function dsTeamActionsForRole(role: DsTeamProjectRole): readonly DsTeamProjectAction[] {
  return role === 'leader'
    ? ['describe', 'inspect', 'dispatch', 'status', 'message', 'request_decision', 'decide_request', 'review', 'graph']
    : ['describe', 'inspect', 'status', 'message', 'submit', 'block'];
}
