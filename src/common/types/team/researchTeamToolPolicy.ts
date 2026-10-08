/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

import {
  RESEARCH_TEAM_CAPABILITY_PROFILE_ENV,
  RESEARCH_TEAM_CAPABILITY_PROJECT_ROOT_ENV,
  RESEARCH_TEAM_CAPABILITY_ROLE_ENV,
  RESEARCH_TEAM_CAPABILITY_ROLE_KIND_ENV,
  RESEARCH_TEAM_CAPABILITY_SCHEMA_ENV,
  RESEARCH_TEAM_CAPABILITY_WORKFLOW_ENV,
  RESEARCH_TEAM_TOOL_POLICY_ALLOWED_ENV,
  RESEARCH_TEAM_TOOL_POLICY_DENIED_ENV,
  RESEARCH_TEAM_TOOL_POLICY_SCHEMA,
  RESEARCH_TEAM_TOOL_POLICY_SCHEMA_ENV,
} from "../../config/builtinMcpConstants";
import type { ResearchTeamRoleKind, ResearchTeamToolActionPolicy } from "./researchTeamContracts";

export type ResearchTeamToolPolicySnapshot = Readonly<{
  schema: typeof RESEARCH_TEAM_TOOL_POLICY_SCHEMA;
  profileId: string;
  workflowId: string;
  roleId: string;
  roleKind: ResearchTeamRoleKind;
  projectRoot: string;
  allowedTools: readonly ResearchTeamToolActionPolicy[];
  deniedTools: readonly ResearchTeamToolActionPolicy[];
}>;

const POLICY_ENV_KEYS = [
  RESEARCH_TEAM_TOOL_POLICY_SCHEMA_ENV,
  RESEARCH_TEAM_TOOL_POLICY_ALLOWED_ENV,
  RESEARCH_TEAM_TOOL_POLICY_DENIED_ENV,
] as const;

export function readResearchTeamToolPolicy(
  env: Readonly<Record<string, string | undefined>> = process.env
): ResearchTeamToolPolicySnapshot | undefined {
  if (POLICY_ENV_KEYS.every((key) => env[key] === undefined)) {
    if (env[RESEARCH_TEAM_CAPABILITY_SCHEMA_ENV] !== undefined) {
      throw new Error('Research Team tool-policy environment is missing for a managed capability.');
    }
    return undefined;
  }
  if (POLICY_ENV_KEYS.some((key) => env[key] === undefined)) {
    throw new Error('Research Team tool-policy environment is incomplete.');
  }
  if (env[RESEARCH_TEAM_TOOL_POLICY_SCHEMA_ENV] !== RESEARCH_TEAM_TOOL_POLICY_SCHEMA) {
    throw new Error('Research Team tool-policy schema is unsupported.');
  }
  const roleKind = requiredText(env[RESEARCH_TEAM_CAPABILITY_ROLE_KIND_ENV], 'role kind');
  if (roleKind !== 'lead' && roleKind !== 'worker') {
    throw new Error('Research Team tool-policy role kind is invalid.');
  }
  return Object.freeze({
    schema: RESEARCH_TEAM_TOOL_POLICY_SCHEMA,
    profileId: requiredText(env[RESEARCH_TEAM_CAPABILITY_PROFILE_ENV], 'profile'),
    workflowId: requiredText(env[RESEARCH_TEAM_CAPABILITY_WORKFLOW_ENV], 'workflow'),
    roleId: requiredText(env[RESEARCH_TEAM_CAPABILITY_ROLE_ENV], 'role'),
    roleKind,
    projectRoot: requiredText(env[RESEARCH_TEAM_CAPABILITY_PROJECT_ROOT_ENV], 'project root'),
    allowedTools: readPolicies(env[RESEARCH_TEAM_TOOL_POLICY_ALLOWED_ENV], 'allowed'),
    deniedTools: readPolicies(env[RESEARCH_TEAM_TOOL_POLICY_DENIED_ENV], 'denied'),
  });
}

export function assertResearchTeamToolActionAuthorized(
  toolName: string,
  action: string,
  env: Readonly<Record<string, string | undefined>> = process.env
): void {
  const policy = readResearchTeamToolPolicy(env);
  if (!policy) return;
  const normalizedTool = requiredText(toolName, 'tool name');
  const normalizedAction = requiredText(action, 'tool action');
  if (
    policy.deniedTools.some((entry) => policyMatches(entry, normalizedTool, normalizedAction)) ||
    !policy.allowedTools.some((entry) => policyMatches(entry, normalizedTool, normalizedAction))
  ) {
    throw new Error(
      'Research Team role ' +
        policy.roleId +
        ' is not authorized for ' +
        normalizedTool +
        '(action=' +
        JSON.stringify(normalizedAction) +
        ').'
    );
  }
}

/** Advertise only actions the current role can execute; preserve standalone tools. */
export function researchTeamAuthorizedToolActions<T extends string>(
  toolName: string,
  actions: readonly T[],
  env: Readonly<Record<string, string | undefined>> = process.env
): T[] {
  const policy = readResearchTeamToolPolicy(env);
  if (!policy) return [...actions];
  return actions.filter(
    (action) =>
      !policy.deniedTools.some((entry) => policyMatches(entry, toolName, action)) &&
      policy.allowedTools.some((entry) => policyMatches(entry, toolName, action))
  );
}

function readPolicies(value: string | undefined, label: string): readonly ResearchTeamToolActionPolicy[] {
  let parsed: unknown;
  try {
    parsed = JSON.parse(requiredText(value, label + ' tool policy'));
  } catch {
    throw new Error('Research Team ' + label + ' tool policy is not valid JSON.');
  }
  if (!Array.isArray(parsed)) throw new Error('Research Team ' + label + ' tool policy must be an array.');
  return Object.freeze(
    parsed.map((entry, index) => {
      if (!isRecord(entry)) throw new Error('Research Team ' + label + ' tool policy ' + index + ' is invalid.');
      const toolName = requiredText(entry.toolName, label + ' tool policy ' + index + ' toolName');
      if (entry.actions === '*') return Object.freeze({ toolName, actions: '*' as const });
      if (!Array.isArray(entry.actions) || !entry.actions.length) {
        throw new Error('Research Team ' + label + ' tool policy ' + index + ' actions are invalid.');
      }
      const actions = entry.actions.map((action, actionIndex) =>
        requiredText(action, label + ' tool policy ' + index + ' action ' + actionIndex)
      );
      return Object.freeze({ toolName, actions: Object.freeze(actions) });
    })
  );
}

function policyMatches(policy: ResearchTeamToolActionPolicy, toolName: string, action: string): boolean {
  return policy.toolName === toolName && (policy.actions === '*' || policy.actions.includes(action));
}

function requiredText(value: unknown, field: string): string {
  if (typeof value !== 'string' || !value.trim())
    throw new Error('Research Team tool-policy ' + field + ' is required.');
  return value.trim();
}

function isRecord(value: unknown): value is Record<string, unknown> {
  return Boolean(value) && typeof value === 'object' && !Array.isArray(value);
}
