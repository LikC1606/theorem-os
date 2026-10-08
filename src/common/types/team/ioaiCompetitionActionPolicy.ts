/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

export const IOAI_COMPETITION_MCP_ACTIONS = Object.freeze([
  'system_status',
  'environment_preflight',
  'bootstrap_run',
  'task_import',
  'evaluator_audit',
  'competition_lock',
  'contest_snapshot',
  'official_submission',
  'baseline_run',
  'benchmark_run',
  'benchmark_read',
  'frontier_snapshot',
  'trial_run',
  'trial_batch',
  'tune_create',
  'tune_ask',
  'tune_tell',
  'tune_status',
  'report_generate',
] as const);

export type IoaiCompetitionMcpAction = (typeof IOAI_COMPETITION_MCP_ACTIONS)[number];
export type IoaiCompetitionPolicyRoleId =
  | 'ioai-lead'
  | `ioai-subagent-${'exploit' | 'explore' | 'debug' | 'audit' | 'fusion'}`
  | `ioai-subagent-${'exploit' | 'explore' | 'debug' | 'audit' | 'fusion'}-${number}`;

const LEAD_ACTIONS = Object.freeze<IoaiCompetitionMcpAction[]>([
  'system_status',
  'competition_lock',
  'environment_preflight',
  'bootstrap_run',
  'task_import',
  'contest_snapshot',
  'evaluator_audit',
  'baseline_run',
  'frontier_snapshot',
  'trial_run',
  'trial_batch',
  'tune_create',
  'tune_ask',
  'tune_tell',
  'tune_status',
  'report_generate',
]);
const AUTHORIZED_LEAD_ACTIONS = Object.freeze<IoaiCompetitionMcpAction[]>([...LEAD_ACTIONS, 'official_submission']);
const SUBAGENT_ACTIONS = Object.freeze<IoaiCompetitionMcpAction[]>(['system_status']);

const ACTION_SET = new Set<IoaiCompetitionMcpAction>(IOAI_COMPETITION_MCP_ACTIONS);

export function isIoaiCompetitionMcpAction(value: unknown): value is IoaiCompetitionMcpAction {
  return typeof value === 'string' && ACTION_SET.has(value as IoaiCompetitionMcpAction);
}

export function getIoaiCompetitionRoleActions(
  roleId: IoaiCompetitionPolicyRoleId,
  options: Readonly<{ officialSubmissionEnabled?: boolean }> = {}
): readonly IoaiCompetitionMcpAction[] {
  if (roleId === 'ioai-lead') {
    return options.officialSubmissionEnabled ? AUTHORIZED_LEAD_ACTIONS : LEAD_ACTIONS;
  }
  return SUBAGENT_ACTIONS;
}

export function getIoaiCompetitionRoleActionCeiling(
  roleId: IoaiCompetitionPolicyRoleId
): readonly IoaiCompetitionMcpAction[] {
  return roleId === 'ioai-lead' ? AUTHORIZED_LEAD_ACTIONS : SUBAGENT_ACTIONS;
}
