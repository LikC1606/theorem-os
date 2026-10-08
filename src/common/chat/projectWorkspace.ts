/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

import type { ProjectGitDomain } from "../types/office/preview";

export const PROJECT_WORKSPACE_SKILL_NAME = 'deepscientist-project-workspace' as const;
export const PROJECT_WORKSPACE_SKILL_PATH = 'resources/skills/project-workspace/SKILL.md' as const;
export const PROJECT_WORKSPACE_TOOL_NAME = 'project_workspace' as const;

export const PROJECT_WORKSPACE_ENV_KEYS = {
  projectRoot: 'DEEPSCIENTIST_PROJECT_ROOT',
  projectId: 'DEEPSCIENTIST_PROJECT_ID',
  conversationId: 'DEEPSCIENTIST_CONVERSATION_ID',
  domain: 'DEEPSCIENTIST_PROJECT_DOMAIN',
  checkpointStages: 'DEEPSCIENTIST_PROJECT_CHECKPOINT_STAGES',
} as const;

export const DEFAULT_PROJECT_CHECKPOINT_STAGES = ['project', 'work', 'result'] as const;

const RESEARCH_STRATEGY_DOMAINS = new Set<ProjectGitDomain>([
  'research',
  'medical_evidence',
  'financial',
  'financial_factor',
  'target_discovery',
  'mathematics',
  'challenge',
]);

const RESEARCH_STRATEGY_EXEMPT_STAGES = new Set(['project', 'report', 'writing', 'review', 'final']);

/**
 * Research checkpoints describe how the recorded work advances the research
 * tree. Initializers and presentation-only commits remain ordinary Git nodes.
 */
export const requiresResearchStrategyForCheckpoint = (domain: ProjectGitDomain, stage: string): boolean => {
  const normalizedStage = stage.trim().toLowerCase();
  return Boolean(
    RESEARCH_STRATEGY_DOMAINS.has(domain) &&
    normalizedStage &&
    !RESEARCH_STRATEGY_EXEMPT_STAGES.has(normalizedStage) &&
    !normalizedStage.endsWith('-report')
  );
};

export type ProjectWorkspaceProfile = {
  domain: ProjectGitDomain;
  checkpointStages: string[];
};

export type ProjectWorkspacePromptOptions = ProjectWorkspaceProfile & {
  workspace?: string;
  projectId?: string;
  conversationId?: string;
};

const describeBoundValue = (value: string | undefined, fallback: string): string => value?.trim() || fallback;

export function buildProjectWorkspacePrompt(options: ProjectWorkspacePromptOptions): string {
  const stages = Array.from(new Set(options.checkpointStages.map((stage) => stage.trim()).filter(Boolean)));
  const hasProjectBinding = Boolean(
    options.workspace?.trim() && options.projectId?.trim() && options.conversationId?.trim()
  );
  if (!hasProjectBinding) {
    return [
      '# Project Workspace Contract',
      '',
      'Project Git availability: unavailable in this runtime because no repository binding was supplied.',
      'Continue the user task without project_workspace calls. Do not claim that a source checkpoint, branch, or Git history was created, and do not invent commit identifiers.',
      'Science Artifact tools may still manage reports, evidence, claims, Viewer state, and artifact snapshots when those tools are available. Those records are not source-project Git commits.',
      'If a later mode instruction asks for project_workspace, this availability rule takes precedence until the runtime supplies a bound project root, project id, and conversation id.',
    ].join('\n');
  }
  return [
    '# Project Workspace Contract',
    '',
    `Authorized project root: ${describeBoundValue(options.workspace, 'the workspace bound by the runtime')}`,
    `Project id: ${describeBoundValue(options.projectId, 'managed by DeepScientist')}`,
    `Conversation id: ${describeBoundValue(options.conversationId, 'the current conversation')}`,
    `Checkpoint domain: ${options.domain}`,
    `Allowed checkpoint stages: ${stages.join(', ') || DEFAULT_PROJECT_CHECKPOINT_STAGES.join(', ')}`,
    `Runtime Skill directory: ${describeBoundValue(options.workspace, 'the workspace bound by the runtime')}/.agents/skills`,
    '',
    `Use the $${PROJECT_WORKSPACE_SKILL_NAME} skill and the ${PROJECT_WORKSPACE_TOOL_NAME} MCP tool for source-project status, verified checkpoints, history, and branch actions. Git is the default project record for every mode; enabling or disabling a continuation mode does not enable or disable it.`,
    'Every bound task starts by reading project_workspace(action="status") once before substantive work. In an ordinary mode, Git is task-scoped memory: save only meaningful verified file changes needed to resume or deliver the current task, then stop when that task ends. Do not create a research roadmap or route-mode history for ordinary work.',
    'Every meaningful research checkpoint must classify the recorded work with routeMode=explore|deepen|fuse|repair|stop: explore compares a materially different route, deepen advances the strongest route, fuse combines compatible verified routes, repair corrects a data/tool/reproducibility fault, and stop records a defensible pause. Initial project setup and presentation-only report, writing, review, or final checkpoints are exempt. The tool writes the Git prefix and metadata; do not hand-write prefixes or create an empty checkpoint only to record a label.',
    'Discovery Mode uses the same project Git record but adds a long-lived research_roadmap. It may revisit and switch research directions across many continuations; a continuation boundary or route-mode change alone is not a reason to create a source checkpoint.',
    'Skill loading contract: use the exact Skill path supplied by the runtime. For a canonical Skill id, the native Codex fallback is <Runtime Skill directory>/<skill-id>/SKILL.md. Do not construct /Applications/.../Resources/skills/<skill-id> or infer a package directory from the id; physical package folders may use different names. Even when a Skill body mentions a relative sibling path, resolve its canonical Skill id through the runtime directory instead.',
    'A failed or empty file read does not count as loading a Skill. Retry once through the canonical runtime Skill directory, then report the unavailable Skill precisely and continue only when its SOP is optional; never claim that an unread Skill was loaded.',
    'The runtime created and bound the authorized project and repository above before the Agent started. Do not create another project, run git init, migrate the conversation, or perform setup in order to use it. Call project_workspace directly; its identity arguments may be omitted because the runtime resolves the authoritative binding.',
    'Read completedResearchStages as the compact resume ledger and use checkpointContract instead of guessing the bound domain, allowed stages, or verification shape. A repository with only its initialization checkpoint and no meaningful project files, portfolio, artifacts, or research checkpoints is a fresh task: do not describe it as restore/resume or load recovery/intake-audit workflows. On an actual resume, use the committed project state. Treat real commits and branches as implemented facts; plans, predictions, and uncommitted work are not commits.',
    'Create a checkpoint only after a meaningful verified change. Provide a concise message, one allowed stage, explicit project-relative includePaths, and verification as a string, {command,exitCode,summary}, an array, or {checks:[...]}. Never use implicit whole-repository staging, and never include credentials, private keys, tokens, caches, build outputs, pre-staged changes, or unrelated user work.',
    'When Discovery Mode is active, attach one researchStage receipt containing stageId, objective, successCriteria, failureCriteria, priorWorkRefs, disposition, supportingEvidenceIds, refutingEvidenceIds, exhaustionEvidenceIds, beliefDelta, reflection, and optional nextObjective. The runtime attaches the objective and run identity. Supported needs supporting evidence; refuted needs refuting evidence; exhausted needs route/search-region exhaustion evidence; runtime_failed is a tool/runtime outcome, not scientific refutation.',
    'Use the bound project root. If project_workspace reports an unavailable or mismatched binding despite the authorized values above, report a runtime fault and stop project Git actions; do not initialize, relocate, replace, reopen, migrate, reset, clean, force-checkout, or rewrite the repository to bypass it.',
    'Use Science Artifact tools separately for reports, evidence, claims, viewers, and artifact snapshots. An artifact snapshot does not replace a source-project checkpoint, and a source-project checkpoint does not replace an artifact publish.',
    'Prepare or activate a branch only after an explicit route decision and only from a clean workspace. Continue one safe route directly when branching adds no real value.',
  ].join('\n');
}
