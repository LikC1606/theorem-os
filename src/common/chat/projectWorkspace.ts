/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

import { PROJECT_GIT_DOMAINS,type ProjectGitDomain } from "../types/office/preview";

export const PROJECT_WORKSPACE_TOOL_NAME = 'project_workspace' as const;

export const PROJECT_WORKSPACE_ENV_KEYS = {
  projectRoot: 'DEEPSCIENTIST_PROJECT_ROOT',
  projectId: 'DEEPSCIENTIST_PROJECT_ID',
  conversationId: 'DEEPSCIENTIST_CONVERSATION_ID',
  domain: 'DEEPSCIENTIST_PROJECT_DOMAIN',
  checkpointStages: 'DEEPSCIENTIST_PROJECT_CHECKPOINT_STAGES',
} as const;

const RESEARCH_STRATEGY_DOMAINS = new Set<ProjectGitDomain>(
  PROJECT_GIT_DOMAINS.filter((domain) => domain !== 'general' && domain !== 'knowledge_deposition')
);

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
