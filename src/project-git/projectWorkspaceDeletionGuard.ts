/**
 * @license
 * Copyright 2026 DeepScientist (deepscientist.cc)
 * SPDX-License-Identifier: Apache-2.0
 */

import type { ProjectGitWorkspaceBinding } from "../common/types/office/preview";
import type { ProjectWorkspaceDeletionPlanRequest } from "./ProjectGitService";

export type ProjectWorkspaceDeletionConversationRecord = {
  id: string;
  type: string;
  extra?: Record<string, unknown>;
};

export type ProjectWorkspaceDeletionAuthorization =
  | { ok: true; request: ProjectWorkspaceDeletionPlanRequest }
  | { ok: false; error: string };

const comparablePath = (value: unknown): string =>
  typeof value === 'string' ? value.trim().replace(/\\/gu, '/').replace(/\/+$/gu, '').toLowerCase() : '';

const bindingFrom = (record: ProjectWorkspaceDeletionConversationRecord): ProjectGitWorkspaceBinding | undefined => {
  const value = record.extra?.project_git;
  if (!value || typeof value !== 'object' || Array.isArray(value)) return undefined;
  return value as ProjectGitWorkspaceBinding;
};

const sharesWorkspace = (
  candidate: ProjectWorkspaceDeletionConversationRecord,
  workspace: string,
  binding: ProjectGitWorkspaceBinding | undefined,
  kind: 'managed' | 'isolated-worktree' | 'temporary'
): boolean => {
  if (comparablePath(candidate.extra?.workspace) === comparablePath(workspace)) return true;
  const candidateBinding = bindingFrom(candidate);
  if (!binding || !candidateBinding) return false;
  if (kind === 'managed') {
    return Boolean(binding.projectId && binding.projectId === candidateBinding.projectId);
  }
  if (kind === 'isolated-worktree') {
    return Boolean(binding.branch && binding.branch === candidateBinding.branch);
  }
  return false;
};

export const authorizeProjectWorkspaceDeletion = (
  conversationId: string,
  conversations: ProjectWorkspaceDeletionConversationRecord[],
  deletingConversationIds: string[] = [conversationId]
): ProjectWorkspaceDeletionAuthorization => {
  const conversation = conversations.find((candidate) => candidate.id === conversationId);
  if (!conversation) return { ok: false, error: 'The conversation no longer exists.' };
  if (conversation.type !== 'acp') {
    return { ok: false, error: 'This conversation does not own a deletable project directory.' };
  }
  const workspace = typeof conversation.extra?.workspace === 'string' ? conversation.extra.workspace.trim() : '';
  if (!workspace) return { ok: false, error: 'The conversation does not have a project directory.' };

  const binding = bindingFrom(conversation);
  let kind: 'managed' | 'isolated-worktree' | 'temporary' | undefined;
  if (
    binding?.schema === 'deepscientist.project_git.v1' &&
    comparablePath(binding.workspaceRoot) === comparablePath(workspace) &&
    (binding.strategy === 'managed' || binding.strategy === 'isolated-worktree')
  ) {
    kind = binding.strategy;
  } else if (!binding && conversation.extra?.is_temporary_workspace === true) {
    kind = 'temporary';
  }
  if (!kind) {
    return { ok: false, error: 'User-selected project directories cannot be deleted with a conversation.' };
  }

  const deletionIds = new Set([conversationId, ...deletingConversationIds]);
  for (const deletingId of deletionIds) {
    const deletingConversation = conversations.find((candidate) => candidate.id === deletingId);
    if (!deletingConversation) {
      return { ok: false, error: 'A conversation selected for deletion no longer exists.' };
    }
    if (!sharesWorkspace(deletingConversation, workspace, binding, kind)) {
      return { ok: false, error: 'A conversation selected for deletion does not belong to this project.' };
    }
  }
  if (
    conversations.some(
      (candidate) => !deletionIds.has(candidate.id) && sharesWorkspace(candidate, workspace, binding, kind)
    )
  ) {
    return { ok: false, error: 'The project directory is still used by another conversation.' };
  }

  return {
    ok: true,
    request: {
      conversationId,
      ...(deletionIds.size > 1 ? { deletingConversationIds: Array.from(deletionIds) } : {}),
      workspace,
      ...(binding ? { binding } : {}),
      ...(kind === 'temporary' ? { temporary: true } : {}),
    },
  };
};
