/**
 * @license
 * Copyright 2026 DeepScientist (deepscientist.cc)
 * SPDX-License-Identifier: Apache-2.0
 */

export {
  DEFAULT_AGENT_WORKTREE_GIT_TIMEOUT_MS,
  cloneProjectGit,
  activateProjectGitResearchBranch,
  compareProjectGitResearchBranches,
  createProjectGitCheckpoint,
  discoverProjectGit,
  getProjectGitBlob,
  getProjectGitWorkingTree,
  integrateProjectGitAgentBranch,
  listProjectGitGraph,
  listProjectGitResearchFrontier,
  prepareProjectGitResearchBranch,
  prepareProjectGitAgentWorktree,
  reconcileProjectGitAgentWorktrees,
  discardProjectGitAgentWorktree,
  createProjectGitResearchTeamDeliveryId,
  createProjectGitResearchTeamTransportIdempotencyKey,
  createProjectGitResearchTeamPayloadHash,
  recordProjectGitResearchTeamAssignment,
  recordProjectGitResearchTeamDelivery,
  recordProjectGitResearchTeamBudgetCancellation,
  recordProjectGitResearchTeamSupersessionPending,
  readProjectGitResearchTeamAssignment,
  listProjectGitResearchTeamAssignments,
  completeProjectGitResearchTeamAssignment,
  supersedeProjectGitResearchTeamAssignment,
  resolveAgentWorktreeGitTimeoutMs,
  resolveProjectGitCommit,
  isProjectGitCommitAncestor,
  runProjectGitRepositoryMutation,
} from "./ProjectGitService";
export type {
  ProjectGitCheckpointRequest,
  ProjectGitCheckpointResult,
  ProjectGitIntegrateAgentBranchRequest,
  ProjectGitIntegrateAgentBranchResult,
  ProjectGitPrepareAgentWorktreeRequest,
  ProjectGitPrepareAgentWorktreeResult,
  ProjectGitResolveCommitRequest,
  ProjectGitCommitAncestorRequest,
  ProjectGitDiscardAgentWorktreeRequest,
  ProjectGitDiscardAgentWorktreeResult,
  ProjectGitResearchTeamAssignmentIntegration,
  ProjectGitMathSourceVerificationReceipt,
  ProjectGitMathVerificationEvidence,
  ProjectGitResearchTeamAssignmentReceipt,
  ProjectGitResearchTeamPreparedGit,
  ProjectGitResearchTeamAssignmentRequest,
  ProjectGitResearchTeamAssignmentListRequest,
  ProjectGitResearchTeamAssignmentSupersession,
  ProjectGitResearchTeamUsageBaseline,
  ProjectGitResearchTeamDelivery,
  ProjectGitResearchTeamDeliveryRequest,
} from "./ProjectGitService";
export type { ProjectGitCloneRequest, ProjectGitCloneResult } from "../common/types/office/preview";

export { mergeProjectManifest, PROJECT_MANIFEST_SCHEMA } from "./projectManifest";
