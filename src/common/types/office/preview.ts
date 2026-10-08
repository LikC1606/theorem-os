/**
 * @license
 * Copyright 2025 DeepScientist (deepscientist.cc)
 * SPDX-License-Identifier: Apache-2.0
 */
import type { ProjectGitDirectionDecision, ResearchStrategy } from "../../chat/researchStrategy";

/** Historical Git checkpoint metadata; no target-discovery runtime is required. */
export interface ProjectGitTargetSummary {
  candidateCount: number;
  advanceCount: number;
  validationCount: number;
  blockerCount: number;
  sourceReadyCount: number;
  sourceCount: number;
  branchCount: number;
  coveredBranchCount?: number;
  requiredBranchCount?: number;
  unresolvedRequiredBranchCount?: number;
  generationLaneCount?: number;
  leadingCoverage?: number;
  topTargets: string[];
}

export type ProjectGitFileStatus = 'added' | 'modified' | 'deleted' | 'renamed' | 'copied' | 'unmerged' | 'unknown';
export interface ProjectGitRepository {
    workspaceRoot: string;
    repoRoot: string;
    workspacePrefix?: string;
    branch?: string;
    head?: string;
    detached: boolean;
    bare: boolean;
    dirty: boolean;
    stagedCount: number;
    modifiedCount: number;
    untrackedCount: number;
    dirtyFileCount: number;
}
export type ProjectGitWorkspaceStrategy = 'managed' | 'isolated-worktree' | 'current-worktree' | 'cloned' | 'disabled';
export type ProjectGitDomain = 'general' | 'research' | 'medical_evidence' | 'knowledge_deposition' | 'financial' | 'financial_factor' | 'target_discovery' | 'mathematics' | 'challenge';
export interface ProjectGitWorkspaceBinding {
    schema: 'deepscientist.project_git.v1';
    strategy: ProjectGitWorkspaceStrategy;
    projectId?: string;
    sourceRoot: string;
    workspaceRoot: string;
    branch?: string;
    baseCommit?: string;
    sourceDirty?: boolean;
    /** Remote origin used to create a cloned workspace, when applicable. */
    remoteUrl?: string;
    /** Ref checked out when the workspace was cloned. */
    remoteRef?: string;
    /** User has not yet reviewed the remote before allowing writes. */
    trustState?: 'unreviewed' | 'reviewed';
}
export interface ProjectGitDiscoverRequest {
    workspace: string;
}
export interface ProjectGitDiscoverResult {
    ok: boolean;
    repository?: ProjectGitRepository;
    error?: string;
}
export interface ProjectGitPerformanceMetric {
    name: string;
    value: number;
    unit?: string;
    direction?: 'maximize' | 'minimize';
}
export interface ProjectGitMetricContext {
    contractId: string;
    evaluationId: string;
    baselineCommit?: string;
    evaluationCode?: {
        path: string;
        runtime?: 'python' | 'node' | 'r' | 'notebook';
        entrypoint?: string;
        sha256?: string;
    };
}
export interface ProjectGitCheckpointArtifactRef {
    runId: string;
    artifactId: string;
    version: number;
    revision?: string;
}
export type ProjectGitResearchStageDisposition = 'supported' | 'refuted' | 'exhausted' | 'inconclusive' | 'runtime_failed';
export interface ProjectGitResearchStageReceipt {
    stageId: string;
    objective: string;
    successCriteria: string[];
    failureCriteria: string[];
    priorWorkRefs: string[];
    disposition: ProjectGitResearchStageDisposition;
    supportingEvidenceIds: string[];
    refutingEvidenceIds: string[];
    exhaustionEvidenceIds?: string[];
    beliefDelta: string;
    reflection: string;
    nextObjective?: string;
}
export interface ProjectGitCommitSummary {
    sha: string;
    shortSha: string;
    parents: string[];
    subject: string;
    bodyPreview?: string;
    authorName?: string;
    authorEmail?: string;
    authoredAt?: string;
    refs: string[];
    changedFileCount: number;
    additions: number;
    deletions: number;
    researchStrategy?: ResearchStrategy;
    checkpoint?: {
        stage: string;
        researchStrategy?: ResearchStrategy;
        routeNodeId?: string;
        repairsNodeId?: string;
        runId?: string;
        conversationId?: string;
        domain?: ProjectGitDomain;
        artifactRef?: ProjectGitCheckpointArtifactRef;
        targetSummary?: ProjectGitTargetSummary;
        verification: string[];
        metrics?: ProjectGitPerformanceMetric[];
        metricContext?: ProjectGitMetricContext;
        goalId?: string;
        researchStage?: ProjectGitResearchStageReceipt;
        directionDecision?: ProjectGitDirectionDecision;
    };
}
export interface ProjectGitGraphRequest extends ProjectGitDiscoverRequest {
    limit?: number;
    skip?: number;
    ref?: string;
    allRefs?: boolean;
}
export interface ProjectGitGraphResult extends ProjectGitDiscoverResult {
    commits: ProjectGitCommitSummary[];
    hasMore: boolean;
    nextSkip?: number;
}
export interface ProjectGitChangedFile {
    path: string;
    oldPath?: string;
    status: ProjectGitFileStatus;
    additions?: number;
    deletions?: number;
    binary: boolean;
}
export interface ProjectGitCommitRequest extends ProjectGitDiscoverRequest {
    sha: string;
}
export interface ProjectGitCommitResult extends ProjectGitDiscoverResult {
    commit?: ProjectGitCommitSummary & {
        body?: string;
        files: ProjectGitChangedFile[];
    };
}
export interface ProjectGitDiffRequest extends ProjectGitCommitRequest {
    path?: string;
    parent?: string;
    contextLines?: number;
}
export interface ProjectGitDiffResult extends ProjectGitDiscoverResult {
    sha?: string;
    base?: string;
    path?: string;
    content: string;
    truncated: boolean;
    binary: boolean;
}
export interface ProjectGitTreeRequest extends ProjectGitCommitRequest {
    path?: string;
}
export interface ProjectGitTreeEntry {
    path: string;
    name: string;
    kind: 'file' | 'directory' | 'submodule';
    mode: string;
    objectId: string;
    changedInRevision?: boolean;
    lastCommit?: {
        sha: string;
        shortSha: string;
        subject: string;
        authoredAt?: string;
    };
}
export interface ProjectGitTreeResult extends ProjectGitDiscoverResult {
    sha?: string;
    path?: string;
    entries: ProjectGitTreeEntry[];
}
export interface ProjectGitBlobRequest extends ProjectGitCommitRequest {
    path: string;
}
export interface ProjectGitBlobResult extends ProjectGitDiscoverResult {
    sha?: string;
    path?: string;
    size?: number;
    binary: boolean;
    truncated: boolean;
    content?: string;
    contentBase64?: string;
}
export interface ProjectGitWorkingTreeResult extends ProjectGitDiscoverResult {
    files: ProjectGitChangedFile[];
}
export interface ProjectGitWorkingDiffRequest extends ProjectGitDiscoverRequest {
    path: string;
    contextLines?: number;
}
export interface ProjectGitWorkingDiffResult extends ProjectGitDiscoverResult {
    path?: string;
    content: string;
    truncated: boolean;
    binary: boolean;
}
export interface ProjectGitPreflightRequest {
    workspace: string;
}
export interface ProjectGitPreflightResult {
    ok: boolean;
    kind?: 'git' | 'non-git';
    repository?: ProjectGitRepository;
    canIsolate?: boolean;
    error?: string;
}
export interface ProjectGitPrepareWorkspaceRequest {
    baseDir: string;
    goal: string;
    conversationId: string;
    strategy: Exclude<ProjectGitWorkspaceStrategy, 'disabled'>;
    sourceWorkspace?: string;
    branchKind?: 'discovery' | 'conversation-fork';
}
export interface ProjectGitPrepareWorkspaceResult {
    ok: boolean;
    workspace?: string;
    projectId?: string;
    created?: boolean;
    binding?: ProjectGitWorkspaceBinding;
    error?: string;
}
export interface ProjectGitCloneRequest {
    /** HTTPS or SSH remote URL; loopback HTTP is accepted only for local development. */
    remoteUrl: string;
    /** Empty or omitted destination lets the service derive a folder from the remote name. */
    destination?: string;
    /** Parent directory used when destination is omitted. */
    baseDir?: string;
    /** Optional branch or tag to check out. */
    ref?: string;
    /** Optional shallow clone depth; omitted means preserve full history. */
    depth?: number;
    /** Conversation binding is required when the clone is initiated by an Agent. */
    conversationId?: string;
}
export interface ProjectGitCloneResult {
    ok: boolean;
    workspace?: string;
    projectId?: string;
    created?: boolean;
    repository?: ProjectGitRepository;
    binding?: ProjectGitWorkspaceBinding;
    remoteUrl?: string;
    remoteRef?: string;
    error?: string;
}
export interface ProjectGitBindConversationRequest extends ProjectGitDiscoverRequest {
    conversationId: string;
}
export interface ProjectGitBindConversationResult extends ProjectGitDiscoverResult {
    commit?: string;
    shortCommit?: string;
}
export interface ProjectGitPrepareManagedRequest {
    baseDir: string;
    goal: string;
}
export interface ProjectGitPrepareManagedResult {
    ok: boolean;
    workspace?: string;
    projectId?: string;
    created?: boolean;
    error?: string;
}
export type ProjectWorkspaceDeletionKind = 'managed' | 'isolated-worktree' | 'temporary';
export interface ProjectWorkspaceDeletionRequest {
    conversationId: string;
    deletingConversationIds?: string[];
}
export type ProjectGitResearchBranchStatus = 'active' | 'candidate' | 'parked' | 'rejected' | 'promoted' | 'completed';
export type ProjectGitAgentWorktreeState = 'clean' | 'dirty' | 'missing';
export interface ProjectGitChangedEvent {
    workspace: string;
    repoRoot?: string;
    reason: 'worktree-prepared' | 'agent-delivered' | 'checkpoint-created' | 'branch-changed' | 'branch-integrated' | 'worktree-discarded' | 'cloned';
    branch?: string;
    head?: string;
}
export interface ProjectGitResearchBranchAgent {
    teamId: string;
    slotId: string;
    roleId: string;
    strategyLane?: string;
    assignmentId: string;
    orchestrationNamespace?: string;
    workflowId?: string;
}
export interface ProjectGitResearchBranch {
    name: string;
    ref: string;
    head: string;
    shortHead: string;
    active: boolean;
    status: ProjectGitResearchBranchStatus;
    parentRef?: string;
    baseCommit?: string;
    goalId?: string;
    routeNodeId?: string;
    objective?: string;
    agent?: ProjectGitResearchBranchAgent;
    worktreePath?: string;
    worktreeState?: ProjectGitAgentWorktreeState;
    worktreeDirtyFileCount?: number;
    mergedInto?: string;
    mergedAt?: string;
    updatedAt?: string;
    latestCheckpoint?: ProjectGitCommitSummary;
}
export interface ProjectGitResearchFrontierRequest extends ProjectGitDiscoverRequest {
    goalId?: string;
    conversationId?: string;
    runId?: string;
}
export interface ProjectGitResearchFrontierResult extends ProjectGitDiscoverResult {
    activeBranch?: string;
    branches: ProjectGitResearchBranch[];
}
export interface ProjectGitPrepareResearchBranchRequest extends ProjectGitDiscoverRequest {
    branch: string;
    from: string;
    parentRef?: string;
    goalId?: string;
    routeNodeId?: string;
    objective?: string;
}
export interface ProjectGitPrepareResearchBranchResult extends ProjectGitDiscoverResult {
    branch?: ProjectGitResearchBranch;
}
export interface ProjectGitActivateResearchBranchRequest extends ProjectGitDiscoverRequest {
    branch: string;
    routeNodeId?: string;
}
export interface ProjectGitActivateResearchBranchResult extends ProjectGitDiscoverResult {
    branch?: ProjectGitResearchBranch;
}
export interface ProjectGitMetricComparison {
    name: string;
    unit?: string;
    direction?: 'maximize' | 'minimize';
    baseValue?: number;
    headValue?: number;
    delta?: number;
    relativeDelta?: number;
    improvement?: number;
    comparable: boolean;
    reason?: string;
}
export interface ProjectGitCompareResearchBranchesRequest extends ProjectGitDiscoverRequest {
    baseRef: string;
    headRef: string;
}
export interface ProjectGitCompareResearchBranchesResult extends ProjectGitDiscoverResult {
    base?: ProjectGitResearchBranch;
    head?: ProjectGitResearchBranch;
    mergeBase?: string;
    ahead: number;
    behind: number;
    changedFileCount: number;
    additions: number;
    deletions: number;
    metrics: ProjectGitMetricComparison[];
}
