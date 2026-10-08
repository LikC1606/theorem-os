/** Copyright 2026 DeepScientist contributors. SPDX-License-Identifier: Apache-2.0 */
export type MathRunBinding = Readonly<{
    schema: 'deepscientist.math.run-binding.v2';
    runId: string;
    taskFile: string;
    taskHash: string;
    workspace: string;
    projectRoot: string;
    baseCommit: string;
    allowedWriteRoots: readonly string[];
    environmentFile: string;
    environmentDigest: string;
    leanToolchain: string;
    lakeExecutableDigest: string;
    toolManifestDigest: string;
    leanSourceRoots: readonly string[];
    generatedSourceRoot: string;
    artifactStoreRoot: string;
    artifactStorePolicyDigest: string;
    buildManifestRef: string;
    buildManifestDigest: string;
    evaluatorConfigured: boolean;
    evaluatorPolicyDigest?: string;
    /** Host-frozen problem identity used by v2 assignments and MCP consumers. */
    problem?: MathRunProblemBinding;
}>;
export type MathRunProblemBinding = Readonly<{
    problemId: string;
    statementHash: string;
    leanStatementHash?: string;
    formalStatement?: string;
    initialRouteFingerprint: string;
    /** Host-frozen source identities used to build lite formalization assignments. */
    verificationTargets?: readonly MathFormalVerificationTarget[];
}>;
export type MathResearchQuestion = Readonly<{
    statement: string;
    assumptions: readonly string[];
    targetConnection: string;
}>;
export type MathAssignmentRequest = Readonly<{
    idempotencyKey: string;
    targetSlotId: string;
    predecessorAssignmentId?: string;
    /** Explicit proof consumers for research findings; omission preserves legacy routing. */
    consumerAssignmentIds?: readonly string[];
    /** Optional explicit question owned by a research assignment. */
    researchQuestion?: MathResearchQuestion;
    kind: 'research' | 'formalize';
    objective: string;
    sharedWritePaths?: readonly string[];
    inputs?: readonly ({
        path: string;
        purpose: string;
    } | {
        artifactRef: string;
        purpose: string;
    })[];
    acceptance: readonly string[];
    /** Frozen declarations that a formal source delivery is allowed to satisfy. */
    verificationTargets?: readonly MathFormalVerificationTarget[];
}>;
export type MathFormalVerificationTarget = Readonly<{
    targetId: string;
    pathRelative: string;
    theoremName: string;
    statementHash: string;
    leanStatementHash?: string;
    expectedSourceDeclarationHash: string;
    claim?: 'statement' | 'negation';
}>;
export type MathWorkerDelivery = Readonly<{
    status: 'completed' | 'blocked';
    summary: string;
    evidence: readonly {
        kind: 'source' | 'kernel' | 'analysis' | 'blocker';
        ref: string;
    }[];
    blockers?: readonly string[];
}>;
export type RuntimeMathAssignment = Readonly<{
    schema: 'deepscientist.math.assignment.v2';
    runId: string;
    bindingDigest: string;
    assignmentId: string;
    scopeId: string;
    baseCommit: string;
    request: MathAssignmentRequest;
    payloadHash: string;
    sourceRootRelative: string;
    draftRoot: string;
    artifactGrants: readonly string[];
}>;
export type MathSourceArtifact = Readonly<{
    schema: 'deepscientist.math.source-artifact.v1';
    assignmentId: string;
    deliveryId: string;
    baseCommit: string;
    pathRelative: string;
    mode: 'patch' | 'file';
    content: string;
    contentSha256: string;
    /** Hash of the resulting source file when `mode` is `patch`. */
    resultContentSha256?: string;
    verificationTargetId: string;
    theoremName: string;
    statementHash: string;
    leanStatementHash?: string;
    expectedSourceDeclarationHash: string;
    claim?: 'statement' | 'negation';
}>;
export type MathIntegrationRequest = Readonly<{
    idempotencyKey: string;
    deliveryIds: readonly string[];
    /** Optional v2 source payloads, positionally aligned with deliveryIds. */
    sourceArtifacts?: readonly MathSourceArtifact[];
    declareSolverReady?: boolean;
    supersedeAssignmentIds?: readonly string[];
}>;
export type MathArtifactReadRequest = Readonly<{
    ref: string;
    offsetBytes?: number;
    maxBytes?: number;
}>;
export type MathArtifactReadResponse = Readonly<{
    text: string;
    sha256: string;
    totalBytes: number;
    nextOffsetBytes?: number;
}>;
export type MathArtifactManifestEntry = Readonly<{
    artifactId: string;
    runId: string;
    assignmentId?: string;
    kind: 'compiler' | 'evidence' | 'diagnostic' | 'evaluator';
    sha256: string;
    bytes: number;
    originalBytes?: number;
    mediaType: string;
    createdAt: string;
    sensitivity: 'solver-visible' | 'runtime-only' | 'evaluator-private';
    truncated: boolean;
}>;
