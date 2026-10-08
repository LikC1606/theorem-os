/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

export const IOAI_COMPETITION_SEARCH_SNAPSHOT_SCHEMA =
  'deepscientist.ioai.competition.search-startup-snapshot.v1' as const;

export type IoaiCompetitionSearchSnapshotArtifact = Readonly<{
  category: string;
  sourcePath: string;
  snapshotPath: string;
  sha256: string;
}>;

export type IoaiCompetitionSearchSnapshotTask = Readonly<{
  taskId: string;
  question: string;
  frontierRevision: number;
  nextAction: string;
  control: Readonly<{
    route: 'bootstrap' | 'first_score' | 'recovery' | 'search';
    fallbackRequired: boolean;
    recoveryKey: string | null;
    firstScore: number | null;
  }>;
  contract: Readonly<{
    allowedModels: readonly string[];
    allowedTools: readonly string[];
    outputSchema: Readonly<Record<string, unknown>>;
    metricDirection: 'maximize' | 'minimize' | 'unknown';
    validationVersion: string;
    evaluatorVersion: string;
    validationCases: readonly string[];
    aggregation: 'identity.v1' | 'arithmetic_mean.v1';
    candidateWallClockSeconds: number;
    knownLimitations: readonly string[];
  }>;
  fingerprint: Readonly<{
    taskFamily: string;
    modality: string;
    outputKind: string;
    recommendedLenses: readonly string[];
  }>;
  artifacts: readonly IoaiCompetitionSearchSnapshotArtifact[];
  baselineScore: number;
  incumbent: Readonly<{
    candidateId: string;
    trialId: string;
    score: number;
  }> | null;
}>;

export type IoaiCompetitionSearchSnapshot = Readonly<{
  schema: typeof IOAI_COMPETITION_SEARCH_SNAPSHOT_SCHEMA;
  generatedAt: string;
  deadlineUtc: string;
  remainingSeconds: number;
  sealId: string;
  sealHash: string;
  taskContractRef: string;
  preflight: Readonly<{
    preflightId: string;
    environmentHash: string;
    receiptHash: string;
    receiptRef: string;
    pythonExecutable: string;
    pythonCommandPrefix: readonly string[];
    csvInventory: readonly string[];
  }>;
  baseline: Readonly<{
    runId: string;
    resultRef: string;
    packetHash: string;
  }>;
  contest: Readonly<{
    snapshotHash: string;
    nextTaskId: string;
    nextAction: string;
    reason: string;
    tasks: readonly IoaiCompetitionSearchSnapshotTask[];
  }>;
  submission: Readonly<{
    enabled: boolean;
    maxSubmissions: number;
    protectedReserve: number;
    sentCount: number;
    remaining: number;
  }>;
}>;
