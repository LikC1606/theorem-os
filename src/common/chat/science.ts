/**
 * @license
 * Copyright 2026 DeepScientist (deepscientist.cc)
 * SPDX-License-Identifier: Apache-2.0
 */

import { isStructuredReportChartCard, type StructuredReportCard } from "./structuredReportCards";
import type { ReportChartSpec } from "./reportChart";
import { getReportChartVisualDefinition } from "./reportChartVisualRegistry";
import type { ResearchStrategy } from "./researchStrategy";

export const SCIENCE_EVENT_SCHEMA = 'deepscientist.science.event.v1';
export const SCIENCE_PANEL_SCHEMA = 'deepscientist.science.panel.v1';
export const RESEARCH_ROUTE_SCHEMA = 'deepscientist.science.research_route.v1' as const;
export const RESEARCH_ROUTE_ARTIFACT_ID = 'research_roadmap' as const;

export type ScienceEvidenceSourceType =
  | 'file'
  | 'paper'
  | 'database_record'
  | 'code'
  | 'command_log'
  | 'dataset'
  | 'table'
  | 'figure'
  | 'notebook'
  | 'manuscript'
  | 'package_check'
  | 'computational_run'
  | 'dataset_analysis'
  | 'parameter_sweep'
  | 'validation_result'
  | 'remote_job'
  | 'environment'
  | 'regression_output'
  | 'statistical_model'
  | 'causal_assumption'
  | 'survey_instrument'
  | 'codebook'
  | 'data_dictionary'
  | 'qualitative_code'
  | 'geospatial_layer'
  | 'replication_package'
  | 'user_input';

export type ScienceClaimType = 'computed' | 'parsed' | 'digitized' | 'hypothesis';

export interface ScienceGitLineAnchorInput {
  kind: 'git_lines';
  commit?: string;
  filePath: string;
  lineStart: number;
  lineEnd?: number;
  side?: 'current' | 'parent';
}

export interface ScienceGitLineAnchor {
  kind: 'git_lines';
  commit: string;
  repoRelativePath: string;
  workspacePath?: string;
  lineStart: number;
  lineEnd: number;
  side?: 'current' | 'parent';
  blobSha?: string;
  contextHash?: string;
}

export interface ScienceEvidenceItem {
  id: string;
  title: string;
  sourceType: ScienceEvidenceSourceType;
  claimType?: ScienceClaimType;
  confidence: 'high' | 'moderate' | 'low' | 'blocked';
  status?: 'available' | 'missing' | 'stale' | 'needs_review';
  summary?: string;
  path?: string;
  url?: string;
  virtualPath?: string;
  command?: string;
  lineStart?: number;
  lineEnd?: number;
  gitAnchor?: ScienceGitLineAnchor;
  cellId?: string;
  artifactId?: string;
  artifactVersion?: number;
  nodeId?: string;
  supportingEvidenceIds?: string[];
  hash?: string;
  version?: number;
  skillUseId?: string;
  connectorId?: string;
  database?: {
    name: string;
    provider?: 'paperclip' | 'bio_tools' | string;
    domain?: string;
    tool?: string;
    endpoint?: string;
    params?: Record<string, unknown>;
    accessDate?: string;
    returnedCount?: number;
    retrievedCount?: number;
    pagination?: string;
    identifierConversions?: string[];
    warnings?: string[];
  };
  region?: {
    filePath: string;
    page?: number;
    x: number;
    y: number;
    width: number;
    height: number;
    coordinateSystem: 'pixel' | 'normalized';
  };
  createdAt?: number;
  revision?: string;
}

export interface ScienceClaim {
  id: string;
  runId: string;
  text: string;
  claimType: ScienceClaimType;
  status: 'supported' | 'partial' | 'hypothesis' | 'blocked';
  supportingEvidenceIds: string[];
  artifactIds?: string[];
  provenanceNodeIds?: string[];
  limitations?: string[];
  createdAt: number;
  revision?: string;
}

export interface ScienceClaimVerification {
  state: 'verified' | 'partial' | 'blocked';
  totalClaims: number;
  supportedClaims: number;
  hypothesisClaims: number;
  unsupportedClaimIds: string[];
  blockingWarningIds: string[];
}

export const SCIENCE_ARTIFACT_TYPES = Object.freeze([
  'report', 'figure', 'table', 'dataset', 'code', 'notebook', 'manuscript',
  'pdf', 'latex', 'html', 'replication_package', 'run_bundle',
] as const);
export type ScienceArtifactType = (typeof SCIENCE_ARTIFACT_TYPES)[number];

export type ScienceArtifactInspectorTab =
  | 'overview'
  | 'inputs'
  | 'code'
  | 'execution_log'
  | 'messages'
  | 'environment'
  | 'history'
  | 'review';

export const SCIENCE_ARTIFACT_VIEWER_KINDS = Object.freeze(['mathematics', 'report_chart', 'proof_trace'] as const);
export type ScienceArtifactViewerKind = (typeof SCIENCE_ARTIFACT_VIEWER_KINDS)[number];

export interface ScienceArtifactViewerSpec {
  kind?: ScienceArtifactViewerKind;
  configPath?: string;
  dataPath?: string;
  indexPath?: string;
  sourcePath?: string;
  tablePath?: string;
  logPath?: string;
  schemaPath?: string;
  editable?: boolean;
  savePolicy?: 'read_only' | 'new_version_required' | 'overwrite_allowed';
  evidenceIds?: string[];
  chartSpec?: ReportChartSpec;
}

export interface ScienceArtifact {
  id: string;
  runId: string;
  type: ScienceArtifactType;
  title: string;
  version: number;
  versionGroupId?: string;
  previousArtifactId?: string;
  previousVersion?: number;
  revision?: string;
  changeSummary?: string;
  status?: 'available' | 'missing' | 'stale' | 'generating' | 'failed';
  primaryPath?: string;
  previewPath?: string;
  thumbnailPath?: string;
  sourcePaths?: string[];
  inputPaths?: string[];
  outputPaths?: string[];
  contentHash?: string;
  sizeBytes?: number;
  mimeType?: string;
  code?: {
    path?: string;
    language?: 'python' | 'r' | 'shell' | 'latex' | 'markdown';
    entrypoint?: string;
    cellIds?: string[];
  };
  execution?: {
    command?: string;
    scriptPath?: string;
    cwd?: string;
    logPath?: string;
    stdoutPreview?: string;
    stderrPreview?: string;
    startedAt?: number;
    endedAt?: number;
    exitCode?: number;
  };
  environment?: {
    kind?: 'local' | 'conda' | 'uv' | 'renv' | 'docker' | 'slurm' | 'modal' | 'ssh';
    python?: string;
    r?: string;
    packages?: Array<{ name: string; version?: string }>;
    lockfilePath?: string;
    hardware?: string;
  };
  inputs?: Array<{
    label?: string;
    role?: 'primary' | 'reference' | 'parameter' | 'metadata' | 'derived';
    path?: string;
    artifactId?: string;
    evidenceId?: string;
    contentHash?: string;
    sizeBytes?: number;
    mimeType?: string;
  }>;
  relatedMessageIds?: string[];
  relatedToolCallIds?: string[];
  defaultInspectorTab?: ScienceArtifactInspectorTab;
  availableTabs?: ScienceArtifactInspectorTab[];
  evidenceIds?: string[];
  provenanceNodeIds?: string[];
  reviewStatus?: 'not_reviewed' | 'passed' | 'warnings' | 'failed';
  viewer?: ScienceArtifactViewerSpec;
  metadata?: Record<string, unknown> & {
  };
  git?: ScienceArtifactGitRef;
  createdAt: number;
}

export type ResearchRouteLifecycle =
  | 'proposed'
  | 'selected'
  | 'running'
  | 'completed'
  | 'verified'
  | 'blocked'
  | 'pruned';

export type ResearchRouteMode = ResearchStrategy;

export interface ResearchRouteEta {
  min?: number;
  max?: number;
  unit: 'minute' | 'hour' | 'day' | 'week';
}

export type ResearchStageDisposition = 'supported' | 'refuted' | 'exhausted' | 'inconclusive' | 'runtime_failed';

export type ResearchStageFailureClass = 'mathematical' | 'insufficient_evidence' | 'tool_runtime';

export type ResearchStageNextAction = 'continue' | 'advance' | 'branch' | 'ask_user' | 'pause' | 'complete';

export type ResearchCompletionCriterionStatus = 'pending' | 'satisfied' | 'unsatisfied' | 'blocked';

export interface ResearchCompletionCriterion {
  id: string;
  requirement: string;
  status: ResearchCompletionCriterionStatus;
  evidenceIds: string[];
  note?: string;
}

export interface ResearchCompletionContract {
  criteria: ResearchCompletionCriterion[];
  updatedAt: number;
}

export interface ResearchStageOutcome {
  disposition: ResearchStageDisposition;
  supportingEvidenceIds: string[];
  refutingEvidenceIds: string[];
  exhaustionEvidenceIds?: string[];
  producedArtifactIds?: string[];
  checkpointCommit?: string;
  beliefDelta: string;
  reflection: string;
  failureClass?: ResearchStageFailureClass;
  nextAction: ResearchStageNextAction;
  nextObjective?: string;
}

export interface ResearchRouteNode {
  id: string;
  parentId?: string;
  parentIds?: string[];
  strategy?: ResearchRouteMode;
  repairsNodeId?: string;
  order: number;
  title: string;
  summary: string;
  lifecycle: ResearchRouteLifecycle;
  eta?: ResearchRouteEta;
  execution?: {
    objective: string;
    hypothesis?: string;
    acceptanceCriteria: string[];
    failureCriteria?: string[];
    exitCriteria?: string[];
    requiredEvidenceIds?: string[];
    priorWorkRefs?: string[];
    doNotRepeat?: string[];
    authoritativeChecks?: string[];
    expectedArtifacts?: string[];
    budget?: {
      maxMinutes?: number;
      maxAttempts?: number;
    };
  };
  outcome?: ResearchStageOutcome;
  evidenceIds?: string[];
  artifactIds?: string[];
  git?: {
    branchRef?: string;
    baseCommit?: string;
    checkpointCommit?: string;
  };
  blockedReason?: string;
  prunedReason?: string;
}

export type ResearchRouteDecisionStatus = 'none' | 'pending' | 'answered' | 'cancelled' | 'timeout' | 'orphaned';

export interface ResearchRouteMap {
  schema: typeof RESEARCH_ROUTE_SCHEMA;
  roadmapId: string;
  goalId?: string;
  objective: string;
  routeMode?: ResearchRouteMode;
  completionContract?: ResearchCompletionContract;
  rootNodeId: string;
  focusNodeId?: string;
  selectedTargetId?: string;
  decision?: {
    requestId?: string;
    status: ResearchRouteDecisionStatus;
    selectableNodeIds?: string[];
    selectedNodeId?: string;
    updatedAt: number;
  };
  nodes: ResearchRouteNode[];
  updatedAt: number;
}

export type ResearchRouteDisplayStatus =
  | 'planned'
  | 'available'
  | 'selected'
  | 'running'
  | 'completed'
  | 'verified'
  | 'blocked'
  | 'pruned';

export interface ResearchRoutePresentationNode {
  id: string;
  parentId?: string;
  parentIds?: string[];
  strategy?: ResearchRouteMode;
  repairsNodeId?: string;
  order: number;
  title: string;
  summary: string;
  displayStatus: ResearchRouteDisplayStatus;
  eta?: ResearchRouteEta;
  etaLabel?: string;
}

export interface ResearchRoutePresentation {
  kind: 'research_route';
  explicitConfirmation: true;
  allowAutoRecommend: false;
  goalId?: string;
  artifactRef: {
    runId: string;
    artifactId: string;
    version?: number;
    baseRevision: string;
  };
  selectedTargetId?: string;
  selectableNodeIds: string[];
  nodes: ResearchRoutePresentationNode[];
}

export type ResearchRouteValidationResult = { ok: true; value: ResearchRouteMap } | { ok: false; error: string };

const RESEARCH_ROUTE_LIFECYCLES = new Set<ResearchRouteLifecycle>([
  'proposed',
  'selected',
  'running',
  'completed',
  'verified',
  'blocked',
  'pruned',
]);
const RESEARCH_ROUTE_MODES = new Set<ResearchRouteMode>(['explore', 'deepen', 'fuse', 'repair', 'stop']);
const RESEARCH_ROUTE_DECISION_STATUSES = new Set<ResearchRouteDecisionStatus>([
  'none',
  'pending',
  'answered',
  'cancelled',
  'timeout',
  'orphaned',
]);
const RESEARCH_ROUTE_ETA_UNITS = new Set<ResearchRouteEta['unit']>(['minute', 'hour', 'day', 'week']);
const RESEARCH_STAGE_DISPOSITIONS = new Set<ResearchStageDisposition>([
  'supported',
  'refuted',
  'exhausted',
  'inconclusive',
  'runtime_failed',
]);
const RESEARCH_STAGE_FAILURE_CLASSES = new Set<ResearchStageFailureClass>([
  'mathematical',
  'insufficient_evidence',
  'tool_runtime',
]);
const RESEARCH_STAGE_NEXT_ACTIONS = new Set<ResearchStageNextAction>([
  'continue',
  'advance',
  'branch',
  'ask_user',
  'pause',
  'complete',
]);
const RESEARCH_COMPLETION_CRITERION_STATUSES = new Set<ResearchCompletionCriterionStatus>([
  'pending',
  'satisfied',
  'unsatisfied',
  'blocked',
]);
const RESEARCH_ROUTE_MAX_NODES = 36;
const RESEARCH_ROUTE_MAX_DEPTH = 8;
export const RESEARCH_ROUTE_PRESENTATION_MAX_NODES = 12;
export const RESEARCH_ROUTE_PRESENTATION_MAX_DEPTH = 3;
export const RESEARCH_ROUTE_MIN_SELECTABLE_NODES = 2;
export const RESEARCH_ROUTE_MAX_SELECTABLE_NODES = 4;

const researchRouteRecord = (value: unknown): Record<string, unknown> | undefined =>
  value && typeof value === 'object' && !Array.isArray(value) ? (value as Record<string, unknown>) : undefined;

const researchRouteString = (value: unknown, maxLength: number): string | undefined => {
  if (typeof value !== 'string') return undefined;
  const normalized = value.trim();
  return normalized && normalized.length <= maxLength ? normalized : undefined;
};

const researchRouteStringArray = (value: unknown, maxItems = 36): string[] | undefined => {
  if (value == null) return undefined;
  if (!Array.isArray(value) || value.length > maxItems) return undefined;
  const result = value.map((item) => researchRouteString(item, 160));
  if (result.some((item) => !item)) return undefined;
  return result as string[];
};

const researchRouteUniqueStringArray = (value: unknown, maxItems = 36): string[] | undefined => {
  const result = researchRouteStringArray(value, maxItems);
  if (!result || new Set(result).size !== result.length) return undefined;
  return result;
};

export const getResearchRouteParentIds = (
  node:
    | Pick<ResearchRouteNode, 'parentId' | 'parentIds'>
    | Pick<ResearchRoutePresentationNode, 'parentId' | 'parentIds'>
): string[] => node.parentIds || (node.parentId ? [node.parentId] : []);

const parseResearchRouteEta = (value: unknown): ResearchRouteEta | undefined => {
  if (value == null) return undefined;
  const record = researchRouteRecord(value);
  if (!record || !RESEARCH_ROUTE_ETA_UNITS.has(record.unit as ResearchRouteEta['unit'])) return undefined;
  const min = typeof record.min === 'number' && Number.isFinite(record.min) && record.min >= 0 ? record.min : undefined;
  const max = typeof record.max === 'number' && Number.isFinite(record.max) && record.max >= 0 ? record.max : undefined;
  if (record.min != null && min == null) return undefined;
  if (record.max != null && max == null) return undefined;
  if (min != null && max != null && max < min) return undefined;
  return { min, max, unit: record.unit as ResearchRouteEta['unit'] };
};

export function validateResearchRouteMap(value: unknown): ResearchRouteValidationResult {
  const record = researchRouteRecord(value);
  if (!record || record.schema !== RESEARCH_ROUTE_SCHEMA) {
    return { ok: false, error: `schema must equal ${RESEARCH_ROUTE_SCHEMA}` };
  }
  const roadmapId = researchRouteString(record.roadmapId, 120);
  const goalId = record.goalId == null ? undefined : researchRouteString(record.goalId, 120);
  const objective = researchRouteString(record.objective, 500);
  const routeMode = record.routeMode == null ? undefined : (record.routeMode as ResearchRouteMode);
  const rootNodeId = researchRouteString(record.rootNodeId, 120);
  const focusNodeId = record.focusNodeId == null ? undefined : researchRouteString(record.focusNodeId, 120);
  const selectedTargetId =
    record.selectedTargetId == null ? undefined : researchRouteString(record.selectedTargetId, 120);
  const updatedAt =
    typeof record.updatedAt === 'number' && Number.isFinite(record.updatedAt) ? record.updatedAt : undefined;
  if (!roadmapId || !objective || !rootNodeId || updatedAt == null || (record.goalId != null && !goalId)) {
    return { ok: false, error: 'roadmapId, objective, rootNodeId, updatedAt, and optional goalId must be valid' };
  }
  if (routeMode != null && !RESEARCH_ROUTE_MODES.has(routeMode)) {
    return { ok: false, error: 'routeMode must be explore, deepen, fuse, repair, or stop when provided' };
  }
  let completionContract: ResearchCompletionContract | undefined;
  if (record.completionContract != null) {
    const completionRecord = researchRouteRecord(record.completionContract);
    const completionUpdatedAt =
      typeof completionRecord?.updatedAt === 'number' && Number.isFinite(completionRecord.updatedAt)
        ? completionRecord.updatedAt
        : undefined;
    if (
      !completionRecord ||
      completionUpdatedAt == null ||
      !Array.isArray(completionRecord.criteria) ||
      completionRecord.criteria.length < 1 ||
      completionRecord.criteria.length > 20
    ) {
      return { ok: false, error: 'completionContract requires updatedAt and 1-20 criteria' };
    }
    const criterionIds = new Set<string>();
    const criteria: ResearchCompletionCriterion[] = [];
    for (const [index, candidate] of completionRecord.criteria.entries()) {
      const criterion = researchRouteRecord(candidate);
      const id = researchRouteString(criterion?.id, 120);
      const requirement = researchRouteString(criterion?.requirement, 500);
      const status = criterion?.status as ResearchCompletionCriterionStatus | undefined;
      const evidenceIds = researchRouteUniqueStringArray(criterion?.evidenceIds, 36) ?? [];
      const note = criterion?.note == null ? undefined : researchRouteString(criterion.note, 500);
      if (
        !criterion ||
        !id ||
        criterionIds.has(id) ||
        !requirement ||
        !status ||
        !RESEARCH_COMPLETION_CRITERION_STATUSES.has(status) ||
        (criterion.evidenceIds != null && !researchRouteUniqueStringArray(criterion.evidenceIds, 36)) ||
        (criterion.note != null && !note)
      ) {
        return { ok: false, error: `completionContract.criteria[${index}] is invalid` };
      }
      if ((status === 'satisfied' || status === 'unsatisfied') && evidenceIds.length === 0) {
        return {
          ok: false,
          error: `completionContract.criteria[${index}] ${status} requires evidenceIds`,
        };
      }
      criterionIds.add(id);
      criteria.push({ id, requirement, status, evidenceIds, note });
    }
    completionContract = { criteria, updatedAt: completionUpdatedAt };
  }
  if (!Array.isArray(record.nodes) || !record.nodes.length || record.nodes.length > RESEARCH_ROUTE_MAX_NODES) {
    return { ok: false, error: `nodes must contain 1-${RESEARCH_ROUTE_MAX_NODES} items` };
  }

  const nodes: ResearchRouteNode[] = [];
  const ids = new Set<string>();
  for (const [index, candidate] of record.nodes.entries()) {
    const node = researchRouteRecord(candidate);
    const id = researchRouteString(node?.id, 120);
    const parentId = node?.parentId == null ? undefined : researchRouteString(node.parentId, 120);
    const parentIds = node?.parentIds == null ? undefined : researchRouteUniqueStringArray(node.parentIds, 4);
    const strategy = node?.strategy == null ? undefined : (node.strategy as ResearchRouteMode);
    const repairsNodeId = node?.repairsNodeId == null ? undefined : researchRouteString(node.repairsNodeId, 120);
    const title = researchRouteString(node?.title, 48);
    const summary = researchRouteString(node?.summary, 240);
    const lifecycle = node?.lifecycle as ResearchRouteLifecycle | undefined;
    const order = typeof node?.order === 'number' && Number.isFinite(node.order) ? node.order : undefined;
    if (
      !node ||
      !id ||
      ids.has(id) ||
      !title ||
      !summary ||
      order == null ||
      !RESEARCH_ROUTE_LIFECYCLES.has(lifecycle!)
    ) {
      return {
        ok: false,
        error: `nodes[${index}] has an invalid or duplicate id, title, summary, order, or lifecycle`,
      };
    }
    if (strategy != null && !RESEARCH_ROUTE_MODES.has(strategy)) {
      return { ok: false, error: `nodes[${index}].strategy must be explore, deepen, fuse, repair, or stop` };
    }
    if (node.parentIds != null && (!parentIds?.length || parentIds.length > 4)) {
      return { ok: false, error: `nodes[${index}].parentIds must contain 1-4 unique node ids` };
    }
    if (parentId && parentIds && parentIds[0] !== parentId) {
      return { ok: false, error: `nodes[${index}].parentId must match the first parentIds entry` };
    }
    const effectiveParentIds = parentIds || (parentId ? [parentId] : []);
    if (effectiveParentIds.length > 1 && strategy !== 'fuse') {
      return { ok: false, error: `nodes[${index}] with multiple parents must use strategy=fuse` };
    }
    if (strategy === 'fuse' && effectiveParentIds.length < 2) {
      return { ok: false, error: `nodes[${index}] strategy=fuse requires at least two parents` };
    }
    if ((strategy === 'repair') !== Boolean(repairsNodeId)) {
      return { ok: false, error: `nodes[${index}] strategy=repair requires repairsNodeId and only repair may set it` };
    }
    const eta = parseResearchRouteEta(node.eta);
    if (node.eta != null && !eta) return { ok: false, error: `nodes[${index}].eta is invalid` };
    const evidenceIds = researchRouteStringArray(node.evidenceIds);
    const artifactIds = researchRouteStringArray(node.artifactIds);
    if ((node.evidenceIds != null && !evidenceIds) || (node.artifactIds != null && !artifactIds)) {
      return { ok: false, error: `nodes[${index}] evidenceIds or artifactIds is invalid` };
    }
    const executionRecord = researchRouteRecord(node.execution);
    const execution = executionRecord
      ? {
          objective: researchRouteString(executionRecord.objective, 500),
          hypothesis:
            executionRecord.hypothesis == null ? undefined : researchRouteString(executionRecord.hypothesis, 500),
          acceptanceCriteria: researchRouteStringArray(executionRecord.acceptanceCriteria, 20),
          failureCriteria: researchRouteStringArray(executionRecord.failureCriteria, 20),
          exitCriteria: researchRouteStringArray(executionRecord.exitCriteria, 20),
          requiredEvidenceIds: researchRouteStringArray(executionRecord.requiredEvidenceIds, 36),
          priorWorkRefs: researchRouteStringArray(executionRecord.priorWorkRefs, 36),
          doNotRepeat: researchRouteStringArray(executionRecord.doNotRepeat, 20),
          authoritativeChecks: researchRouteStringArray(executionRecord.authoritativeChecks, 20),
          expectedArtifacts: researchRouteStringArray(executionRecord.expectedArtifacts, 20),
          budget: (() => {
            const budget = researchRouteRecord(executionRecord.budget);
            if (!budget) return undefined;
            const maxMinutes =
              typeof budget.maxMinutes === 'number' && Number.isFinite(budget.maxMinutes) && budget.maxMinutes > 0
                ? Math.min(10_080, Math.floor(budget.maxMinutes))
                : undefined;
            const maxAttempts =
              typeof budget.maxAttempts === 'number' && Number.isFinite(budget.maxAttempts) && budget.maxAttempts > 0
                ? Math.min(100, Math.floor(budget.maxAttempts))
                : undefined;
            return maxMinutes || maxAttempts ? { maxMinutes, maxAttempts } : undefined;
          })(),
        }
      : undefined;
    if (executionRecord && (!execution?.objective || !execution.acceptanceCriteria)) {
      return { ok: false, error: `nodes[${index}].execution requires objective and acceptanceCriteria` };
    }
    if (
      executionRecord &&
      ((executionRecord.failureCriteria != null && !execution?.failureCriteria) ||
        (executionRecord.priorWorkRefs != null && !execution?.priorWorkRefs) ||
        (executionRecord.doNotRepeat != null && !execution?.doNotRepeat) ||
        (executionRecord.authoritativeChecks != null && !execution?.authoritativeChecks) ||
        (executionRecord.expectedArtifacts != null && !execution?.expectedArtifacts) ||
        (executionRecord.budget != null && !execution?.budget))
    ) {
      return { ok: false, error: `nodes[${index}].execution contains invalid stage criteria, prior work, or budget` };
    }
    const outcomeRecord = researchRouteRecord(node.outcome);
    const outcome = outcomeRecord
      ? {
          disposition: outcomeRecord.disposition as ResearchStageDisposition,
          supportingEvidenceIds: researchRouteStringArray(outcomeRecord.supportingEvidenceIds, 36),
          refutingEvidenceIds: researchRouteStringArray(outcomeRecord.refutingEvidenceIds, 36),
          exhaustionEvidenceIds: researchRouteStringArray(outcomeRecord.exhaustionEvidenceIds, 36),
          producedArtifactIds: researchRouteStringArray(outcomeRecord.producedArtifactIds, 36),
          checkpointCommit:
            outcomeRecord.checkpointCommit == null
              ? undefined
              : researchRouteString(outcomeRecord.checkpointCommit, 160),
          beliefDelta: researchRouteString(outcomeRecord.beliefDelta, 500),
          reflection: researchRouteString(outcomeRecord.reflection, 800),
          failureClass:
            outcomeRecord.failureClass == null ? undefined : (outcomeRecord.failureClass as ResearchStageFailureClass),
          nextAction: outcomeRecord.nextAction as ResearchStageNextAction,
          nextObjective:
            outcomeRecord.nextObjective == null ? undefined : researchRouteString(outcomeRecord.nextObjective, 500),
        }
      : undefined;
    if (
      outcomeRecord &&
      (!RESEARCH_STAGE_DISPOSITIONS.has(outcome!.disposition) ||
        !outcome?.supportingEvidenceIds ||
        !outcome.refutingEvidenceIds ||
        !outcome.beliefDelta ||
        !outcome.reflection ||
        !RESEARCH_STAGE_NEXT_ACTIONS.has(outcome.nextAction) ||
        (outcomeRecord.producedArtifactIds != null && !outcome.producedArtifactIds) ||
        (outcomeRecord.exhaustionEvidenceIds != null && !outcome.exhaustionEvidenceIds) ||
        (outcomeRecord.checkpointCommit != null && !outcome.checkpointCommit) ||
        (outcome.failureClass != null && !RESEARCH_STAGE_FAILURE_CLASSES.has(outcome.failureClass)))
    ) {
      return { ok: false, error: `nodes[${index}].outcome is invalid` };
    }
    if (outcome?.disposition === 'supported' && outcome.supportingEvidenceIds.length === 0) {
      return { ok: false, error: `nodes[${index}].outcome supported requires supportingEvidenceIds` };
    }
    if (outcome && outcome.disposition === 'refuted' && outcome.refutingEvidenceIds.length === 0) {
      return { ok: false, error: `nodes[${index}].outcome ${outcome.disposition} requires refutingEvidenceIds` };
    }
    if (
      outcome?.disposition === 'exhausted' &&
      !outcome.exhaustionEvidenceIds?.length &&
      outcome.refutingEvidenceIds.length === 0
    ) {
      return {
        ok: false,
        error: `nodes[${index}].outcome exhausted requires exhaustionEvidenceIds (or legacy refutingEvidenceIds)`,
      };
    }
    if (outcome?.disposition === 'runtime_failed' && outcome.failureClass !== 'tool_runtime') {
      return { ok: false, error: `nodes[${index}].outcome runtime_failed requires failureClass=tool_runtime` };
    }
    const gitRecord = researchRouteRecord(node.git);
    if (node.git != null && !gitRecord) return { ok: false, error: `nodes[${index}].git is invalid` };
    const git = gitRecord
      ? {
          branchRef: gitRecord.branchRef == null ? undefined : researchRouteString(gitRecord.branchRef, 240),
          baseCommit: gitRecord.baseCommit == null ? undefined : researchRouteString(gitRecord.baseCommit, 160),
          checkpointCommit:
            gitRecord.checkpointCommit == null ? undefined : researchRouteString(gitRecord.checkpointCommit, 160),
        }
      : undefined;
    if (
      gitRecord &&
      ((gitRecord.branchRef != null && !git?.branchRef) ||
        (gitRecord.baseCommit != null && !git?.baseCommit) ||
        (gitRecord.checkpointCommit != null && !git?.checkpointCommit))
    ) {
      return { ok: false, error: `nodes[${index}].git contains an invalid reference` };
    }
    if (lifecycle === 'proposed' && (gitRecord || artifactIds?.length)) {
      return {
        ok: false,
        error: `nodes[${index}] is virtual/proposed and cannot claim Git or completed artifact references before selection`,
      };
    }
    ids.add(id);
    nodes.push({
      id,
      parentId,
      parentIds,
      strategy,
      repairsNodeId,
      order,
      title,
      summary,
      lifecycle: lifecycle!,
      eta,
      execution: execution as ResearchRouteNode['execution'],
      outcome: outcome as ResearchRouteNode['outcome'],
      evidenceIds,
      artifactIds,
      git,
      blockedReason: node.blockedReason == null ? undefined : researchRouteString(node.blockedReason, 240),
      prunedReason: node.prunedReason == null ? undefined : researchRouteString(node.prunedReason, 240),
    });
  }

  if (
    !ids.has(rootNodeId) ||
    (focusNodeId && !ids.has(focusNodeId)) ||
    (selectedTargetId && !ids.has(selectedTargetId))
  ) {
    return { ok: false, error: 'rootNodeId, focusNodeId, and selectedTargetId must reference existing nodes' };
  }
  const rootNode = nodes.find((node) => node.id === rootNodeId);
  if (rootNode && getResearchRouteParentIds(rootNode).length) {
    return { ok: false, error: 'rootNodeId must identify a root node without parents' };
  }
  const nodeById = new Map(nodes.map((node) => [node.id, node]));
  for (const node of nodes) {
    const parents = getResearchRouteParentIds(node);
    if (parents.some((parent) => parent === node.id)) {
      return { ok: false, error: `node ${node.id} cannot reference itself as a parent` };
    }
    if (parents.some((parent) => !ids.has(parent))) {
      return { ok: false, error: `node ${node.id} references a missing parent` };
    }
    if (node.repairsNodeId && (node.repairsNodeId === node.id || !ids.has(node.repairsNodeId))) {
      return { ok: false, error: `node ${node.id} references an invalid repairsNodeId` };
    }
  }
  const depthMemo = new Map<string, number>();
  const visiting = new Set<string>();
  const depthFromRoot = (node: ResearchRouteNode): number => {
    const cached = depthMemo.get(node.id);
    if (cached != null) return cached;
    if (visiting.has(node.id)) return Number.POSITIVE_INFINITY;
    visiting.add(node.id);
    const parents = getResearchRouteParentIds(node);
    const depth =
      node.id === rootNodeId
        ? 1
        : parents.length
          ? Math.max(...parents.map((parentId) => depthFromRoot(nodeById.get(parentId)!))) + 1
          : Number.NaN;
    visiting.delete(node.id);
    depthMemo.set(node.id, depth);
    return depth;
  };
  for (const node of nodes) {
    const depth = depthFromRoot(node);
    if (!Number.isFinite(depth)) {
      return { ok: false, error: `node ${node.id} creates a cycle or is not connected to rootNodeId` };
    }
    if (depth > RESEARCH_ROUTE_MAX_DEPTH) {
      return { ok: false, error: `node ${node.id} exceeds the maximum route depth` };
    }
  }

  let decision: ResearchRouteMap['decision'];
  if (record.decision != null) {
    const decisionRecord = researchRouteRecord(record.decision);
    const status = decisionRecord?.status as ResearchRouteDecisionStatus | undefined;
    const decisionUpdatedAt =
      typeof decisionRecord?.updatedAt === 'number' && Number.isFinite(decisionRecord.updatedAt)
        ? decisionRecord.updatedAt
        : undefined;
    const selectableNodeIds = researchRouteUniqueStringArray(decisionRecord?.selectableNodeIds, 4);
    const selectedNodeId =
      decisionRecord?.selectedNodeId == null ? undefined : researchRouteString(decisionRecord.selectedNodeId, 120);
    const requestId =
      decisionRecord?.requestId == null ? undefined : researchRouteString(decisionRecord.requestId, 160);
    if (!decisionRecord || !status || !RESEARCH_ROUTE_DECISION_STATUSES.has(status) || decisionUpdatedAt == null) {
      return { ok: false, error: 'decision status and updatedAt are invalid' };
    }
    if (decisionRecord.selectableNodeIds != null && !selectableNodeIds) {
      return {
        ok: false,
        error: `decision.selectableNodeIds must contain ${RESEARCH_ROUTE_MIN_SELECTABLE_NODES}-${RESEARCH_ROUTE_MAX_SELECTABLE_NODES} unique valid node ids`,
      };
    }
    if (selectableNodeIds?.some((id) => !ids.has(id))) {
      return { ok: false, error: 'decision.selectableNodeIds must reference existing nodes' };
    }
    if (
      (status === 'pending' || status === 'answered') &&
      (!selectableNodeIds ||
        selectableNodeIds.length < RESEARCH_ROUTE_MIN_SELECTABLE_NODES ||
        selectableNodeIds.length > RESEARCH_ROUTE_MAX_SELECTABLE_NODES)
    ) {
      return {
        ok: false,
        error: `a pending or answered decision requires ${RESEARCH_ROUTE_MIN_SELECTABLE_NODES}-${RESEARCH_ROUTE_MAX_SELECTABLE_NODES} selectableNodeIds; requestId is optional`,
      };
    }
    if (status === 'pending' && selectableNodeIds) {
      const focusId = focusNodeId || rootNodeId;
      for (const selectableId of selectableNodeIds) {
        const selectable = nodeById.get(selectableId);
        if (!selectable || selectable.lifecycle !== 'proposed') {
          return { ok: false, error: 'pending selectableNodeIds must reference virtual proposed nodes' };
        }
        if (!isResearchRouteNodeAvailable(selectable, nodeById)) {
          return { ok: false, error: 'pending selectableNodeIds must reference currently available virtual nodes' };
        }
        const queue = [{ id: selectable.id, depth: 0 }];
        const seen = new Set<string>();
        let focusDepth: number | undefined;
        while (queue.length) {
          const current = queue.shift()!;
          if (seen.has(current.id)) continue;
          seen.add(current.id);
          if (current.id === focusId) {
            focusDepth = current.depth;
            break;
          }
          getResearchRouteParentIds(nodeById.get(current.id)!).forEach((parent) =>
            queue.push({ id: parent, depth: current.depth + 1 })
          );
        }
        if (focusDepth == null) {
          return { ok: false, error: 'pending selectableNodeIds must descend from focusNodeId' };
        }
        if (focusDepth >= RESEARCH_ROUTE_PRESENTATION_MAX_DEPTH) {
          return { ok: false, error: 'pending selectableNodeIds must be within the visible route depth' };
        }
      }
    }
    if (
      selectedNodeId &&
      (!ids.has(selectedNodeId) || (selectableNodeIds?.length && !selectableNodeIds.includes(selectedNodeId)))
    ) {
      return { ok: false, error: 'decision.selectedNodeId must be one of the selectable nodes' };
    }
    if (status === 'pending' && selectedNodeId) {
      return { ok: false, error: 'a pending decision cannot already contain selectedNodeId' };
    }
    if (status === 'answered' && !selectedNodeId) {
      return { ok: false, error: 'an answered decision requires selectedNodeId' };
    }
    decision = { requestId, status, selectableNodeIds, selectedNodeId, updatedAt: decisionUpdatedAt };
  }

  return {
    ok: true,
    value: {
      schema: RESEARCH_ROUTE_SCHEMA,
      roadmapId,
      goalId,
      objective,
      routeMode,
      completionContract,
      rootNodeId,
      focusNodeId,
      selectedTargetId,
      decision,
      nodes,
      updatedAt,
    },
  };
}

export const readResearchRouteMap = (metadata: unknown): ResearchRouteMap | undefined => {
  const record = researchRouteRecord(metadata);
  if (!record || !Object.hasOwn(record, 'researchRoute')) return undefined;
  const result = validateResearchRouteMap(record.researchRoute);
  return result.ok ? result.value : undefined;
};

export const isResearchRouteNodeAvailable = (
  node: ResearchRouteNode,
  byId: ReadonlyMap<string, ResearchRouteNode>
): boolean => {
  if (node.lifecycle !== 'proposed') return false;
  const parents = getResearchRouteParentIds(node);
  if (!parents.length) return true;
  return parents.every((parentId) => {
    const parent = byId.get(parentId);
    return parent?.lifecycle === 'completed' || parent?.lifecycle === 'verified';
  });
};

export type ResearchRouteBranchSelectionResult = { ok: true; node?: ResearchRouteNode } | { ok: false; error: string };

/**
 * Branch operations require an explicit route decision. While a decision is
 * pending, no branch may be selected; an answer must identify the exact node.
 */
export const validateResearchRouteBranchSelection = (
  route: ResearchRouteMap | undefined,
  routeNodeId?: string
): ResearchRouteBranchSelectionResult => {
  const decision = route?.decision;
  if (!decision || decision.status === 'none') return { ok: true };
  if (decision.status === 'pending') {
    return { ok: false, error: 'A research route decision is still pending; wait for an explicit user selection.' };
  }
  if (decision.status !== 'answered') return { ok: true };
  const selectedNodeId = decision.selectedNodeId;
  const requestedNodeId = researchRouteString(routeNodeId, 120);
  if (!selectedNodeId || !requestedNodeId) {
    return { ok: false, error: 'An answered research route requires routeNodeId for branch operations.' };
  }
  if (requestedNodeId !== selectedNodeId) {
    return { ok: false, error: 'routeNodeId must match the explicitly selected research route node.' };
  }
  const node = route?.nodes.find((candidate) => candidate.id === selectedNodeId);
  if (!node) return { ok: false, error: 'The selected research route node no longer exists.' };
  if (node.lifecycle === 'proposed') {
    return { ok: false, error: 'Patch the selected research route node before creating or activating a branch.' };
  }
  return { ok: true, node };
};

export function buildResearchRoutePresentation(
  route: ResearchRouteMap,
  artifactRef: ResearchRoutePresentation['artifactRef']
): ResearchRoutePresentation {
  const byId = new Map(route.nodes.map((node) => [node.id, node]));
  const focusId = route.focusNodeId || route.rootNodeId;
  const depthById = new Map<string, number>([[focusId, 1]]);
  const ordered = route.nodes.toSorted((left, right) => left.order - right.order || left.id.localeCompare(right.id));
  let changed = true;
  while (changed) {
    changed = false;
    for (const node of ordered) {
      if (depthById.has(node.id)) continue;
      const parentDepths = getResearchRouteParentIds(node)
        .map((parentId) => depthById.get(parentId))
        .filter((depth): depth is number => depth != null);
      if (parentDepths.length) {
        depthById.set(node.id, Math.min(...parentDepths) + 1);
        changed = true;
      }
    }
  }

  const selectableIds = new Set(route.decision?.selectableNodeIds || []);
  const requiredIds = new Set<string>([focusId]);
  const addPathToFocus = (nodeId: string): void => {
    const seen = new Set<string>();
    const visit = (currentId: string): void => {
      if (seen.has(currentId)) return;
      seen.add(currentId);
      const current = byId.get(currentId);
      if (!current) return;
      requiredIds.add(current.id);
      if (current.id === focusId) return;
      getResearchRouteParentIds(current).forEach(visit);
    };
    visit(nodeId);
  };
  for (const nodeId of selectableIds) addPathToFocus(nodeId);

  const relativeDepth = (node: ResearchRouteNode): number => {
    if (node.id === focusId) return 1;
    const queue = [{ id: node.id, depth: 1 }];
    const seen = new Set<string>();
    while (queue.length) {
      const current = queue.shift()!;
      if (seen.has(current.id)) continue;
      seen.add(current.id);
      const candidate = byId.get(current.id);
      if (!candidate) continue;
      for (const parentId of getResearchRouteParentIds(candidate)) {
        if (parentId === focusId) return current.depth + 1;
        queue.push({ id: parentId, depth: current.depth + 1 });
      }
    }
    return Number.POSITIVE_INFINITY;
  };

  const requiredNodes = ordered
    .filter((node) => requiredIds.has(node.id))
    .toSorted((left, right) => relativeDepth(left) - relativeDepth(right) || left.order - right.order);
  const optionalNodes = ordered.filter(
    (node) => !requiredIds.has(node.id) && relativeDepth(node) <= RESEARCH_ROUTE_PRESENTATION_MAX_DEPTH
  );
  const optionalBudget = Math.max(0, RESEARCH_ROUTE_PRESENTATION_MAX_NODES - requiredNodes.length);
  const visibleNodes = [...requiredNodes, ...optionalNodes.slice(0, optionalBudget)];
  const visibleIds = new Set(visibleNodes.map((node) => node.id));
  const visibleSelectableNodeIds = [...selectableIds].filter((id) => visibleIds.has(id));
  return {
    kind: 'research_route',
    explicitConfirmation: true,
    allowAutoRecommend: false,
    goalId: route.goalId,
    artifactRef,
    selectedTargetId: route.selectedTargetId,
    selectableNodeIds: visibleSelectableNodeIds,
    nodes: visibleNodes.map((node) => {
      const parentIds = getResearchRouteParentIds(node).filter((parentId) => visibleIds.has(parentId));
      const displayStatus: ResearchRouteDisplayStatus =
        node.lifecycle === 'proposed'
          ? isResearchRouteNodeAvailable(node, byId)
            ? 'available'
            : 'planned'
          : node.lifecycle;
      return Object.assign(
        {
          id: node.id,
          parentId: node.parentId && visibleIds.has(node.parentId) ? node.parentId : undefined,
          strategy: node.strategy,
          repairsNodeId: node.repairsNodeId,
          order: node.order,
          title: node.title,
          summary: node.summary,
          displayStatus,
          eta: node.eta,
        },
        parentIds.length ? { parentIds } : {}
      );
    }),
  };
}

export interface ScienceArtifactPage {
  id: string;
  runId: string;
  title: string;
  kind:
    | 'report'
    | 'artifact_workspace'
    | 'figure'
    | 'table'
    | 'code'
    | 'log'
    | 'latex'
    | 'notebook'
    | 'pdf'
    | 'provenance';
  layout: 'report_artifact_inspector' | 'single_preview' | 'split_editor_preview' | 'ledger' | 'drawer';
  panes: Array<{
    id: string;
    type:
      | 'report'
      | 'preview'
      | 'inspector'
      | 'code'
      | 'execution_log'
      | 'latex_editor'
      | 'compiled_pdf'
      | 'notebook'
      | 'evidence_ledger'
      | 'provenance_chain';
    target?: {
      artifactId?: string;
      artifactVersion?: number;
      evidenceId?: string;
      claimId?: string;
      path?: string;
    };
  }>;
  revision?: string;
}

export type ScienceProvenanceEdgeType =
  | 'derived_from'
  | 'uses_input'
  | 'uses_code'
  | 'has_log'
  | 'generated'
  | 'supports'
  | 'contradicts'
  | 'validates'
  | 'cites'
  | 'annotates'
  | 'supersedes'
  | 'selected_by_skill'
  | 'answers';

export interface ScienceProvenanceNode {
  id: string;
  type: 'input' | 'activity' | 'output' | 'environment' | 'claim' | 'skill_use' | 'review' | 'user_decision';
  label: string;
  artifactId?: string;
  evidenceIds?: string[];
  parents?: string[];
  command?: string;
  path?: string;
  contentHash?: string;
  createdAt: number;
  metadata?: Record<string, unknown>;
  revision?: string;
}

export interface ScienceProvenanceEdge {
  id: string;
  runId: string;
  from:
    | { kind: 'evidence'; id: string }
    | { kind: 'artifact'; id: string; version?: number }
    | { kind: 'node'; id: string }
    | { kind: 'claim'; id: string }
    | { kind: 'skill_use'; id: string }
    | { kind: 'message'; id: string };
  to:
    | { kind: 'evidence'; id: string }
    | { kind: 'artifact'; id: string; version?: number }
    | { kind: 'node'; id: string }
    | { kind: 'claim'; id: string }
    | { kind: 'skill_use'; id: string }
    | { kind: 'message'; id: string };
  type: ScienceProvenanceEdgeType;
  label?: string;
  confidence?: 'certain' | 'inferred' | 'declared';
  createdAt: number;
}

export interface ScienceGraphWarning {
  id: string;
  runId: string;
  severity: 'info' | 'warning' | 'error';
  code:
    | 'missing_source'
    | 'missing_edge'
    | 'unopenable_evidence'
    | 'untraced_artifact'
    | 'unsupported_claim'
    | 'broken_reference'
    | 'stale_version'
    | 'missing_environment'
    | 'missing_execution_log';
  message: string;
  target?:
    | { kind: 'evidence'; id: string }
    | { kind: 'artifact'; id: string; version?: number }
    | { kind: 'claim'; id: string }
    | { kind: 'node'; id: string }
    | { kind: 'edge'; id: string };
  blocking?: boolean;
  createdAt: number;
}

export interface ScienceSkillUse {
  id: string;
  runId: string;
  skillId: string;
  skillName: string;
  source: 'deepscientist' | 'k-dense' | 'auto-empirical' | 'nature-skills' | 'sciagent' | 'local' | 'custom';
  sourceUrl?: string;
  version?: string;
  purpose:
    | 'routing'
    | 'database_lookup'
    | 'package_workflow'
    | 'pipeline'
    | 'visualization'
    | 'writing'
    | 'review'
    | 'empirical_design'
    | 'causal_inference'
    | 'replication'
    | 'citation_audit'
    | 'paper_reading'
    | 'data_availability'
    | 'proposal'
    | 'patent_drafting'
    | 'presentation'
    | 'experiment_log'
    | 'codebook'
    | 'qualitative_analysis';
  status: 'selected' | 'used' | 'blocked' | 'unavailable';
  triggeredBy: string;
  selectedBecause?: string;
  limitations?: string[];
  evidenceIds?: string[];
  artifactIds?: string[];
  createdAt: number;
  revision?: string;
}

export type ScienceResultSummaryMetricBasis = 'measured' | 'synthetic' | 'literature' | 'estimated' | 'pending';

export interface ScienceResultSummaryMetric {
  key: string;
  label: string;
  role: 'primary' | 'baseline' | 'secondary';
  value?: number;
  unit?: string;
  direction?: 'maximize' | 'minimize';
  interval?: {
    kind: 'confidence' | 'credible' | 'range';
    lower: number;
    upper: number;
    level?: number;
    method?: string;
  };
  comparison?: string;
  basis: ScienceResultSummaryMetricBasis;
  evidenceIds?: string[];
}

export type ScienceResultSummaryFactKey =
  | 'system'
  | 'dataset'
  | 'sample_size'
  | 'replicates'
  | 'condition'
  | 'method'
  | 'comparator'
  | 'scope'
  | 'threshold'
  | 'environment'
  | 'endpoint'
  | 'participants'
  | 'events'
  | 'censoring'
  | 'validation'
  | 'data_release'
  | 'modalities'
  | 'other';

export interface ScienceResultSummaryFact {
  key?: ScienceResultSummaryFactKey;
  label: string;
  value: string;
  evidenceIds?: string[];
}

export interface ScienceResultSummaryBlock {
  type: 'result_summary';
  variant?: 'generic' | 'survival_prediction';
  title?: string;
  takeaway: string;
  metrics: ScienceResultSummaryMetric[];
  facts?: ScienceResultSummaryFact[];
  note?: string;
  evidenceIds?: string[];
}

export const SCIENCE_REPORT_VISUAL_ROLES = [
  'report.summary',
  'research.question',
  'research.hypothesis',
  'research.method',
  'evidence.source',
  'claim.conclusion',
  'data.dataset',
  'data.table',
  'visual.figure',
  'run.computation',
  'quality.validation',
  'risk.limitation',
  'trace.provenance',
  'math.formal',
  'medical.appraisal',
  'domain.portfolio',
] as const;

export type ScienceReportVisualRole = (typeof SCIENCE_REPORT_VISUAL_ROLES)[number];

export type ScienceReportBlock =
  | { type: 'paragraph'; text: string; evidenceIds?: string[] }
  | { type: 'bullet_list'; items: Array<{ text: string; evidenceIds?: string[]; confidence?: string }> }
  | { type: 'checklist'; items: Array<{ label: string; detail?: string; status?: string; evidenceIds?: string[] }> }
  | ScienceResultSummaryBlock
  | { type: 'figure_ref'; artifactId: string }
  | { type: 'table_ref'; artifactId: string }
  | { type: 'artifact_ref'; artifactId: string }
  | {
      type: 'artifact_embed';
      artifactId: string;
      display?: 'inline' | 'wide' | 'compact';
      renderer?:
        | 'auto'
        | 'image'
        | 'svg'
        | 'html'
        | 'pdf'
        | 'table'
        | 'notebook'
        | 'latex_pdf'
        | 'report_chart'
        | 'proof_trace';
      caption?: string;
      evidenceIds?: string[];
      showSource?: boolean;
      maxHeight?: number;
    }
  | { type: 'code_ref'; artifactId: string }
  | { type: 'card_ref'; cardId: string };

export interface SciencePanelData {
  schema: typeof SCIENCE_PANEL_SCHEMA;
  runId: string;
  conversationId?: string;
  projectRoot?: string;
  question: string;
  generatedAt: number;
  summary?: string;
  status: 'completed' | 'partial' | 'blocked' | 'failed' | 'running' | 'draft';
  stats: {
    searches: number;
    artifacts: number;
    evidence: number;
    commands: number;
    validations: number;
    warnings: number;
  };
  report: {
    revision?: string;
    title: string;
    /** @deprecated Accepted only while restoring legacy runs; public panels strip this field. */
    visualWaiverReason?: string;
    sections: Array<{
      id: string;
      role?: string;
      visualRole?: ScienceReportVisualRole;
      heading: string;
      blocks: ScienceReportBlock[];
    }>;
    evidence?: ScienceEvidenceItem[];
    claims?: ScienceClaim[];
  };
  evidence: ScienceEvidenceItem[];
  artifacts: ScienceArtifact[];
  cards?: StructuredReportCard[];
  cardDiagnostics?: string[];
  visualReview?: ScienceReportVisualReview;
  /** Trusted process projection for the Mathematics Viewer; the renderer never verifies local HMAC receipts. */
  mathematics?: {
    portfolioIntegrity?: 'trusted' | 'untrusted_terminal';
    verifiedOfficialReceiptIds: string[];
  };
  pages?: ScienceArtifactPage[];
  claims?: ScienceClaim[];
  verification?: ScienceClaimVerification;
  provenance: ScienceProvenanceNode[];
  edges?: ScienceProvenanceEdge[];
  graphWarnings?: ScienceGraphWarning[];
  usedSkills?: ScienceSkillUse[];
  methods?: {
    queryPlan?: string[];
    commands?: string[];
    environmentSummary?: string;
    limitations?: string[];
  };
  researchRoute?: ResearchRoutePresentation;
  git?: ScienceArtifactGitRef;
  sourceGit?: ScienceSourceGitRef;
}

export type ScienceReportVisualReviewStatus = 'included' | 'recommended' | 'waived' | 'simplify' | 'not_required';

export interface ScienceReportVisualReview {
  status: ScienceReportVisualReviewStatus;
  demand: 'required' | 'recommended' | 'not_required';
  visualCount: number;
  /** Present on newly reviewed reports; omitted by legacy persisted panels. */
  explicitLeadVisualCount?: number;
  /** Present on newly reviewed reports; omitted by legacy persisted panels. */
  supportingVisualCount?: number;
  recommendedRange: { min: number; max: number };
  primaryRange: { min: 1; max: 2 };
  artifactIds: string[];
  cardIds: string[];
  message: string;
}

const SCIENCE_REPORT_VISUAL_RENDERERS = new Set(['image', 'svg', 'report_chart', 'proof_trace']);
const SCIENCE_REPORT_VISUAL_ARTIFACT_TYPES = new Set<ScienceArtifactType>(['figure']);
const SCIENCE_REPORT_VISUAL_VIEWERS = new Set<ScienceArtifactViewerKind>(['report_chart', 'proof_trace']);
const SCIENCE_REPORT_IMAGE_PATH = /\.(?:gif|jpe?g|png|svg|tiff?|webp)$/iu;

const structuredNumericObservationCount = (
  report: SciencePanelData['report'],
  cards: readonly StructuredReportCard[]
): number => {
  const summaryValues = report.sections.flatMap((section) =>
    section.blocks.flatMap((block) =>
      block.type === 'result_summary'
        ? block.metrics.flatMap((metric) => [metric.value, metric.interval?.lower, metric.interval?.upper])
        : []
    )
  );
  const cardValues = cards.flatMap((card) => {
    if (card.lifecycle === 'empty' || card.lifecycle === 'error' || card.lifecycle === 'unsupported') return [];
    if (card.kind === 'metric_strip') {
      return card.metrics.flatMap((metric) => (typeof metric.value === 'number' ? [metric.value] : []));
    }
    if (card.kind === 'timeseries') return card.series.flatMap((series) => series.points.map((point) => point.y));
    if (card.kind === 'ranked_list') {
      return card.items.flatMap((item) => (typeof item.value === 'number' ? [item.value] : []));
    }
    if (card.kind === 'data_table') {
      return card.rows.flatMap((row) =>
        Object.values(row).filter((value): value is number => typeof value === 'number')
      );
    }
    return [];
  });
  return [...summaryValues, ...cardValues].filter(
    (value): value is number => typeof value === 'number' && Number.isFinite(value)
  ).length;
};

const isScienceReportVisualArtifact = (
  block: Extract<ScienceReportBlock, { type: 'artifact_embed' }>,
  artifact: ScienceArtifact | undefined
): boolean => {
  if (!artifact) return false;
  if (artifact.status === 'missing' || artifact.status === 'failed') return false;
  if (block.renderer && SCIENCE_REPORT_VISUAL_RENDERERS.has(block.renderer)) return true;
  if (SCIENCE_REPORT_VISUAL_ARTIFACT_TYPES.has(artifact.type)) return true;
  if (artifact.viewer?.kind && SCIENCE_REPORT_VISUAL_VIEWERS.has(artifact.viewer.kind)) return true;
  return [artifact.previewPath, artifact.primaryPath].some(
    (candidate) => typeof candidate === 'string' && SCIENCE_REPORT_IMAGE_PATH.test(candidate)
  );
};

export const reviewScienceReportVisuals = (
  report: SciencePanelData['report'],
  artifacts: readonly ScienceArtifact[],
  reportStatus: SciencePanelData['status'],
  cards: readonly StructuredReportCard[] = [],
  internalVisualWaiverReason?: string
): ScienceReportVisualReview => {
  const artifactById = new Map(artifacts.map((artifact) => [artifact.id, artifact]));
  const cardById = new Map(cards.map((card) => [card.id, card]));
  const artifactIds = Array.from(
    new Set(
      report.sections.flatMap((section) =>
        section.blocks.flatMap((block) =>
          block.type === 'artifact_embed' && isScienceReportVisualArtifact(block, artifactById.get(block.artifactId))
            ? [block.artifactId]
            : []
        )
      )
    )
  );
  const cardIds = Array.from(
    new Set(
      report.sections.flatMap((section) =>
        section.blocks.flatMap((block) =>
          block.type === 'card_ref' && isStructuredReportChartCard(cardById.get(block.cardId)) ? [block.cardId] : []
        )
      )
    )
  );
  const visualCount = artifactIds.length + cardIds.length;
  const explicitLeadVisualCount = report.sections.reduce(
    (count, section) =>
      count +
      section.blocks.filter((block) => {
        if (block.type !== 'artifact_embed') return false;
        const artifact = artifactById.get(block.artifactId);
        const chartSpec = artifact?.viewer?.chartSpec;
        const chartDefinition = getReportChartVisualDefinition(chartSpec?.recipe);
        return (
          isScienceReportVisualArtifact(block, artifact) &&
          chartSpec?.visualIntent?.placement === 'lead' &&
          chartDefinition?.leadEligible !== false
        );
      }).length,
    0
  );
  const supportingVisualCount = Math.max(0, visualCount - explicitLeadVisualCount);
  const placementSummary = { explicitLeadVisualCount, supportingVisualCount };
  const numericObservationCount = structuredNumericObservationCount(report, cards);
  const demand =
    reportStatus !== 'completed' && reportStatus !== 'partial'
      ? 'not_required'
      : numericObservationCount >= 2
        ? 'required'
        : 'recommended';
  const reportBlockCount = report.sections.reduce((count, section) => count + section.blocks.length, 0);
  const isNonTrivialReport = report.sections.length >= 2 || reportBlockCount >= 4;
  const recommendedRange = isNonTrivialReport ? { min: 2, max: 4 } : { min: 1, max: 3 };
  const primaryRange = { min: 1, max: 2 } as const;

  if (visualCount > recommendedRange.max) {
    return {
      status: 'simplify',
      demand,
      visualCount,
      ...placementSummary,
      recommendedRange,
      primaryRange,
      artifactIds,
      cardIds,
      message:
        'The report has too many visuals for a clear reading path. Keep one or two lead visuals, retain only supporting visuals that answer distinct reader questions, and move the rest to compact references or collapsed evidence.',
    };
  }
  if (visualCount >= recommendedRange.min) {
    return {
      status: 'included',
      demand,
      visualCount,
      ...placementSummary,
      recommendedRange,
      primaryRange,
      artifactIds,
      cardIds,
      message:
        'The report has a useful visual reading path. Keep one or two lead visuals near the result summary, place supporting visuals beside the section they explain, and preserve captions and evidence links.',
    };
  }

  if (visualCount > 0) {
    return {
      status: 'recommended',
      demand,
      visualCount,
      ...placementSummary,
      recommendedRange,
      primaryRange,
      artifactIds,
      cardIds,
      message:
        'The current visual may be sufficient. Add a supporting visual only when it answers a different reader question about comparison, mechanism, robustness, or limitations; otherwise keep the report compact.',
    };
  }

  // The waiver is an internal editorial decision. Keep accepting the legacy
  // report field for callers that have not migrated yet, but never return the
  // reason as part of the public review object or report panel.
  const waiverReason = (internalVisualWaiverReason || report.visualWaiverReason)?.trim();
  if (waiverReason && demand !== 'required') {
    return {
      status: 'waived',
      demand,
      visualCount,
      ...placementSummary,
      recommendedRange,
      primaryRange,
      artifactIds,
      cardIds,
      message:
        'The report does not need a visual for this evidence shape. Keep the reading path compact and do not add a decorative image.',
    };
  }

  if (reportStatus !== 'completed' && reportStatus !== 'partial') {
    return {
      status: 'not_required',
      demand,
      visualCount,
      ...placementSummary,
      recommendedRange,
      primaryRange,
      artifactIds,
      cardIds,
      message: 'A draft, running, blocked, or failed report does not need a primary visual yet.',
    };
  }

  if (demand === 'required') {
    return {
      status: 'recommended',
      demand,
      visualCount,
      ...placementSummary,
      recommendedRange,
      primaryRange,
      artifactIds,
      cardIds,
      message:
        'The report contains comparable structured numeric results but no primary visual. Add one evidence-bound lead chart or chart card before completion; use two to four visuals only when they answer distinct comparison, trend, robustness, or risk questions. Never fabricate missing values.',
    };
  }

  return {
    status: 'recommended',
    demand,
    visualCount,
    ...placementSummary,
    recommendedRange,
    primaryRange,
    artifactIds,
    cardIds,
    message:
      'The report has no primary visual. Add one evidence-bearing chart, verified source image, editable diagram, or domain Viewer when it materially improves understanding. If the available material is narrative or not meaningfully visualizable, keep the report compact without adding decoration.',
  };
};

export type ScienceArtifactAction =
  | 'describe'
  | 'status'
  | 'reserve_id'
  | 'get'
  | 'list'
  | 'query_many'
  | 'transact'
  | 'create'
  | 'patch'
  | 'replace'
  | 'append'
  | 'version'
  | 'checkpoint'
  | 'research_frontier'
  | 'prepare_branch'
  | 'activate_branch'
  | 'compare_branches'
  | 'snapshot'
  | 'publish'
  | 'annotate'
  | 'focus_page';

export type ScienceArtifactResourceKind =
  | 'run'
  | 'report'
  | 'artifact'
  | 'page'
  | 'evidence'
  | 'claim'
  | 'provenance'
  | 'skill_use'
  | 'annotation'
  | 'memory';

export interface ScienceArtifactMemoryEvent {
  id: string;
  runId: string;
  artifactId?: string;
  artifactVersion?: number;
  actor: 'user' | 'agent' | 'system';
  action: ScienceArtifactAction | 'edit' | 'ask';
  summary: string;
  changedPaths?: string[];
  evidenceIds?: string[];
  claimIds?: string[];
  commit?: string;
  timestamp: number;
  hidden: true;
}

export interface ScienceArtifactEvent {
  schema: typeof SCIENCE_EVENT_SCHEMA;
  eventId: string;
  runId: string;
  action: ScienceArtifactAction;
  timestamp: number;
  conversationId?: string;
  messageId?: string;
  toolCallId?: string;
  target?: {
    kind?: ScienceArtifactResourceKind;
    id?: string;
    version?: number;
    pageId?: string;
  };
  baseRevision?: string;
  resultingRevision?: string;
  artifactIds?: string[];
  pageIds?: string[];
  evidenceIds?: string[];
  claimIds?: string[];
  provenanceNodeIds?: string[];
  panel?: SciencePanelData;
  edges?: ScienceProvenanceEdge[];
  warnings?: ScienceGraphWarning[];
  git?: ScienceArtifactGitRef;
  sourceGit?: ScienceSourceGitRef;
  gitAnchor?: ScienceGitLineAnchor;
  memoryId?: string;
  displayIntent?: 'background' | 'open' | 'focus';
  snapshot?: {
    includePaths?: ScienceArtifactSnapshotIncludePath[];
    files?: ScienceArtifactGitFile[];
  };
}

export interface ScienceArtifactSnapshotIncludePath {
  path: string;
  role?:
    | 'primary'
    | 'preview'
    | 'thumbnail'
    | 'input'
    | 'source'
    | 'output'
    | 'code'
    | 'log'
    | 'environment'
    | 'reference'
    | 'other';
  artifactId?: string;
  artifactVersion?: number;
  recursive?: boolean;
  snapshotId?: string;
}

export interface ScienceArtifactGitFile {
  path: string;
  relativePath?: string;
  role?: ScienceArtifactSnapshotIncludePath['role'];
  artifactId?: string;
  artifactVersion?: number;
  mode: 'copied' | 'pointer' | 'missing' | 'ignored';
  storedPath?: string;
  sha256?: string;
  sizeBytes?: number;
  reason?: string;
}

export interface ScienceArtifactGitRef {
  projectId?: string;
  repoPath?: string;
  commit?: string;
  shortCommit?: string;
  snapshotPath?: string;
  runPath?: string;
  status?: 'committed' | 'unchanged' | 'unavailable';
  files?: ScienceArtifactGitFile[];
  changedFiles?: string[];
  error?: string;
  warning?: string;
}

export interface ScienceSourceGitRef {
  repoRoot?: string;
  branch?: string;
  commit: string;
  shortCommit: string;
  subject: string;
  stage?: string;
  researchStrategy?: ResearchRouteMode;
  routeNodeId?: string;
  repairsNodeId?: string;
  domain?: import("../types/office/preview").ProjectGitDomain;
  artifactRef?: {
    runId: string;
    artifactId: string;
    version: number;
    revision?: string;
  };
  targetSummary?: import("../types/office/preview").ProjectGitTargetSummary;
  changedFiles: string[];
  verification?: string[];
  metrics?: Array<{
    name: string;
    value: number;
    unit?: string;
    direction?: 'maximize' | 'minimize';
  }>;
  metricContext?: import("../types/office/preview").ProjectGitMetricContext;
  goalId?: string;
  researchStage?: import("../types/office/preview").ProjectGitResearchStageReceipt;
  directionDecision?: import("./researchStrategy").ProjectGitDirectionDecision;
}

export interface ScienceArtifactFileProvenanceRecord {
  projectId?: string;
  projectRoot?: string;
  runId: string;
  conversationId?: string;
  messageId?: string;
  toolCallId?: string;
  eventId?: string;
  action?: ScienceArtifactAction;
  timestamp: number;
  path: string;
  relativePath?: string;
  role?: ScienceArtifactSnapshotIncludePath['role'];
  artifactId?: string;
  artifactVersion?: number;
  artifactTitle?: string;
  artifactType?: ScienceArtifactType;
  evidenceIds?: string[];
  provenanceNodeIds?: string[];
  mode: ScienceArtifactGitFile['mode'];
  storedPath?: string;
  sha256?: string;
  sizeBytes?: number;
  reason?: string;
  commit?: string;
  shortCommit?: string;
  snapshotPath?: string;
  status?: 'tracked' | 'modified' | 'missing' | 'pointer' | 'ignored' | 'untracked' | 'unknown';
}

export interface ScienceArtifactFileProvenanceHistoryItem {
  commit?: string;
  shortCommit?: string;
  timestamp: number;
  action?: ScienceArtifactAction;
  role?: ScienceArtifactSnapshotIncludePath['role'];
  artifactId?: string;
  artifactVersion?: number;
  mode?: ScienceArtifactGitFile['mode'];
}

export interface ScienceArtifactFileProvenanceResult {
  ok: boolean;
  status: 'tracked' | 'modified' | 'missing' | 'pointer' | 'ignored' | 'untracked' | 'unknown';
  filePath: string;
  relativePath?: string;
  projectId?: string;
  projectRoot?: string;
  record?: ScienceArtifactFileProvenanceRecord;
  history?: ScienceArtifactFileProvenanceHistoryItem[];
  error?: string;
}
