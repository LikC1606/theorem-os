/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

import {
  buildInitialTargetDiscoveryPortfolio,
  inspectTargetDiscoveryPortfolio,
  isTargetDiscoveryPortfolio,
  type TargetCandidate,
  type TargetCandidateStatus,
  type TargetDiscoveryGenerationLane,
  type TargetDiscoveryPortfolio,
  type TargetDiscoveryImportReceipt,
  type TargetDiscoveryRankingQuality,
  type TargetDiscoveryStage,
} from "./targetDiscovery";

export const TARGET_DISCOVERY_IMPORT_TEMPLATE_NAME = 'deepscientist-target-candidates-template.csv';
export const TARGET_DISCOVERY_IMPORT_MIME = 'text/csv;charset=utf-8';

export type TargetDiscoveryImportMode = 'merge' | 'replace';

export type TargetDiscoveryImportIssue = {
  severity: 'error' | 'warning';
  code: string;
  message: string;
  row?: number;
  field?: string;
};

export type TargetDiscoveryImportSummary = {
  candidateCount: number;
  newCandidateCount: number;
  updatedCandidateCount: number;
  warningCount: number;
  rankingQuality?: TargetDiscoveryRankingQuality;
};

export type TargetDiscoveryImportResult = {
  valid: boolean;
  sourceName: string;
  mode: TargetDiscoveryImportMode;
  portfolio?: TargetDiscoveryPortfolio;
  issues: TargetDiscoveryImportIssue[];
  summary: TargetDiscoveryImportSummary;
};

export type ParseTargetDiscoveryImportOptions = {
  sourceName: string;
  projectRoot?: string;
  existingPortfolio?: TargetDiscoveryPortfolio;
  knownEvidenceIds?: string[];
  mode?: TargetDiscoveryImportMode;
  now?: number;
};

export type TargetDiscoveryImportRequest = {
  projectRoot: string;
  sourcePath: string;
  mode?: TargetDiscoveryImportMode;
  portfolio?: TargetDiscoveryPortfolio;
  knownEvidenceIds?: string[];
};

export type TargetDiscoveryImportPreviewResponse = {
  valid: boolean;
  sourceName: string;
  issues: TargetDiscoveryImportIssue[];
  summary: TargetDiscoveryImportSummary;
};

export type TargetDiscoveryImportCommitResponse = TargetDiscoveryImportPreviewResponse & {
  portfolio: TargetDiscoveryPortfolio;
  writtenPaths: string[];
};

export type TargetDiscoveryImportReconcileRequest = { projectRoot: string };

export type TargetDiscoveryImportReconcileResponse = {
  valid: boolean;
  changed: boolean;
  canonicalRegistryExists: boolean;
  updatedAt?: number;
  issues: TargetDiscoveryImportIssue[];
  receipt?: TargetDiscoveryImportReceipt;
};

export type TargetDiscoveryImportTemplateResponse = {
  fileName: string;
  mimeType: string;
  contentBase64: string;
};

type Row = Record<string, unknown>;

const SAFE_ID = /^[a-z0-9][a-z0-9._-]*$/iu;
const STATUSES = new Set<TargetCandidateStatus>(['advance', 'needs_evidence', 'hold', 'reject']);
const DIRECTIONS = new Set<NonNullable<TargetCandidate['interventionDirection']>>([
  'inhibit',
  'activate',
  'degrade',
  'replace',
  'unknown',
]);
const GENERATION_LANES = new Set<TargetDiscoveryGenerationLane>([
  'human_genetics',
  'patient_state',
  'perturbation_inverse_design',
  'mechanistic_path',
  'understudied_space',
  'translational_control',
  'other',
]);
const EARLY_STAGES = new Set<TargetDiscoveryStage>(['intake', 'data_audit', 'branching']);

const cleanHeader = (value: unknown): string =>
  String(value ?? '')
    .trim()
    .replace(/([a-z0-9])([A-Z])/gu, '$1_$2')
    .toLowerCase()
    .replace(/[^a-z0-9]+/gu, '_')
    .replace(/^_+|_+$/gu, '');

const cleanRow = (row: Row): Row =>
  Object.fromEntries(Object.entries(row).map(([key, value]) => [cleanHeader(key), value]));

const textValue = (value: unknown): string => String(value ?? '').trim();
const optionalText = (value: unknown): string | undefined => textValue(value) || undefined;
const listValue = (value: unknown): string[] =>
  textValue(value)
    .split(/[;|\n]/gu)
    .map((item) => item.trim())
    .filter(Boolean);

const finiteNumber = (value: unknown): number | undefined => {
  if (typeof value === 'number') return Number.isFinite(value) ? value : undefined;
  const text = textValue(value).replaceAll(',', '');
  if (!text) return undefined;
  const parsed = Number(text);
  return Number.isFinite(parsed) ? parsed : undefined;
};

const proportion = (value: unknown): number | undefined => {
  const text = textValue(value);
  if (!text) return undefined;
  if (text.endsWith('%')) {
    const parsed = finiteNumber(text.slice(0, -1));
    return parsed == null ? undefined : parsed / 100;
  }
  return finiteNumber(value);
};

const sourceTitle = (sourceName: string): string =>
  sourceName
    .replace(/\.csv$/iu, '')
    .replaceAll(/[_-]+/gu, ' ')
    .trim() || 'Imported target candidates';

const addIssue = (
  issues: TargetDiscoveryImportIssue[],
  severity: TargetDiscoveryImportIssue['severity'],
  code: string,
  message: string,
  context: Pick<TargetDiscoveryImportIssue, 'row' | 'field'> = {}
): void => {
  issues.push({ severity, code, message, ...context });
};

const optionalList = (row: Row, field: string, previous: string[] | undefined): string[] =>
  textValue(row[field]) ? listValue(row[field]) : previous || [];

const firstPopulatedValue = (row: Row, fields: string[]): unknown => {
  for (const field of fields) {
    if (textValue(row[field])) return row[field];
  }
  return undefined;
};

const normalizeRankingRows = (rows: Row[]): Row[] => {
  const aliasedScores = rows
    .map((row) => finiteNumber(firstPopulatedValue(row, ['score', 'priority_score'])))
    .filter((value): value is number => value != null && value >= 0);
  const largestAliasedScore = aliasedScores.length ? Math.max(...aliasedScores) : undefined;
  const inferredAliasedMaximum =
    largestAliasedScore == null ? undefined : largestAliasedScore <= 1 ? 1 : Math.max(100, largestAliasedScore);

  return rows.map((row) => {
    const aliasedScore = firstPopulatedValue(row, ['score', 'priority_score']);
    return {
      ...row,
      candidate_id: firstPopulatedValue(row, ['candidate_id', 'target_id', 'gene_id', 'ensembl_gene_id', 'id']),
      symbol: firstPopulatedValue(row, ['symbol', 'target_symbol', 'gene_symbol']),
      name: firstPopulatedValue(row, ['name', 'target_name', 'gene_name']),
      priority_index: firstPopulatedValue(row, ['priority_index', 'score', 'priority_score']),
      max_priority_index:
        firstPopulatedValue(row, ['max_priority_index', 'max_score', 'score_max']) ??
        (aliasedScore == null ? undefined : inferredAliasedMaximum),
      coverage: firstPopulatedValue(row, ['coverage', 'evidence_coverage']),
    };
  });
};

const readRows = async (
  data: ArrayBuffer | Uint8Array,
  sourceName: string,
  issues: TargetDiscoveryImportIssue[]
): Promise<Row[]> => {
  const XLSX = await import('xlsx-republish');
  try {
    const workbook = XLSX.read(data, { type: 'array', dense: false, raw: true });
    const sheetName = workbook.SheetNames[0];
    if (!sheetName) return [];
    return XLSX.utils
      .sheet_to_json<Row>(workbook.Sheets[sheetName], { defval: '', raw: true })
      .map(cleanRow)
      .filter((row) => Object.values(row).some((value) => textValue(value)));
  } catch (error) {
    addIssue(
      issues,
      'error',
      'invalid_csv',
      `Unable to read ${sourceName}: ${error instanceof Error ? error.message : String(error)}`
    );
    return [];
  }
};

const parseCandidate = (
  row: Row,
  rowNumber: number,
  fallbackRank: number,
  previous: TargetCandidate | undefined,
  knownEvidenceIds: Set<string> | undefined,
  issues: TargetDiscoveryImportIssue[]
): TargetCandidate | undefined => {
  const id = textValue(row.candidate_id || row.id);
  const symbol = textValue(row.symbol);
  if (!id)
    addIssue(issues, 'error', 'required_field', 'candidate_id is required.', {
      row: rowNumber,
      field: 'candidate_id',
    });
  if (!symbol) addIssue(issues, 'error', 'required_field', 'symbol is required.', { row: rowNumber, field: 'symbol' });
  if (!id || !symbol) return undefined;
  if (!SAFE_ID.test(id)) {
    addIssue(
      issues,
      'error',
      'unsafe_candidate_id',
      'candidate_id may contain only letters, numbers, dots, underscores, and hyphens.',
      { row: rowNumber, field: 'candidate_id' }
    );
    return undefined;
  }

  const rawRank = finiteNumber(row.rank);
  const rank = rawRank ?? previous?.rank ?? fallbackRank;
  if (!Number.isInteger(rank) || rank < 1) {
    addIssue(issues, 'error', 'invalid_rank', 'rank must be an integer greater than or equal to 1.', {
      row: rowNumber,
      field: 'rank',
    });
  }
  const rawStatus = optionalText(row.status);
  const status = (rawStatus || previous?.status || 'needs_evidence') as TargetCandidateStatus;
  if (!STATUSES.has(status)) {
    addIssue(issues, 'error', 'invalid_status', `Unsupported candidate status: ${status}.`, {
      row: rowNumber,
      field: 'status',
    });
  }
  const priorityIndex = finiteNumber(row.priority_index) ?? previous?.priorityIndex ?? 0;
  const maxPriorityIndex = finiteNumber(row.max_priority_index) ?? previous?.maxPriorityIndex ?? priorityIndex;
  if (priorityIndex < 0 || maxPriorityIndex < 0 || priorityIndex > maxPriorityIndex) {
    addIssue(
      issues,
      'error',
      'invalid_priority',
      'priority_index and max_priority_index must be non-negative, and priority_index cannot exceed the maximum.',
      { row: rowNumber, field: 'priority_index' }
    );
  }
  const coverage = proportion(row.coverage) ?? previous?.coverage ?? 0;
  if (coverage < 0 || coverage > 1) {
    addIssue(issues, 'error', 'invalid_coverage', 'coverage must be between 0 and 1, or a percentage.', {
      row: rowNumber,
      field: 'coverage',
    });
  }
  const rankStability = proportion(row.rank_stability) ?? previous?.rankStability;
  if (rankStability != null && (rankStability < 0 || rankStability > 1)) {
    addIssue(issues, 'error', 'invalid_rank_stability', 'rank_stability must be between 0 and 1.', {
      row: rowNumber,
      field: 'rank_stability',
    });
  }
  const rawDirection = optionalText(row.intervention_direction);
  const interventionDirection = rawDirection
    ? (rawDirection as TargetCandidate['interventionDirection'])
    : previous?.interventionDirection;
  if (interventionDirection && !DIRECTIONS.has(interventionDirection)) {
    addIssue(
      issues,
      'error',
      'invalid_intervention_direction',
      `Unsupported intervention_direction: ${interventionDirection}.`,
      { row: rowNumber, field: 'intervention_direction' }
    );
  }

  const rawGenerationLane = optionalText(row.generation_lane);
  const generationLane = rawGenerationLane
    ? (rawGenerationLane as TargetDiscoveryGenerationLane)
    : previous?.generation?.lane;
  const generationBranchIds = optionalList(row, 'mechanism_branch_ids', previous?.generation?.branchIds);
  const generationRationale = optionalText(row.generation_rationale) || previous?.generation?.rationale;
  const desiredState = optionalText(row.desired_state) || previous?.generation?.desiredState;
  const cheapTest = optionalText(row.cheap_test) || previous?.generation?.cheapTest;
  const killCriterion = optionalText(row.kill_criterion) || previous?.generation?.killCriterion;
  const generationFieldsProvided = [
    row.generation_lane,
    row.mechanism_branch_ids,
    row.generation_rationale,
    row.desired_state,
    row.cheap_test,
    row.kill_criterion,
  ].some((value) => Boolean(textValue(value)));
  if (generationLane && !GENERATION_LANES.has(generationLane)) {
    addIssue(issues, 'error', 'invalid_generation_lane', `Unsupported generation_lane: ${generationLane}.`, {
      row: rowNumber,
      field: 'generation_lane',
    });
  }
  if (
    generationFieldsProvided &&
    (!generationLane || !generationBranchIds.length || !generationRationale || !cheapTest || !killCriterion)
  ) {
    addIssue(
      issues,
      'error',
      'incomplete_generation_record',
      'A generation record requires generation_lane, mechanism_branch_ids, generation_rationale, cheap_test, and kill_criterion.',
      { row: rowNumber, field: 'generation_lane' }
    );
  }
  const generation =
    generationLane && generationBranchIds.length && generationRationale && cheapTest && killCriterion
      ? {
          lane: generationLane,
          branchIds: generationBranchIds,
          rationale: generationRationale,
          desiredState,
          cheapTest,
          killCriterion,
        }
      : previous?.generation;

  const evidenceIds = optionalList(row, 'evidence_ids', previous?.evidenceIds);
  const opposingEvidenceIds = optionalList(row, 'opposing_evidence_ids', previous?.opposingEvidenceIds);
  if (knownEvidenceIds) {
    for (const evidenceId of [...evidenceIds, ...opposingEvidenceIds]) {
      if (!knownEvidenceIds.has(evidenceId)) {
        addIssue(issues, 'error', 'unknown_evidence', `Evidence ${evidenceId} is not registered in this Science run.`, {
          row: rowNumber,
          field: 'evidence_ids',
        });
      }
    }
  }
  const completedValidation = (previous?.validationResults || []).some((result) => result.status !== 'not_run');
  if (status === 'advance' && !completedValidation) {
    addIssue(
      issues,
      'error',
      'advance_without_validation',
      'A CSV import cannot mark a new or unvalidated candidate as advance. Register validation results first.',
      { row: rowNumber, field: 'status' }
    );
  }

  return {
    ...previous,
    id,
    symbol,
    name: optionalText(row.name) || previous?.name,
    aliases: optionalList(row, 'aliases', previous?.aliases),
    interventionDirection,
    proposedModality: optionalText(row.proposed_modality) || previous?.proposedModality,
    rank,
    priorityIndex,
    maxPriorityIndex,
    coverage,
    rankStability,
    status,
    summary: optionalText(row.summary) || previous?.summary,
    generation,
    channelScores: previous?.channelScores || [],
    evidenceIds,
    opposingEvidenceIds,
    gaps: optionalList(row, 'gaps', previous?.gaps),
    validationPlan: previous?.validationPlan || [],
  };
};

export async function parseTargetDiscoveryImport(
  data: ArrayBuffer | Uint8Array,
  options: ParseTargetDiscoveryImportOptions
): Promise<TargetDiscoveryImportResult> {
  const issues: TargetDiscoveryImportIssue[] = [];
  const rows = normalizeRankingRows(await readRows(data, options.sourceName, issues));
  if (!rows.length) addIssue(issues, 'error', 'empty_csv', 'The CSV does not contain any candidate rows.');
  const now = options.now ?? Date.now();
  const mode = options.mode || 'merge';
  const existing = options.existingPortfolio ? structuredClone(options.existingPortfolio) : undefined;
  const portfolio =
    existing ||
    buildInitialTargetDiscoveryPortfolio({
      title: sourceTitle(options.sourceName),
      objective: 'Review imported target candidates',
      nextActionLabel: 'Review imported candidates and evidence coverage',
      scoringNote: 'Imported priorities are screening inputs, not probabilities of biological or clinical success.',
      projectRoot: options.projectRoot,
      updatedAt: now,
    });
  portfolio.context.projectRoot = options.projectRoot || portfolio.context.projectRoot;

  const previousCandidates = new Map((existing?.candidates || []).map((candidate) => [candidate.id, candidate]));
  const merged = mode === 'merge' ? new Map(previousCandidates) : new Map<string, TargetCandidate>();
  const importedIds = new Set<string>();
  const seenRanks = new Map<number, number>();
  const knownEvidenceIds = options.knownEvidenceIds ? new Set(options.knownEvidenceIds) : undefined;
  let newCandidateCount = 0;
  let updatedCandidateCount = 0;

  rows.forEach((row, index) => {
    const rowNumber = index + 2;
    const requestedId = textValue(row.candidate_id || row.id);
    if (requestedId && importedIds.has(requestedId)) {
      addIssue(issues, 'error', 'duplicate_candidate', `candidate_id ${requestedId} appears more than once.`, {
        row: rowNumber,
        field: 'candidate_id',
      });
      return;
    }
    const previous = requestedId ? previousCandidates.get(requestedId) : undefined;
    const candidate = parseCandidate(row, rowNumber, index + 1, previous, knownEvidenceIds, issues);
    if (!candidate) return;
    importedIds.add(candidate.id);
    const earlierRankRow = seenRanks.get(candidate.rank);
    if (earlierRankRow) {
      addIssue(issues, 'error', 'duplicate_rank', `rank ${candidate.rank} is also used on row ${earlierRankRow}.`, {
        row: rowNumber,
        field: 'rank',
      });
    } else {
      seenRanks.set(candidate.rank, rowNumber);
    }
    merged.set(candidate.id, candidate);
    if (previous) updatedCandidateCount += 1;
    else newCandidateCount += 1;
  });

  portfolio.candidates = [...merged.values()].toSorted(
    (left, right) => left.rank - right.rank || left.id.localeCompare(right.id)
  );
  const candidateById = new Map(portfolio.candidates.map((candidate) => [candidate.id, candidate]));
  const selectedBranches = portfolio.branches.filter((branch) => branch.status !== 'pruned');
  for (const branch of portfolio.branches) {
    const preservedUnscopedCandidateIds = (branch.candidateIds || []).filter((candidateId) => {
      const candidate = candidateById.get(candidateId);
      return candidate && !candidate.generation?.branchIds.length;
    });
    const defaultBranchCandidateIds =
      selectedBranches.length === 1 && selectedBranches[0]?.id === branch.id
        ? portfolio.candidates
            .filter((candidate) => !candidate.generation?.branchIds.length)
            .map((candidate) => candidate.id)
        : [];
    const generatedCandidateIds = portfolio.candidates
      .filter((candidate) => candidate.generation?.branchIds.includes(branch.id))
      .map((candidate) => candidate.id);
    branch.candidateIds = [
      ...new Set([...preservedUnscopedCandidateIds, ...defaultBranchCandidateIds, ...generatedCandidateIds]),
    ];
  }
  portfolio.updatedAt = now;
  if (portfolio.candidates.length) {
    const promotedFromEarlyStage = EARLY_STAGES.has(portfolio.stage);
    if (promotedFromEarlyStage) portfolio.stage = 'screening';
    if (portfolio.status === 'planning') portfolio.status = 'running';
    if (
      promotedFromEarlyStage ||
      (portfolio.nextActions.length === 1 && portfolio.nextActions[0]?.id === 'initialize-target-discovery')
    ) {
      portfolio.nextActions = [
        {
          id: 'review-imported-targets',
          label: 'Review imported candidates and evidence coverage',
          kind: 'decision',
          priority: 'now',
          owner: 'agent',
        },
      ];
    }
  }
  if (!isTargetDiscoveryPortfolio(portfolio)) {
    addIssue(issues, 'error', 'invalid_portfolio', 'The imported rows could not be converted into a target portfolio.');
  }
  const integrity = inspectTargetDiscoveryPortfolio(portfolio);
  integrity.diagnostics.forEach((diagnostic) => {
    if (issues.some((issue) => issue.code === diagnostic.code && issue.message === diagnostic.message)) return;
    addIssue(issues, diagnostic.severity, diagnostic.code, diagnostic.message);
  });

  const summary: TargetDiscoveryImportSummary = {
    candidateCount: importedIds.size,
    newCandidateCount,
    updatedCandidateCount,
    warningCount: issues.filter((item) => item.severity === 'warning').length,
    rankingQuality: integrity.quality,
  };
  const valid = !issues.some((item) => item.severity === 'error');
  return { valid, sourceName: options.sourceName, mode, portfolio: valid ? portfolio : undefined, issues, summary };
}

const quoteCsv = (value: string): string => `"${value.replaceAll('"', '""')}"`;

const TARGET_DISCOVERY_REGISTRY_HEADERS = [
  'candidate_id',
  'symbol',
  'name',
  'rank',
  'status',
  'priority_index',
  'max_priority_index',
  'coverage',
  'rank_stability',
  'intervention_direction',
  'proposed_modality',
  'generation_lane',
  'mechanism_branch_ids',
  'generation_rationale',
  'desired_state',
  'cheap_test',
  'kill_criterion',
  'summary',
  'aliases',
  'evidence_ids',
  'opposing_evidence_ids',
  'gaps',
] as const;

export function buildTargetDiscoveryCandidateRegistry(portfolio: TargetDiscoveryPortfolio): Uint8Array {
  const rows = portfolio.candidates
    .toSorted((left, right) => left.rank - right.rank || left.id.localeCompare(right.id))
    .map((candidate) => [
      candidate.id,
      candidate.symbol,
      candidate.name || '',
      String(candidate.rank),
      candidate.status,
      String(candidate.priorityIndex),
      String(candidate.maxPriorityIndex),
      String(candidate.coverage),
      candidate.rankStability == null ? '' : String(candidate.rankStability),
      candidate.interventionDirection || '',
      candidate.proposedModality || '',
      candidate.generation?.lane || '',
      (candidate.generation?.branchIds || []).join(';'),
      candidate.generation?.rationale || '',
      candidate.generation?.desiredState || '',
      candidate.generation?.cheapTest || '',
      candidate.generation?.killCriterion || '',
      candidate.summary || '',
      (candidate.aliases || []).join(';'),
      candidate.evidenceIds.join(';'),
      candidate.opposingEvidenceIds.join(';'),
      candidate.gaps.join(';'),
    ]);
  const csv = [TARGET_DISCOVERY_REGISTRY_HEADERS, ...rows]
    .map((row) => row.map((value) => quoteCsv(String(value))).join(','))
    .join('\n');
  return new TextEncoder().encode(`\uFEFF${csv}\n`);
}

export function buildTargetDiscoveryImportTemplate(): Uint8Array {
  const example = [
    'example_target_1',
    'GENE1',
    'Example target',
    '1',
    'needs_evidence',
    '0',
    '0',
    '0',
    '',
    'inhibit',
    'small-molecule inhibitor',
    '',
    '',
    '',
    '',
    '',
    '',
    'Replace this row with a real candidate and evidence-bounded summary.',
    'GENE1_ALIAS',
    '',
    '',
    'External validation pending',
  ];
  const csv = `\uFEFF${TARGET_DISCOVERY_REGISTRY_HEADERS.map(quoteCsv).join(',')}\n${example.map(quoteCsv).join(',')}\n`;
  return new TextEncoder().encode(csv);
}
