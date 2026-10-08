import { z } from 'zod';

const reportArtifactRefSchema = z.object({
  artifactId: z.string().trim().min(1).max(160),
  version: z.number().int().positive(),
  revision: z.string().trim().min(1).max(240).optional(),
  contentSha256: z.string().regex(/^[a-f0-9]{64}$/iu).optional(),
  role: z.string().trim().min(1).max(80).optional(),
}).strict();

export const STRUCTURED_REPORT_CARD_SCHEMA = 'deepscientist.report_card.v1' as const;
export const MAX_STRUCTURED_REPORT_CARDS = 24;
export const MAX_STRUCTURED_REPORT_CARD_ROWS = 100;
export const MAX_STRUCTURED_REPORT_PAGE_SIZE = 20;

const boundedString = (max: number) => z.string().trim().min(1).max(max);
const isoTimestamp = z.string().datetime({ offset: true });
const finiteNumber = z.number().finite();
const uniqueStrings = (maxItems: number, maxLength = 160) =>
  z
    .array(boundedString(maxLength))
    .max(maxItems)
    .superRefine((items, context) => {
      if (new Set(items).size !== items.length)
        context.addIssue({ code: z.ZodIssueCode.custom, message: 'must be unique' });
    });

const previewTargetSchema = z.discriminatedUnion('kind', [
  z.object({ kind: z.literal('artifact'), artifactId: boundedString(160) }).strict(),
  z.object({ kind: z.literal('evidence'), evidenceId: boundedString(160) }).strict(),
]);

const cardBase = z.object({
  schema: z.literal(STRUCTURED_REPORT_CARD_SCHEMA),
  id: boundedString(120),
  title: boundedString(160),
  snapshotId: boundedString(160),
  artifactRef: reportArtifactRefSchema,
  evidenceIds: uniqueStrings(24),
  refreshedAt: isoTimestamp,
  lifecycle: z.enum(['loading', 'ready', 'empty', 'error', 'unsupported']),
  freshness: z.enum(['current', 'stale', 'no_change']),
  completeness: z.enum(['complete', 'partial']),
  dataMode: z.enum(['HISTORICAL', 'SIMULATION', 'LIVE_READ_ONLY']).optional(),
  /** Compatibility metadata from previously saved report cards. */
  tradeCapability: z.literal('disabled').optional(),
  previewTarget: previewTargetSchema,
  moduleId: boundedString(80).optional(),
  reportSectionRole: boundedString(80).optional(),
  statusReason: boundedString(300).optional(),
  capability: z
    .object({ reason: boundedString(300) })
    .strict()
    .optional(),
  previousSnapshotId: boundedString(160).optional(),
  checkedAt: isoTimestamp.optional(),
  simulationAssumptionsArtifactRef: reportArtifactRefSchema.optional(),
});

const metricStripCardSchema = cardBase.extend({
  kind: z.literal('metric_strip'),
  metrics: z
    .array(
      z
        .object({
          id: boundedString(80),
          label: boundedString(80),
          value: z.union([finiteNumber, boundedString(120)]),
          unit: boundedString(32).optional(),
          change: finiteNumber.optional(),
          direction: z.enum(['up', 'down', 'flat', 'neutral']).optional(),
        })
        .strict()
    )
    .min(1)
    .max(4),
});

const timeseriesCardSchema = cardBase.extend({
  kind: z.literal('timeseries'),
  visualization: z.enum(['line', 'sparkline']).optional(),
  xLabel: boundedString(80).optional(),
  yLabel: boundedString(80).optional(),
  series: z
    .array(
      z
        .object({
          id: boundedString(80),
          label: boundedString(80),
          unit: boundedString(32).optional(),
          points: z
            .array(z.object({ x: z.union([isoTimestamp, finiteNumber]), y: finiteNumber }).strict())
            .min(1)
            .max(24),
        })
        .strict()
    )
    .min(1)
    .max(4),
});

const tableCellSchema = z.union([boundedString(200), finiteNumber, z.boolean(), z.null()]);
const dataTableCardSchema = cardBase.extend({
  kind: z.literal('data_table'),
  visualization: z.enum(['table', 'treemap', 'candlestick']).optional(),
  pageSize: z.number().int().min(1).max(MAX_STRUCTURED_REPORT_PAGE_SIZE).optional(),
  columns: z
    .array(z.object({ key: boundedString(80), label: boundedString(80), unit: boundedString(32).optional() }).strict())
    .min(1)
    .max(8),
  rows: z.array(z.record(tableCellSchema)).max(MAX_STRUCTURED_REPORT_CARD_ROWS),
});

const rankedListCardSchema = cardBase.extend({
  kind: z.literal('ranked_list'),
  visualization: z.enum(['ranked_list', 'hbar_rank', 'donut']).optional(),
  pageSize: z.number().int().min(1).max(MAX_STRUCTURED_REPORT_PAGE_SIZE).optional(),
  items: z
    .array(
      z
        .object({
          id: boundedString(120),
          rank: z.number().int().positive(),
          label: boundedString(160),
          value: z.union([finiteNumber, boundedString(120)]).optional(),
          detail: boundedString(300).optional(),
          evidenceIds: uniqueStrings(8).optional(),
        })
        .strict()
    )
    .max(MAX_STRUCTURED_REPORT_CARD_ROWS),
});

const evidenceListCardSchema = cardBase.extend({
  kind: z.literal('evidence_list'),
  visualization: z.enum(['evidence_list', 'timeline']).optional(),
  pageSize: z.number().int().min(1).max(MAX_STRUCTURED_REPORT_PAGE_SIZE).optional(),
  items: z
    .array(
      z
        .object({
          evidenceId: boundedString(160),
          title: boundedString(240),
          source: boundedString(160),
          asOf: isoTimestamp,
          detail: boundedString(300).optional(),
        })
        .strict()
    )
    .max(MAX_STRUCTURED_REPORT_CARD_ROWS),
});

export const structuredReportCardSchema = z
  .discriminatedUnion('kind', [
    metricStripCardSchema,
    timeseriesCardSchema,
    dataTableCardSchema,
    rankedListCardSchema,
    evidenceListCardSchema,
  ])
  .superRefine((card, context) => {
    if (card.kind === 'data_table') {
      const keys = card.columns.map((column) => column.key);
      if (new Set(keys).size !== keys.length) {
        context.addIssue({ code: z.ZodIssueCode.custom, path: ['columns'], message: 'column keys must be unique' });
      }
      const allowed = new Set(keys);
      card.rows.forEach((row, rowIndex) => {
        const unknownKey = Object.keys(row).find((key) => !allowed.has(key));
        if (unknownKey) {
          context.addIssue({
            code: z.ZodIssueCode.custom,
            path: ['rows', rowIndex, unknownKey],
            message: 'row key is not declared by columns',
          });
        }
      });
    }
    if (
      card.lifecycle === 'ready' &&
      ((card.kind === 'data_table' && card.rows.length === 0) ||
        (card.kind === 'ranked_list' && card.items.length === 0) ||
        (card.kind === 'evidence_list' && card.items.length === 0))
    ) {
      context.addIssue({
        code: z.ZodIssueCode.custom,
        path: [card.kind === 'data_table' ? 'rows' : 'items'],
        message: 'ready cards require at least one visible item',
      });
    }
    if (card.lifecycle === 'unsupported' && !card.capability?.reason) {
      context.addIssue({
        code: z.ZodIssueCode.custom,
        path: ['capability'],
        message: 'unsupported cards require a visible capability reason',
      });
    }
    if (card.freshness === 'no_change' && (!card.previousSnapshotId || !card.checkedAt)) {
      context.addIssue({
        code: z.ZodIssueCode.custom,
        path: ['freshness'],
        message: 'no_change requires previousSnapshotId and checkedAt',
      });
    }
    if (card.dataMode === 'SIMULATION' && !card.simulationAssumptionsArtifactRef) {
      context.addIssue({
        code: z.ZodIssueCode.custom,
        path: ['simulationAssumptionsArtifactRef'],
        message: 'simulation cards require an assumptions artifact',
      });
    }
  });

export type StructuredReportCard = z.infer<typeof structuredReportCardSchema>;

const STRUCTURED_REPORT_CHART_VISUALIZATIONS = new Set([
  'line',
  'sparkline',
  'treemap',
  'candlestick',
  'hbar_rank',
  'donut',
  'timeline',
]);

export const isStructuredReportChartCard = (card: StructuredReportCard | undefined): boolean => {
  if (!card || card.lifecycle === 'empty' || card.lifecycle === 'error' || card.lifecycle === 'unsupported') {
    return false;
  }
  if (card.kind === 'timeseries') return true;
  return 'visualization' in card && STRUCTURED_REPORT_CHART_VISUALIZATIONS.has(card.visualization || '');
};

export type StructuredReportCardCollectionContext = {
  artifactRefs?: ReadonlySet<string>;
  evidenceIds?: ReadonlySet<string>;
};

export type StructuredReportCardCollectionResult =
  { ok: true; cards: StructuredReportCard[] } | { ok: false; cards: StructuredReportCard[]; errors: string[] };

const artifactRefKey = (artifactId: string, version: number): string => `${artifactId}@${version}`;

export function validateStructuredReportCards(
  value: unknown,
  context: StructuredReportCardCollectionContext = {}
): StructuredReportCardCollectionResult {
  if (!Array.isArray(value)) return { ok: false, cards: [], errors: ['cards must be an array'] };
  if (value.length > MAX_STRUCTURED_REPORT_CARDS) {
    return { ok: false, cards: [], errors: [`cards cannot exceed ${MAX_STRUCTURED_REPORT_CARDS} items`] };
  }

  const cards: StructuredReportCard[] = [];
  const errors: string[] = [];
  const ids = new Set<string>();
  value.forEach((candidate, index) => {
    const parsed = structuredReportCardSchema.safeParse(candidate);
    if (!parsed.success) {
      errors.push(`cards[${index}]: ${parsed.error.issues.map((issue) => issue.message).join('; ')}`);
      return;
    }
    if (ids.has(parsed.data.id)) {
      errors.push(`cards[${index}]: duplicate card id ${parsed.data.id}`);
      return;
    }
    ids.add(parsed.data.id);
    const cardErrors: string[] = [];
    if (
      context.artifactRefs &&
      !context.artifactRefs.has(artifactRefKey(parsed.data.artifactRef.artifactId, parsed.data.artifactRef.version))
    ) {
      cardErrors.push(
        `cards[${index}]: unknown artifact ${artifactRefKey(parsed.data.artifactRef.artifactId, parsed.data.artifactRef.version)}`
      );
    }
    const linkedArtifactRefs = [
      parsed.data.simulationAssumptionsArtifactRef,
      parsed.data.previewTarget.kind === 'artifact'
        ? { artifactId: parsed.data.previewTarget.artifactId, version: parsed.data.artifactRef.version }
        : undefined,
    ].filter((ref): ref is { artifactId: string; version: number } => Boolean(ref));
    linkedArtifactRefs.forEach((ref) => {
      if (context.artifactRefs && !context.artifactRefs.has(artifactRefKey(ref.artifactId, ref.version))) {
        cardErrors.push(`cards[${index}]: unknown linked artifact ${artifactRefKey(ref.artifactId, ref.version)}`);
      }
    });
    const linkedEvidenceIds = [
      ...parsed.data.evidenceIds,
      ...(parsed.data.kind === 'ranked_list'
        ? parsed.data.items.flatMap((item) => item.evidenceIds ?? [])
        : parsed.data.kind === 'evidence_list'
          ? parsed.data.items.map((item) => item.evidenceId)
          : []),
      ...(parsed.data.previewTarget.kind === 'evidence' ? [parsed.data.previewTarget.evidenceId] : []),
    ];
    const missingEvidence = linkedEvidenceIds.find((evidenceId) => !context.evidenceIds?.has(evidenceId));
    if (context.evidenceIds && missingEvidence) {
      cardErrors.push(`cards[${index}]: unknown evidence ${missingEvidence}`);
    }
    errors.push(...cardErrors);
    if (!cardErrors.length) cards.push(parsed.data);
  });
  return errors.length ? { ok: false, cards, errors } : { ok: true, cards };
}
