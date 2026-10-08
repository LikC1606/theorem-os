import { z } from 'zod';
import { financeConsentGrantSchema } from "./consent";
import { createFinanceResultEnvelopeSchema } from "./schemas";
import type { FinanceToolName } from "./types";

const boundedString = (max: number) => z.string().trim().min(1).max(max);
const finiteNumber = z.number().finite();
const isoTimestamp = z.string().datetime({ offset: true });
const market = z.enum(['us', 'cn', 'hk', 'cross_market']);
const symbol = boundedString(32);
const baseShape = {
  runId: boundedString(160),
  sessionId: boundedString(160).optional(),
  requestId: boundedString(160).optional(),
};

const sourcePointerSchema = z
  .object({
    evidenceIds: z.array(boundedString(160)).max(24),
    artifactIds: z.array(boundedString(160)).max(24),
  })
  .strict()
  .optional();

export const financeMarketOverviewInputSchema = z
  .object({
    ...baseShape,
    markets: z.array(market).min(1).max(4).optional(),
    window: z.enum(['1d', '5d', '1m', '3m', '1y']).optional(),
    asOf: isoTimestamp.optional(),
  })
  .strict();

export const financeSectorSearchInputSchema = z
  .object({
    ...baseShape,
    query: boundedString(160),
    market: market.optional(),
    limit: z.number().int().min(1).max(20).optional(),
  })
  .strict();

export const financeSectorMoversInputSchema = z
  .object({
    ...baseShape,
    market,
    sectorIds: z.array(boundedString(80)).max(40).optional(),
    direction: z.enum(['leaders', 'laggards', 'both']).optional(),
    limit: z.number().int().min(1).max(50).optional(),
    asOf: isoTimestamp.optional(),
  })
  .strict();

const securityFilterSchema = z
  .object({
    minMarketCap: finiteNumber.nonnegative().optional(),
    maxMarketCap: finiteNumber.nonnegative().optional(),
    minChangePct: finiteNumber.optional(),
    maxChangePct: finiteNumber.optional(),
    minVolume: finiteNumber.nonnegative().optional(),
  })
  .strict();

export const financeSecurityScreenInputSchema = z
  .object({
    ...baseShape,
    market,
    sectorId: boundedString(80).optional(),
    filters: securityFilterSchema.optional(),
    limit: z.number().int().min(1).max(100).optional(),
    asOf: isoTimestamp.optional(),
  })
  .strict();

export const financeSecuritySnapshotInputSchema = z
  .object({
    ...baseShape,
    symbol,
    market: market.optional(),
    sections: z
      .array(z.enum(['profile', 'quote', 'financials', 'valuation']))
      .min(1)
      .max(4)
      .optional(),
    asOf: isoTimestamp.optional(),
  })
  .strict();

const financeNewsEventsInputObject = z
  .object({
    ...baseShape,
    symbols: z.array(symbol).max(40).optional(),
    query: boundedString(300).optional(),
    from: isoTimestamp.optional(),
    to: isoTimestamp.optional(),
    limit: z.number().int().min(1).max(100).optional(),
  })
  .strict();
export const financeNewsEventsInputSchema = financeNewsEventsInputObject.superRefine((value, context) => {
  if (!value.symbols?.length && !value.query) {
    context.addIssue({ code: z.ZodIssueCode.custom, message: 'symbols or query is required' });
  }
});

const financePriceSeriesInputObject = z
  .object({
    ...baseShape,
    symbol,
    market: market.optional(),
    start: isoTimestamp,
    end: isoTimestamp,
    adjustment: z.enum(['none', 'split', 'total_return']),
    currency: boundedString(16).optional(),
  })
  .strict();
export const financePriceSeriesInputSchema = financePriceSeriesInputObject.superRefine((value, context) => {
  if (Date.parse(value.start) > Date.parse(value.end)) {
    context.addIssue({ code: z.ZodIssueCode.custom, path: ['start'], message: 'start must not follow end' });
  }
});

const financeRelationshipMapInputObject = z
  .object({
    ...baseShape,
    seedSymbols: z.array(symbol).max(20).optional(),
    eventEvidenceIds: z.array(boundedString(160)).max(40).optional(),
    maxDepth: z.number().int().min(1).max(3).optional(),
    maxNodes: z.number().int().min(2).max(100).optional(),
    sourcePointers: sourcePointerSchema,
  })
  .strict();
export const financeRelationshipMapInputSchema = financeRelationshipMapInputObject.superRefine((value, context) => {
  if (!value.seedSymbols?.length && !value.eventEvidenceIds?.length) {
    context.addIssue({ code: z.ZodIssueCode.custom, message: 'seedSymbols or eventEvidenceIds is required' });
  }
});

const portfolioPositionSchema = z
  .object({
    symbol,
    market: market.optional(),
    weight: finiteNumber.min(0).max(1),
    currency: boundedString(16).optional(),
  })
  .strict();

const portfolioPolicySchema = z
  .object({
    inceptionAt: isoTimestamp,
    priceRule: boundedString(240),
    benchmarkSymbols: z.array(symbol).min(1).max(10),
    currency: boundedString(16),
    feesBps: finiteNumber.nonnegative(),
    slippageBps: finiteNumber.nonnegative(),
    rebalance: boundedString(120),
  })
  .strict();

export const financeResearchPortfolioInputSchema = z
  .object({
    ...baseShape,
    action: z.enum([
      'get',
      'watchlist_create',
      'watchlist_update',
      'simulation_create',
      'simulation_update',
      'simulation_evaluate',
    ]),
    portfolioId: boundedString(120).optional(),
    revision: boundedString(160).optional(),
    idempotencyKey: boundedString(160).optional(),
    name: boundedString(160).optional(),
    policy: portfolioPolicySchema.optional(),
    positions: z.array(portfolioPositionSchema).max(100).optional(),
    consent: financeConsentGrantSchema.optional(),
  })
  .strict();

const holdingRowInputSchema = z
  .object({
    symbol: symbol.optional(),
    name: boundedString(160).optional(),
    market: market.optional(),
    quantity: finiteNumber.nonnegative().optional(),
    weight: finiteNumber.min(0).max(1).optional(),
    currency: boundedString(16).optional(),
    cost: finiteNumber.nonnegative().optional(),
  })
  .strict();

const holdingsSourceSchema = z.discriminatedUnion('kind', [
  z.object({ kind: z.literal('structured_rows'), rows: z.array(holdingRowInputSchema).min(1).max(500) }).strict(),
  z.object({ kind: z.literal('local_text'), text: boundedString(100_000) }).strict(),
  z
    .object({
      kind: z.literal('image_reference'),
      referenceId: boundedString(240),
      processing: z.enum(['local', 'cloud']),
    })
    .strict(),
]);

export const financeHoldingsParseInputSchema = z
  .object({
    ...baseShape,
    source: holdingsSourceSchema,
    consent: financeConsentGrantSchema.optional(),
  })
  .strict();

const marketIndexSchema = z
  .object({
    symbol,
    name: boundedString(160),
    last: finiteNumber,
    changePct: finiteNumber,
    currency: boundedString(16),
  })
  .strict();
const sectorSchema = z
  .object({
    id: boundedString(80),
    name: boundedString(160),
    market,
    path: z.array(boundedString(120)).max(8),
    score: finiteNumber.optional(),
  })
  .strict();
const securitySchema = z
  .object({
    symbol,
    name: boundedString(160),
    market,
    sectorId: boundedString(80).optional(),
    last: finiteNumber.optional(),
    changePct: finiteNumber.optional(),
    marketCap: finiteNumber.nonnegative().optional(),
    volume: finiteNumber.nonnegative().optional(),
    currency: boundedString(16).optional(),
    reasons: z.array(boundedString(240)).max(8),
  })
  .strict();
const metricSchema = z
  .object({
    key: boundedString(80),
    label: boundedString(120),
    value: finiteNumber,
    unit: boundedString(32).optional(),
    period: boundedString(80).optional(),
  })
  .strict();

export const financeToolDataSchemas = {
  finance_market_overview: z.object({ indices: z.array(marketIndexSchema).max(40) }).strict(),
  finance_sector_search: z.object({ matches: z.array(sectorSchema).max(20) }).strict(),
  finance_sector_movers: z
    .object({
      items: z.array(sectorSchema.extend({ changePct: finiteNumber, breadthPct: finiteNumber.optional() })).max(50),
    })
    .strict(),
  finance_security_screen: z.object({ items: z.array(securitySchema).max(100) }).strict(),
  finance_security_snapshot: z
    .object({
      security: securitySchema,
      metrics: z.array(metricSchema).max(80),
      availableSections: z.array(boundedString(80)).max(20),
    })
    .strict(),
  finance_news_events: z
    .object({
      items: z
        .array(
          z
            .object({
              id: boundedString(120),
              title: boundedString(300),
              source: boundedString(160),
              publishedAt: isoTimestamp,
              url: boundedString(2048).optional(),
              symbols: z.array(symbol).max(20),
              summary: boundedString(1000).optional(),
            })
            .strict()
        )
        .max(100),
    })
    .strict(),
  finance_price_series: z
    .object({
      symbol,
      adjustment: z.enum(['none', 'split', 'total_return']),
      points: z.array(z.object({ at: isoTimestamp, value: finiteNumber }).strict()).max(10_000),
    })
    .strict(),
  finance_relationship_map: z
    .object({
      nodes: z
        .array(z.object({ id: boundedString(120), label: boundedString(160), kind: boundedString(80) }).strict())
        .max(100),
      edges: z
        .array(
          z
            .object({
              id: boundedString(120),
              from: boundedString(120),
              to: boundedString(120),
              relation: boundedString(120),
              evidenceIds: z.array(boundedString(160)).max(20),
            })
            .strict()
        )
        .max(300),
      counterevidenceIds: z.array(boundedString(160)).max(40),
    })
    .strict(),
  finance_research_portfolio: z
    .object({
      portfolioId: boundedString(120),
      revision: boundedString(160),
      kind: z.enum(['watchlist', 'simulation']),
      status: z.enum(['ready', 'partial']),
      positions: z.array(portfolioPositionSchema.extend({ value: finiteNumber.optional() })).max(100),
      resourceChanges: z.array(boundedString(240)).max(100),
    })
    .strict(),
  finance_holdings_parse: z
    .object({
      rows: z
        .array(holdingRowInputSchema.extend({ confidence: finiteNumber.min(0).max(1), rowId: boundedString(120) }))
        .max(500),
      lowConfidenceRowIds: z.array(boundedString(120)).max(500),
      redacted: z.literal(true),
      processing: z.enum(['local', 'cloud', 'structured']),
    })
    .strict(),
} satisfies Record<FinanceToolName, z.ZodTypeAny>;

export const financeToolInputSchemas = {
  finance_market_overview: financeMarketOverviewInputSchema,
  finance_sector_search: financeSectorSearchInputSchema,
  finance_sector_movers: financeSectorMoversInputSchema,
  finance_security_screen: financeSecurityScreenInputSchema,
  finance_security_snapshot: financeSecuritySnapshotInputSchema,
  finance_news_events: financeNewsEventsInputSchema,
  finance_price_series: financePriceSeriesInputSchema,
  finance_relationship_map: financeRelationshipMapInputSchema,
  finance_research_portfolio: financeResearchPortfolioInputSchema,
  finance_holdings_parse: financeHoldingsParseInputSchema,
} satisfies Record<FinanceToolName, z.ZodTypeAny>;

export const financeToolMcpInputShapes = {
  finance_market_overview: financeMarketOverviewInputSchema.shape,
  finance_sector_search: financeSectorSearchInputSchema.shape,
  finance_sector_movers: financeSectorMoversInputSchema.shape,
  finance_security_screen: financeSecurityScreenInputSchema.shape,
  finance_security_snapshot: financeSecuritySnapshotInputSchema.shape,
  finance_news_events: financeNewsEventsInputObject.shape,
  finance_price_series: financePriceSeriesInputObject.shape,
  finance_relationship_map: financeRelationshipMapInputObject.shape,
  finance_research_portfolio: financeResearchPortfolioInputSchema.shape,
  finance_holdings_parse: financeHoldingsParseInputSchema.shape,
} satisfies Record<FinanceToolName, z.ZodRawShape>;

export const financeToolResultSchemas = {
  finance_market_overview: createFinanceResultEnvelopeSchema(financeToolDataSchemas.finance_market_overview),
  finance_sector_search: createFinanceResultEnvelopeSchema(financeToolDataSchemas.finance_sector_search),
  finance_sector_movers: createFinanceResultEnvelopeSchema(financeToolDataSchemas.finance_sector_movers),
  finance_security_screen: createFinanceResultEnvelopeSchema(financeToolDataSchemas.finance_security_screen),
  finance_security_snapshot: createFinanceResultEnvelopeSchema(financeToolDataSchemas.finance_security_snapshot),
  finance_news_events: createFinanceResultEnvelopeSchema(financeToolDataSchemas.finance_news_events),
  finance_price_series: createFinanceResultEnvelopeSchema(financeToolDataSchemas.finance_price_series),
  finance_relationship_map: createFinanceResultEnvelopeSchema(financeToolDataSchemas.finance_relationship_map),
  finance_research_portfolio: createFinanceResultEnvelopeSchema(financeToolDataSchemas.finance_research_portfolio),
  finance_holdings_parse: createFinanceResultEnvelopeSchema(financeToolDataSchemas.finance_holdings_parse),
} satisfies Record<FinanceToolName, z.ZodTypeAny>;

export type FinanceToolInput<TName extends FinanceToolName> = z.infer<(typeof financeToolInputSchemas)[TName]>;
