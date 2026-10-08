/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

import {
  MATHEMATICS_UPSTREAM_PREMISE_SOURCES,
  symbolicMathTokens,
  type MathematicsUpstreamPremise,
  type MathematicsUpstreamPremiseSource,
  type MathematicsUpstreamSearchAttempt,
} from "../common/chat/mathematics";
import crypto from 'node:crypto';
import { scoreInstalledPremiseForGoal } from "./installedPackageSearch";

/* Sequential awaits in this file are bounded retry backoff, not unbounded polling. */
/* eslint-disable no-await-in-loop */

const LEANSEARCH_ENDPOINT = 'https://leansearch.net/search';
const LOOGLE_ENDPOINT = 'https://loogle.lean-lang.org/json';
const DEFAULT_RESULT_LIMIT = 6;
const DEFAULT_TIMEOUT_MS = 8_000;
const DEFAULT_MAX_RETRIES = 2;
const DEFAULT_RETRY_BASE_DELAY_MS = 200;
const MAX_RETRY_DELAY_MS = 5_000;
const MAX_RESPONSE_BYTES = 2 * 1024 * 1024;
const PREMISE_CACHE_TTL_MS = 30_000;
const PREMISE_CACHE_MAX_ENTRIES = 128;

type FetchLike = (input: string | URL | Request, init?: RequestInit) => Promise<Response>;

const transientHttpStatus = (status: number): boolean =>
  status === 408 || status === 425 || status === 429 || status >= 500;

const retryAfterMilliseconds = (headers: Headers, now = Date.now()): number | undefined => {
  const value = headers.get('retry-after')?.trim();
  if (!value) return undefined;
  const seconds = Number(value);
  if (Number.isFinite(seconds) && seconds >= 0) {
    return Math.min(MAX_RETRY_DELAY_MS, Math.max(0, Math.round(seconds * 1_000)));
  }
  const timestamp = Date.parse(value);
  return Number.isFinite(timestamp) ? Math.min(MAX_RETRY_DELAY_MS, Math.max(0, timestamp - now)) : undefined;
};

const retryDelayMilliseconds = (headers: Headers, attempt: number, baseDelayMs: number): number => {
  const hinted = retryAfterMilliseconds(headers);
  if (hinted !== undefined) return hinted;
  const exponential = baseDelayMs * 2 ** Math.max(0, attempt - 1);
  const jitter = Math.min(100, Math.round(baseDelayMs / 2));
  return Math.min(MAX_RETRY_DELAY_MS, exponential + jitter);
};

const waitForRetry = (delayMs: number): Promise<void> =>
  delayMs <= 0 ? Promise.resolve() : new Promise((resolve) => setTimeout(resolve, delayMs));

export type MathematicsUpstreamPremiseSearchResult = Readonly<{
  premises: readonly MathematicsUpstreamPremise[];
  attempts: readonly MathematicsUpstreamSearchAttempt[];
  /** Replay metadata for the exact public responses used to build the result. */
  provenance?: readonly Readonly<{
    source: MathematicsUpstreamPremiseSource;
    queryHash: string;
    responseHash?: string;
    fetchedAt: number;
    cacheHit: boolean;
  }>[];
}>;

export type MathematicsLiveFailureRetrievalRequest = Readonly<{
  goal: string;
  failureKind:
    'unknown_identifier' | 'type_mismatch' | 'instance_synthesis_failed' | 'unsolved_goals' | 'tactic_failed';
  failureDiagnostic?: string;
  importModules?: readonly string[];
  sourceFile?: string;
  proofStateFingerprint?: string;
  targetGoal?: string;
}>;

const documentationUrl = (declarationName: string): string =>
  `https://leanprover-community.github.io/mathlib4_docs/find/?pattern=${encodeURIComponent(declarationName)}#doc`;

const objectValue = (value: unknown): Record<string, unknown> | undefined =>
  value !== null && typeof value === 'object' && !Array.isArray(value) ? (value as Record<string, unknown>) : undefined;

const stringValue = (value: unknown): string | undefined =>
  typeof value === 'string' && value.trim() ? value.trim() : undefined;

const nameValue = (value: unknown): string | undefined => {
  if (typeof value === 'string') return stringValue(value);
  if (!Array.isArray(value)) return undefined;
  const components = value.filter(
    (component): component is string => typeof component === 'string' && Boolean(component)
  );
  return components.length === value.length && components.length > 0 ? components.join('.') : undefined;
};

const premiseTokens = (value: string): ReadonlySet<string> => symbolicMathTokens([value]);

const premiseOverlap = (premise: MathematicsUpstreamPremise, goalTokens: ReadonlySet<string>): number => {
  const tokens = premiseTokens(`${premise.declarationName} ${premise.declarationType}`);
  return [...goalTokens].filter((token) => tokens.has(token)).length;
};

const namespaceOverlap = (premise: MathematicsUpstreamPremise, goal: string): number => {
  if (!premise.sourceModule) return 0;
  const goalTokens = premiseTokens(goal);
  const moduleTokens = premiseTokens(premise.sourceModule);
  return [...moduleTokens].filter((token) => goalTokens.has(token)).length;
};

/** Rank public-index hits against the active goal without granting proof authority. */
export function rankUpstreamLeanPremises(
  premises: readonly MathematicsUpstreamPremise[],
  goal: string,
  limit = DEFAULT_RESULT_LIMIT
): readonly MathematicsUpstreamPremise[] {
  const goalTokens = premiseTokens(goal);
  return Object.freeze(
    [...premises]
      .map((premise) => {
        const overlap = premiseOverlap(premise, goalTokens);
        const shape = scoreInstalledPremiseForGoal(premise, goal);
        const namespace = namespaceOverlap(premise, goal);
        return {
          premise,
          // The shape score is deliberately capped: a public index is still
          // advisory and must not overpower exact lexical matches or provider
          // order when two candidates have equivalent conclusions.
          score: overlap * 2 + Math.min(96, shape) + namespace * 2 + (premise.source === 'loogle' ? 1 : 0),
        };
      })
      .toSorted((left, right) => right.score - left.score || left.premise.providerRank - right.premise.providerRank)
      .slice(0, Math.max(1, Math.min(32, limit)))
      .map(({ premise }) => premise)
  );
}

export function parseLeanSearchPremises(
  value: unknown,
  limit = DEFAULT_RESULT_LIMIT
): readonly MathematicsUpstreamPremise[] {
  const batch = Array.isArray(value) && Array.isArray(value[0]) ? value[0] : undefined;
  if (!batch) throw new TypeError('leansearch_invalid_response');
  const premises: MathematicsUpstreamPremise[] = [];
  for (const item of batch) {
    const result = objectValue(objectValue(item)?.result);
    const declarationName = nameValue(result?.name);
    const declarationType = stringValue(result?.signature) ?? stringValue(result?.type);
    if (!declarationName || !declarationType) continue;
    premises.push(
      Object.freeze({
        source: 'leansearch' as const,
        declarationName,
        declarationType,
        ...(nameValue(result?.module_name) ? { sourceModule: nameValue(result?.module_name) } : {}),
        documentationUrl: documentationUrl(declarationName),
        providerRank: premises.length + 1,
        compatibility: 'unverified' as const,
        targetValidationRequired: true as const,
      })
    );
    if (premises.length >= limit) break;
  }
  return Object.freeze(premises);
}

export function parseLooglePremises(
  value: unknown,
  limit = DEFAULT_RESULT_LIMIT
): readonly MathematicsUpstreamPremise[] {
  const root = objectValue(value);
  if (!root) throw new TypeError('loogle_invalid_response');
  if (typeof root.error === 'string') throw new TypeError('loogle_query_rejected');
  if (!Array.isArray(root.hits)) throw new TypeError('loogle_invalid_response');
  const premises: MathematicsUpstreamPremise[] = [];
  for (const item of root.hits) {
    const hit = objectValue(item);
    const declarationName = stringValue(hit?.name);
    const declarationType = stringValue(hit?.type);
    if (!declarationName || !declarationType) continue;
    premises.push(
      Object.freeze({
        source: 'loogle' as const,
        declarationName,
        declarationType,
        ...(stringValue(hit?.module) ? { sourceModule: stringValue(hit?.module) } : {}),
        documentationUrl: documentationUrl(declarationName),
        providerRank: premises.length + 1,
        compatibility: 'unverified' as const,
        targetValidationRequired: true as const,
      })
    );
    if (premises.length >= limit) break;
  }
  return Object.freeze(premises);
}

async function requestJson(
  fetchImpl: FetchLike,
  source: MathematicsUpstreamPremiseSource,
  query: string,
  resultLimit: number,
  timeoutMs: number,
  maxRetries: number,
  retryBaseDelayMs: number
): Promise<PremiseRequestResult> {
  for (let attempt = 0; ; attempt += 1) {
    const controller = new AbortController();
    const timeout = setTimeout(() => controller.abort(), timeoutMs);
    let response: Response;
    try {
      try {
        response =
          source === 'leansearch'
            ? await fetchImpl(LEANSEARCH_ENDPOINT, {
                method: 'POST',
                headers: { 'content-type': 'application/json', 'user-agent': 'DeepScientist premise retrieval' },
                body: JSON.stringify({ query: [query], num_results: resultLimit }),
                signal: controller.signal,
              })
            : await fetchImpl(`${LOOGLE_ENDPOINT}?${new URLSearchParams({ q: query })}`, {
                method: 'GET',
                headers: { 'user-agent': 'DeepScientist premise retrieval' },
                signal: controller.signal,
              });
      } catch (error) {
        if (attempt >= maxRetries) throw error;
        await waitForRetry(retryDelayMilliseconds(new Headers(), attempt + 1, retryBaseDelayMs));
        continue;
      }
    } finally {
      clearTimeout(timeout);
    }
    if (!response.ok) {
      if (transientHttpStatus(response.status) && attempt < maxRetries) {
        await waitForRetry(retryDelayMilliseconds(response.headers, attempt + 1, retryBaseDelayMs));
        continue;
      }
      throw new TypeError(`${source}_http_${response.status}`);
    }
    const contentLength = Number(response.headers.get('content-length'));
    if (Number.isFinite(contentLength) && contentLength > MAX_RESPONSE_BYTES) {
      throw new TypeError(`${source}_response_too_large`);
    }
    const body = await response.text();
    if (Buffer.byteLength(body, 'utf8') > MAX_RESPONSE_BYTES) {
      throw new TypeError(`${source}_response_too_large`);
    }
    let payload: unknown;
    try {
      payload = JSON.parse(body) as unknown;
    } catch {
      throw new TypeError(`${source}_invalid_response`);
    }
    const premises =
      source === 'leansearch'
        ? parseLeanSearchPremises(payload, resultLimit)
        : parseLooglePremises(payload, resultLimit);
    return Object.freeze({
      premises,
      responseHash: crypto.createHash('sha256').update(body, 'utf8').digest('hex'),
      fetchedAt: Date.now(),
    });
  }
}

const errorCode = (source: MathematicsUpstreamPremiseSource, error: unknown): string => {
  if (error instanceof TypeError && /^[a-z]+_[a-z0-9_]+$/u.test(error.message)) return error.message;
  if (error instanceof Error && error.name === 'AbortError') return `${source}_timeout`;
  return `${source}_unavailable`;
};

type PremiseCacheEntry = Readonly<{
  expiresAt: number;
  premises: readonly MathematicsUpstreamPremise[];
  responseHash: string;
  fetchedAt: number;
}>;

type PremiseRequestResult = Readonly<{
  premises: readonly MathematicsUpstreamPremise[];
  responseHash: string;
  fetchedAt: number;
  cacheHit?: boolean;
}>;

type PremiseProvenance = Readonly<{
  source: MathematicsUpstreamPremiseSource;
  queryHash: string;
  responseHash?: string;
  fetchedAt: number;
  cacheHit: boolean;
}>;

type PremiseSearchOutcome = Readonly<{
  premises: readonly MathematicsUpstreamPremise[];
  provenance?: PremiseProvenance;
  attempt: MathematicsUpstreamSearchAttempt;
}>;

// Worker turns often ask for the same live goal within one scheduling wave.
// Coalesce those requests in-process and retain successful public-index hits
// briefly; errors are never cached, so an unavailable index can recover on the
// next attempt.
const premiseCacheByFetcher = new WeakMap<object, Map<string, PremiseCacheEntry>>();
const premiseInflightByFetcher = new WeakMap<object, Map<string, Promise<PremiseRequestResult>>>();

const normalizedPremiseQuery = (query: string): string => query.trim().replace(/\s+/gu, ' ');

const loogleQueryForGoal = (goal: string): string => {
  const target = goal.includes('⊢') ? goal.slice(goal.lastIndexOf('⊢') + 1) : goal;
  return [...target]
    .map((character) => {
      const codePoint = character.codePointAt(0) ?? 0;
      return codePoint < 32 || codePoint === 127 || '"`;'.includes(character) ? ' ' : character;
    })
    .join('')
    .replace(/\s+/gu, ' ')
    .trim()
    .slice(0, 1_800);
};

type LeanFailurePremiseQueryPlan = Readonly<{
  leanSearchInstruction: string;
  fallbackInstruction: string;
}>;

const leanFailurePremiseQueryPlan = (
  failureKind: MathematicsLiveFailureRetrievalRequest['failureKind']
): LeanFailurePremiseQueryPlan => {
  switch (failureKind) {
    case 'unknown_identifier':
      return Object.freeze({
        leanSearchInstruction:
          'Resolve the unknown Lean identifier by finding its fully qualified declaration, defining module, or an equivalent theorem applicable to the target.',
        fallbackInstruction:
          'Find a Mathlib declaration with this conclusion and report the fully qualified name and module import.',
      });
    case 'type_mismatch':
      return Object.freeze({
        leanSearchInstruction:
          'Find a theorem whose conclusion unifies with this Lean target and can be tested with exact or apply.',
        fallbackInstruction: 'Find a theorem whose conclusion unifies with this Lean target.',
      });
    case 'instance_synthesis_failed':
      return Object.freeze({
        leanSearchInstruction:
          'Find the Mathlib typeclass instance, constructor, or module import needed to synthesize the failed instance in this target.',
        fallbackInstruction:
          'Find an instance or constructor for the typeclass obligation implied by this Lean target.',
      });
    case 'unsolved_goals':
      return Object.freeze({
        leanSearchInstruction:
          'Find a theorem that closes the remaining Lean goal directly with exact/apply, or exposes a short rewrite that closes it.',
        fallbackInstruction: 'Find a theorem whose conclusion closes this remaining Lean goal.',
      });
    case 'tactic_failed':
      return Object.freeze({
        leanSearchInstruction:
          'The current tactic family failed. Find a direct theorem for exact/apply/rewrite so the proof can switch tactics without repeating blind automation.',
        fallbackInstruction: 'Find a direct theorem that avoids the failed tactic family for this Lean target.',
      });
  }
};

const boundedCachePut = (cache: Map<string, PremiseCacheEntry>, key: string, result: PremiseRequestResult): void => {
  cache.delete(key);
  cache.set(key, Object.freeze({ expiresAt: Date.now() + PREMISE_CACHE_TTL_MS, ...result }));
  while (cache.size > PREMISE_CACHE_MAX_ENTRIES) {
    const oldest = cache.keys().next().value;
    if (oldest === undefined) break;
    cache.delete(oldest);
  }
};

const requestJsonCoalesced = async (
  fetchImpl: FetchLike,
  source: MathematicsUpstreamPremiseSource,
  query: string,
  resultLimit: number,
  timeoutMs: number,
  maxRetries: number,
  retryBaseDelayMs: number
): Promise<PremiseRequestResult> => {
  const fetcher = fetchImpl as unknown as object;
  let cache = premiseCacheByFetcher.get(fetcher);
  if (!cache) {
    cache = new Map();
    premiseCacheByFetcher.set(fetcher, cache);
  }
  const key = `${source}\0${normalizedPremiseQuery(query)}\0${resultLimit}\0${timeoutMs}\0${maxRetries}\0${retryBaseDelayMs}`;
  const cached = cache.get(key);
  if (cached) {
    if (cached.expiresAt > Date.now()) {
      cache.delete(key);
      cache.set(key, cached);
      return Object.freeze({
        premises: cached.premises,
        responseHash: cached.responseHash,
        fetchedAt: cached.fetchedAt,
        cacheHit: true,
      });
    }
    cache.delete(key);
  }
  let inflight = premiseInflightByFetcher.get(fetcher);
  if (!inflight) {
    inflight = new Map();
    premiseInflightByFetcher.set(fetcher, inflight);
  }
  const active = inflight.get(key);
  if (active) return active;
  const request = requestJson(fetchImpl, source, query, resultLimit, timeoutMs, maxRetries, retryBaseDelayMs)
    .then((result) => {
      boundedCachePut(cache!, key, result);
      return result;
    })
    .finally(() => {
      inflight!.delete(key);
    });
  inflight.set(key, request);
  return request;
};

export async function searchUpstreamLeanPremises(
  queries: Readonly<Partial<Record<MathematicsUpstreamPremiseSource, string>>>,
  options: Readonly<{
    fetchImpl?: FetchLike;
    resultLimit?: number;
    timeoutMs?: number;
    maxRetries?: number;
    retryBaseDelayMs?: number;
    queryVariants?: Readonly<Partial<Record<MathematicsUpstreamPremiseSource, readonly string[]>>>;
  }> = {}
): Promise<MathematicsUpstreamPremiseSearchResult> {
  const fetchImpl = options.fetchImpl ?? globalThis.fetch;
  const resultLimit = Math.max(1, Math.min(6, options.resultLimit ?? DEFAULT_RESULT_LIMIT));
  const timeoutMs = Math.max(500, Math.min(30_000, options.timeoutMs ?? DEFAULT_TIMEOUT_MS));
  const maxRetries = Math.max(0, Math.min(4, Math.floor(options.maxRetries ?? DEFAULT_MAX_RETRIES)));
  const retryBaseDelayMs = Math.max(
    0,
    Math.min(2_000, Math.floor(options.retryBaseDelayMs ?? DEFAULT_RETRY_BASE_DELAY_MS))
  );
  const requested = MATHEMATICS_UPSTREAM_PREMISE_SOURCES.flatMap((source) => {
    const values = [queries[source] ?? '', ...(options.queryVariants?.[source] ?? [])]
      .map((value) => value.trim())
      .filter(Boolean);
    return [...new Set(values)].map((query) => ({ source, query }));
  });
  const outcomes: readonly PremiseSearchOutcome[] = await Promise.all(
    requested.map(async ({ source, query }): Promise<PremiseSearchOutcome> => {
      try {
        const result = await requestJsonCoalesced(
          fetchImpl,
          source,
          query,
          resultLimit,
          timeoutMs,
          maxRetries,
          retryBaseDelayMs
        );
        return {
          premises: result.premises,
          provenance: Object.freeze({
            source,
            queryHash: crypto.createHash('sha256').update(normalizedPremiseQuery(query), 'utf8').digest('hex'),
            responseHash: result.responseHash,
            fetchedAt: result.fetchedAt,
            cacheHit: result.cacheHit === true,
          }),
          attempt: Object.freeze({ source, status: 'ok' as const, resultCount: result.premises.length }),
        };
      } catch (error) {
        return {
          premises: Object.freeze([]),
          provenance: undefined,
          attempt: Object.freeze({
            source,
            status: 'unavailable' as const,
            resultCount: 0,
            errorCode: errorCode(source, error),
          }),
        };
      }
    })
  );
  const byDeclaration = new Map<string, MathematicsUpstreamPremise>();
  for (const outcome of outcomes) {
    for (const premise of outcome.premises) {
      if (!byDeclaration.has(premise.declarationName)) byDeclaration.set(premise.declarationName, premise);
    }
  }
  return Object.freeze({
    premises: Object.freeze([...byDeclaration.values()]),
    attempts: Object.freeze(outcomes.map(({ attempt }) => attempt)),
    provenance: Object.freeze(outcomes.flatMap(({ provenance }) => (provenance ? [provenance] : []))),
  });
}

/**
 * Build a bounded public-index lookup from a live Lean failure.  The caller
 * still must run #check and target compilation before adopting any result.
 */
export async function retrieveLeanPremisesForFailure(
  request: MathematicsLiveFailureRetrievalRequest,
  options: Readonly<{
    fetchImpl?: FetchLike;
    resultLimit?: number;
    timeoutMs?: number;
  }> = {}
): Promise<MathematicsUpstreamPremiseSearchResult> {
  const goal = request.goal.trim();
  if (!goal) throw new TypeError('live failure retrieval requires a goal');
  const queryPlan = leanFailurePremiseQueryPlan(request.failureKind);
  const query = [
    queryPlan.leanSearchInstruction,
    request.failureDiagnostic?.trim() ? `First Lean diagnostic: ${request.failureDiagnostic.trim()}` : '',
    'Live goal:',
    goal,
    request.importModules?.length ? `Current imports: ${request.importModules.join(', ')}` : '',
    request.sourceFile ? `Source file: ${request.sourceFile}` : '',
  ]
    .filter(Boolean)
    .join('\n');
  const targetGoal = request.targetGoal?.trim() || goal;
  const loogleQuery = loogleQueryForGoal(targetGoal) || loogleQueryForGoal(goal);
  const primary = await searchUpstreamLeanPremises({ leansearch: query, loogle: loogleQuery }, options);
  const targetTokens = premiseTokens(targetGoal);
  // A nonempty unrelated answer is not successful retrieval. Structural applicability
  // is still checked by Lean; this only determines whether to explore another query.
  if (primary.premises.some((premise) => premiseOverlap(premise, targetTokens) >= Math.min(2, targetTokens.size || 1))) {
    // Providers return their own order, which is useful for provenance but not
    // for choosing the next proof action. Apply the same target-shape ranking
    // used for fallback merges before handing the result to a Worker.
    return Object.freeze({
      ...primary,
      premises: rankUpstreamLeanPremises(primary.premises, targetGoal, options.resultLimit ?? DEFAULT_RESULT_LIMIT),
    });
  }
  const fallback = await searchUpstreamLeanPremises(
    {},
    {
      ...options,
      queryVariants: {
        leansearch: [`${queryPlan.fallbackInstruction}\n${targetGoal}`],
        loogle: [targetGoal],
      },
    }
  );
  return Object.freeze({
    premises: rankUpstreamLeanPremises(
      [
        ...new Map(
          [...primary.premises, ...fallback.premises].map((premise) => [
            `${premise.source}\0${premise.declarationName}`,
            premise,
          ])
        ).values(),
      ],
      targetGoal,
      options.resultLimit ?? DEFAULT_RESULT_LIMIT
    ),
    attempts: Object.freeze([...primary.attempts, ...fallback.attempts]),
    provenance: Object.freeze([...(primary.provenance ?? []), ...(fallback.provenance ?? [])]),
  });
}

/* eslint-enable no-await-in-loop */
