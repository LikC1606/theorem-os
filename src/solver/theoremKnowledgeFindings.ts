import { z } from 'zod';
import { canonicalMathJson, mathDigest } from '../math/mathRuntimeIo';
import type { TheoremKnowledgeBase } from './theoremKnowledge';

const hash = z.string().regex(/^[a-f0-9]{64}$/u);
const text = z.string().min(1).max(1_000_000);
const contract = z.object({
  kind: z.enum(['research', 'sketch', 'lemma', 'goal']),
  statement: text,
  statementKind: z.enum(['research-objective', 'closed-task-type', 'source-header']),
  premises: z.array(z.string().max(12_000)).max(128),
}).strict();
const scope = z.object({
  problemId: z.string().min(1), problemReceiptDigest: hash, environmentDigest: z.string().min(1),
  source: contract, dependencies: z.array(contract).max(1024),
}).strict();
const provenance = z.object({
  source: z.string().min(1), sourceDigest: hash, runId: z.string().min(1),
  taskId: z.string().min(1), taskDigest: hash, groupId: z.string().min(1),
  deliveryId: z.string().min(1), sourceCommit: z.string().regex(/^[a-f0-9]{40}(?:[a-f0-9]{24})?$/u),
  findingDigest: hash, notesDigest: hash,
}).strict();
const finding = z.object({
  evidence: z.literal('recorded-advisory-not-replayed'), acceptance: z.literal('not-assessed'),
  conclusion: z.enum(['supporting', 'refuted', 'inconclusive']),
  summary: text, finding: text, notes: text, scope,
  evidenceRefs: z.array(z.string().max(2000)).max(256),
  obstructions: z.array(z.object({ mechanism: z.string().min(1).max(500), scope: z.string().min(1).max(2000),
    evidenceRefs: z.array(z.string().max(2000)).max(256) }).strict()).max(256),
  remainingObligations: z.array(z.string().max(12_000)).max(256),
  /** Exact recorded text only; these conditions do not authorize scheduling or reopening. */
  reconsiderWhen: z.array(z.string().max(12_000)).max(256),
}).strict();

export const knowledgeRouteFindingSchema = finding.extend({ id: hash, scopeDigest: hash,
  provenance: z.array(provenance).min(1).max(4096) }).strict();
export type KnowledgeRouteContract = z.infer<typeof contract>;
export type KnowledgeRouteFinding = z.infer<typeof knowledgeRouteFindingSchema>;
export type KnowledgeRouteFindingCandidate = z.infer<typeof finding> & { provenance: z.infer<typeof provenance> };

/** Run-local task names never enter the recorded mathematical scope identity. */
export function knowledgeRouteScopeDigest(value: KnowledgeRouteFinding['scope']): string {
  return mathDigest(canonicalMathJson({ ...value,
    dependencies: [...value.dependencies].sort((a, b) => canonicalMathJson(a).localeCompare(canonicalMathJson(b))) }));
}
const identity = (value: Omit<KnowledgeRouteFinding, 'id' | 'provenance'>) => mathDigest(canonicalMathJson(value));

/** Advisory research is kept separate from checked declarations and cannot supply an acceptance receipt. */
export function buildKnowledgeRouteFindings(candidates: readonly KnowledgeRouteFindingCandidate[],
  previous: readonly KnowledgeRouteFinding[] = []): KnowledgeRouteFinding[] {
  validateKnowledgeRouteFindings(previous);
  const entries = new Map(previous.map(item => [item.id, structuredClone(item)]));
  for (const candidate of candidates) {
    const { provenance: origin, ...raw } = candidate;
    const details = finding.parse(raw); provenance.parse(origin);
    const scopeDigest = knowledgeRouteScopeDigest(details.scope), value = { ...details, scopeDigest };
    const id = identity(value), existing = entries.get(id);
    if (existing) {
      if (!existing.provenance.some(item => canonicalMathJson(item) === canonicalMathJson(origin))) existing.provenance.push(origin);
    } else entries.set(id, { ...value, id, provenance: [origin] });
  }
  const result = [...entries.values()].sort((a, b) => a.id.localeCompare(b.id));
  for (const item of result) item.provenance.sort((a, b) => canonicalMathJson(a).localeCompare(canonicalMathJson(b)));
  validateKnowledgeRouteFindings(result);
  return result;
}

export function validateKnowledgeRouteFindings(entries: readonly KnowledgeRouteFinding[]): void {
  const ids = new Set<string>();
  for (const value of entries) {
    const parsed = knowledgeRouteFindingSchema.safeParse(value);
    if (!parsed.success) throw new Error('math_knowledge_finding_schema_invalid');
    const { id, provenance: origins, ...details } = parsed.data;
    if (ids.has(id) || identity(details) !== id || knowledgeRouteScopeDigest(details.scope) !== details.scopeDigest)
      throw new Error('math_knowledge_finding_identity_changed');
    if (origins.some(origin => origin.findingDigest !== mathDigest(details.finding) || origin.notesDigest !== mathDigest(details.notes)))
      throw new Error('math_knowledge_finding_source_changed');
    ids.add(id);
  }
}

type SearchBase = Pick<TheoremKnowledgeBase, 'routeFindings'>;
export type KnowledgeRouteFindingSearchOptions = {
  goal?: string; limit?: number; problemId?: string; environmentDigest?: string; problemReceiptDigest?: string;
};
const terms = (value: string) => [...new Set(value.toLowerCase().match(/[\p{L}\p{N}_']{2,}/gu) ?? [])];
const preview = (value: string, max: number) => value.length <= max ? value : value.slice(0, max - 1).replace(/[\uD800-\uDBFF]$/u, '') + '…';

/** Retrieval can recall a renamed task, but text matches never establish equivalent hypotheses or invalidate a route. */
export function searchKnowledgeRouteFindings(base: SearchBase, query: string,
  options: KnowledgeRouteFindingSearchOptions = {}) {
  const limit = options.limit ?? 10;
  if (typeof query !== 'string' || Buffer.byteLength(query) > 4000 ||
      (options.goal !== undefined && (typeof options.goal !== 'string' || Buffer.byteLength(options.goal) > 16000)) ||
      (!query.trim() && !options.goal?.trim()) || !Number.isSafeInteger(limit) || limit < 1 || limit > 32 ||
      [options.problemId, options.environmentDigest, options.problemReceiptDigest].some(value => value !== undefined &&
        (typeof value !== 'string' || !value.trim() || Buffer.byteLength(value) > 256)))
    throw new Error('math_knowledge_invalid_query');
  const inputs = terms(query + '\n' + (options.goal ?? ''));
  const hits = (base.routeFindings ?? []).flatMap(item => {
    if (options.problemId && item.scope.problemId !== options.problemId) return [];
    const statements = [item.scope.source.statement, ...item.scope.dependencies.map(value => value.statement)];
    const haystack = new Set(terms([...statements, item.summary].join('\n')));
    const matched = inputs.filter(value => haystack.has(value));
    const exactStatement = Boolean(options.goal && statements.includes(options.goal));
    if (!matched.length && !exactStatement) return [];
    const environmentMatch = options.environmentDigest === undefined ? 'unknown' :
      item.scope.environmentDigest === options.environmentDigest ? 'match' : 'different';
    const problemReceiptMatch = options.problemReceiptDigest === undefined ? 'unknown' :
      item.scope.problemReceiptDigest === options.problemReceiptDigest ? 'match' : 'different';
    return [{ id: item.id, scopeDigest: item.scopeDigest, conclusion: item.conclusion, summary: preview(item.summary, 1200),
      problemId: item.scope.problemId, environmentMatch, problemReceiptMatch,
      statementMatch: exactStatement ? 'exact-recorded-text' as const : 'lexical-only' as const,
      scopeMatch: exactStatement && environmentMatch === 'match' && problemReceiptMatch === 'match'
        ? 'statement-and-recorded-environment' as const : 'not-established' as const,
      evidence: item.evidence, acceptance: item.acceptance, score: matched.length + (exactStatement ? 1000 : 0),
      matched, requiresScopeReview: true as const,
      readWith: { command: 'knowledge finding', id: item.id } }];
  }).sort((a, b) => b.score - a.score || a.id.localeCompare(b.id));
  return { schema: 'theorem-os.knowledge-route-search.v1' as const, evidence: 'recorded-advisory-not-replayed' as const,
    acceptance: 'not-assessed' as const, advisoryOnly: true as const, total: hits.length, hits: hits.slice(0, limit) };
}

/** The complete note and exact input contracts remain available without installing historical proof sources. */
export function getKnowledgeRouteFinding(base: SearchBase, id: string) {
  const entry = base.routeFindings?.find(item => item.id === id);
  if (!entry) throw new Error('math_knowledge_finding_not_found');
  validateKnowledgeRouteFindings([entry]);
  return { schema: 'theorem-os.knowledge-route-finding.v1' as const, advisoryOnly: true as const,
    reuse: 'Review the exact assumptions, evidence and reconsideration conditions. A recorded refutation does not refute the original theorem or authorize parking a task. Recheck local Lean claims in the current environment.',
    ...entry };
}

/** Exact JSON pages keep long arguments readable without silently dropping their assumptions or evidence. */
export function getKnowledgeRouteFindingPage(base: SearchBase, id: string,
  options: { startOffset?: number; maxBytes?: number } = {}) {
  const { startOffset: begin = 0, maxBytes = 16000 } = options;
  if (!Number.isSafeInteger(begin) || begin < 0 || !Number.isSafeInteger(maxBytes) || maxBytes < 1024 || maxBytes > 65536)
    throw new Error('math_knowledge_finding_options_invalid');
  const entry = getKnowledgeRouteFinding(base, id), source = canonicalMathJson(entry);
  const splitsSurrogate = (offset: number) => offset > 0 && offset < source.length &&
    /[\uD800-\uDBFF]/u.test(source[offset - 1]!) && /[\uDC00-\uDFFF]/u.test(source[offset]!);
  if (begin > source.length || splitsSurrogate(begin)) throw new Error('math_knowledge_finding_position_invalid');
  const sha256 = mathDigest(source), bytes = Buffer.byteLength(source);
  const packet = (end: number) => ({ schema: 'theorem-os.knowledge-route-finding-page.v1' as const, id: entry.id,
    scopeDigest: entry.scopeDigest, evidence: entry.evidence, acceptance: entry.acceptance, advisoryOnly: true as const,
    sha256, bytes, offsetEncoding: 'utf16-code-unit' as const, endOffsetExclusive: true as const,
    display: { startOffset: begin, endOffset: end, bytes: Buffer.byteLength(source.slice(begin, end)) },
    text: source.slice(begin, end), truncated: end < source.length, ...(end < source.length ? { nextOffset: end } : {}) });
  const fits = (end: number) => Buffer.byteLength(JSON.stringify(packet(end))) + 1 <= maxBytes;
  if (fits(source.length)) return packet(source.length);
  if (!fits(begin)) throw new Error('math_knowledge_finding_budget_too_small');
  let lower = begin + 1, upper = Math.min(source.length - 1, begin + maxBytes), best = begin;
  while (lower <= upper) {
    const middle = Math.floor((lower + upper) / 2), end = splitsSurrogate(middle) ? middle - 1 : middle;
    if (fits(end)) { best = end; lower = middle + 1; } else upper = middle - 1;
  }
  if (best === begin && begin < source.length) throw new Error('math_knowledge_finding_budget_too_small');
  return packet(best);
}
