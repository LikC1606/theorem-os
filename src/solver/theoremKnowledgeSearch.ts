import { canonicalMathJson, mathDigest } from '../math/mathRuntimeIo';
import { maskLeanCommentsAndStrings } from '../math/leanSyntax';
import { knowledgeGoalSurfaceShape } from './theoremKnowledgeGoal';
import type { TheoremKnowledgeBase, TheoremKnowledgeEntry } from './theoremKnowledge';

export type KnowledgeSearchOptions = {
  goal?: string; limit?: number; problemId?: string; environmentDigest?: string; problemReceiptDigest?: string;
};
type KnowledgeSearchBase = Pick<TheoremKnowledgeBase, 'entries' | 'evidence'>;
type PreferenceMatch = 'match' | 'different' | 'unknown' | 'not-requested';
const boilerplate = new Set(['submission', 'helpers', 'helper', 'theorem', 'lemma', 'def', 'abbrev', 'opaque',
  'by', 'fun', 'type', 'prop', 'sort', 'forall', 'exists', 'let', 'in', 'have', 'show',
  'the', 'a', 'an', 'to', 'from', 'of', 'for', 'with', 'this', 'that', 'and', 'or', 'is',
  'it', 'its', 'their', 'they', 'them', 'our', 'your', 'which', 'whose', 'where',
  'be', 'been', 'being', 'are', 'was', 'were', 'has', 'had', 'does', 'did',
  'would', 'should', 'could', 'will', 'please', 'find', 'need', 'want', 'looking']);
const aliases: Readonly<Record<string, string>> = {
  'ℝ≥0∞': 'ENNReal', 'ℝ≥0': 'NNReal', 'ℝ': 'Real', 'ℕ': 'Nat', 'ℤ': 'Int', 'ℚ': 'Rat', 'ℂ': 'Complex',
  '∀': 'forall ', '∃': 'exists ', '↔': ' iff ', '<->': ' iff ', '→': ' arrow ', '->': ' arrow ',
  '¬': ' not ', '∧': ' and ', '∨': ' or ', '≤': ' le ', '<=': ' le ', '≥': ' ge ', '>=': ' ge ',
  '≠': ' ne ', '!=': ' ne ', '∈': ' mem ', '∑': ' sum ', '∏': ' prod ',
};
const leanText = (value: string) => (/--|\/-|"/u.test(value) ? maskLeanCommentsAndStrings(value) : value)
  .replace(/\b_root_\./gu, '').replace(/ℝ≥0∞|ℝ≥0|[ℝℕℤℚℂ∀∃↔→¬∧∨≤≥≠∈∑∏]|<->|->|<=|>=|!=/gu, match => aliases[match]!);
const canonical = (value: string) => leanText(value).toLowerCase().replace(/\s+/gu, '');
const termAliases = new Map([['pderiv', ['partial', 'derivative', 'derivatives']]]);

function terms(value: string, binders = false): string[] {
  return textTerms(leanText(value), binders);
}

function textTerms(text: string, binders: boolean): string[] {
  const bound = new Set<string>();
  if (binders) {
    for (const match of text.matchAll(/(?:[([{]|\bforall\b|\bexists\b|^|\n)\s*([\p{L}_][\p{L}\p{M}\p{N}_' \t]*?)\s*:/gu))
      for (const name of match[1]!.trim().split(/\s+/u)) bound.add(name);
  }
  const result = new Set<string>();
  for (const match of text.matchAll(/[\p{L}\p{N}_][\p{L}\p{M}\p{N}_'.]*/gu)) {
    for (const segment of match[0].split('.').filter(part => !bound.has(part))) {
      const pieces = segment.replace(/([a-z])([A-Z])/gu, '$1 $2').replace(/([A-Z]+)([A-Z][a-z])/gu, '$1 $2').split(/[_\s]+/u);
      for (const token of [...pieces, ...(pieces.length > 1 && !segment.includes('_') ? [segment] : [])]) {
        const lower = token.toLowerCase();
        if (lower && !boilerplate.has(lower) && (lower.length > 1 || /[\p{N}]|[^\x00-\x7f]/u.test(lower))) {
          result.add(lower);
          for (const alias of termAliases.get(lower) ?? []) result.add(alias);
        }
      }
    }
  }
  return [...result];
}

function typeExpression(item: TheoremKnowledgeEntry): string {
  if (item.typeKind !== 'source-header') return item.type;
  const header = item.type.replace(/^(?:(?:theorem|lemma|def|abbrev|opaque)\s+)?[\p{L}_][\p{L}\p{M}\p{N}_'.]*\s*/u, '');
  let depth = 0;
  for (let index = 0; index < header.length; index++) {
    const character = header[index]!;
    if ('([{'.includes(character)) depth++;
    else if (')]}'.includes(character)) depth--;
    else if (character === ':' && depth === 0) {
      const binders = header.slice(0, index).trim(), body = header.slice(index + 1).trim();
      return binders ? `forall ${binders}, ${body}` : body;
    }
  }
  return item.type;
}

function goalTarget(value: string): string {
  const marker = Math.max(value.lastIndexOf('⊢'), value.lastIndexOf('|-'));
  return marker < 0 ? value : value.slice(marker + (value[marker] === '⊢' ? 1 : 2));
}

export function knowledgeSearchGroup(item: TheoremKnowledgeEntry): string {
  return mathDigest(canonicalMathJson({ name: item.name, type: item.type, typeKind: item.typeKind, declaration: item.declaration }));
}

function preference(requested: string | undefined, recorded: readonly (string | undefined)[]): PreferenceMatch {
  if (requested === undefined) return 'not-requested';
  const known = recorded.filter((value): value is string => Boolean(value));
  return known.includes(requested) ? 'match' : known.length ? 'different' : 'unknown';
}

export function knowledgeVersionSummary(item: TheoremKnowledgeEntry, options: KnowledgeSearchOptions = {}) {
  return { id: item.id, contextDigest: item.contextDigest, environmentDigest: item.environmentDigest,
    problemIds: [...new Set(item.provenance.map(origin => origin.problemId))].sort(),
    sourceKinds: [...new Set(item.provenance.map(origin => origin.kind))].sort(),
    problemReceiptDigests: [...new Set(item.provenance.map(origin => origin.problemReceiptDigest).filter(Boolean))].sort(),
    premisesCount: item.premises.length, premisesDigest: mathDigest(canonicalMathJson(item.premises)),
    dependenciesDigest: mathDigest(canonicalMathJson(item.dependencies)),
    dependencyCoverage: item.dependencies.coverage,
    environmentMatch: preference(options.environmentDigest, [item.environmentDigest, ...item.provenance.map(origin => origin.environmentDigest)]),
    problemReceiptMatch: preference(options.problemReceiptDigest, item.provenance.map(origin => origin.problemReceiptDigest)),
  };
}

function versionPreference(item: TheoremKnowledgeEntry, options: KnowledgeSearchOptions): number[] {
  const receiptMatch = preference(options.problemReceiptDigest, item.provenance.map(origin => origin.problemReceiptDigest)),
    environmentMatch = preference(options.environmentDigest, [item.environmentDigest, ...item.provenance.map(origin => origin.environmentDigest)]),
    labels = [receiptMatch, environmentMatch];
  return [labels.filter(label => label === 'match').length, -labels.filter(label => label === 'different').length,
    receiptMatch === 'match' ? 1 : 0, environmentMatch === 'match' ? 1 : 0];
}

function validateQuery(query: string, options: KnowledgeSearchOptions): void {
  const limit = options.limit ?? 10, goal = options.goal ?? '';
  if (typeof query !== 'string' || typeof goal !== 'string' || !Number.isInteger(limit) || limit < 1 || limit > 32 ||
      Buffer.byteLength(query) > 4000 || Buffer.byteLength(goal) > 16000 || (!query.trim() && !goal.trim()) ||
      [options.environmentDigest, options.problemReceiptDigest].some(value => value !== undefined &&
        (typeof value !== 'string' || !value.trim() || Buffer.byteLength(value) > 256))) throw new Error('math_knowledge_invalid_query');
}

function prepareSearch(base: KnowledgeSearchBase, options: KnowledgeSearchOptions, relevant: ReadonlySet<string>) {
  const goalSurface = options.goal ? knowledgeGoalSurfaceShape(goalTarget(options.goal)) : undefined;
  const texts = new Map<string, string>(), plainTerms = new Map<string, Set<string>>(), boundTerms = new Map<string, Set<string>>();
  const text = (value: string) => {
    let result = texts.get(value);
    if (result === undefined) { result = leanText(value); texts.set(value, result); }
    return result;
  };
  const field = (value: string, binders = false) => {
    const cache = binders ? boundTerms : plainTerms;
    let result = cache.get(value);
    if (!result) { result = new Set(textTerms(text(value), binders)); cache.set(value, result); }
    return result;
  };
  const documents = base.entries.filter(item => !options.problemId || item.provenance.some(origin => origin.problemId === options.problemId))
    .map(item => {
      const type = typeExpression(item);
      return { item, group: knowledgeSearchGroup(item), fields: [field(item.name), field(type, true),
        field([...item.dependencies.statement, ...item.dependencies.proof].map(reference => reference.name).join(' ')),
        field(item.description), field(item.provenance.map(origin => origin.problemId).join(' '))],
        normalizedType: text(type).toLowerCase().replace(/\s+/gu, ''), surfaceShape: goalSurface ? knowledgeGoalSurfaceShape(type) : undefined };
    });
  const groupsByToken = new Map<string, Set<string>>();
  for (const document of documents) {
    for (const field of document.fields) for (const token of field) {
      if (!relevant.has(token)) continue;
      let groups = groupsByToken.get(token);
      if (!groups) { groups = new Set(); groupsByToken.set(token, groups); }
      groups.add(document.group);
    }
  }
  return { documents, goalSurface, groupCount: new Set(documents.map(document => document.group)).size,
    frequencies: new Map([...groupsByToken].map(([token, groups]) => [token, groups.size])) };
}

/** Lexical and goal-shape ranking is advisory; matching metadata never establishes applicability. */
export function searchTheoremKnowledge(base: KnowledgeSearchBase, query: string, options: KnowledgeSearchOptions = {}) {
  return searchTheoremKnowledgeBatch(base, [query], options)[0]!;
}

/** Preparation belongs to this call, so later calls always observe current entry metadata. */
export function searchTheoremKnowledgeBatch(base: KnowledgeSearchBase, queries: readonly string[], options: KnowledgeSearchOptions = {}) {
  if (!Array.isArray(queries) || queries.length < 1 || queries.length > 8) throw new Error('math_knowledge_invalid_query');
  for (const query of queries) validateQuery(query, options);
  const goal = options.goal ?? '', relevant = new Set(terms(goal, true));
  for (const query of new Set(queries))
    for (const term of terms(query.trim() ? query : goalTarget(goal), !query.trim())) relevant.add(term);
  const prepared = prepareSearch(base, options, relevant), results = new Map<string, ReturnType<typeof searchPrepared>>();
  return queries.map(query => {
    const cached = results.get(query);
    if (cached) return structuredClone(cached);
    const result = searchPrepared(prepared, base.evidence, query, options);
    results.set(query, result);
    return result;
  });
}

function searchPrepared(prepared: ReturnType<typeof prepareSearch>, evidence: KnowledgeSearchBase['evidence'], query: string,
  options: KnowledgeSearchOptions) {
  const limit = options.limit ?? 10, goal = options.goal ?? '', { documents, groupCount, frequencies } = prepared;
  const goalOnly = !query.trim(), primary = terms(goalOnly ? goalTarget(goal) : query, goalOnly),
    goalTerms = terms(goal, true), normalizedGoal = canonical(goalTarget(goal));
  const identifier = query.trim().replace(/^_root_\./u, '').toLowerCase();
  const nameQuery = /^[\p{L}_][\p{L}\p{M}\p{N}_'.]*$/u.test(identifier);
  const relevant = [...new Set([...primary, ...goalTerms])];
  const idf = new Map(relevant.map(term => [term, 1 + Math.log((groupCount + 1) /
    (1 + (frequencies.get(term) ?? 0)))]));
  const primaryWeight = primary.reduce((sum, term) => sum + idf.get(term)!, 0);
  const scored = documents.map(document => {
    const { item, fields } = document, normalizedName = item.name.replace(/^_root_\./u, '').toLowerCase();
    const nameScore = !goalOnly && nameQuery ? normalizedName === identifier ? 5000 :
      normalizedName.split('.').at(-1) === identifier ? 4500 : normalizedName.endsWith(`.${identifier}`) ? 4700 : 0 : 0;
    const matched = primary.filter(term => fields.some(field => field.has(term)));
    if (!goalOnly && !nameScore && !matched.length) return undefined;
    const main = primary.filter(term => fields[0]!.has(term) || fields[1]!.has(term));
    const dependencies = primary.filter(term => fields[2]!.has(term));
    const exactGoal = Boolean(normalizedGoal && normalizedGoal === document.normalizedType),
      trailingGoal = Boolean(normalizedGoal.length >= 8 && document.normalizedType.endsWith(normalizedGoal)),
      surfaceMatch = prepared.goalSurface !== undefined && prepared.goalSurface === document.surfaceShape;
    if (goalOnly && !main.length && !exactGoal && !trailingGoal && !surfaceMatch) return undefined;
    const coverage = primaryWeight ? main.reduce((sum, term) => sum + idf.get(term)!, 0) / primaryWeight : 0;
    let score = nameScore;
    for (const term of primary) {
      const significance = idf.get(term)!;
      score += significance * ((fields[0]!.has(term) ? 8 : 0) + (fields[1]!.has(term) ? 5 : 0)) * (0.1 + coverage * coverage);
      score += significance * ((fields[2]!.has(term) ? 1 : 0) + (fields[3]!.has(term) ? 0.15 : 0) + (fields[4]!.has(term) ? 0.05 : 0));
    }
    score += 100 * coverage * coverage;
    if (normalizedGoal) {
      let goalScore = exactGoal ? 3000 : surfaceMatch ? 2000 : trailingGoal ? 1000 : 0;
      const denominator = goalTerms.reduce((sum, term) => sum + idf.get(term)!, 0);
      const covered = goalTerms.reduce((sum, term) => sum + (fields[1]!.has(term) ? idf.get(term)! : 0), 0);
      if (denominator) goalScore += 80 * (covered / denominator) ** 2;
      score += goalScore * (goalOnly || main.length || nameScore ? 1 : dependencies.length ? 0.1 : 0.01);
    }
    const tier = goalOnly ? 1 : nameScore ? 4 : main.length ? 3 : dependencies.length ? 2 : matched.length ? 1 : 0;
    return score > 0 ? { ...document, score, tier, matched } : undefined;
  }).filter((value): value is NonNullable<typeof value> => value !== undefined)
    .sort((left, right) => right.tier - left.tier || right.score - left.score || left.item.id.localeCompare(right.item.id));
  const groups = new Map<string, typeof scored>();
  for (const hit of scored) { const versions = groups.get(hit.group) ?? []; versions.push(hit); groups.set(hit.group, versions); }
  return { schema: 'theorem-os.theorem-knowledge-search.v1', evidence, requiresFreshCheck: true,
    preferenceEvidence: 'recorded-metadata-not-applicability', total: groups.size, totalVersions: scored.length,
    hits: [...groups.values()].slice(0, limit).map(versions => {
      const groupScore = versions[0]!.score;
      versions.sort((left, right) => {
        const a = versionPreference(left.item, options), b = versionPreference(right.item, options);
        for (let index = 0; index < a.length; index++) if (a[index] !== b[index]) return b[index]! - a[index]!;
        return right.tier - left.tier || right.score - left.score || left.item.id.localeCompare(right.item.id);
      });
      const { item, matched } = versions[0]!, selected = knowledgeVersionSummary(item, options);
      return { id: item.id, name: item.name, kind: item.kind, typeKind: item.typeKind,
        typePreview: item.type.slice(0, 800), typeTruncated: item.type.length > 800, description: item.description.slice(0, 500),
        problemIds: selected.problemIds, sourceKinds: selected.sourceKinds, dependencyCoverage: item.dependencies.coverage,
        score: groupScore, matched, environmentMatch: selected.environmentMatch, problemReceiptMatch: selected.problemReceiptMatch,
        versionCount: versions.length, versions: versions.slice(0, 8).map(version => knowledgeVersionSummary(version.item, options)),
        versionsTruncated: versions.length > 8 };
    }) };
}
