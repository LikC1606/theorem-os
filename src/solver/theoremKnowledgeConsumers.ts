import { canonicalMathJson, mathDigest } from '../math/mathRuntimeIo';
import type { TheoremKnowledgeBase, TheoremKnowledgeEntry } from './theoremKnowledge';

export type KnowledgeConsumersOptions = { offset?: number; limit?: number; maxBytes?: number };
type MetadataField = 'name' | 'file' | 'type' | 'premises' | 'elaboration' | 'files';
type Field = {
  format: 'text' | 'json'; bytes: number; sha256: string; complete: boolean;
  value?: unknown; preview?: string; count?: number; read: { field: MetadataField; startOffset: number };
};
const validInteger = (value: unknown, minimum: number, maximum: number) =>
  typeof value === 'number' && Number.isSafeInteger(value) && value >= minimum && value <= maximum;
const preview = (text: string) => {
  let end = Math.min(160, text.length);
  if (end && end < text.length && text.charCodeAt(end - 1) >= 0xd800 && text.charCodeAt(end - 1) <= 0xdbff &&
      text.charCodeAt(end) >= 0xdc00 && text.charCodeAt(end) <= 0xdfff) end--;
  return text.slice(0, end);
};
const field = (name: MetadataField, value: unknown): Field => {
  const format = typeof value === 'string' ? 'text' : 'json';
  const text = format === 'text' ? value as string : canonicalMathJson(value);
  return { format, bytes: Buffer.byteLength(text), sha256: mathDigest(text), complete: false,
    ...(Array.isArray(value) ? { count: value.length } : {}), read: { field: name, startOffset: 0 } };
};

/** Invert observed references within one exact archived context; never infer an application. */
export function getKnowledgeConsumers(base: TheoremKnowledgeBase, id: string, options: KnowledgeConsumersOptions = {}) {
  if (!options || typeof options !== 'object' || Array.isArray(options))
    throw new Error('math_knowledge_consumers_options_invalid');
  const { offset = 0, limit = 8, maxBytes = 16000 } = options;
  if (!validInteger(offset, 0, Number.MAX_SAFE_INTEGER) || !validInteger(limit, 1, 32) || !validInteger(maxBytes, 1024, 65536))
    throw new Error('math_knowledge_consumers_options_invalid');
  const root = base.entries.find(item => item.id === id);
  if (!root) throw new Error('math_knowledge_theorem_not_found');
  const knownEnvironment = typeof root.environmentDigest === 'string' && Boolean(root.environmentDigest.trim());
  const contextEntries = base.entries.filter(item => item.contextDigest === root.contextDigest);
  const unknownEnvironments = contextEntries.filter(item => !item.environmentDigest?.trim()).length;
  const scope = knownEnvironment ? contextEntries.filter(item =>
    item.environmentDigest === root.environmentDigest) : [];
  const uses = (entry: TheoremKnowledgeEntry) => (['statement', 'proof'] as const).filter(kind =>
    entry.dependencies[kind].some(reference => reference.file === root.file && reference.name === root.name))
    .map(kind => kind === 'statement' ? 'statement-use' as const : 'proof-use' as const);
  const matches = scope.map(entry => ({ entry, uses: uses(entry) })).filter(item => item.uses.length)
    .sort((left, right) => left.entry.name.localeCompare(right.entry.name) || left.entry.file.localeCompare(right.entry.file) ||
      left.entry.id.localeCompare(right.entry.id));
  if (offset > matches.length) throw new Error('math_knowledge_consumers_position_invalid');
  const recorded = scope.filter(item => item.dependencies.coverage === 'recorded').length;
  const makeRow = ({ entry, uses }: typeof matches[number]) => {
    const files = base.contexts[entry.contextDigest]!;
    const elaboration = entry.elaboration;
    const fields = { name: field('name', entry.name), file: field('file', entry.file), type: field('type', entry.type),
      premises: field('premises', entry.premises), elaboration: field('elaboration', elaboration ?? null) };
    return { id: entry.id, uses, referenceCoverage: entry.dependencies.coverage === 'recorded' ? 'recorded' as const : 'unknown' as const,
      typeKind: entry.typeKind, fields,
      elaborationCoverage: elaboration === undefined ? 'unknown' as const : 'recorded' as const,
      context: { digest: entry.contextDigest, read: { field: 'files' as const, startOffset: 0 } },
      read: { metadata: { command: 'knowledge get' as const, id: entry.id, metadata: true as const },
        source: { command: 'knowledge source' as const, id: entry.id,
          ...(Buffer.byteLength(entry.file) + Buffer.byteLength(entry.name) <= 512 ? { file: entry.file, name: entry.name } : {}) } },
      sourceSha256: files[entry.file]! };
  };
  type Consumer = ReturnType<typeof makeRow>;
  const consumers: Consumer[] = [];
  const packet = () => ({ schema: 'theorem-os.theorem-knowledge-consumers.v1' as const, rootId: root.id,
    contextDigest: root.contextDigest, evidence: base.evidence, requiresFreshCheck: true as const,
    environmentMatch: knownEnvironment ? 'exact' as const : 'unknown' as const,
    coverage: { status: !knownEnvironment || recorded < scope.length || unknownEnvironments ? 'unknown' as const : 'recorded' as const,
      scopedEntries: scope.length, recordedEntries: recorded, unavailableEntries: scope.length - recorded,
      unknownEnvironmentEntries: unknownEnvironments },
    referenceSemantics: 'local-transitive-closure' as const, applicationArguments: 'not-recorded' as const,
    use: 'historical-advisory' as const, absence: 'not-evidence-of-no-consumers' as const,
    total: matches.length, offset, consumers, truncated: offset + consumers.length < matches.length,
    ...(offset + consumers.length < matches.length ? { nextOffset: offset + consumers.length } : {}) });
  const fits = () => Buffer.byteLength(JSON.stringify(packet())) + 1 <= maxBytes;
  if (!fits()) throw new Error('math_knowledge_consumers_budget_too_small');
  for (const match of matches.slice(offset, offset + limit)) {
    const row = makeRow(match);
    consumers.push(row);
    if (!fits()) {
      consumers.pop();
      if (!consumers.length) throw new Error('math_knowledge_consumers_budget_too_small');
      break;
    }
    const elaboration = match.entry.elaboration;
    const values = { name: match.entry.name, file: match.entry.file, type: match.entry.type,
      premises: match.entry.premises, elaboration: elaboration ?? null };
    for (const name of Object.keys(row.fields) as (keyof typeof row.fields)[]) {
      const current = row.fields[name]!, value = values[name];
      if (current.bytes <= (name === 'type' ? 1024 : 512)) {
        current.value = value; current.complete = true;
        if (fits()) continue;
        delete current.value; current.complete = false;
      }
      const text = typeof value === 'string' ? value : canonicalMathJson(value);
      current.preview = preview(text);
      if (!fits()) delete current.preview;
    }
  }
  return packet();
}
