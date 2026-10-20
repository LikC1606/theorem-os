import { canonicalMathJson, mathDigest } from '../math/mathRuntimeIo';
import { readKnowledgeSource, type TheoremKnowledgeBase } from './theoremKnowledge';
import { knowledgeSearchGroup, knowledgeVersionSummary } from './theoremKnowledgeSearch';
import { largestFittingPage, splitsSurrogate } from './textPage';

const fieldNames = ['name', 'file', 'type', 'premises', 'environmentDigest', 'description', 'dependencies',
  'provenance', 'relatedVersions', 'files', 'elaboration'] as const;
export type KnowledgeMetadataField = typeof fieldNames[number];
export type KnowledgeMetadataOptions = { field?: KnowledgeMetadataField; startOffset?: number; maxBytes?: number };
type FieldDescriptor = {
  format: 'text' | 'json'; sha256: string; bytes: number; count?: number; complete: boolean;
  value?: unknown; read?: { field: KnowledgeMetadataField; startOffset: number };
};
const invalidOptions = (): never => { throw new Error('math_knowledge_metadata_options_invalid'); };
const validInteger = (value: unknown, minimum: number, maximum: number) =>
  typeof value === 'number' && Number.isSafeInteger(value) && value >= minimum && value <= maximum;

/** Keep archived proof bodies out of metadata; every deferred field has an exact continuation. */
export function getKnowledgeMetadata(base: TheoremKnowledgeBase, id: string, options: KnowledgeMetadataOptions = {}) {
  if (!options || typeof options !== 'object' || Array.isArray(options)) invalidOptions();
  const { field: selected, startOffset, maxBytes = 16000 } = options;
  if ((selected !== undefined && !fieldNames.includes(selected)) ||
      (startOffset !== undefined && !validInteger(startOffset, 0, Number.MAX_SAFE_INTEGER)) ||
      (selected === undefined && startOffset !== undefined) || !validInteger(maxBytes, 1024, 65536)) invalidOptions();

  const { entry, files } = readKnowledgeSource(base, id);
  const prepare = (name: KnowledgeMetadataField) => {
    let value: unknown;
    if (name === 'relatedVersions') {
      const group = knowledgeSearchGroup(entry);
      value = base.entries.filter(other => knowledgeSearchGroup(other) === group)
        .map(other => knowledgeVersionSummary(other)).sort((left, right) => left.id.localeCompare(right.id));
    } else if (name === 'files') value = Object.keys(files).sort().map(file => ({ file, sha256: files[file]! }));
    else value = name === 'environmentDigest' ? entry.environmentDigest ?? null :
      name === 'elaboration' ? entry.elaboration ?? null : entry[name];
    const format = typeof value === 'string' ? 'text' as const : 'json' as const;
    const text = format === 'text' ? value as string : canonicalMathJson(value);
    return { value, format, text, sha256: mathDigest(text), bytes: Buffer.byteLength(text),
      ...(Array.isArray(value) ? { count: value.length } : {}) };
  };
  const identity = { schema: 'theorem-os.theorem-knowledge-metadata.v1' as const, id: entry.id,
    contextDigest: entry.contextDigest, sourceSha256: files[entry.file]!, typeKind: entry.typeKind, kind: entry.kind,
    evidence: base.evidence, requiresFreshCheck: true as const,
    contextCoverage: 'metadata-only-not-complete-lean-context' as const };
  const fits = (packet: unknown) => Buffer.byteLength(JSON.stringify(packet)) + 1 <= maxBytes;

  if (selected !== undefined) {
    const current = prepare(selected), begin = startOffset ?? 0;
    if (begin > current.text.length || splitsSurrogate(current.text, begin))
      throw new Error('math_knowledge_metadata_position_invalid');
    const packet = (end: number) => ({ ...identity, mode: 'field' as const, field: selected, format: current.format,
      sha256: current.sha256, bytes: current.bytes, offsetEncoding: 'utf16-code-unit' as const,
      endOffsetExclusive: true as const,
      display: { startOffset: begin, endOffset: end, bytes: Buffer.byteLength(current.text.slice(begin, end)) },
      text: current.text.slice(begin, end), truncated: end < current.text.length,
      ...(end < current.text.length ? { nextOffset: end } : {}) });
    return largestFittingPage(current.text, begin, current.text.length, maxBytes, packet, 'math_knowledge_metadata_budget_too_small');
  }

  const prepared = fieldNames.map(name => ({ name, ...prepare(name) }));
  const fields = Object.fromEntries(prepared.map(({ name, format, sha256, bytes, count }) => {
    return [name, { format, sha256, bytes, ...(count === undefined ? {} : { count }), complete: false,
      read: { field: name, startOffset: 0 } } satisfies FieldDescriptor];
  })) as Record<KnowledgeMetadataField, FieldDescriptor>;
  const packet = { ...identity, mode: 'summary' as const, allFieldsComplete: false, fields,
    proofSource: { readWith: 'knowledge source', fileField: 'file', nameField: 'name' } };
  if (!fits(packet)) throw new Error('math_knowledge_metadata_budget_too_small');
  for (const { name, value } of prepared) {
    const deferred = fields[name], { read: _read, ...details } = deferred;
    fields[name] = { ...details, complete: true, value };
    if (!fits(packet)) fields[name] = deferred;
  }
  packet.allFieldsComplete = fieldNames.every(name => fields[name].complete);
  return packet;
}
