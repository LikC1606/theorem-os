import { locateKnowledgeDeclaration, readKnowledgeSource, type TheoremKnowledgeBase } from './theoremKnowledge';

export type KnowledgeSourceOptions = {
  file?: string; name?: string; startLine?: number; lines?: number; startOffset?: number; maxBytes?: number;
};

const invalidOptions = () => { throw new Error('math_knowledge_source_options_invalid'); };
const validInteger = (value: unknown, minimum: number, maximum: number) =>
  typeof value === 'number' && Number.isSafeInteger(value) && value >= minimum && value <= maximum;
const splitsSurrogate = (source: string, offset: number) => offset > 0 && offset < source.length &&
  source.charCodeAt(offset - 1) >= 0xd800 && source.charCodeAt(offset - 1) <= 0xdbff &&
  source.charCodeAt(offset) >= 0xdc00 && source.charCodeAt(offset) <= 0xdfff;

/** Return exact source bytes as a bounded excerpt, without asserting a complete Lean context. */
export function getKnowledgeSource(base: TheoremKnowledgeBase, id: string, options: KnowledgeSourceOptions = {}) {
  if (!options || typeof options !== 'object' || Array.isArray(options)) invalidOptions();
  const { file, name, startLine, startOffset, lines = 80, maxBytes = 16000 } = options;
  if ((file !== undefined && (typeof file !== 'string' || !file)) ||
      (name !== undefined && (typeof name !== 'string' || !name)) ||
      (startLine !== undefined && !validInteger(startLine, 1, Number.MAX_SAFE_INTEGER)) ||
      (startOffset !== undefined && !validInteger(startOffset, 0, Number.MAX_SAFE_INTEGER)) ||
      !validInteger(lines, 1, 200) || !validInteger(maxBytes, 1024, 65536) ||
      (name !== undefined && (startLine !== undefined || startOffset !== undefined)) ||
      (startLine !== undefined && startOffset !== undefined)) invalidOptions();

  const { entry, file: selectedFile, sha256, source } = readKnowledgeSource(base, id, file);
  const lineStarts = [0];
  for (let offset = source.indexOf('\n'); offset >= 0; offset = source.indexOf('\n', offset + 1))
    lineStarts.push(offset + 1);
  const lineAt = (offset: number) => {
    let lower = 0, upper = lineStarts.length;
    while (lower < upper) {
      const middle = Math.floor((lower + upper) / 2);
      if (lineStarts[middle]! <= offset) lower = middle + 1;
      else upper = middle;
    }
    return lower;
  };
  const declaration = name === undefined ? undefined : locateKnowledgeDeclaration(source, name);
  const mode = declaration ? 'name' : startOffset === undefined ? 'lines' : 'offset';
  if ((startLine !== undefined && startLine > lineStarts.length) ||
      (startOffset !== undefined && (startOffset > source.length || splitsSurrogate(source, startOffset))))
    throw new Error('math_knowledge_source_position_invalid');
  const begin = declaration?.startOffset ?? startOffset ?? lineStarts[(startLine ?? 1) - 1]!;
  const selectionEnd = declaration?.endOffset ?? source.length;
  const firstLine = lineAt(begin);
  const requestedEnd = Math.min(selectionEnd, lineStarts[firstLine - 1 + lines] ?? source.length);
  const sourceBytes = Buffer.byteLength(source);
  const packet = (end: number) => {
    const text = source.slice(begin, end), truncated = end < selectionEnd;
    return { id: entry.id, contextDigest: entry.contextDigest, file: selectedFile, sha256,
      evidence: base.evidence, requiresFreshCheck: true as const,
      contextCoverage: 'source-excerpt-not-complete-context' as const,
      sourceBytes, sourceLines: lineStarts.length, offsetEncoding: 'utf16-code-unit' as const,
      endOffsetExclusive: true as const, mode,
      display: { startOffset: begin, endOffset: end, startLine: firstLine,
        endLine: lineAt(end > begin ? end - 1 : begin), bytes: Buffer.byteLength(text) },
      text, truncated,
      ...(truncated ? { nextOffset: end, nextStartLine: lineAt(end) } : {}),
      ...(declaration ? { declaration: { name: declaration.name, qualifiedName: declaration.qualifiedName,
        namespace: declaration.namespace, kind: declaration.kind,
        startOffset: declaration.startOffset, bodyOffset: declaration.bodyOffset, endOffset: declaration.endOffset,
        startLine: lineAt(declaration.startOffset), endLine: lineAt(declaration.endOffset - 1),
        complete: end === declaration.endOffset } } : {}),
    };
  };
  // Include JSON escaping, metadata, and the CLI's trailing newline in the byte budget.
  const fits = (value: ReturnType<typeof packet>) => Buffer.byteLength(JSON.stringify(value)) + 1 <= maxBytes;
  if (requestedEnd - begin <= maxBytes) {
    const whole = packet(requestedEnd);
    if (fits(whole)) return whole;
  }
  if (!fits(packet(begin))) throw new Error('math_knowledge_source_budget_too_small');
  let lower = begin + 1, upper = Math.min(requestedEnd - 1, begin + maxBytes), best = begin;
  while (lower <= upper) {
    const middle = Math.floor((lower + upper) / 2);
    const end = splitsSurrogate(source, middle) ? middle - 1 : middle;
    if (fits(packet(end))) { best = end; lower = middle + 1; }
    else upper = middle - 1;
  }
  if (best === begin && requestedEnd > begin) throw new Error('math_knowledge_source_budget_too_small');
  return packet(best);
}
