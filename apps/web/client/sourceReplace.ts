import { sourceSearchPattern, type SourceSelection } from './sourceText';

export type SourceReplacement = { from: number; to: number; text: string; count: number };

// Plan one native edit. Search highlights are capped, but replacement scans the complete source.
export function sourceReplaceEdit(source: string, query: string, replacement: string, options: {
  caseSensitive?: boolean; selection?: SourceSelection; maxBytes?: number;
} = {}): SourceReplacement | 'too-large' | undefined {
  const pattern = sourceSearchPattern(query, options.caseSensitive);
  if (!pattern) return undefined;
  const selection = options.selection;
  if (selection && (!Number.isSafeInteger(selection.start) || !Number.isSafeInteger(selection.end)
    || selection.start < 0 || selection.end <= selection.start || selection.end > source.length)) return undefined;

  const changes: SourceSelection[] = [];
  const encoder = new TextEncoder(), replacementBytes = encoder.encode(replacement).length;
  let byteDelta = 0;
  for (const match of source.matchAll(pattern)) {
    const start = match.index, end = start + match[0].length;
    if (selection && (start !== selection.start || end !== selection.end)) continue;
    if (match[0] === replacement) continue;
    changes.push({ start, end });
    byteDelta += replacementBytes - encoder.encode(match[0]).length;
  }
  if (!changes.length) return undefined;
  // Permit repairing an oversized scratch buffer without letting replacements grow it further.
  const sourceBytes = encoder.encode(source).length;
  if (sourceBytes + byteDelta > Math.max(sourceBytes, options.maxBytes ?? Infinity)) return 'too-large';

  const from = changes[0].start, to = changes.at(-1)!.end;
  const parts: string[] = [];
  let cursor = from;
  for (const change of changes) {
    parts.push(source.slice(cursor, change.start), replacement);
    cursor = change.end;
  }
  return { from, to, text: parts.join(''), count: changes.length };
}
