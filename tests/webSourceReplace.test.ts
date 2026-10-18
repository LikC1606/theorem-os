import { describe, expect, it } from 'vitest';
import { sourceReplaceEdit } from '../apps/web/client/sourceReplace';

function replace(source: string, query: string, replacement: string, options?: Parameters<typeof sourceReplaceEdit>[3]) {
  const edit = sourceReplaceEdit(source, query, replacement, options);
  expect(edit).toBeTruthy();
  expect(edit).not.toBe('too-large');
  if (!edit || edit === 'too-large') throw new Error('Expected an editable replacement');
  return { source: source.slice(0, edit.from) + edit.text + source.slice(edit.to), count: edit.count };
}

describe('literal source replacement', () => {
  it('keeps regex punctuation, replacement tokens, backslashes and markup literal', () => {
    const query = '[a+b].*? \\x', replacement = '$& $1 $$ $` $\' \\n <img src=x>';
    const source = `-- before ${query}\n-- ${query} after`;
    expect(replace(source, query, replacement)).toEqual({ source: `-- before ${replacement}\n-- ${replacement} after`, count: 2 });
  });

  it('replaces only the exact selected occurrence and preserves neighboring text and Unicode', () => {
    const source = '🙂 needle\nα needle\nneedle', start = source.indexOf('needle', 4);
    expect(replace(source, 'needle', 'β🙂', { selection: { start, end: start + 6 } })).toEqual({
      source: '🙂 needle\nα β🙂\nneedle', count: 1,
    });
  });

  it('does not accept a substring or overlap that is not an actual search match', () => {
    expect(sourceReplaceEdit('aaaa', 'aa', 'b', { selection: { start: 1, end: 3 } })).toBeUndefined();
    expect(sourceReplaceEdit('needle', 'needle', 'x', { selection: { start: 0, end: 3 } })).toBeUndefined();
    expect(sourceReplaceEdit('x needle', 'needle', 'x', { selection: { start: 0, end: 6 } })).toBeUndefined();
  });

  it('uses non-overlapping matches from the original source and never recursively replaces inserted text', () => {
    expect(replace('aaaaa', 'aa', 'aaa')).toEqual({ source: 'aaaaaaa', count: 2 });
    expect(replace('x x', 'x', 'xx')).toEqual({ source: 'xx xx', count: 2 });
  });

  it('replaces the full file beyond the displayed 1000 matches', () => {
    const source = `prefix\n${'needle '.repeat(1203)}\nlast needle`;
    const result = replace(source, 'needle', 'α');
    expect(result).toEqual({ source: `prefix\n${'α '.repeat(1203)}\nlast α`, count: 1204 });
    expect(result.source.includes('needle')).toBe(false);
  });

  it('deletes matches with an empty replacement, including a source consisting entirely of matches', () => {
    expect(replace('-- a\n-- a\n', 'a', '')).toEqual({ source: '-- \n-- \n', count: 2 });
    expect(replace('aaaa', 'aa', '')).toEqual({ source: '', count: 2 });
    expect(replace('x\nx\n', 'x\n', '')).toEqual({ source: '', count: 2 });
  });

  it('shares Unicode case folding with literal search and counts only text that changes', () => {
    expect(replace('k K K', 'k', 'K')).toEqual({ source: 'K K K', count: 2 });
    expect(replace('k K K', 'k', 'K', { caseSensitive: true })).toEqual({ source: 'K K K', count: 1 });
    expect(replace('β Β β', 'β', 'β')).toEqual({ source: 'β β β', count: 1 });
  });

  it('does not plan edits for unchanged text, absent matches, or invalid queries', () => {
    expect(sourceReplaceEdit('same same', 'same', 'same')).toBeUndefined();
    expect(sourceReplaceEdit('same', 'absent', 'x')).toBeUndefined();
    for (const query of ['', 'a'.repeat(257)]) expect(sourceReplaceEdit('a'.repeat(300), query, 'x')).toBeUndefined();
  });

  it('measures the entire resulting source in UTF-8 before building a large replacement', () => {
    const source = '-- α α';
    expect(sourceReplaceEdit(source, 'α', '🙂', { maxBytes: 10 })).toBe('too-large');
    expect(replace(source, 'α', '🙂', { maxBytes: 12 })).toEqual({ source: '-- 🙂 🙂', count: 2 });
    expect(sourceReplaceEdit('x'.repeat(5000), 'x', 'long'.repeat(5000), { maxBytes: 32768 })).toBe('too-large');
  });

  it('allows shrinking an oversized draft but blocks further growth', () => {
    const source = 'prefix α α';
    expect(replace(source, 'α', 'a', { maxBytes: 4 })).toEqual({ source: 'prefix a a', count: 2 });
    expect(sourceReplaceEdit(source, 'α', '🙂', { maxBytes: 4 })).toBe('too-large');
    expect(replace(source, 'α', 'β', { maxBytes: 4 })).toEqual({ source: 'prefix β β', count: 2 });
  });

  it.each([[-1, 2], [0, 0], [2, 1], [0, 4], [0.5, 2], [0, 1.5], [NaN, 1], [0, Infinity]])(
    'rejects invalid selection offsets %s..%s', (start, end) => {
      expect(sourceReplaceEdit('aaa', 'a', 'b', { selection: { start, end } })).toBeUndefined();
    },
  );
});
