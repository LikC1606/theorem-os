import { describe, expect, it } from 'vitest';
import { findSourceMatches, leanTokens } from '../apps/web/client/sourceText';

describe('literal source search', () => {
  it('treats regular expression punctuation, markup and spaces as literal text', () => {
    const query = '<tag> a+b[0].*? \\x';
    const source = `prefix\n${query}\nnot a wildcard\n${query}`;
    const result = findSourceMatches(source, query);
    expect(result.matches.map(match => source.slice(match.start, match.end))).toEqual([query, query]);
    expect(result.matches.map(({ line, column }) => ({ line, column }))).toEqual([
      { line: 2, column: 1 }, { line: 4, column: 1 },
    ]);
    expect(result.truncated).toBe(false);
  });

  it('keeps Unicode offsets valid while reporting readable line and column positions', () => {
    const source = '😀α Needle\nβ needle';
    expect(findSourceMatches(source, 'NEEDLE').matches).toEqual([
      { start: 4, end: 10, line: 1, column: 4 },
      { start: 13, end: 19, line: 2, column: 3 },
    ]);
    expect(findSourceMatches(source, 'Needle', true).matches).toHaveLength(1);
    expect(findSourceMatches(source, 'NEEDLE', true).matches).toHaveLength(0);
  });

  it('supports matches across lexical boundaries and line breaks without changing the source', () => {
    const source = 'theorem α : True := by\n  exact True.intro';
    const query = 'True := by\n  exact';
    const result = findSourceMatches(source, query);
    expect(result.matches).toEqual([{ start: 12, end: 30, line: 1, column: 13 }]);
    expect(source.slice(result.matches[0]!.start, result.matches[0]!.end)).toBe(query);
    expect(findSourceMatches('aaaa', 'aa').matches.map(match => [match.start, match.end])).toEqual([[0, 2], [2, 4]]);
  });

  it('distinguishes an exact result limit from omitted matches', () => {
    expect(findSourceMatches('x x', 'x', false, 2)).toMatchObject({ matches: [{ start: 0 }, { start: 2 }], truncated: false });
    expect(findSourceMatches('x x x', 'x', false, 2)).toMatchObject({ matches: [{ start: 0 }, { start: 2 }], truncated: true });
    expect(findSourceMatches('x '.repeat(1001), 'x')).toMatchObject({ truncated: true });
    expect(findSourceMatches('x '.repeat(1001), 'x').matches).toHaveLength(1000);
  });

  it('rejects empty or overlong queries without producing empty ranges', () => {
    for (const query of ['', 'a'.repeat(257)]) expect(findSourceMatches('a'.repeat(300), query)).toEqual({ matches: [], truncated: false });
    expect(findSourceMatches('a'.repeat(256), 'a'.repeat(256)).matches).toHaveLength(1);
    expect(findSourceMatches('', 'a')).toEqual({ matches: [], truncated: false });
  });
});

describe('Lean reading tokens', () => {
  const text = (source: string) => leanTokens(source).map(token => ({ text: source.slice(token.start, token.end), kind: token.kind }));

  it('keeps nested and unfinished comments intact instead of coloring their apparent code', () => {
    const nested = '/- theorem outer\n /- exact sorry -/\n trailing 42 -/';
    expect(text(`${nested}\n-- def x := sorry\ntheorem actual : True := by trivial`)).toEqual([
      { text: nested, kind: 'comment' }, { text: '-- def x := sorry', kind: 'comment' },
      { text: 'theorem', kind: 'keyword' }, { text: 'by', kind: 'keyword' }, { text: 'trivial', kind: 'tactic' },
    ]);
    expect(text('/- open /- nested -/ theorem sorry')).toEqual([{ text: '/- open /- nested -/ theorem sorry', kind: 'comment' }]);
  });

  it('does not parse keywords inside escaped strings, characters, quoted names or identifiers', () => {
    const source = 'def «theorem sorry» := "exact \\" sorry"\ndef x\' := \'α\'\n-- retained comment\nfoo.sorry exact\' sorry';
    expect(text(source)).toEqual([
      { text: 'def', kind: 'keyword' }, { text: '"exact \\" sorry"', kind: 'string' },
      { text: 'def', kind: 'keyword' }, { text: "'α'", kind: 'string' },
      { text: '-- retained comment', kind: 'comment' }, { text: 'sorry', kind: 'placeholder' },
    ]);
  });

  it('recognizes ordinary proof syntax and keeps token ranges ordered and non-overlapping', () => {
    const source = 'theorem α₂ (x\' : Nat) : 42 = 0x2a := by\n  norm_num\nexample : True := by admit';
    const tokens = leanTokens(source);
    expect(tokens.map(token => source.slice(token.start, token.end))).toEqual([
      'theorem', '42', '0x2a', 'by', 'norm_num', 'example', 'by', 'admit',
    ]);
    for (const [index, token] of tokens.entries()) {
      expect(token.start).toBeGreaterThanOrEqual(index ? tokens[index - 1]!.end : 0);
      expect(token.end).toBeGreaterThan(token.start);
      expect(token.end).toBeLessThanOrEqual(source.length);
    }
  });

  it('bounds token output for large inputs and still handles unclosed strings as inert text', () => {
    const tokens = leanTokens('theorem '.repeat(9000));
    expect(tokens.length).toBeLessThanOrEqual(8000);
    expect(text('"theorem <img src=x> sorry')).toEqual([{ text: '"theorem <img src=x> sorry', kind: 'string' }]);
    expect(leanTokens('')).toEqual([]);
  });
});
