import { afterEach, describe, expect, it, vi } from 'vitest';
import * as diff from 'diff';
import { compareSources, type SourceComparison, type SourceDiffRow } from '../apps/web/client/sourceDiff';

vi.mock('diff', async importOriginal => {
  const original = await importOriginal<typeof import('diff')>();
  return { ...original, diffLines: vi.fn(original.diffLines) };
});

type LineRow = Exclude<SourceDiffRow, { kind: 'gap' }>;
const lineRows = (comparison: SourceComparison): LineRow[] => comparison.rows.filter((row): row is LineRow => row.kind !== 'gap');
const normalized = (source: string) => source.replace(/\r\n?/g, '\n');
const reconstruct = (comparison: SourceComparison, side: 'old' | 'new') => lineRows(comparison)
  .filter(row => row.kind !== (side === 'old' ? 'added' : 'removed'))
  .map(row => row.text + (row.noNewline ? '' : '\n')).join('');
const numberedSource = (count: number) => Array.from({ length: count }, (_, index) => `line ${index + 1}\n`).join('');

afterEach(() => vi.resetAllMocks());

describe('line-based source comparison', () => {
  it('keeps accurate line numbers and groups adjacent removals and additions into one change', () => {
    const comparison = compareSources('first\nold one\nold two\nlast\n', 'first\nnew\nlast\n', false);
    expect(comparison).toMatchObject({ status: 'ready', added: 1, removed: 2, changeCount: 1, omittedLines: 0, lineEndingsChanged: false });
    expect(comparison.rows).toEqual([
      { kind: 'context', text: 'first', oldLine: 1, newLine: 1, noNewline: false },
      { kind: 'removed', text: 'old one', oldLine: 2, noNewline: false, changeId: 0 },
      { kind: 'removed', text: 'old two', oldLine: 3, noNewline: false, changeId: 0 },
      { kind: 'added', text: 'new', newLine: 2, noNewline: false, changeId: 0 },
      { kind: 'context', text: 'last', oldLine: 4, newLine: 3, noNewline: false },
    ]);
  });

  it('assigns consecutive IDs only when unchanged lines separate changes', () => {
    const comparison = compareSources('one\nkeep\ntwo\n', 'new one\nkeep\nnew two\n', false);
    expect(comparison.changeCount).toBe(2);
    expect(lineRows(comparison).map(row => row.changeId)).toEqual([0, 0, undefined, 1, 1]);
  });

  it.each([
    ['', ''], ['', 'first'], ['first', ''], ['\n', ''], ['', '\n\n'],
    ['repeat\nrepeat\nend\n', 'repeat\nnew\nrepeat\nend\n'],
    ['a\nb\na\nb\nc', 'a\nb\nc\na\nb\n'],
    ['\t  α <script>alert("x")</script>  \n尾行', '\t α <img src=x onerror=alert(1)> \n尾行'],
    ['a\r\nb\rc', 'a\nb\nnew\r\n'],
  ])('reconstructs both complete normalized sources without losing text: %j -> %j', (before, after) => {
    const comparison = compareSources(before, after, false);
    expect(comparison.status).not.toBe('unavailable');
    expect(reconstruct(comparison, 'old')).toBe(normalized(before));
    expect(reconstruct(comparison, 'new')).toBe(normalized(after));
    for (const side of ['old', 'new'] as const) {
      const numbers = lineRows(comparison).flatMap(row => row[`${side}Line`] === undefined ? [] : [row[`${side}Line`]]);
      expect(numbers).toEqual(Array.from({ length: numbers.length }, (_, index) => index + 1));
    }
  });

  it('treats empty text as zero lines', () => {
    expect(compareSources('', '', false)).toEqual({
      status: 'identical', added: 0, removed: 0, rows: [], changeCount: 0, omittedLines: 0, lineEndingsChanged: false,
    });
    expect(compareSources('', 'a', false).rows).toEqual([{ kind: 'added', text: 'a', newLine: 1, noNewline: true, changeId: 0 }]);
    expect(compareSources('a\n', '', false).rows).toEqual([{ kind: 'removed', text: 'a', oldLine: 1, noNewline: false, changeId: 0 }]);
  });

  it('represents blank lines without a phantom line after a terminal newline', () => {
    expect(compareSources('', '\n\n', false).rows).toEqual([
      { kind: 'added', text: '', newLine: 1, noNewline: false, changeId: 0 },
      { kind: 'added', text: '', newLine: 2, noNewline: false, changeId: 0 },
    ]);
    expect(compareSources('a\n\n', 'a\n', false)).toMatchObject({ added: 0, removed: 1, rows: [
      { kind: 'context', text: 'a', oldLine: 1, newLine: 1, noNewline: false },
      { kind: 'removed', text: '', oldLine: 2, noNewline: false, changeId: 0 },
    ] });
  });

  it.each([['a', 'a\n', true, false], ['a\n', 'a', false, true]] as const)(
    'preserves a meaningful terminal newline change: %j -> %j', (before, after, removedFlag, addedFlag) => {
      const comparison = compareSources(before, after, false);
      expect(comparison).toMatchObject({ status: 'ready', added: 1, removed: 1, changeCount: 1, lineEndingsChanged: false });
      expect(comparison.rows).toEqual([
        { kind: 'removed', text: 'a', oldLine: 1, noNewline: removedFlag, changeId: 0 },
        { kind: 'added', text: 'a', newLine: 1, noNewline: addedFlag, changeId: 0 },
      ]);
    },
  );

  it('keeps literal spaces, tabs, Unicode and HTML without trimming or escaping them', () => {
    const before = '\t  α <script>alert("x")</script>  ', after = '\t α <img src=x onerror=alert(1)> ';
    const comparison = compareSources(before, after, false);
    expect(lineRows(comparison).map(row => row.text)).toEqual([before, after]);
    expect(comparison).toMatchObject({ added: 1, removed: 1 });
  });
});

describe('line ending normalization', () => {
  it.each([
    ['a\r\nb\r\n', 'a\nb\n'], ['a\rb\r', 'a\nb\n'], ['a\r\nb\rc', 'a\nb\nc'],
    ['\r\n', '\r'],
  ])('reports equivalent content with changed raw line endings: %j -> %j', (before, after) => {
    expect(compareSources(before, after, false)).toMatchObject({
      status: 'identical', added: 0, removed: 0, changeCount: 0, lineEndingsChanged: true,
    });
  });

  it('does not flag equal CRLF input as changed or hide real content differences', () => {
    expect(compareSources('a\r\n', 'a\r\n').lineEndingsChanged).toBe(false);
    expect(compareSources('a\r\n', 'b\n')).toMatchObject({ status: 'ready', added: 1, removed: 1, lineEndingsChanged: false });
  });
});

describe('context folding and bounded rendering', () => {
  it('retains three context lines around a change and folds only the other context', () => {
    const before = numberedSource(20), after = before.replace('line 10\n', 'replacement\n');
    const comparison = compareSources(before, after);
    expect(comparison).toMatchObject({ added: 1, removed: 1, changeCount: 1, omittedLines: 0 });
    expect(comparison.rows).toEqual([
      { kind: 'gap', count: 6 },
      ...[7, 8, 9].map(line => ({ kind: 'context', text: `line ${line}`, oldLine: line, newLine: line, noNewline: false })),
      { kind: 'removed', text: 'line 10', oldLine: 10, noNewline: false, changeId: 0 },
      { kind: 'added', text: 'replacement', newLine: 10, noNewline: false, changeId: 0 },
      ...[11, 12, 13].map(line => ({ kind: 'context', text: `line ${line}`, oldLine: line, newLine: line, noNewline: false })),
      { kind: 'gap', count: 7 },
    ]);
  });

  it.each([5, 6, 7])('merges adjacent context windows without repeating their %i shared lines', sharedCount => {
    const middle = numberedSource(sharedCount);
    const comparison = compareSources(`first\n${middle}last\n`, `new first\n${middle}new last\n`);
    expect(comparison.changeCount).toBe(2);
    expect(lineRows(comparison).filter(row => row.kind === 'context')).toHaveLength(Math.min(6, sharedCount));
    expect(comparison.rows.filter(row => row.kind === 'gap')).toEqual(sharedCount > 6 ? [{ kind: 'gap', count: sharedCount - 6 }] : []);
    const numbers = lineRows(comparison).filter(row => row.kind === 'context').map(row => row.oldLine);
    expect(new Set(numbers).size).toBe(numbers.length);
  });

  it('can show all unchanged lines and keeps a no-newline marker at EOF', () => {
    const source = 'one\ntwo\nthree';
    expect(compareSources(source, source).rows).toEqual([{ kind: 'gap', count: 3 }]);
    const full = compareSources(source, source, false);
    expect(full.status).toBe('identical');
    expect(full.rows).toHaveLength(3);
    expect(full.rows[2]).toEqual({ kind: 'context', text: 'three', oldLine: 3, newLine: 3, noNewline: true });
  });

  it('caps full rendering at 2,000 rows while preserving complete change totals', () => {
    const before = numberedSource(2_500), after = before.replace('line 1200\n', 'replacement\n');
    const comparison = compareSources(before, after, false);
    expect(comparison).toMatchObject({ status: 'ready', added: 1, removed: 1, changeCount: 1, omittedLines: 501 });
    expect(comparison.rows).toHaveLength(2_000);
    expect(lineRows(comparison).at(-1)).toMatchObject({ oldLine: 1_999, newLine: 1_999 });
  });

  it('counts changes beyond the render cap without treating folded context as omitted rows', () => {
    const before = numberedSource(2_100), after = `${before}new final\n`;
    const full = compareSources(before, after, false), folded = compareSources(before, after);
    expect(full).toMatchObject({ added: 1, removed: 0, changeCount: 1, omittedLines: 101 });
    expect(full.rows).toHaveLength(2_000);
    expect(folded).toMatchObject({ added: 1, removed: 0, changeCount: 1, omittedLines: 0 });
    expect(folded.rows).toHaveLength(5);
    expect(folded.rows[0]).toEqual({ kind: 'gap', count: 2_097 });
    expect(folded.rows.at(-1)).toEqual({ kind: 'added', text: 'new final', newLine: 2_101, noNewline: false, changeId: 0 });
  });

  it('counts gap rows toward the cap while excluding their folded line count from omissions', () => {
    const before = `${numberedSource(10)}old\n`, after = `${numberedSource(10)}${'new\n'.repeat(1_998)}`;
    const comparison = compareSources(before, after);
    expect(comparison).toMatchObject({ status: 'ready', added: 1_998, removed: 1, changeCount: 1, omittedLines: 3 });
    expect(comparison.rows).toHaveLength(2_000);
    expect(comparison.rows[0]).toEqual({ kind: 'gap', count: 7 });
  });
});

describe('source comparison resource limits', () => {
  it('allows the product source and candidate size ceilings together', () => {
    expect(compareSources('a'.repeat(32 * 1024), 'b'.repeat(128 * 1024))).toMatchObject({
      status: 'ready', added: 1, removed: 1, changeCount: 1, omittedLines: 0,
    });
  });

  it('accepts exactly 256 KiB and rejects larger combined UTF-8 input', () => {
    expect(compareSources('', 'a'.repeat(256 * 1024)).status).toBe('ready');
    expect(compareSources('a', 'b'.repeat(256 * 1024)).status).toBe('unavailable');
    const unicode = '题'.repeat(Math.floor(256 * 1024 / 3));
    expect(compareSources('a', unicode).status).toBe('ready');
    expect(compareSources('aa', unicode).status).toBe('unavailable');
  });

  it('passes finite time and edit budgets to the established diff algorithm', () => {
    const spy = vi.mocked(diff.diffLines);
    compareSources('before', 'after');
    expect(spy).toHaveBeenCalledWith('before', 'after', { timeout: 80, maxEditLength: 2_000 });
  });

  it('returns no fabricated rows or totals when the algorithm exhausts its budget', () => {
    vi.mocked(diff.diffLines).mockReturnValueOnce(undefined);
    expect(compareSources('before', 'after')).toEqual({
      status: 'unavailable', added: 0, removed: 0, rows: [], changeCount: 0, omittedLines: 0, lineEndingsChanged: false,
    });
  });

  it('handles unexpected diff failures without exposing a partial comparison', () => {
    vi.mocked(diff.diffLines).mockImplementationOnce(() => { throw new Error('fixture algorithm failure'); });
    expect(compareSources('before', 'after')).toMatchObject({ status: 'unavailable', rows: [], added: 0, removed: 0 });
  });

  it('gives up on unrelated inputs whose edit distance exceeds the limit', () => {
    const before = Array.from({ length: 1_001 }, (_, index) => `old ${index}\n`).join('');
    const after = Array.from({ length: 1_001 }, (_, index) => `new ${index}\n`).join('');
    expect(compareSources(before, after)).toMatchObject({ status: 'unavailable', rows: [] });
  });
});
