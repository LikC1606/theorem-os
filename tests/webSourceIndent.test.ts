import { describe, expect, it } from 'vitest';
import { sourceIndentEdit, type IndentDirection } from '../apps/web/client/sourceIndent';

function apply(source: string, start: number, end: number, direction: IndentDirection) {
  const edit = sourceIndentEdit(source, start, end, direction);
  expect(edit).toBeDefined();
  return { source: source.slice(0, edit!.from) + edit!.text + source.slice(edit!.to),
    start: edit!.selectionStart, end: edit!.selectionEnd };
}

describe('source indentation edit plans', () => {
  it('inserts two spaces at the current line start and moves the caret with its text', () => {
    const source = 'theorem t : True := by\nexact True.intro\n-- untouched';
    const from = source.indexOf('exact'), caret = from + 5;
    expect(sourceIndentEdit(source, caret, caret, 'indent')).toEqual({
      from, to: from, text: '  ', selectionStart: caret + 2, selectionEnd: caret + 2,
    });
    expect(apply(source, caret, caret, 'indent')).toEqual({
      source: 'theorem t : True := by\n  exact True.intro\n-- untouched', start: caret + 2, end: caret + 2,
    });
  });

  it('outdents the current line without replacing its body or neighboring lines', () => {
    const source = 'head\n    exact h\ntail';
    expect(sourceIndentEdit(source, 11, 11, 'outdent')).toEqual({
      from: 5, to: 7, text: '', selectionStart: 9, selectionEnd: 9,
    });
    expect(apply(source, 11, 11, 'outdent')).toEqual({ source: 'head\n  exact h\ntail', start: 9, end: 9 });
  });

  it('indents a multiline selection with one minimal continuous replacement', () => {
    expect(sourceIndentEdit('a\nb\nc', 0, 5, 'indent')).toEqual({
      from: 0, to: 4, text: '  a\n  b\n  ', selectionStart: 2, selectionEnd: 11,
    });
    expect(apply('a\nb\nc', 0, 5, 'indent')).toEqual({ source: '  a\n  b\n  c', start: 2, end: 11 });
  });

  it('maps a partial multiline selection and ordered bounds from a backward selection', () => {
    const backwardSelection = { start: 1, end: 5, direction: 'backward' } as const;
    expect(apply('ab\ncd\nef', backwardSelection.start, backwardSelection.end, 'indent')).toEqual({
      source: '  ab\n  cd\nef', start: 3, end: 9,
    });
  });

  it.each([['LF', '\n'], ['CRLF', '\r\n'], ['CR', '\r']])('preserves %s separators byte for byte', (_, newline) => {
    const source = `a${newline}b${newline}c`, end = `a${newline}b`.length;
    const indented = apply(source, 0, end, 'indent');
    expect(indented).toEqual({ source: `  a${newline}  b${newline}c`, start: 2, end: end + 4 });
    expect(apply(indented.source, indented.start, indented.end, 'outdent')).toEqual({ source, start: 0, end });
  });

  it.each([['LF', '\n'], ['CRLF', '\r\n']])('excludes the next line when a selection ends at its %s line start', (_, newline) => {
    const source = `a${newline}  b`, end = `a${newline}`.length;
    expect(sourceIndentEdit(source, 0, end, 'indent')).toEqual({
      from: 0, to: 0, text: '  ', selectionStart: 2, selectionEnd: end + 2,
    });
    expect(apply(source, 0, end, 'indent').source).toBe(`  a${newline}  b`);
    expect(sourceIndentEdit(source, 0, end, 'outdent')).toBeUndefined();
  });

  it('includes the next line when the selection extends into its first character', () => {
    expect(apply('a\nb\nc', 0, 3, 'indent')).toEqual({ source: '  a\n  b\nc', start: 2, end: 7 });
  });

  it('outdents mixed leading spaces and tabs without changing internal whitespace', () => {
    const source = '  a\n b\n\tc\n \td\nx\n    y';
    expect(apply(source, 0, source.length, 'outdent')).toEqual({
      source: 'a\nb\nc\n\td\nx\n  y', start: 0, end: source.length - 7,
    });
    expect(apply(' \t  body', 5, 5, 'outdent').source).toBe('\t  body');
    expect(apply('\t  body', 5, 5, 'outdent').source).toBe('  body');
  });

  it('omits unchanged outer lines from an outdent replacement', () => {
    expect(sourceIndentEdit('x\n  y\nz', 0, 7, 'outdent')).toEqual({
      from: 2, to: 4, text: '', selectionStart: 0, selectionEnd: 5,
    });
    expect(sourceIndentEdit('  a\nb\n  c', 0, 9, 'outdent')).toEqual({
      from: 0, to: 8, text: 'a\nb\n', selectionStart: 0, selectionEnd: 5,
    });
  });

  it.each([0, 1, 2, 3, 5])('clamps a caret inside removed indentation and maps offset %s', caret => {
    expect(apply('  abc', caret, caret, 'outdent')).toEqual({
      source: 'abc', start: Math.max(0, caret - 2), end: Math.max(0, caret - 2),
    });
  });

  it('maps selection endpoints inside removed prefixes without reversing them', () => {
    expect(apply('    x', 1, 3, 'outdent')).toEqual({ source: '  x', start: 0, end: 1 });
    expect(apply('  x', 0, 2, 'outdent')).toEqual({ source: 'x', start: 0, end: 0 });
    expect(apply('  a\n  b', 1, 5, 'outdent')).toEqual({ source: 'a\nb', start: 0, end: 2 });
  });

  it('moves a caret at line start after the inserted indentation', () => {
    expect(apply('a\nb', 2, 2, 'indent')).toEqual({ source: 'a\n  b', start: 4, end: 4 });
    expect(apply('a\nb', 3, 3, 'indent')).toEqual({ source: 'a\n  b', start: 5, end: 5 });
  });

  it('handles an empty source and the first empty line before a leading newline', () => {
    expect(sourceIndentEdit('', 0, 0, 'indent')).toEqual({ from: 0, to: 0, text: '  ', selectionStart: 2, selectionEnd: 2 });
    expect(apply('\nnext', 0, 0, 'indent')).toEqual({ source: '  \nnext', start: 2, end: 2 });
    expect(apply('\nnext', 0, 1, 'indent')).toEqual({ source: '  \nnext', start: 2, end: 3 });
  });

  it('handles trailing empty lines and whitespace-only lines without adding newlines', () => {
    expect(apply('a\n', 2, 2, 'indent')).toEqual({ source: 'a\n  ', start: 4, end: 4 });
    expect(apply('a\n', 0, 2, 'indent')).toEqual({ source: '  a\n', start: 2, end: 4 });
    expect(apply('\n\n', 0, 2, 'indent')).toEqual({ source: '  \n  \n', start: 2, end: 6 });
    expect(apply(' \n\t\n  ', 0, 6, 'outdent')).toEqual({ source: '\n\n', start: 0, end: 2 });
  });

  it('preserves Unicode bytes and maps UTF-16 selection offsets', () => {
    const source = '\u{1f600}\u03b1\n  \u03b2\u{1f600}z';
    const indented = apply(source, 7, 9, 'indent');
    expect(indented).toEqual({ source: '\u{1f600}\u03b1\n    \u03b2\u{1f600}z', start: 9, end: 11 });
    expect(indented.source.slice(indented.start, indented.end)).toBe('\u{1f600}');
    const outdented = apply(source, 7, 9, 'outdent');
    expect(outdented).toEqual({ source: '\u{1f600}\u03b1\n\u03b2\u{1f600}z', start: 5, end: 7 });
    expect(outdented.source.slice(outdented.start, outdented.end)).toBe('\u{1f600}');
    expect(apply(source, 1, 1, 'indent')).toMatchObject({ start: 3, end: 3 });
  });

  it.each(['', 'unindented', 'a\nb', '\n\n', '\u00a0body'])('returns no edit when selected lines have no removable prefix: %j', source => {
    expect(sourceIndentEdit(source, 0, source.length, 'outdent')).toBeUndefined();
  });

  it.each([[-1, 0], [0, -1], [2, 1], [0, 4], [0.5, 1], [0, 1.5], [NaN, 1], [0, Infinity]])(
    'rejects an invalid selection range %s..%s', (start, end) => {
      expect(sourceIndentEdit('abc', start, end, 'indent')).toBeUndefined();
    },
  );
});
