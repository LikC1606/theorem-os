export type IndentDirection = 'indent' | 'outdent';

export function sourceIndentEdit(source: string, start: number, end: number, direction: IndentDirection): {
  from: number; to: number; text: string; selectionStart: number; selectionEnd: number;
} | undefined {
  if (!Number.isInteger(start) || !Number.isInteger(end) || start < 0 || end < start || end > source.length) return undefined;

  const lineStarts = [0];
  for (const match of source.matchAll(/\r\n|\r|\n/g)) lineStarts.push(match.index + match[0].length);
  const first = lineStarts.findLastIndex(offset => offset <= start);
  const last = start === end ? first : lineStarts.findLastIndex(offset => offset < end);
  const changes: Array<{ from: number; to: number; text: string }> = [];
  for (let index = first; index <= last; index++) {
    const from = lineStarts[index]!;
    if (direction === 'indent') changes.push({ from, to: from, text: '  ' });
    else {
      const count = source[from] === '\t' ? 1 : source[from] === ' ' ? source[from + 1] === ' ' ? 2 : 1 : 0;
      if (count) changes.push({ from, to: from + count, text: '' });
    }
  }
  if (!changes.length) return undefined;

  const from = changes[0]!.from, to = changes.at(-1)!.to;
  const parts: string[] = [];
  let cursor = from;
  for (const change of changes) {
    parts.push(source.slice(cursor, change.from), change.text);
    cursor = change.to;
  }
  const mapPosition = (position: number) => {
    let delta = 0;
    for (const change of changes) {
      if (position < change.from) break;
      if (position <= change.to) return change.from + delta + change.text.length;
      delta += change.text.length - (change.to - change.from);
    }
    return position + delta;
  };
  return { from, to, text: parts.join(''), selectionStart: mapPosition(start), selectionEnd: mapPosition(end) };
}
