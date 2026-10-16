import { diffLines } from 'diff';

export type SourceDiffRow =
  | {
      kind: 'context' | 'added' | 'removed';
      text: string;
      oldLine?: number;
      newLine?: number;
      noNewline: boolean;
      changeId?: number;
    }
  | { kind: 'gap'; count: number };

export type SourceComparison = {
  status: 'ready' | 'identical' | 'unavailable';
  added: number;
  removed: number;
  rows: SourceDiffRow[];
  changeCount: number;
  omittedLines: number;
  lineEndingsChanged: boolean;
};

const maximumInputBytes = 256 * 1024;
const maximumRows = 2_000;
const contextLines = 3;
const encoder = new TextEncoder();

function unavailable(): SourceComparison {
  return { status: 'unavailable', added: 0, removed: 0, rows: [], changeCount: 0, omittedLines: 0, lineEndingsChanged: false };
}

export function compareSources(before: string, after: string, changesOnly = true): SourceComparison {
  if (before.length + after.length > maximumInputBytes
    || encoder.encode(before).byteLength + encoder.encode(after).byteLength > maximumInputBytes) return unavailable();

  const oldSource = before.replace(/\r\n?/g, '\n'), newSource = after.replace(/\r\n?/g, '\n');
  let changes;
  try { changes = diffLines(oldSource, newSource, { timeout: 80, maxEditLength: 2_000 }); }
  catch { return unavailable(); }
  if (!changes) return unavailable();

  const comparison: SourceComparison = {
    status: oldSource === newSource ? 'identical' : 'ready', added: 0, removed: 0,
    rows: [], changeCount: 0, omittedLines: 0,
    lineEndingsChanged: oldSource === newSource && before !== after,
  };
  let oldLine = 1, newLine = 1, previousChanged = false;

  for (let componentIndex = 0; componentIndex < changes.length; componentIndex++) {
    const component = changes[componentIndex];
    if (component.value === '') continue;
    const kind = component.added ? 'added' : component.removed ? 'removed' : 'context';
    const changed = kind !== 'context';
    if (changed && !previousChanged) comparison.changeCount++;
    const changeId = changed ? comparison.changeCount - 1 : undefined;
    const endsWithNewline = component.value.endsWith('\n');
    const lines = component.value.split('\n');
    if (endsWithNewline) lines.pop();
    if (kind === 'added') comparison.added += lines.length;
    if (kind === 'removed') comparison.removed += lines.length;

    const emitLines = (start: number, end: number) => {
      const renderedEnd = Math.min(end, start + maximumRows - comparison.rows.length);
      for (let index = start; index < renderedEnd; index++) {
        comparison.rows.push({
          kind, text: lines[index], noNewline: !endsWithNewline && index === lines.length - 1,
          ...(kind !== 'added' ? { oldLine: oldLine + index } : {}),
          ...(kind !== 'removed' ? { newLine: newLine + index } : {}),
          ...(changed ? { changeId } : {}),
        });
      }
      comparison.omittedLines += end - renderedEnd;
    };
    const emitGap = (count: number) => {
      if (count > 0 && comparison.rows.length < maximumRows) comparison.rows.push({ kind: 'gap', count });
    };

    if (changed || !changesOnly) emitLines(0, lines.length);
    else {
      const next = changes[componentIndex + 1];
      const nextChanged = Boolean(next?.added || next?.removed);
      const leading = previousChanged ? Math.min(contextLines, lines.length) : 0;
      const trailing = nextChanged ? Math.min(contextLines, lines.length - leading) : 0;
      emitLines(0, leading);
      emitGap(lines.length - leading - trailing);
      emitLines(lines.length - trailing, lines.length);
    }

    if (kind !== 'added') oldLine += lines.length;
    if (kind !== 'removed') newLine += lines.length;
    previousChanged = changed;
  }
  return comparison;
}
