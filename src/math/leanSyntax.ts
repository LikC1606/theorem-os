/** Mask comments and string literals while preserving line boundaries and source offsets. */
export function maskLeanCommentsAndStrings(source: string): string {
  return maskLeanText(source, true);
}

/** Preserve string-valued definitions when preparing a statement-only snapshot. */
export function maskLeanComments(source: string): string {
  return maskLeanText(source, false);
}

function maskLeanText(source: string, maskStrings: boolean): string {
  const chunks: string[] = [];
  let visibleStart = 0;
  let hiddenStart = -1;
  let blockDepth = 0;
  let lineComment = false;
  let quote = false;
  let escaped = false;
  const beginHidden = (index: number) => {
    chunks.push(source.slice(visibleStart, index));
    hiddenStart = index;
  };
  const endHidden = (index: number) => {
    chunks.push(source.slice(hiddenStart, index).replace(/[^\r\n]+/g, text => ' '.repeat(text.length)));
    visibleStart = index;
    hiddenStart = -1;
  };
  for (let index = 0; index < source.length; index++) {
    const current = source[index];
    const next = source[index + 1];
    if (lineComment) {
      if (current === '\n') { lineComment = false; endHidden(index + 1); }
    } else if (blockDepth) {
      if (current === '/' && next === '-') { blockDepth++; index++; }
      else if (current === '-' && next === '/') {
        if (--blockDepth === 0) endHidden(index + 2);
        index++;
      }
    } else if (quote) {
      if (escaped) escaped = false;
      else if (current === '\\') escaped = true;
      else if (current === '"') { quote = false; if (maskStrings) endHidden(index + 1); }
    } else if (current === '-' && next === '-') {
      beginHidden(index); lineComment = true; index++;
    } else if (current === '/' && next === '-') {
      beginHidden(index); blockDepth = 1; index++;
    } else if (current === '"') {
      if (maskStrings) beginHidden(index);
      quote = true;
    }
  }
  if (hiddenStart >= 0) endHidden(source.length);
  chunks.push(source.slice(visibleStart));
  return chunks.join('');
}
