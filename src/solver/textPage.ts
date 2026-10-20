/** Exact UTF-16 text pages for bounded advisory read tools. */
export const splitsSurrogate = (text: string, offset: number) => offset > 0 && offset < text.length &&
  text.charCodeAt(offset - 1) >= 0xd800 && text.charCodeAt(offset - 1) <= 0xdbff &&
  text.charCodeAt(offset) >= 0xdc00 && text.charCodeAt(offset) <= 0xdfff;

/**
 * The longest page `packet(begin, end)` whose JSON plus the CLI's trailing newline fits `maxBytes`, never splitting a
 * surrogate pair. `end` is the page limit; `wholeFirst` tries the whole page before the binary search.
 */
export function largestFittingPage<Packet>(text: string, begin: number, end: number, maxBytes: number,
  packet: (end: number) => Packet, budgetError: string, wholeFirst = end - begin <= maxBytes): Packet {
  const fits = (value: Packet) => Buffer.byteLength(JSON.stringify(value)) + 1 <= maxBytes;
  if (wholeFirst) {
    const whole = packet(end);
    if (fits(whole)) return whole;
  }
  if (!fits(packet(begin))) throw new Error(budgetError);
  let lower = begin + 1, upper = Math.min(end - 1, begin + maxBytes), best = begin;
  while (lower <= upper) {
    const middle = Math.floor((lower + upper) / 2), candidate = splitsSurrogate(text, middle) ? middle - 1 : middle;
    if (fits(packet(candidate))) { best = candidate; lower = middle + 1; } else upper = middle - 1;
  }
  if (best === begin && end > begin) throw new Error(budgetError);
  return packet(best);
}
