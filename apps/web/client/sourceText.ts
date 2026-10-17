export type SourceMatch = { start: number; end: number; line: number; column: number };
export type LeanToken = { start: number; end: number; kind: 'comment' | 'keyword' | 'tactic' | 'placeholder' | 'string' | 'number' };

export function findSourceMatches(source: string, query: string, caseSensitive = false, maxMatches = 1000): { matches: SourceMatch[]; truncated: boolean } {
  const matches: SourceMatch[] = [];
  if (!query || query.length > 256) return { matches, truncated: false };
  const pattern = new RegExp(query.replace(/[.*+?^${}()|[\]\\]/g, '\\$&'), caseSensitive ? 'gu' : 'giu');
  const limit = Math.max(1, Math.min(1000, Number.isFinite(maxMatches) ? Math.floor(maxMatches) : 1000));
  let line = 1, column = 1, scanned = 0;
  for (const found of source.matchAll(pattern)) {
    if (matches.length >= limit) return { matches, truncated: true };
    const start = found.index;
    while (scanned < start) {
      const codePoint = source.codePointAt(scanned)!;
      if (codePoint === 10) { line++; column = 1; } else column++;
      scanned += codePoint > 0xffff ? 2 : 1;
    }
    matches.push({ start, end: start + found[0].length, line, column });
  }
  return { matches, truncated: false };
}

const keywords = new Set(('import namespace end section variable variables theorem lemma def abbrev opaque axiom constant example ' +
  'instance class structure inductive deriving where extends open export scoped attribute set_option universe universes ' +
  'noncomputable private protected mutual partial unsafe termination_by decreasing_by macro syntax elab ' +
  'by fun forall exists let in if then else match with do return have show from suffices ' +
  'Prop Type Sort true false').split(' '));
const tactics = new Set(('intro intros exact apply refine constructor cases rcases obtain induction ' +
  'simp simp_all simpa simp? dsimp rfl rw rwa ring ring_nf linarith nlinarith norm_num omega aesop ' +
  'tauto trivial decide native_decide assumption contradiction ext congr convert change calc ' +
  'unfold specialize subst use left right repeat first all_goals any_goals try done').split(' '));

// A bounded lexical pass for reading, without interpreting Lean or its proof status.
export function leanTokens(source: string): LeanToken[] {
  const tokens: LeanToken[] = [];
  const identifier = /[\p{L}_][\p{L}\p{M}\p{N}_'.!?]*/uy;
  const number = /(?:0[xX][0-9a-fA-F]+|\d+(?:\.\d+)?)/y;
  let offset = 0;
  while (offset < source.length && tokens.length < 8000) {
    const start = offset;
    if (source.startsWith('--', offset)) {
      const end = source.indexOf('\n', offset);
      offset = end < 0 ? source.length : end;
      tokens.push({ start, end: offset, kind: 'comment' });
    } else if (source.startsWith('/-', offset)) {
      let depth = 1;
      offset += 2;
      while (offset < source.length && depth) {
        if (source.startsWith('/-', offset)) { depth++; offset += 2; }
        else if (source.startsWith('-/', offset)) { depth--; offset += 2; }
        else offset++;
      }
      tokens.push({ start, end: offset, kind: 'comment' });
    } else if (source[offset] === '"') {
      offset++;
      while (offset < source.length) {
        if (source[offset] === '\\') offset = Math.min(source.length, offset + 2);
        else if (source[offset++] === '"') break;
      }
      tokens.push({ start, end: offset, kind: 'string' });
    } else if (source[offset] === '«') {
      const end = source.indexOf('»', offset + 1);
      offset = end < 0 ? source.length : end + 1;
    } else if (source[offset] === "'" && /^'(?:\\(?:u\{[\da-fA-F]+\}|x[\da-fA-F]{2}|.)|[^'\\\r\n])'/u.test(source.slice(offset, offset + 16))) {
      const character = /^'(?:\\(?:u\{[\da-fA-F]+\}|x[\da-fA-F]{2}|.)|[^'\\\r\n])'/u.exec(source.slice(offset, offset + 16))![0];
      offset += character.length;
      tokens.push({ start, end: offset, kind: 'string' });
    } else {
      identifier.lastIndex = number.lastIndex = offset;
      const name = identifier.exec(source)?.[0];
      const numeric = name ? undefined : number.exec(source)?.[0];
      if (name) {
        offset += name.length;
        const kind = name === 'sorry' || name === 'admit' ? 'placeholder' : keywords.has(name) ? 'keyword' : tactics.has(name) ? 'tactic' : undefined;
        if (kind) tokens.push({ start, end: offset, kind });
      } else if (numeric) {
        offset += numeric.length;
        tokens.push({ start, end: offset, kind: 'number' });
      } else offset++;
    }
  }
  return tokens;
}
