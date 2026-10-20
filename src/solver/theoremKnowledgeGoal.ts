import { maskLeanComments, maskLeanCommentsAndStrings } from '../math/leanSyntax';

type SurfaceToken = string | readonly ['bound', number, ...string[]];
type Scope = ReadonlyMap<string, number>;
const simpleName = /^[\p{L}_][\p{L}\p{M}\p{N}_']*$/u;
const binders = new Map([['∀', 'forall'], ['forall', 'forall'], ['∑', 'sum'], ['∏', 'prod']]);
const unsupported = new Set(['∃', 'exists', '∫', 'Σ', 'Π', '⨆', '⨅', 'fun', 'λ', 'let', 'letI', 'have', 'haveI',
  'match', 'by', 'where', 'do', 'if', 'then', 'else', '↦', '=>', ':=', '//', '|', '?', '_', '⊢', "'", '«', '»', '`', '$']);
const aliases = new Map([['ℕ', 'Nat'], ['ℤ', 'Int'], ['ℚ', 'Rat'], ['ℝ', 'Real'], ['ℂ', 'Complex'],
  ['→', '->'], ['↔', '<->']]);
const ambiguousSumTail = new Set(['=', '≠', '<', '>', '≤', '≥', '∧', '∨', '→', '->', '↔', '<->',
  '∈', '∉', '⊆', '⊂', '⊇', '⊃', ',', ';', ':']);

export type KnowledgeResidualView = Readonly<{ display: string; target: string; goal: string; caseLabel?: string;
  localContext: 'closed-for-retrieval' | 'target-only' | 'no-locals'; fallbackReason?: string }>;

/** Split Lean's displayed cases, closing only simple local declarations. Never an elaborated type. */
export function knowledgeResidualViews(value: string): KnowledgeResidualView[] {
  if (!/⊢|\|-/u.test(value)) return [{ display: value, target: value, goal: value, localContext: 'no-locals' }];
  const blocks = value.split(/(?=^\s*case\s+[^\n]+$)/gmu).filter(block => block.trim());
  const result: KnowledgeResidualView[] = [];
  for (const block of blocks) {
    const markers = [...block.matchAll(/⊢|\|-/gu)];
    if (markers.length !== 1) {
      // Unsupported displays are searched as a whole, never by silently taking their final target.
      result.push({ display: block, target: block, goal: block, localContext: 'target-only', fallbackReason: 'ambiguous-goal-display' });
      continue;
    }
    const marker = markers[0]!, before = block.slice(0, marker.index), target = block.slice(marker.index! + marker[0].length).trim();
    const lines = before.trim().split('\n').map(line => line.trim()).filter(Boolean);
    const caseLabel = lines[0]?.startsWith('case ') ? lines.shift()!.slice(5).trim() : undefined;
    const binders: string[] = [], names = new Set<string>();
    let supported = true;
    for (const line of lines) {
      const declaration = /^([\p{L}_][\p{L}\p{M}\p{N}_' \t]*)\s*:\s*(.+)$/u.exec(line);
      if (!declaration || /:=|[✝†]|\.{3}|…/u.test(line)) { supported = false; break; }
      const declared = declaration[1]!.trim().split(/\s+/u), type = declaration[2]!.trim();
      if (!type || declared.some(name => !simpleName.test(name) || names.has(name) || name === '_')) { supported = false; break; }
      // Unbalanced or multiline locals and local definitions cannot be faithfully closed here.
      const stack: string[] = [];
      for (const char of type) {
        if ('([{'.includes(char)) stack.push(char);
        else if (')]}'.includes(char) && stack.pop() !== '([{'.charAt(')]}'.indexOf(char))) { supported = false; break; }
      }
      if (stack.length || !supported) { supported = false; break; }
      declared.forEach(name => names.add(name));
      binders.push(`(${declared.join(' ')} : ${type})`);
    }
    result.push({ display: block.trim(), target, goal: supported && binders.length ? `∀ ${binders.join(' ')}, ${target}` : target,
      ...(caseLabel ? { caseLabel } : {}), localContext: !supported ? 'target-only' : binders.length ? 'closed-for-retrieval' : 'no-locals',
      ...(!supported ? { fallbackReason: 'unsupported-local-declaration' } : {}) });
  }
  return result;
}

/** A conservative ranking surface, never evidence of Lean equivalence or applicability. */
export function knowledgeGoalSurfaceShape(value: string): string | undefined {
  if (maskLeanComments(value).includes('"')) return undefined;
  const tokens = [...maskLeanCommentsAndStrings(value).matchAll(
    /[\p{L}_][\p{L}\p{M}\p{N}_']*(?:\.[\p{L}_][\p{L}\p{M}\p{N}_']*)*|[0-9]+|<->|->|=>|:=|\/\/|[^\s]/gu
  )].map(match => match[0]);
  if (!tokens.length || tokens.length > 8192 || tokens.some(token => unsupported.has(token))) return undefined;
  const pairs = new Map<number, number>(), stack: number[] = [];
  for (let index = 0; index < tokens.length; index++) {
    const token = tokens[index]!;
    if (['(', '[', '{'].includes(token)) stack.push(index);
    else if ([')', ']', '}'].includes(token)) {
      const start = stack.pop();
      if (start === undefined || ['(', '[', '{'].indexOf(tokens[start]!) !== [')', ']', '}'].indexOf(token)) return undefined;
      pairs.set(start, index);
    }
  }
  if (stack.length) return undefined;
  let nextBinding = 0;

  function splitAt(start: number, end: number, separator: string): number | undefined {
    for (let index = start; index < end; index++) {
      if (tokens[index] === separator) return index;
      if (pairs.has(index)) index = pairs.get(index)!;
    }
    return undefined;
  }

  function normalize(start: number, end: number, scope: Scope, depth: number, sumBody = false): SurfaceToken[] | undefined {
    if (depth > 64) return undefined;
    const output: SurfaceToken[] = [];
    for (let index = start; index < end; index++) {
      const token = tokens[index]!, binder = binders.get(token);
      if (sumBody && (ambiguousSumTail.has(token) || binder === 'forall')) return undefined;
      if (binder) {
        const local = new Map(scope), header: SurfaceToken[] = [binder];
        let cursor = index + 1, declared = false;
        const declare = (names: readonly string[], typeStart: number, typeEnd: number, opening: string, closing: string) => {
          if (!names.length || names.some(name => !simpleName.test(name) || local.has(name) || name === '_root_') ||
              new Set(names).size !== names.length || typeStart >= typeEnd) return false;
          const type = normalize(typeStart, typeEnd, local, depth + 1);
          if (!type) return false;
          header.push(opening);
          for (const name of names) {
            const id = nextBinding++;
            local.set(name, id); header.push(['bound', id]);
          }
          header.push(':', ...type, closing); declared = true;
          return true;
        };
        if (binder === 'forall') {
          while (cursor < end && ['(', '[', '{'].includes(tokens[cursor]!)) {
            const close = pairs.get(cursor);
            if (close === undefined || close >= end) return undefined;
            const colon = splitAt(cursor + 1, close, ':');
            if (colon === undefined) {
              if (tokens[cursor] !== '[' || cursor + 1 === close) return undefined;
              const type = normalize(cursor + 1, close, local, depth + 1);
              if (!type) return undefined;
              header.push('[', ...type, ']');
            } else if (!declare(tokens.slice(cursor + 1, colon), colon + 1, close, tokens[cursor]!, tokens[close]!)) return undefined;
            cursor = close + 1;
          }
        }
        if (tokens[cursor] !== ',') {
          const comma = splitAt(cursor, end, ','), colon = comma === undefined ? undefined : splitAt(cursor, comma, ':');
          if (comma === undefined || colon === undefined || (binder !== 'forall' && colon !== cursor + 1)) return undefined;
          for (let check = colon + 1; check < comma; check++) {
            if (pairs.has(check)) check = pairs.get(check)!;
            else if (binders.has(tokens[check]!)) return undefined;
          }
          if (!declare(tokens.slice(cursor, colon), colon + 1, comma, '(', ')')) return undefined;
          cursor = comma;
        }
        if (!declared || cursor + 1 >= end) return undefined;
        const body = normalize(cursor + 1, end, local, depth + 1, binder !== 'forall');
        return body ? [...output, ...header, ',', ...body] : undefined;
      }
      const close = pairs.get(index);
      if (close !== undefined) {
        // Dependent arrows outside an explicit forall are outside this small supported surface.
        if (splitAt(index + 1, close, ':') !== undefined && ['→', '->'].includes(tokens[close + 1] ?? '')) return undefined;
        const contents = normalize(index + 1, close, scope, depth + 1);
        if (!contents) return undefined;
        output.push(token, ...contents, tokens[close]!); index = close;
      } else {
        const [head, ...fields] = token.split('.'), bound = scope.get(head!);
        output.push(bound === undefined ? aliases.get(token) ?? token : ['bound', bound, ...fields]);
      }
    }
    return output;
  }

  const result = normalize(0, tokens.length, new Map(), 0);
  return result && nextBinding ? JSON.stringify(result) : undefined;
}
