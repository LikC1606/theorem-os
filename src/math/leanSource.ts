import crypto from 'node:crypto';
import { maskLeanCommentsAndStrings, leanScopeCommands, leanScopeNamespace, updateLeanScopes, type LeanScope } from './leanSyntax';

const hashBytes = (value: Uint8Array | string) => crypto.createHash('sha256').update(value).digest('hex');

export const inspectLeanSource = (
  source: string
): { sorryCount: number; admitCount: number; axioms: string[] } => {
  const inspectedSource = maskLeanCommentsAndStrings(source);
  let sorryCount = 0;
  let admitCount = 0;
  const axioms: string[] = [];
  for (const match of inspectedSource.matchAll(/\b(?:(sorry)\b|(admit)\b|axiom\s+([A-Za-z0-9_'.]+))/gu)) {
    if (match[1]) sorryCount += 1;
    else if (match[2]) admitCount += 1;
    else if (axioms.length < 64) axioms.push(match[3]);
  }
  return {
    sorryCount,
    admitCount,
    axioms,
  };
};

type MathematicsLeanSourceDeclarationKind = 'theorem' | 'definition' | 'instance';

type LeanSourceDeclaration = Readonly<{
  startOffset: number;
  bodyOffset: number;
  name: string;
  canonicalHeader: string;
  kind: MathematicsLeanSourceDeclarationKind;
}>;

export type MathematicsLeanSourceDeclaration = Readonly<{
  startOffset: number;
  name: string;
  declarationType: string;
  kind: MathematicsLeanSourceDeclarationKind;
}>;

const isLeanNameCharacter = (value: string | undefined): boolean =>
  Boolean(value && /[\p{L}\p{M}\p{N}_'.]/u.test(value));

export function inspectScopedLeanDeclarations(source: string) {
  const scopes: LeanScope[] = [], commands = leanScopeCommands(maskLeanCommentsAndStrings(source));
  let command = commands.next();
  return inspectLeanDeclarations(source).map(declaration => {
    while (!command.done && command.value.index < declaration.startOffset) {
      updateLeanScopes(scopes, command.value[1], command.value[2]?.trim());
      command = commands.next();
    }
    const namespace = leanScopeNamespace(scopes);
    const qualifiedName = declaration.name.startsWith('_root_.') ? declaration.name.slice(7) :
      [namespace, declaration.name].filter(Boolean).join('.');
    return { ...declaration, namespace, qualifiedName };
  });
}

/** Reopen a declaration's namespaces and active lookup scopes for a closed type query. */
export function leanDeclarationContextCommands(source: string, theoremName: string) {
  const declarations = inspectScopedLeanDeclarations(source);
  const target = declarations.find(declaration => declaration.qualifiedName === theoremName) ??
    declarations.find(declaration => declaration.name === theoremName);
  if (!target) throw new Error('Lean type query declaration was not found.');
  const regions = inspectLeanDeclarationRegions(source);
  const frames: string[][] = [[]];
  const ends: string[] = [];
  for (const command of leanScopeCommands(maskLeanCommentsAndStrings(source))) {
    if (command.index >= target.startOffset) break;
    if (regions.some(region => command.index >= region.startOffset && command.index < region.endOffset)) continue;
    const kind = command[1];
    if (kind === 'namespace' || kind === 'section') {
      frames.push([command[0].trim()]); ends.push(`end${command[2]?.trim() ? ' ' + command[2].trim() : ''}`);
    } else if (kind === 'end') { if (frames.length > 1) { frames.pop(); ends.pop(); } }
    else if (kind === 'open') frames.at(-1)!.push(command[0].trim());
  }
  return { before: frames.flat(), after: ends.reverse() };
}

/**
 * Extract named declaration headers without mistaking a binder default such
 * as `(x : Nat := 0)` for the declaration/body boundary. This is deliberately
 * a small lexer rather than a regular expression: comments, strings, and
 * balanced delimiter groups are all skipped while searching for the top-level
 * `:=` or a line-leading equation clause `|`. Lean permits Unicode and
 * apostrophes in identifiers, so a single quote is not a string delimiter here.
 */
function* leanSourceDeclarations(source: string): Generator<LeanSourceDeclaration, void, void> {
  const declarationKeywords: Readonly<Record<string, string>> = {
    t: 'theorem', l: 'lemma', d: 'def', i: 'instance', o: 'opaque', a: 'abbrev',
  };
  const codePointBefore = (offset: number): string | undefined => {
    if (offset <= 0) return undefined;
    const previous = source.charCodeAt(offset - 1);
    if (previous >= 0xdc00 && previous <= 0xdfff && offset >= 2) return source.slice(offset - 2, offset);
    return source[offset - 1];
  };
  const codePointAt = (offset: number): string | undefined => {
    if (offset >= source.length) return undefined;
    const value = source.codePointAt(offset);
    return value === undefined ? undefined : String.fromCodePoint(value);
  };
  let index = 0;
  let blockDepth = 0;
  let lineComment = false;
  let quote: '"' | undefined;
  let escaped = false;

  const skipTrivia = (start: number): number => {
    let cursor = start;
    while (cursor < source.length) {
      if (/\s/u.test(source[cursor])) {
        cursor += 1;
        continue;
      }
      if (source[cursor] === '-' && source[cursor + 1] === '-') {
        cursor += 2;
        while (cursor < source.length && source[cursor] !== '\n') cursor += 1;
        continue;
      }
      if (source[cursor] === '/' && source[cursor + 1] === '-') {
        cursor += 2;
        let depth = 1;
        while (cursor < source.length && depth > 0) {
          if (source[cursor] === '/' && source[cursor + 1] === '-') {
            depth += 1;
            cursor += 2;
          } else if (source[cursor] === '-' && source[cursor + 1] === '/') {
            depth -= 1;
            cursor += 2;
          } else cursor += 1;
        }
        continue;
      }
      break;
    }
    return cursor;
  };

  // Keep the canonicalizer beside the lexer state it serves; this parser is
  // intentionally self-contained so declaration-header behavior stays local.
  // eslint-disable-next-line unicorn/consistent-function-scoping
  const canonicalize = (value: string): string => {
    let result = '';
    let cursor = 0;
    let nestedBlockDepth = 0;
    let inLineComment = false;
    let stringQuote: '"' | undefined;
    let stringEscaped = false;
    let pendingSpace = false;
    while (cursor < value.length) {
      const current = value[cursor];
      const next = value[cursor + 1];
      if (inLineComment) {
        if (current === '\n') {
          inLineComment = false;
          pendingSpace = true;
        }
        cursor += 1;
        continue;
      }
      if (nestedBlockDepth > 0) {
        if (current === '/' && next === '-') {
          nestedBlockDepth += 1;
          cursor += 2;
        } else if (current === '-' && next === '/') {
          nestedBlockDepth -= 1;
          cursor += 2;
          pendingSpace = true;
        } else cursor += 1;
        continue;
      }
      if (stringQuote) {
        if (pendingSpace && result) result += ' ';
        pendingSpace = false;
        result += current;
        if (stringEscaped) stringEscaped = false;
        else if (current === '\\') stringEscaped = true;
        else if (current === stringQuote) stringQuote = undefined;
        cursor += 1;
        continue;
      }
      if (current === '-' && next === '-') {
        inLineComment = true;
        cursor += 2;
        continue;
      }
      if (current === '/' && next === '-') {
        nestedBlockDepth = 1;
        cursor += 2;
        continue;
      }
      if (current === '"') {
        if (pendingSpace && result) result += ' ';
        pendingSpace = false;
        stringQuote = current;
        result += current;
      } else if (/\s/u.test(current)) {
        pendingSpace = true;
      } else {
        if (pendingSpace && result) result += ' ';
        pendingSpace = false;
        result += current;
      }
      cursor += 1;
    }
    return result.trim();
  };

  while (index < source.length) {
    const current = source[index];
    const next = source[index + 1];
    if (lineComment) {
      if (current === '\n') lineComment = false;
      index += 1;
      continue;
    }
    if (blockDepth > 0) {
      if (current === '/' && next === '-') {
        blockDepth += 1;
        index += 2;
      } else if (current === '-' && next === '/') {
        blockDepth -= 1;
        index += 2;
      } else index += 1;
      continue;
    }
    if (quote) {
      if (escaped) escaped = false;
      else if (current === '\\') escaped = true;
      else if (current === quote) quote = undefined;
      index += 1;
      continue;
    }
    if (current === '-' && next === '-') {
      lineComment = true;
      index += 2;
      continue;
    }
    if (current === '/' && next === '-') {
      blockDepth = 1;
      index += 2;
      continue;
    }
    if (current === '"') {
      quote = current;
      index += 1;
      continue;
    }
    const keyword = declarationKeywords[current!];
    if (
      !keyword ||
      !source.startsWith(keyword, index) ||
      isLeanNameCharacter(codePointBefore(index)) ||
      isLeanNameCharacter(codePointAt(index + keyword.length))
    ) {
      index += 1;
      continue;
    }
    const nameStart = skipTrivia(index + keyword.length);
    const name = /^[\p{L}\p{M}\p{N}_'.]+/u.exec(source.slice(nameStart))?.[0] ?? '';
    const nameEnd = nameStart + name.length;
    if (!name) {
      index += keyword.length;
      continue;
    }
    let cursor = nameEnd;
    let parenDepth = 0;
    let bracketDepth = 0;
    let braceDepth = 0;
    let localBlockDepth = 0;
    let localLineComment = false;
    let localQuote: '"' | undefined;
    let localEscaped = false;
    let proofStart = -1;
    let bodyOffset = -1;
    let hasTopLevelMatchType = false;
    while (cursor < source.length) {
      const value = source[cursor];
      const following = source[cursor + 1];
      if (localLineComment) {
        if (value === '\n') localLineComment = false;
        cursor += 1;
        continue;
      }
      if (localBlockDepth > 0) {
        if (value === '/' && following === '-') {
          localBlockDepth += 1;
          cursor += 2;
        } else if (value === '-' && following === '/') {
          localBlockDepth -= 1;
          cursor += 2;
        } else cursor += 1;
        continue;
      }
      if (localQuote) {
        if (localEscaped) localEscaped = false;
        else if (value === '\\') localEscaped = true;
        else if (value === localQuote) localQuote = undefined;
        cursor += 1;
        continue;
      }
      if (value === '-' && following === '-') {
        localLineComment = true;
        cursor += 2;
        continue;
      }
      if (value === '/' && following === '-') {
        localBlockDepth = 1;
        cursor += 2;
        continue;
      }
      if (value === '"') {
        localQuote = value;
        cursor += 1;
        continue;
      }
      if (
        parenDepth === 0 &&
        bracketDepth === 0 &&
        braceDepth === 0 &&
        source.startsWith('match', cursor) &&
        !isLeanNameCharacter(codePointBefore(cursor)) &&
        !isLeanNameCharacter(codePointAt(cursor + 5))
      )
        hasTopLevelMatchType = true;
      if (value === '(') parenDepth += 1;
      else if (value === ')') parenDepth = Math.max(0, parenDepth - 1);
      else if (value === '[') bracketDepth += 1;
      else if (value === ']') bracketDepth = Math.max(0, bracketDepth - 1);
      else if (value === '{') braceDepth += 1;
      else if (value === '}') braceDepth = Math.max(0, braceDepth - 1);
      else if (value === ':' && following === '=' && parenDepth === 0 && bracketDepth === 0 && braceDepth === 0) {
        proofStart = cursor;
        bodyOffset = cursor + 2;
        break;
      } else if (
        value === '|' &&
        !hasTopLevelMatchType &&
        following !== '|' &&
        following !== '>' &&
        parenDepth === 0 &&
        bracketDepth === 0 &&
        braceDepth === 0 &&
        /^\s*$/u.test(source.slice(source.lastIndexOf('\n', cursor - 1) + 1, cursor))
      ) {
        // Equation clauses are the body itself, unlike the := separator.
        // Include the first pipe in the protected body; defaults, strings and
        // nested match expressions in binders were skipped above. A top-level
        // match return type stays on the established := path conservatively.
        proofStart = cursor;
        bodyOffset = cursor;
        break;
      }
      cursor += 1;
    }
    if (proofStart >= 0) {
      const startOffset = index;
      index = Math.max(bodyOffset, proofStart + 1);
      const header = source.slice(nameStart, proofStart);
      yield Object.freeze({
        startOffset,
        bodyOffset,
        name,
        kind:
          keyword === 'theorem' || keyword === 'lemma' ? 'theorem' : keyword === 'instance' ? 'instance' : 'definition',
        get canonicalHeader() {
          return canonicalize(header);
        },
      });
    } else index = nameEnd;
  }
}

const leanSourceDeclarationCache = new Map<string, readonly LeanSourceDeclaration[]>();
const LEAN_SOURCE_DECLARATION_CACHE_MAX_ENTRIES = 128;

const cachedLeanSourceDeclarations = (source: string): readonly LeanSourceDeclaration[] => {
  const key = hashBytes(source);
  const cached = leanSourceDeclarationCache.get(key);
  if (cached) {
    leanSourceDeclarationCache.delete(key);
    leanSourceDeclarationCache.set(key, cached);
    return cached;
  }
  const declarations = Object.freeze([...leanSourceDeclarations(source)]);
  leanSourceDeclarationCache.set(key, declarations);
  while (leanSourceDeclarationCache.size > LEAN_SOURCE_DECLARATION_CACHE_MAX_ENTRIES) {
    const oldest = leanSourceDeclarationCache.keys().next().value;
    if (oldest === undefined) break;
    leanSourceDeclarationCache.delete(oldest);
  }
  return declarations;
};

const sourceDeclarationHash = (declaration: LeanSourceDeclaration): string =>
  hashBytes(declaration.canonicalHeader);

export const declarationHashes = (source: string): Map<string, string> => {
  const hashes = new Map<string, string>();
  for (const declaration of cachedLeanSourceDeclarations(source)) {
    const declarationHash = sourceDeclarationHash(declaration);
    hashes.set(declaration.name, declarationHash);
    const local = declaration.name.split('.').at(-1);
    if (local && local !== declaration.name) hashes.set(local, declarationHash);
  }
  return hashes;
};

export const hashMathFormalSourceDeclaration = (formalStatement: string, theoremName: string): string | undefined => {
  const localRequestedName = theoremName.split('.').at(-1);
  for (const declaration of cachedLeanSourceDeclarations(formalStatement)) {
    const localDeclaredName = declaration.name.split('.').at(-1);
    if (declaration.name !== theoremName && localDeclaredName !== localRequestedName) continue;
    return sourceDeclarationHash(declaration);
  }
  return undefined;
};

/**
 * Return the named theorem, definition, and instance headers visible in a
 * Lean source file.
 * This is a read-only index primitive for bounded premise retrieval; it does
 * not execute Lean and therefore cannot be treated as proof evidence.
 */
export const inspectLeanDeclarations = (source: string): readonly MathematicsLeanSourceDeclaration[] =>
  Object.freeze(
    [...cachedLeanSourceDeclarations(source)].map(({ startOffset, name, kind, canonicalHeader }) =>
      Object.freeze({ startOffset, name, kind, declarationType: canonicalHeader })
    )
  );

/** Conservative source regions for construction edits; kernel verification remains independent. */
export const inspectLeanDeclarationRegions = (source: string) =>
  [...cachedLeanSourceDeclarations(source)].map((declaration) => {
    const lineStart = source.lastIndexOf('\n', declaration.startOffset - 1) + 1;
    const indentation = source.slice(lineStart, declaration.startOffset).match(/^\s*/u)?.[0].length ?? 0;
    let endOffset = source.length;
    let cursor = source.indexOf('\n', declaration.bodyOffset);
    while (cursor >= 0 && cursor + 1 < source.length) {
      const start = cursor + 1;
      const end = source.indexOf('\n', start);
      const line = source.slice(start, end < 0 ? undefined : end);
      if (line.trim() && !line.trimStart().startsWith('--') && (line.match(/^\s*/u)?.[0].length ?? 0) <= indentation) {
        endOffset = start;
        break;
      }
      cursor = end;
    }
    return {
      name: declaration.name,
      startOffset: declaration.startOffset,
      declarationType: declaration.canonicalHeader,
      bodyOffset: declaration.bodyOffset,
      endOffset,
    };
  });
