/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

export type LeanEvalHoleDagNode = Readonly<{
  name: string;
  basename: string;
  kind: 'theorem' | 'definition' | 'instance' | 'unknown';
  dependsOn: readonly string[];
}>;

export type LeanEvalHoleSchedule = Readonly<{
  waves: readonly (readonly string[])[];
  ready: readonly string[];
  completed: readonly string[];
  blocked: readonly string[];
}>;

const stripLeanTrivia = (source: string): string => {
  let output = '';
  let blockDepth = 0;
  let lineComment = false;
  let quote = false;
  let escaped = false;
  for (let index = 0; index < source.length; index += 1) {
    const current = source[index]!;
    const next = source[index + 1];
    if (lineComment) {
      if (current === '\n') {
        lineComment = false;
        output += '\n';
      }
      continue;
    }
    if (blockDepth > 0) {
      if (current === '/' && next === '-') {
        blockDepth += 1;
        index += 1;
      } else if (current === '-' && next === '/') {
        blockDepth -= 1;
        index += 1;
      }
      continue;
    }
    if (quote) {
      if (escaped) escaped = false;
      else if (current === '\\') escaped = true;
      else if (current === '"') quote = false;
      output += ' ';
      continue;
    }
    if (current === '-' && next === '-') {
      lineComment = true;
      index += 1;
    } else if (current === '/' && next === '-') {
      blockDepth = 1;
      index += 1;
    } else if (current === '"') {
      quote = true;
      output += ' ';
    } else output += current;
  }
  return output;
};

type ScopedDeclaration = Readonly<{ kind: string; basename: string; namespace: string; position: number }>;

const holeScheduleRank = (node: LeanEvalHoleDagNode): number =>
  node.kind === 'definition' || node.kind === 'instance' ? 0 : node.kind === 'theorem' ? 1 : 2;

const scopedDeclarations = (source: string): readonly ScopedDeclaration[] => {
  const cleaned = stripLeanTrivia(source);
  const stack: string[] = [];
  const entries: ScopedDeclaration[] = [];
  for (const [line, raw] of cleaned.split('\n').entries()) {
    const namespace = /^\s*namespace\s+([\p{L}\p{M}\p{N}_][\p{L}\p{M}\p{N}_'.]*)(?![\p{L}\p{M}\p{N}_'])/u.exec(
      raw
    )?.[1];
    if (namespace) stack.push(namespace);
    const declaration =
      /^\s*(?:noncomputable\s+)?(def|theorem|lemma|instance)\s+([\p{L}\p{M}\p{N}_][\p{L}\p{M}\p{N}_'.]*)(?![\p{L}\p{M}\p{N}_'])/u.exec(
        raw
      );
    if (declaration) {
      entries.push(
        Object.freeze({ kind: declaration[1]!, basename: declaration[2]!, namespace: stack.join('.'), position: line })
      );
    }
    const end = /^\s*end(?:\s+([\p{L}\p{M}\p{N}_][\p{L}\p{M}\p{N}_'.]*)(?![\p{L}\p{M}\p{N}_']))?/u.exec(raw);
    if (end && stack.length) {
      const requested = end[1];
      if (!requested || requested === stack.at(-1) || requested === stack.join('.')) stack.pop();
    }
  }
  return Object.freeze(entries);
};

/** Return all missing configured holes, including the exact namespace path. */
export function assertLeanEvalHoleCompleteness(expectedNames: readonly string[], declaredSource: string): void {
  if (!Array.isArray(expectedNames) || expectedNames.length === 0)
    throw new TypeError('LeanEval expected holes are required');
  const declarations = scopedDeclarations(declaredSource).filter(
    (entry) => entry.namespace === 'Submission' || entry.namespace.startsWith('Submission.')
  );
  const missing = expectedNames.filter((name) => {
    const basename = name.split('.').at(-1) ?? name;
    const expectedPath = name.startsWith('Submission.') ? name : `Submission.${name}`;
    return !declarations.some(
      (entry) =>
        `${entry.namespace}.${entry.basename}` === expectedPath ||
        (entry.namespace === 'Submission' && entry.basename === basename)
    );
  });
  if (missing.length) throw new Error(`LeanEval submission is missing configured holes: ${missing.join(', ')}`);
  const duplicates = expectedNames
    .map((name) => (name.startsWith('Submission.') ? name : `Submission.${name}`))
    .filter(
      (expectedPath, index, names) =>
        declarations.filter((entry) => `${entry.namespace}.${entry.basename}` === expectedPath).length > 1 &&
        names.indexOf(expectedPath) === index
    );
  if (duplicates.length)
    throw new Error(`LeanEval submission declares configured holes more than once: ${duplicates.join(', ')}`);
}

export function assertLeanEvalSubmissionNamespace(declaredSource: string): void {
  const cleaned = stripLeanTrivia(declaredSource);
  if (!/^\s*namespace\s+Submission\b/mu.test(cleaned) || !/^\s*end\s+Submission\b/mu.test(cleaned)) {
    throw new Error('LeanEval submission namespace must be Submission');
  }
}

export function assertLeanEvalSubmissionOwned(declaredSource: string): void {
  assertLeanEvalSubmissionNamespace(declaredSource);
  const outsideDeclarations = scopedDeclarations(declaredSource).filter(
    (entry) => entry.namespace !== 'Submission' && !entry.namespace.startsWith('Submission.')
  );
  if (outsideDeclarations.length) {
    throw new Error(
      `LeanEval submission contains declarations outside the allowed Submission namespace: ${outsideDeclarations
        .map((entry) => entry.basename)
        .join(', ')}`
    );
  }
}

export function assertLeanEvalSubmissionComplete(expectedNames: readonly string[], declaredSource: string): void {
  assertLeanEvalSubmissionOwned(declaredSource);
  assertLeanEvalHoleCompleteness(expectedNames, declaredSource);
}

/** Definitions and instances are scheduled before theorem consumers when dependencies permit. */
export function scheduleLeanEvalHoles(
  nodes: readonly LeanEvalHoleDagNode[],
  completedNames: readonly string[] = []
): LeanEvalHoleSchedule {
  if (!Array.isArray(nodes)) throw new TypeError('LeanEval hole DAG must be an array');
  const names = new Set<string>();
  const basenames = new Set<string>();
  for (const node of nodes) {
    if (names.has(node.name)) throw new Error(`LeanEval hole DAG contains duplicate node: ${node.name}`);
    if (basenames.has(node.basename))
      throw new Error(`LeanEval hole DAG contains duplicate basename: ${node.basename}`);
    names.add(node.name);
    basenames.add(node.basename);
  }
  const byBasename = new Map(nodes.map((node) => [node.basename, node.name]));
  const completed = new Set(completedNames);
  const waves: string[][] = [];
  while (true) {
    const candidates = nodes
      .filter((node) => !completed.has(node.name))
      .filter((node) =>
        node.dependsOn.every(
          (dependency: string) => completed.has(dependency) || completed.has(byBasename.get(dependency) ?? dependency)
        )
      );
    const foundationReady = candidates.some((node) => node.kind === 'definition' || node.kind === 'instance');
    const wave = candidates
      .filter((node) => !foundationReady || node.kind === 'definition' || node.kind === 'instance')
      .toSorted((left, right) => {
        return holeScheduleRank(left) - holeScheduleRank(right) || left.name.localeCompare(right.name);
      })
      .map((node) => node.name);
    if (!wave.length) break;
    waves.push(wave);
    wave.forEach((name) => completed.add(name));
  }
  const ready = waves.at(0) ?? [];
  const blocked = nodes.filter((node) => !completed.has(node.name)).map((node) => node.name);
  return Object.freeze({
    waves: Object.freeze(waves.map((wave) => Object.freeze(wave))),
    ready: Object.freeze(ready),
    completed: Object.freeze([...completedNames, ...waves.flat()]),
    blocked: Object.freeze(blocked),
  });
}

export function assertLeanEvalHoleDagAcyclic(nodes: readonly LeanEvalHoleDagNode[]): void {
  const names = new Set<string>();
  const basenames = new Set<string>();
  for (const node of nodes) {
    if (names.has(node.name)) throw new Error(`LeanEval hole DAG contains duplicate node: ${node.name}`);
    if (basenames.has(node.basename))
      throw new Error(`LeanEval hole DAG contains duplicate basename: ${node.basename}`);
    names.add(node.name);
    basenames.add(node.basename);
  }
  const byName = new Map(nodes.map((node) => [node.name, node]));
  const byBasename = new Map(nodes.map((node) => [node.basename, node.name]));
  const visiting = new Set<string>();
  const visited = new Set<string>();
  const visit = (name: string): void => {
    if (visiting.has(name)) throw new Error('LeanEval hole DAG contains a cycle');
    if (visited.has(name)) return;
    const node = byName.get(name);
    if (!node) throw new Error(`LeanEval hole DAG references unknown dependency: ${name}`);
    visiting.add(name);
    for (const dependency of node.dependsOn) visit(byBasename.get(dependency) ?? dependency);
    visiting.delete(name);
    visited.add(name);
  };
  nodes.forEach((node) => visit(node.name));
}
