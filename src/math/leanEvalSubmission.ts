/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

import { maskLeanCommentsAndStrings } from './leanSyntax';
import { inspectScopedLeanDeclarations } from './leanSource';

type ScopedDeclaration = Readonly<{ basename: string; namespace: string }>;

const scopedDeclarations = (cleaned: string): readonly ScopedDeclaration[] => {
  return Object.freeze(inspectScopedLeanDeclarations(cleaned).map(({ qualifiedName }) => {
    const end = qualifiedName.lastIndexOf('.');
    return Object.freeze({ basename: qualifiedName.slice(end + 1), namespace: qualifiedName.slice(0, Math.max(0, end)) });
  }));
};

/** Generated workspaces may flatten the original LeanEval namespace. */
export function resolveLeanEvalSubmissionName(name: string, source: string): string {
  const names = scopedDeclarations(maskLeanCommentsAndStrings(source))
    .map(entry => `${entry.namespace}.${entry.basename}`);
  const qualified = name.startsWith('LeanEval.') ? name.replace(/^LeanEval\./u, 'Submission.') :
    name.startsWith('Submission.') ? name : `Submission.${name}`;
  const resolved = names.includes(qualified) ? qualified : `Submission.${name.split('.').at(-1)}`;
  if (names.filter(item => item === resolved).length !== 1)
    throw new Error(`LeanEval submission declaration is missing or ambiguous: ${name}`);
  return resolved;
}

/** Require every configured hole, including its exact namespace path. */
function assertHoleCompleteness(expectedNames: readonly string[], entries: readonly ScopedDeclaration[]): void {
  if (!Array.isArray(expectedNames) || expectedNames.length === 0)
    throw new TypeError('LeanEval expected holes are required');
  const declarations = entries.filter(
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

function assertSubmissionNamespace(cleaned: string): void {
  if (!/^\s*namespace\s+Submission\b/mu.test(cleaned) || !/^\s*end\s+Submission\b/mu.test(cleaned)) {
    throw new Error('LeanEval submission namespace must be Submission');
  }
}

function assertSubmissionOwned(cleaned: string, entries: readonly ScopedDeclaration[]): void {
  assertSubmissionNamespace(cleaned);
  const outsideDeclarations = entries.filter(
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

export function assertLeanEvalHoleCompleteness(expectedNames: readonly string[], declaredSource: string): void {
  assertHoleCompleteness(expectedNames, scopedDeclarations(maskLeanCommentsAndStrings(declaredSource)));
}

export function assertLeanEvalSubmissionNamespace(declaredSource: string): void {
  assertSubmissionNamespace(maskLeanCommentsAndStrings(declaredSource));
}

export function assertLeanEvalSubmissionOwned(declaredSource: string): void {
  const cleaned = maskLeanCommentsAndStrings(declaredSource);
  assertSubmissionOwned(cleaned, scopedDeclarations(cleaned));
}

export function assertLeanEvalSubmissionComplete(expectedNames: readonly string[], declaredSource: string): void {
  const cleaned = maskLeanCommentsAndStrings(declaredSource);
  const declarations = scopedDeclarations(cleaned);
  assertSubmissionOwned(cleaned, declarations);
  assertHoleCompleteness(expectedNames, declarations);
}
