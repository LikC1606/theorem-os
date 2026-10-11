
import type { LeanEvalCatalogProblem } from "./leanEvalCatalogAdapter";

export const LEAN_EVAL_HELD_OUT_FAMILIES = [
  'arithmetic',
  'finite_structure',
  'algebraic_identity',
  'induction',
] as const;
export type LeanEvalHeldOutFamily = (typeof LEAN_EVAL_HELD_OUT_FAMILIES)[number];

const normalizedSearchText = (problem: LeanEvalCatalogProblem): string =>
  [problem.id, problem.title, problem.module, ...problem.tags]
    .join(' ')
    .replace(/([a-z])([A-Z])/gu, '$1 $2')
    .replace(/[_-]+/gu, ' ')
    .toLowerCase();

/** Classify only from public catalog metadata; no statement or solution source is read. */
export function classifyLeanEvalHeldOutFamily(problem: LeanEvalCatalogProblem): LeanEvalHeldOutFamily | 'unclassified' {
  const text = normalizedSearchText(problem);
  if (/\b(?:induction|recursive|recursion|well founded)\b/u.test(text)) return 'induction';
  if (
    /\b(?:finite (?:sets?|groups?|graphs?|structures?)|combinatorics?|graphs?|permutations?|enumeration|fintype|finite structure)\b/u.test(
      text
    )
  ) {
    return 'finite_structure';
  }
  if (/\b(?:(?:algebraic|polynomial(?: ring)?|ring|field) identit(?:y|ies))\b/u.test(text)) {
    return 'algebraic_identity';
  }
  if (/\b(?:arithmetic|number theory|integer (?:inequalit(?:y|ies)|multiplication))\b/u.test(text)) return 'arithmetic';
  // A domain keyword is not evidence of difficulty or a proof mechanism.
  return 'unclassified';
}
