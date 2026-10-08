/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

import type { LeanEvalProblemAnalysis } from "./leanEvalProblemAnalyzer";
import type { LeanEvalOutcomeSummary } from "./leanEvalOutcomeLedger";
import type { MathExecutionPolicy } from "../common/types/team/mathematicsTeam";

export const LEAN_EVAL_ARCHETYPES = [
  'algebra',
  'analysis',
  'topology',
  'combinatorics',
  'number_theory',
  'category_theory',
  'dynamics',
  'logic',
  'geometry',
  'pde',
  'probability',
  'representation_theory',
  'algebraic_geometry',
  'functional_analysis',
  'general',
] as const;
export type LeanEvalArchetype = (typeof LEAN_EVAL_ARCHETYPES)[number];

export type LeanEvalTacticStep = Readonly<{
  tactic: string;
  budgetMs: number;
  when: string;
}>;

export type LeanEvalRoute = Readonly<{
  archetype: LeanEvalArchetype;
  confidence: number;
  modelPriority: readonly string[];
  tacticLadder: readonly LeanEvalTacticStep[];
  premiseQueries: readonly string[];
  features: Readonly<{ imports: readonly string[]; keywords: readonly string[] }>;
}>;

/** Convert immutable route metadata into the assignment-carried execution
 * cursor. Keeping this conversion in the routing layer prevents callers from
 * copying only the labels and accidentally dropping the tactic/query order. */
export function executionPolicyFromLeanEvalRoute(route: LeanEvalRoute): MathExecutionPolicy {
  return Object.freeze({
    modelPriority: route.modelPriority,
    tacticLadder: route.tacticLadder,
    premiseQueries: route.premiseQueries,
    tacticIndex: 0,
    premiseQueryIndex: 0,
    attemptedModels: Object.freeze([]),
    attemptedTactics: Object.freeze([]),
    attemptedPremiseQueries: Object.freeze([]),
  });
}

/**
 * Reorder only strategies with enough verified history to be informative.
 * Unknown and sparse strategies retain their route order, preserving
 * exploration and keeping old ledgers backwards compatible.
 */
export function calibrateLeanEvalExecutionPolicy(
  policy: MathExecutionPolicy,
  history: Pick<LeanEvalOutcomeSummary, 'byModel' | 'byTactic'>,
  minimumAttempts = 2
): MathExecutionPolicy {
  if (!Number.isSafeInteger(minimumAttempts) || minimumAttempts < 1 || minimumAttempts > 100) {
    throw new TypeError('Lean-Eval calibration minimumAttempts must be an integer in [1,100]');
  }
  const score = (bucket: { attempts: number; successes: number } | undefined): number | undefined => {
    if (!bucket || bucket.attempts < minimumAttempts) return undefined;
    // Beta(1,1) posterior mean: a conservative estimate for small samples.
    return (bucket.successes + 1) / (bucket.attempts + 2);
  };
  const reorderModels = (models: readonly string[]): readonly string[] => {
    const observed = models
      .map((model, index) => ({ model, index, score: score(history.byModel[model]) }))
      .filter((entry): entry is { model: string; index: number; score: number } => entry.score !== undefined);
    if (observed.length < 2) return models;
    const ranked = observed
      .toSorted((left, right) => right.score - left.score || left.index - right.index)
      .map((entry) => entry.model);
    const result = [...models];
    observed.toSorted((left, right) => left.index - right.index).forEach((entry, index) => {
      result[entry.index] = ranked[index]!;
    });
    return Object.freeze(result);
  };
  const reorderTactics = (
    steps: readonly MathExecutionPolicy['tacticLadder'][number][]
  ): readonly MathExecutionPolicy['tacticLadder'][number][] => {
    const observed = steps
      .map((step, index) => ({ step, index, score: score(history.byTactic[step.tactic]) }))
      .filter(
        (
          entry
        ): entry is {
          step: MathExecutionPolicy['tacticLadder'][number];
          index: number;
          score: number;
        } => entry.score !== undefined
      );
    if (observed.length < 2) return steps;
    const ranked = observed
      .toSorted((left, right) => right.score - left.score || left.index - right.index)
      .map((entry) => entry.step);
    const result = [...steps];
    observed.toSorted((left, right) => left.index - right.index).forEach((entry, index) => {
      result[entry.index] = ranked[index]!;
    });
    return Object.freeze(result);
  };
  const modelPriority = reorderModels(policy.modelPriority);
  const tacticLadder = reorderTactics(policy.tacticLadder);
  if (modelPriority === policy.modelPriority && tacticLadder === policy.tacticLadder) return policy;
  return Object.freeze({ ...policy, modelPriority, tacticLadder });
}

const routeTable: Readonly<
  Record<
    LeanEvalArchetype,
    Readonly<{ keywords: readonly string[]; models: readonly string[]; tactics: readonly string[] }>
  >
> = {
  algebra: {
    keywords: ['Ring', 'Field', 'Ideal', 'Polynomial', 'Module', 'Group', 'monoid', 'ring'],
    models: ['deepseek-flash', 'glm-flash'],
    tactics: ['ring', 'nlinarith', 'simp', 'aesop', 'library_search'],
  },
  analysis: {
    keywords: ['Continuous', 'Measure', 'Integral', 'deriv', 'lim', 'Filter', 'Norm', 'Topological'],
    models: ['deepseek-flash', 'glm-flash'],
    tactics: ['norm_num', 'simp', 'linarith', 'positivity', 'aesop', 'library_search'],
  },
  topology: {
    keywords: ['TopologicalSpace', 'Compact', 'Connected', 'Metric', 'Open', 'Closed', 'IsCompact'],
    models: ['deepseek-flash', 'glm-flash'],
    tactics: ['simp', 'aesop', 'apply?', 'library_search'],
  },
  combinatorics: {
    keywords: ['Finset', 'Fintype', 'Card', 'SimpleGraph', 'Walk', 'path', 'count'],
    models: ['deepseek-flash', 'glm-flash'],
    tactics: ['simp', 'omega', 'norm_num', 'aesop', 'library_search'],
  },
  number_theory: {
    // Nat/Int occur in almost every Lean problem and are not useful domain
    // evidence on their own. Prefer arithmetic structures and theorems that
    // actually distinguish a number-theory route.
    keywords: ['Prime', 'Divisibility', 'ZMod', 'Coprime', 'factorization'],
    models: ['deepseek-flash', 'glm-flash'],
    tactics: ['norm_num', 'omega', 'linarith', 'ring', 'aesop', 'library_search'],
  },
  category_theory: {
    keywords: ['Category', 'Functor', 'NaturalTransformation', 'Iso', 'Monoidal'],
    models: ['deepseek-flash', 'glm-flash'],
    tactics: ['simp', 'aesop', 'exact?', 'apply?', 'library_search'],
  },
  dynamics: {
    keywords: ['Dynamical', 'Ergodic', 'MeasurePreserving', 'Orbit', 'Lyapunov', 'Entropy'],
    models: ['deepseek-flash', 'glm-flash'],
    tactics: ['simp', 'norm_num', 'linarith', 'aesop', 'library_search'],
  },
  logic: {
    keywords: ['FirstOrder', 'Satisfiable', 'Provable', 'Semantic', 'Formula', 'Theory', '\u00ac', '\u2200', '\u2203'],
    models: ['deepseek-flash', 'glm-flash'],
    tactics: ['rfl', 'simp', 'tauto', 'aesop', 'exact?', 'library_search'],
  },
  geometry: {
    keywords: ['Euclidean', 'Affine', 'Convex', 'Simplex', 'Manifold', 'Geometry', 'Isometry', 'Circle', 'Sphere'],
    models: ['deepseek-flash', 'glm-flash'],
    tactics: ['simp', 'ring', 'linarith', 'nlinarith', 'norm_num', 'aesop', 'library_search'],
  },
  pde: {
    keywords: ['PDE', 'PartialDerivative', 'Laplacian', 'Harmonic', 'Sobolev', 'HeatKernel', 'weak_solution'],
    models: ['deepseek-flash', 'glm-flash'],
    tactics: ['simp', 'positivity', 'linarith', 'nlinarith', 'norm_num', 'aesop', 'library_search'],
  },
  probability: {
    keywords: ['Probability', 'MeasureTheory', 'Indep', 'Expectation', 'Variance', 'AlmostEverywhere', 'Martingale'],
    models: ['deepseek-flash', 'glm-flash'],
    tactics: ['simp', 'norm_num', 'positivity', 'linarith', 'aesop', 'library_search'],
  },
  representation_theory: {
    keywords: ['Representation', 'ModuleCat', 'Character', 'Irrep', 'LieAlgebra', 'GroupAlgebra', 'Schur'],
    models: ['deepseek-flash', 'glm-flash'],
    tactics: ['simp', 'aesop', 'exact?', 'apply?', 'library_search'],
  },
  algebraic_geometry: {
    keywords: ['Scheme', 'Spec', 'Morphism', 'Sheaf', 'Variety', 'Zariski', 'AffineScheme', 'Projective'],
    models: ['deepseek-flash', 'glm-flash'],
    tactics: ['simp', 'aesop', 'exact?', 'apply?', 'library_search'],
  },
  functional_analysis: {
    keywords: [
      'NormedSpace',
      'Banach',
      'Hilbert',
      'ContinuousLinearMap',
      'InnerProduct',
      'OperatorNorm',
      'WeakTopology',
    ],
    models: ['deepseek-flash', 'glm-flash'],
    tactics: ['simp', 'norm_num', 'positivity', 'linarith', 'aesop', 'library_search'],
  },
  general: {
    keywords: [],
    models: ['deepseek-flash', 'glm-flash'],
    tactics: [
      'rfl',
      'simp',
      'norm_num',
      'omega',
      'linarith',
      'nlinarith',
      'ring',
      'aesop',
      'exact?',
      'apply?',
      'library_search',
    ],
  },
};

const leanIdentifierTokens = (source: string): readonly string[] => {
  const tokens: string[] = [];
  for (const match of source.matchAll(/[\p{L}_][\p{L}\p{M}\p{N}_'.]*|[¬∀∃]/gu)) {
    const identifier = match[0]?.toLowerCase();
    if (!identifier) continue;
    tokens.push(identifier);
    for (const component of identifier.split('.')) if (component) tokens.push(component);
  }
  return Object.freeze(tokens);
};

const keywordMatches = (tokens: readonly string[], keyword: string): boolean => {
  const normalized = keyword.toLowerCase();
  if (!/^[\p{L}_][\p{L}\p{M}\p{N}_']*$/u.test(normalized)) {
    return tokens.some((token) => token.includes(normalized));
  }
  return tokens.some(
    (token) =>
      token === normalized || (normalized.length >= 5 && (token.startsWith(normalized) || token.endsWith(normalized)))
  );
};

const tacticStep = (tactic: string, index: number): LeanEvalTacticStep =>
  Object.freeze({
    tactic,
    budgetMs: Math.min(30_000, 2_000 + index * 3_000),
    when:
      index < 2
        ? 'Try on a closed or simplification-friendly goal.'
        : 'Use after the previous rung fails and the goal shape remains compatible.',
  });

export function routeLeanEvalProblem(analysis: LeanEvalProblemAnalysis): LeanEvalRoute {
  const declarationTokens = leanIdentifierTokens(analysis.holes.map((hole) => hole.declarationBody).join(' '));
  const importTokensByModule = analysis.imports.map(leanIdentifierTokens);
  let best: LeanEvalArchetype = 'general';
  let bestScore = 0;
  let bestKeywords: string[] = [];
  for (const archetype of LEAN_EVAL_ARCHETYPES) {
    const keywords = routeTable[archetype].keywords.filter(
      (keyword) =>
        keywordMatches(declarationTokens, keyword) ||
        importTokensByModule.some((tokens) => keywordMatches(tokens, keyword))
    );
    const importBoost = importTokensByModule.filter((tokens) =>
      routeTable[archetype].keywords.some((keyword) => keywordMatches(tokens, keyword))
    ).length;
    // Imports are stronger evidence than declaration identifiers. Exact Lean
    // identifier boundaries prevent String/ring and ModelWithCorners/model
    // collisions from hijacking a specific route.
    const score = keywords.length * 2 + importBoost * 4;
    if (score > bestScore) {
      best = archetype;
      bestScore = score;
      bestKeywords = keywords;
    }
  }
  const table = routeTable[best];
  const confidence = Math.max(0.25, Math.min(0.99, best === 'general' ? 0.3 : 0.4 + bestScore / 20));
  const tacticLadder = table.tactics.map(tacticStep);
  return Object.freeze({
    archetype: best,
    confidence,
    modelPriority: Object.freeze([...table.models]),
    tacticLadder: Object.freeze(tacticLadder),
    premiseQueries: Object.freeze([
      ...bestKeywords.slice(0, 3).map((keyword) => `${keyword} exact theorem`),
      `${best} Mathlib theorem matching the active Lean goal`,
    ]),
    features: Object.freeze({ imports: analysis.imports, keywords: Object.freeze(bestKeywords) }),
  });
}

export function buildLeanEvalTacticLadder(archetype: LeanEvalArchetype = 'general'): readonly LeanEvalTacticStep[] {
  return Object.freeze(routeTable[archetype].tactics.map(tacticStep));
}
