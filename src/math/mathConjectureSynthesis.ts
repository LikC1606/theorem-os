import {
  AlgebraBudget,
  ExactAlgebra,
  MathAlgebraError,
  ZERO,
  addR,
  gcd,
  mulR,
  negR,
  parseRational,
  rational,
  rationalText,
  solveLinear,
  type Polynomial,
  type Rational,
  type RationalExpression,
} from "./mathExactAlgebra";

import { mathSynthesisInputSchema, type MathSynthesisInput } from "../common/chat/team/mathToolContract";
export type { MathSynthesisInput } from "../common/chat/team/mathToolContract";

export interface MathSynthesisConstraint {
  sample: Record<string, string>;
  row: string[];
  rhs: string;
  rankBefore: number;
  rankAfter: number;
  rejectedCoefficients?: string[];
}
export interface MathSynthesisResult {
  status: 'candidates' | 'no_candidate_in_scope' | 'unsupported' | 'interrupted';
  reason?: string;
  mathematicalScope: 'identity-equations' | 'sampled-constraints';
  solverReady: false;
  originalTargetAccepted: false;
  candidates: Array<{ expression: string; coefficients: string[]; residualZero: boolean }>;
  domainObligations: string[];
  constraints: MathSynthesisConstraint[];
  skippedSamples: Array<{ sample: Record<string, string>; reason: string }>;
  solutionSpace?: {
    particular: string[];
    nullspace: string[][];
    rank: number;
    rows: number;
    constantDimension?: number;
  };
  operations: number;
}

function invalid(reason: string): never {
  throw new MathAlgebraError('unsupported', reason);
}
export function parseMathSynthesisInput(value: unknown): MathSynthesisInput {
  const parsed = mathSynthesisInputSchema.safeParse(value);
  if (!parsed.success)
    invalid(parsed.error.issues.map((issue) => issue.path.join('.') + ': ' + issue.message).join('; '));
  return parsed.data;
}

/** Coefficient rows of sum theta_i * expressions_i = rhs, with all denominators retained. */
function coefficientSystem(
  algebra: ExactAlgebra,
  expressions: RationalExpression[],
  rhs: RationalExpression
): { rows: Rational[][]; rhs: Rational[] } {
  const all = [...expressions, rhs];
  const numerators = all.map((expr, index) => {
    let p = expr.numerator;
    for (let i = 0; i < all.length; i++) if (i !== index) p = algebra.mul(p, all[i].denominator);
    return p;
  });
  const keys = [...new Set(numerators.flatMap((p) => [...p.keys()]))].toSorted();
  if (keys.length > 4096) invalid('matrix row limit');
  return {
    rows: keys.map((key) => numerators.slice(0, -1).map((p) => p.get(key) ?? ZERO)),
    rhs: keys.map((key) => numerators.at(-1)!.get(key) ?? ZERO),
  };
}

function combination(algebra: ExactAlgebra, basis: RationalExpression[], vector: Rational[]): RationalExpression {
  return basis.reduce(
    (value, term, index) => algebra.plus(value, algebra.times(algebra.number(vector[index]), term)),
    algebra.number(ZERO)
  );
}
function normalize(vector: Rational[], budget: AlgebraBudget): Rational[] {
  let denominator = BigInt(1);
  for (const v of vector) denominator = budget.integer((denominator / gcd(denominator, v.d, budget)) * v.d);
  const integers = vector.map((v) => budget.integer(v.n * (denominator / v.d)));
  let divisor = BigInt(0);
  for (const value of integers) {
    budget.tick();
    divisor = gcd(divisor, value, budget);
  }
  if (!divisor) return vector;
  if (integers.find((v) => v !== BigInt(0))! < BigInt(0)) divisor = -divisor;
  return integers.map((v) => rational(v / divisor, BigInt(1), budget));
}

/** Canonical quotient coordinates eliminate the *whole* constant intersection, not just constant basis vectors. */
function quotientRepresentatives(
  algebra: ExactAlgebra,
  basis: RationalExpression[],
  nullspace: Rational[][]
): { vectors: Rational[][]; dimension: number; constants: Rational[][] } {
  if (!nullspace.length) return { vectors: [], dimension: 0, constants: [] };
  const functions = nullspace.map((v) => combination(algebra, basis, v));
  const rows = algebra.variables.flatMap(
    (_, index) =>
      coefficientSystem(
        algebra,
        functions.map((f) => algebra.differentiate(f, index)),
        algebra.number(ZERO)
      ).rows
  );
  const constantCoordinates = solveLinear(
    rows,
    rows.map(() => ZERO),
    nullspace.length,
    algebra.budget
  ).nullspace;
  const constants = constantCoordinates.map((coords) =>
    nullspace[0].map((_, col) =>
      coords.reduce((total, c, i) => addR(total, mulR(c, nullspace[i][col], algebra.budget), algebra.budget), ZERO)
    )
  );
  // RREF the constant subspace to select a unique representative modulo additive constants.
  const reduced: Array<{ pivot: number; row: Rational[] }> = [];
  const reduce = (v: Rational[]): Rational[] => {
    let out = [...v];
    for (const { pivot, row } of reduced) {
      const scale = out[pivot];
      out = out.map((value, i) => addR(value, negR(mulR(scale, row[i], algebra.budget)), algebra.budget));
    }
    return out;
  };
  for (const constant of constants) {
    const row = reduce(constant),
      pivot = row.findIndex((v) => v.n !== BigInt(0));
    if (pivot < 0) continue;
    const scale = rational(row[pivot].d, row[pivot].n, algebra.budget);
    reduced.push({ pivot, row: row.map((v) => mulR(v, scale, algebra.budget)) });
  }
  const vectors: Rational[][] = [];
  let span = [...constants],
    rank = solveLinear(
      span,
      span.map(() => ZERO),
      basis.length,
      algebra.budget
    ).rank;
  for (const v of nullspace) {
    const nextRank = solveLinear(
      [...span, v],
      [...span, v].map(() => ZERO),
      basis.length,
      algebra.budget
    ).rank;
    if (nextRank > rank) {
      vectors.push(normalize(reduce(v), algebra.budget));
      span.push(v);
      rank = nextRank;
    }
  }
  return { vectors, dimension: constants.length, constants };
}

export function runMathConjectureSynthesis(
  rawInput: unknown,
  options: { deadlineAt?: number; signal?: AbortSignal; maxOperations?: number } = {}
): MathSynthesisResult {
  const budget = new AlgebraBudget(options);
  const result: MathSynthesisResult = {
    status: 'unsupported',
    mathematicalScope: 'identity-equations',
    solverReady: false,
    originalTargetAccepted: false,
    candidates: [],
    domainObligations: [],
    constraints: [],
    skippedSamples: [],
    operations: 0,
  };
  try {
    budget.tick();
    const input = parseMathSynthesisInput(rawInput),
      algebra = new ExactAlgebra(input.variables, budget);
    const denominator = algebra.parse(input.denominator);
    const basis = input.basis.map((source) => algebra.divide(algebra.parse(source), denominator));
    const substitutions = input.variables.map((v) => algebra.parse((input.shift ?? input.transition)![v]));
    const rhs = algebra.parse(input.rhs ?? '0');
    const residuals = basis.map((b) => algebra.minus(algebra.substitute(b, substitutions), b));
    const domain = (input.domain ?? []).map((source) => {
      const match = /^(.*?)(!=|<=|>=|=|<|>)(.*?)$/.exec(source);
      if (!match) invalid('unsupported domain predicate');
      return { expression: algebra.minus(algebra.parse(match[1]), algebra.parse(match[3])), relation: match[2] };
    });
    const allExpressions = [...basis, ...substitutions, rhs, ...residuals, ...domain.map((d) => d.expression)];
    const obligations: Polynomial[] = allExpressions.flatMap((e) => [...e.obligations, e.denominator]);
    result.domainObligations = [
      ...new Set(
        obligations
          .filter((p) => !([...p].length === 1 && [...p][0][0].split(',').every((e) => e === '0')))
          .map((p) => `(${algebra.polynomialText(p)}) != 0`)
      ),
    ];
    const legal = (sample: Record<string, string>): { row: Rational[]; rhs: Rational } | undefined => {
      const values = input.variables.map((v) => parseRational(sample[v], budget));
      if (allExpressions.some((e) => algebra.evaluate(e, values) === undefined)) return undefined;
      for (const condition of domain) {
        const n = algebra.evaluate(condition.expression, values)!.n;
        if (
          !(condition.relation === '='
            ? n === BigInt(0)
            : condition.relation === '!='
              ? n !== BigInt(0)
              : condition.relation === '<'
                ? n < BigInt(0)
                : condition.relation === '<='
                  ? n <= BigInt(0)
                  : condition.relation === '>'
                    ? n > BigInt(0)
                    : n >= BigInt(0))
        )
          return undefined;
      }
      return { row: residuals.map((r) => algebra.evaluate(r, values)!), rhs: algebra.evaluate(rhs, values)! };
    };
    let rows: Rational[][] = [],
      values: Rational[] = [];
    const addSample = (sample: Record<string, string>, rejected?: Rational[]): boolean => {
      const row = legal(sample);
      if (!row) {
        result.skippedSamples.push({ sample, reason: 'outside original denominator or domain conditions' });
        return false;
      }
      const before = solveLinear(rows, values, basis.length, budget).rank;
      rows.push(row.row);
      values.push(row.rhs);
      const after = solveLinear(rows, values, basis.length, budget).rank;
      result.constraints.push({
        sample,
        row: row.row.map(rationalText),
        rhs: rationalText(row.rhs),
        rankBefore: before,
        rankAfter: after,
        ...(rejected ? { rejectedCoefficients: rejected.map(rationalText) } : {}),
      });
      return true;
    };
    if (input.seedSamples !== undefined) {
      result.mathematicalScope = 'sampled-constraints';
      for (const sample of input.seedSamples) addSample(sample);
    } else {
      const system = coefficientSystem(algebra, residuals, rhs);
      rows = system.rows;
      values = system.rhs;
    }
    for (let iteration = 0; iteration <= basis.length + 1; iteration++) {
      const solution = solveLinear(rows, values, basis.length, budget);
      result.solutionSpace = {
        particular: solution.particular.map(rationalText),
        nullspace: solution.nullspace.map((row) => row.map(rationalText)),
        rank: solution.rank,
        rows: rows.length,
      };
      if (solution.inconsistent) {
        result.status = 'no_candidate_in_scope';
        result.reason = 'current coefficient equations inconsistent';
        break;
      }
      let vectors: Rational[][];
      if (input.kind === 'rational_invariant') {
        const quotient = quotientRepresentatives(algebra, basis, solution.nullspace);
        vectors = quotient.vectors;
        result.solutionSpace.constantDimension = quotient.dimension;
      } else {
        let particular = solution.particular;
        const current = combination(algebra, basis, particular),
          zero = input.variables.map(() => ZERO);
        const boundary = algebra.evaluate(current, zero);
        // Remove a free additive constant only after proving that direction is in
        // the homogeneous solution space and state-independent. Preserve scale.
        if (boundary?.n)
          for (const direction of quotientRepresentatives(algebra, basis, solution.nullspace).constants) {
            const constant = combination(algebra, basis, direction);
            if (input.variables.some((_, index) => algebra.differentiate(constant, index).numerator.size !== 0))
              continue;
            const value = algebra.evaluate(constant, zero);
            if (!value?.n) continue;
            const scale = rational(boundary.n * value.d, boundary.d * value.n, budget);
            particular = particular.map((v, i) => addR(v, negR(mulR(scale, direction[i], budget)), budget));
            break;
          }
        vectors = [particular];
      }
      if (!vectors.length) {
        result.status = 'no_candidate_in_scope';
        result.reason = 'no_nonconstant_candidate_in_current_space';
        break;
      }
      const vector = vectors[0],
        candidate = combination(algebra, basis, vector);
      // Reconstruct and substitute the complete candidate independently of coefficient equations.
      const residual = algebra.minus(algebra.minus(algebra.substitute(candidate, substitutions), candidate), rhs);
      result.candidates = [
        {
          expression: algebra.text(candidate),
          coefficients: vector.map(rationalText),
          residualZero: residual.numerator.size === 0,
        },
      ];
      if (
        result.candidates[0].expression.length > 8192 ||
        result.domainObligations.some((condition) => condition.length > 8192)
      )
        invalid('candidate or domain expression byte limit');
      if (!residual.numerator.size) {
        result.status = 'candidates';
        break;
      }
      let witness: Record<string, string> | undefined;
      // A bounded deterministic rational grid, generated lazily (never allocate a Cartesian product).
      const grid = ['1', '2', '3', '1/2', '-1', '0', '-2'];
      for (let index = 0; index < Math.min(256, grid.length ** input.variables.length); index++) {
        budget.tick();
        let code = index;
        const sample = Object.fromEntries(
          input.variables.map((v) => {
            const value = grid[code % grid.length];
            code = Math.floor(code / grid.length);
            return [v, value];
          })
        );
        if (!legal(sample)) continue;
        const value = algebra.evaluate(
          residual,
          input.variables.map((v) => parseRational(sample[v], budget))
        );
        if (value?.n) {
          witness = sample;
          break;
        }
      }
      if (witness && input.seedSamples !== undefined) {
        addSample(witness, vector);
        continue;
      }
      if (input.seedSamples !== undefined && result.mathematicalScope === 'sampled-constraints') {
        const system = coefficientSystem(algebra, residuals, rhs);
        rows = system.rows;
        values = system.rhs;
        result.mathematicalScope = 'identity-equations';
        continue;
      }
      result.status = 'no_candidate_in_scope';
      result.reason = 'candidate remains unproved within current resources';
      break;
    }
    if (result.status === 'unsupported') {
      result.status = 'no_candidate_in_scope';
      result.reason = 'finite refinement limit reached';
    }
  } catch (error) {
    if (!(error instanceof MathAlgebraError)) throw error;
    result.status = error.category;
    result.reason = error.message;
    result.candidates = [];
  }
  result.operations = budget.operations;
  if (JSON.stringify(result).length > 262144)
    return {
      ...result,
      status: 'unsupported',
      reason: 'result byte limit',
      candidates: [],
      constraints: [],
      domainObligations: [],
      solutionSpace: undefined,
    };
  return result;
}
