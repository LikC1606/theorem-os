import { describe, expect, it } from 'vitest';
import {
  ExactAlgebra,
  addR,
  mulR,
  parseRational,
  rationalText,
  ZERO,
} from '../src/math/mathExactAlgebra';
import {
  runMathConjectureSynthesis,
  type MathSynthesisInput,
} from '../src/math/mathConjectureSynthesis';

const difference = (rhs = 'n^2'): MathSynthesisInput => ({
  kind: 'finite_difference',
  scalar: 'rational',
  variables: ['n'],
  basis: ['1', 'n', 'n^2', 'n^3'],
  denominator: '1',
  shift: { n: 'n+1' },
  rhs,
});
const invariant = (a = 1): MathSynthesisInput => ({
  kind: 'rational_invariant',
  scalar: 'real',
  variables: ['x', 'y'],
  basis: ['1', 'x', 'y', 'x^2', 'x*y', 'y^2'],
  denominator: 'x*y',
  transition: { x: 'y', y: `(${a}+y^2)/x` },
  domain: ['x>0', 'y>0'],
});

describe('math conjecture synthesis', () => {
  it.each([
    ['n^2', ['0', '1/6', '-1/2', '1/3']],
    ['n', ['0', '-1/2', '1/2', '0']],
    ['n^2+2*n', ['0', '-5/6', '1/2', '1/3']],
  ])('computes unknown difference coefficients for %s', (rhs, coefficients) => {
    const result = runMathConjectureSynthesis(difference(rhs as string));
    expect(result.status).toBe('candidates');
    expect(result.candidates[0]).toMatchObject({ coefficients, residualZero: true });
    expect(result.originalTargetAccepted).toBe(false);
  });
  it('reports scope failure for insufficient degree without widening family', () => {
    expect(runMathConjectureSynthesis({ ...difference(), basis: ['1', 'n', 'n^2'] })).toMatchObject({
      status: 'no_candidate_in_scope',
      reason: 'current coefficient equations inconsistent',
    });
  });
  it('removes a free additive constant after an invertible basis change without rescaling', () => {
    const input = { ...difference(), basis: ['n^3+7', '1+n', 'n^2+1', 'n-1'] };
    const result = runMathConjectureSynthesis(input),
      algebra = new ExactAlgebra(['n']);
    expect(result.status, result.reason).toBe('candidates');
    expect(rationalText(algebra.evaluate(algebra.parse(result.candidates[0].expression), [parseRational('0')])!)).toBe(
      '0'
    );
    expect(result.candidates[0].residualZero).toBe(true);
  });
  it.each([1, 2, 3])('computes changing rational invariants at a=%s', (a) => {
    const result = runMathConjectureSynthesis(invariant(a));
    expect(result.status, result.reason).toBe('candidates');
    expect(result.candidates[0]).toMatchObject({
      coefficients: [String(a), '0', '0', '1', '0', '1'],
      residualZero: true,
    });
    expect(result.domainObligations.length).toBeGreaterThan(0);
  });
  it('uses computed counterexamples as rows excluding previous candidates', () => {
    const result = runMathConjectureSynthesis({ ...invariant(), seedSamples: [] });
    expect(result.status, result.reason).toBe('candidates');
    const updates = result.constraints.filter((row) => row.rejectedCoefficients);
    expect(updates.length).toBeGreaterThan(0);
    for (const update of updates) {
      const algebra = new ExactAlgebra(['x']);
      const sum = update.row.reduce(
        (value, coefficient, i) =>
          addR(
            value,
            mulR(parseRational(coefficient), parseRational(update.rejectedCoefficients![i]), algebra.budget),
            algebra.budget
          ),
        ZERO
      );
      expect(rationalText(sum)).not.toBe(update.rhs);
      expect(update.rankAfter).toBeGreaterThan(update.rankBefore);
    }
  });
  it('computes quotient by constant subspace for a mixed basis', () => {
    const input = invariant();
    const result = runMathConjectureSynthesis({ ...input, basis: ['1+x*y', 'x', 'y', 'x^2+x*y', '1-x*y', 'y^2'] });
    expect(result.status, result.reason).toBe('candidates');
    expect(result.candidates[0].residualZero).toBe(true);
    expect(result.solutionSpace?.constantDimension).toBe(1);
  });
  it('gets the same nonconstant function modulo constants under invertible mixed bases', () => {
    const ordinary = runMathConjectureSynthesis(invariant()),
      transformed = runMathConjectureSynthesis({
        ...invariant(),
        basis: ['1+x*y', 'x', 'y', 'x^2+x*y', '1-x*y', 'y^2'],
      });
    const algebra = new ExactAlgebra(['x', 'y']);
    const left = algebra.parse(ordinary.candidates[0].expression),
      right = algebra.parse(transformed.candidates[0].expression);
    const ratio = algebra.divide(algebra.differentiate(left, 0), algebra.differentiate(right, 0));
    expect(algebra.differentiate(ratio, 0).numerator.size).toBe(0);
    expect(algebra.differentiate(ratio, 1).numerator.size).toBe(0);
    expect(algebra.differentiate(algebra.minus(left, algebra.times(ratio, right)), 1).numerator.size).toBe(0);
  });
  it('retains conditional domain even for an identity whose original division was cancelled', () => {
    const result = runMathConjectureSynthesis({
      ...difference('0'),
      basis: ['(n-1)/(n-1)'],
      seedSamples: [{ n: '1' }],
    });
    expect(result.skippedSamples).toHaveLength(1);
    expect(result.domainObligations.length).toBeGreaterThan(0);
    expect(result.solverReady).toBe(false);
  });
  it('does not elevate sample success on a restricted algebraic subset to an identity', () => {
    const result = runMathConjectureSynthesis({
      ...difference('n^2'),
      basis: ['n'],
      domain: ['n=0'],
      seedSamples: [{ n: '0' }],
    });
    expect(result.status).toBe('no_candidate_in_scope');
    expect(result.reason).toBe('current coefficient equations inconsistent');
  });
  it('independent residual rejects mutated coefficients', () => {
    const input = difference(),
      result = runMathConjectureSynthesis(input),
      algebra = new ExactAlgebra(['n']);
    const changed = [...result.candidates[0].coefficients];
    changed[2] = '1';
    const source = changed.map((c, i) => `(${c})*(${input.basis[i]})`).join('+');
    const expression = algebra.parse(source),
      residual = algebra.minus(
        algebra.minus(algebra.substitute(expression, [algebra.parse('n+1')]), expression),
        algebra.parse('n^2')
      );
    expect(residual.numerator.size).toBeGreaterThan(0);
  });
  it('does not treat constant-only solutions as mathematical discovery', () => {
    expect(runMathConjectureSynthesis({ ...invariant(), basis: ['x*y', '2*x*y'] })).toMatchObject({
      status: 'no_candidate_in_scope',
      reason: 'no_nonconstant_candidate_in_current_space',
    });
  });
  it('skips forbidden denominator points and duplicate witnesses do not inflate rank', () => {
    const result = runMathConjectureSynthesis({
      ...invariant(),
      seedSamples: [
        { x: '0', y: '1' },
        { x: '1', y: '1' },
        { x: '1', y: '1' },
      ],
    });
    expect(result.skippedSamples).toHaveLength(1);
    expect(result.constraints[1].rankAfter).toBe(result.constraints[1].rankBefore);
    expect(result.candidates[0].residualZero).toBe(true);
  });
  it('recomputes samples after variable renaming and basis reordering', () => {
    const result = runMathConjectureSynthesis({
      ...invariant(2),
      variables: ['v', 'u'],
      basis: ['u^2', 'u*v', 'v^2', 'u', 'v', '1'],
      denominator: 'u*v',
      transition: { v: 'u', u: '(2+u^2)/v' },
      domain: ['v>0', 'u>0'],
      seedSamples: [{ v: '1', u: '1' }],
    });
    expect(result.status, result.reason).toBe('candidates');
    expect(result.candidates[0]).toMatchObject({ coefficients: ['1', '0', '1', '0', '0', '2'], residualZero: true });
  });
  it.each([
    { scalar: 'natural' },
    { denominator: 'theta' },
    { basis: ['f(n)'] },
    { verified: true },
    { domain: ['∀ x, x>0'] },
  ])('rejects unsupported semantics or injected protocol %j', (patch) => {
    expect(runMathConjectureSynthesis({ ...difference(), ...patch }).status).toBe('unsupported');
  });
  it('keeps unsupported resource limits distinct from refutation and cancellation', () => {
    expect(runMathConjectureSynthesis(invariant(), { maxOperations: 10 }).status).toBe('unsupported');
    expect(runMathConjectureSynthesis(invariant(), { deadlineAt: 1 }).status).toBe('interrupted');
  });
});
