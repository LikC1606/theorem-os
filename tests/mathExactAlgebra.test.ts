import { describe, expect, it } from 'vitest';
import {
  AlgebraBudget,
  ExactAlgebra,
  parseRational,
  printMathExpressionLean,
  rationalText,
  solveLinear,
} from '../src/math/mathExactAlgebra';

describe('bounded exact algebra', () => {
  it('keeps large rational arithmetic exact and unary minus below powers', () => {
    const a = new ExactAlgebra(['x']);
    expect(rationalText(a.evaluate(a.parse('-x^2 + 9007199254740993/3'), [parseRational('2')])!)).toBe(
      '3002399751580327'
    );
  });
  it.each(['x.foo', 'f(x)', 'x^2^3', 'x^-1', '1.2', 'theta*x', 'x=1', '(x+1)/(x-x)'])(
    'rejects %s without executing input',
    (source) => {
      expect(() => new ExactAlgebra(['x']).parse(source)).toThrow();
    }
  );
  it('preserves cancelled denominator domains', () => {
    const a = new ExactAlgebra(['x']);
    expect(a.evaluate(a.parse('(x^2-1)/(x-1)'), [parseRational('1')])).toBeUndefined();
    expect(a.evaluate(a.parse('(1/x)^0'), [parseRational('0')])).toBeUndefined();
  });
  it('substitutes all variables simultaneously', () => {
    const a = new ExactAlgebra(['x', 'y']);
    expect(
      rationalText(
        a.evaluate(a.substitute(a.parse('x+y'), [a.parse('y'), a.parse('(1+y^2)/x')]), [
          parseRational('2'),
          parseRational('3'),
        ])!
      )
    ).toBe('8');
  });
  it('solves deficient and inconsistent exact systems', () => {
    const rows = [
      ['1', '1'],
      ['2', '2'],
      ['0', '0'],
    ].map((row) => row.map((x) => parseRational(x)));
    const solution = solveLinear(
      rows,
      ['3', '6', '0'].map((x) => parseRational(x)),
      2
    );
    expect({
      rank: solution.rank,
      particular: solution.particular.map(rationalText),
      nullspace: solution.nullspace.map((r) => r.map(rationalText)),
    }).toEqual({ rank: 1, particular: ['3', '0'], nullspace: [['-1', '1']] });
    expect(
      solveLinear(
        rows,
        ['3', '7', '0'].map((x) => parseRational(x)),
        2
      ).inconsistent
    ).toBe(true);
  });
  it('enforces budget in multiplication and rejects cancelled work', () => {
    expect(() => new ExactAlgebra(['x'], new AlgebraBudget({ maxOperations: 20 })).parse('(1+x)^16')).toThrow('limit');
    expect(() => new ExactAlgebra(['x'], new AlgebraBudget({ signal: AbortSignal.abort() })).parse('x')).toThrow(
      'cancelled'
    );
  });
  it('bounds expanded exponents and exact integer bit growth', () => {
    expect(() => new ExactAlgebra(['x']).parse('((x^16)^16)^16')).toThrow('degree limit');
    expect(() => new ExactAlgebra(['x']).parse(`(${'9'.repeat(800)})^2`)).toThrow('bit limit');
  });
  it('prints only parsed arithmetic with explicit scalar types', () => {
    expect(printMathExpressionLean('-x^2+1/3', ['x'], 'rational')).toContain('ℚ');
    expect(() => printMathExpressionLean('by sorry', ['x'], 'real')).toThrow();
    expect(() => printMathExpressionLean('1', ['x» := by sorry'], 'real')).toThrow();
  });
});
