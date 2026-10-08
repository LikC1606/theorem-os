/** Bounded exact arithmetic. No evaluation of source text or floating point coefficients. */
export class MathAlgebraError extends Error {
  constructor(
    public readonly category: 'unsupported' | 'interrupted',
    message: string
  ) {
    super(message);
  }
}

export class AlgebraBudget {
  operations = 0;
  constructor(readonly options: { deadlineAt?: number; signal?: AbortSignal; maxOperations?: number } = {}) {}
  tick(amount = 1): void {
    this.operations += amount;
    if (
      this.options.signal?.aborted ||
      (this.options.deadlineAt !== undefined && Date.now() >= this.options.deadlineAt)
    )
      throw new MathAlgebraError('interrupted', 'computation cancelled or deadline reached');
    if (this.operations > (this.options.maxOperations ?? 2_000_000))
      throw new MathAlgebraError('unsupported', 'arithmetic operation limit');
  }
  integer(value: bigint): bigint {
    this.tick();
    if (value.toString(2).length > 4096) throw new MathAlgebraError('unsupported', 'rational bit limit');
    return value;
  }
}

export interface Rational {
  n: bigint;
  d: bigint;
}
export const ZERO: Rational = { n: BigInt(0), d: BigInt(1) };
export const ONE: Rational = { n: BigInt(1), d: BigInt(1) };
export function gcd(a: bigint, b: bigint, budget?: AlgebraBudget): bigint {
  a = a < BigInt(0) ? -a : a;
  b = b < BigInt(0) ? -b : b;
  while (b) {
    budget?.tick();
    [a, b] = [b, a % b];
  }
  return a;
}
export function rational(n: bigint, d = BigInt(1), budget = new AlgebraBudget()): Rational {
  budget.integer(n);
  budget.integer(d);
  if (!d) throw new MathAlgebraError('unsupported', 'zero denominator');
  if (!n) return ZERO;
  const g = gcd(n, d, budget) * (d < BigInt(0) ? -BigInt(1) : BigInt(1));
  return { n: n / g, d: d / g };
}
export const rationalText = (v: Rational): string => (v.d === BigInt(1) ? `${v.n}` : `${v.n}/${v.d}`);
export function parseRational(text: string, budget = new AlgebraBudget()): Rational {
  if (!/^[+-]?\d+(?:\/\d+)?$/.test(text) || text.length > 2400)
    throw new MathAlgebraError('unsupported', 'sample must be an exact integer or rational');
  const [n, d] = text.split('/');
  return rational(BigInt(n), d === undefined ? BigInt(1) : BigInt(d), budget);
}
export const addR = (a: Rational, b: Rational, k: AlgebraBudget): Rational =>
  rational(a.n * b.d + b.n * a.d, a.d * b.d, k);
export const mulR = (a: Rational, b: Rational, k: AlgebraBudget): Rational => rational(a.n * b.n, a.d * b.d, k);
export const negR = (a: Rational): Rational => ({ n: -a.n, d: a.d });
export const divR = (a: Rational, b: Rational, k: AlgebraBudget): Rational => rational(a.n * b.d, a.d * b.n, k);

export type Polynomial = Map<string, Rational>;
export interface RationalExpression {
  numerator: Polynomial;
  denominator: Polynomial;
  obligations: Polynomial[];
}
export class ExactAlgebra {
  constructor(
    readonly variables: string[],
    readonly budget = new AlgebraBudget()
  ) {}
  constant(v: Rational): Polynomial {
    return v.n ? new Map([[this.variables.map(() => 0).join(','), v]]) : new Map();
  }
  one(): Polynomial {
    return this.constant(ONE);
  }
  variable(name: string): Polynomial {
    const index = this.variables.indexOf(name);
    if (index < 0) throw new MathAlgebraError('unsupported', `undeclared variable: ${name}`);
    return new Map([[this.variables.map((_, i) => (i === index ? 1 : 0)).join(','), ONE]]);
  }
  add(a: Polynomial, b: Polynomial): Polynomial {
    const out = new Map(a);
    for (const [key, value] of b) {
      const sum = addR(out.get(key) ?? ZERO, value, this.budget);
      if (sum.n) out.set(key, sum);
      else out.delete(key);
    }
    this.check(out);
    return out;
  }
  scale(a: Polynomial, b: Rational): Polynomial {
    return new Map(
      [...a]
        .map(([key, value]) => [key, mulR(value, b, this.budget)])
        .filter(([, value]) => (value as Rational).n !== BigInt(0)) as Array<[string, Rational]>
    );
  }
  sub(a: Polynomial, b: Polynomial): Polynomial {
    return this.add(a, this.scale(b, { n: -BigInt(1), d: BigInt(1) }));
  }
  mul(a: Polynomial, b: Polynomial): Polynomial {
    const out: Polynomial = new Map();
    for (const [ka, va] of a)
      for (const [kb, vb] of b) {
        this.budget.tick();
        const ea = ka.split(',').map(Number),
          eb = kb.split(',').map(Number);
        if (ea.some((exponent, i) => exponent + eb[i] > 256))
          throw new MathAlgebraError('unsupported', 'expanded degree limit');
        const key = ea.map((e, i) => e + eb[i]).join(',');
        const sum = addR(out.get(key) ?? ZERO, mulR(va, vb, this.budget), this.budget);
        if (sum.n) out.set(key, sum);
        else out.delete(key);
        this.check(out);
      }
    return out;
  }
  check(p: Polynomial): void {
    if (p.size > 4096) throw new MathAlgebraError('unsupported', 'sparse polynomial term limit');
  }
  wrap(numerator: Polynomial, denominator = this.one(), obligations: Polynomial[] = []): RationalExpression {
    if (!denominator.size) throw new MathAlgebraError('unsupported', 'zero polynomial denominator');
    const unique = new Map<string, Polynomial>();
    for (const obligation of obligations) {
      this.budget.tick();
      const key = this.polynomialText(obligation);
      unique.set(key, obligation);
      if (unique.size > 512) throw new MathAlgebraError('unsupported', 'definition domain obligation limit');
    }
    return { numerator, denominator, obligations: [...unique.values()] };
  }
  number(v: Rational): RationalExpression {
    return this.wrap(this.constant(v));
  }
  plus(a: RationalExpression, b: RationalExpression): RationalExpression {
    if (this.polynomialText(a.denominator) === this.polynomialText(b.denominator))
      return this.wrap(this.add(a.numerator, b.numerator), a.denominator, [...a.obligations, ...b.obligations]);
    return this.wrap(
      this.add(this.mul(a.numerator, b.denominator), this.mul(b.numerator, a.denominator)),
      this.mul(a.denominator, b.denominator),
      [...a.obligations, ...b.obligations]
    );
  }
  minus(a: RationalExpression, b: RationalExpression): RationalExpression {
    return this.plus(a, { ...b, numerator: this.scale(b.numerator, { n: -BigInt(1), d: BigInt(1) }) });
  }
  times(a: RationalExpression, b: RationalExpression): RationalExpression {
    return this.wrap(this.mul(a.numerator, b.numerator), this.mul(a.denominator, b.denominator), [
      ...a.obligations,
      ...b.obligations,
    ]);
  }
  divide(a: RationalExpression, b: RationalExpression): RationalExpression {
    return this.wrap(this.mul(a.numerator, b.denominator), this.mul(a.denominator, b.numerator), [
      ...a.obligations,
      ...b.obligations,
      b.numerator,
    ]);
  }
  power(a: RationalExpression, exponent: number): RationalExpression {
    let out = this.number(ONE),
      base = a,
      n = exponent;
    while (n) {
      this.budget.tick();
      if (n % 2) out = this.times(out, base);
      n = Math.floor(n / 2);
      if (n) base = this.times(base, base);
    }
    return { ...out, obligations: [...out.obligations, ...a.obligations] };
  }
  derivative(p: Polynomial, index: number): Polynomial {
    const out: Polynomial = new Map();
    for (const [key, value] of p) {
      const exp = key.split(',').map(Number);
      if (exp[index]) {
        const multiplier = exp[index]--;
        out.set(exp.join(','), mulR(value, rational(BigInt(multiplier)), this.budget));
      }
    }
    return out;
  }
  differentiate(a: RationalExpression, index: number): RationalExpression {
    return this.wrap(
      this.sub(
        this.mul(this.derivative(a.numerator, index), a.denominator),
        this.mul(a.numerator, this.derivative(a.denominator, index))
      ),
      this.mul(a.denominator, a.denominator),
      a.obligations
    );
  }
  substitutePolynomial(p: Polynomial, substitutions: RationalExpression[]): RationalExpression {
    let result = this.number(ZERO);
    for (const [key, value] of p) {
      let term = this.number(value);
      const exp = key.split(',').map(Number);
      for (let i = 0; i < exp.length; i++) if (exp[i]) term = this.times(term, this.power(substitutions[i], exp[i]));
      result = this.plus(result, term);
    }
    return result;
  }
  substitute(a: RationalExpression, substitutions: RationalExpression[]): RationalExpression {
    const result = this.divide(
      this.substitutePolynomial(a.numerator, substitutions),
      this.substitutePolynomial(a.denominator, substitutions)
    );
    for (const p of a.obligations) {
      const condition = this.substitutePolynomial(p, substitutions);
      result.obligations.push(...condition.obligations, condition.numerator);
      if (result.obligations.length > 4096)
        throw new MathAlgebraError('unsupported', 'substituted domain obligation limit');
    }
    result.obligations.push(...substitutions.flatMap((s) => s.obligations));
    return this.wrap(result.numerator, result.denominator, result.obligations);
  }
  evaluatePolynomial(p: Polynomial, values: Rational[]): Rational {
    let result = ZERO;
    for (const [key, value] of p) {
      let term = value;
      for (const [i, exponent] of key.split(',').map(Number).entries())
        for (let n = 0; n < exponent; n++) term = mulR(term, values[i], this.budget);
      result = addR(result, term, this.budget);
    }
    return result;
  }
  evaluate(a: RationalExpression, values: Rational[]): Rational | undefined {
    for (const condition of a.obligations) if (!this.evaluatePolynomial(condition, values).n) return undefined;
    const denominator = this.evaluatePolynomial(a.denominator, values);
    if (!denominator.n) return undefined;
    return divR(this.evaluatePolynomial(a.numerator, values), denominator, this.budget);
  }
  polynomialText(p: Polynomial): string {
    if (!p.size) return '0';
    return [...p]
      .toSorted(([a], [b]) => a.localeCompare(b))
      .map(([key, value]) => {
        const factors = key
          .split(',')
          .map(Number)
          .flatMap((power, i) => (power ? [power === 1 ? this.variables[i] : `${this.variables[i]}^${power}`] : []));
        return [`(${rationalText(value)})`, ...factors].join('*');
      })
      .join('+');
  }
  text(a: RationalExpression): string {
    return `(${this.polynomialText(a.numerator)})/(${this.polynomialText(a.denominator)})`;
  }
  parse(source: string): RationalExpression {
    if (typeof source !== 'string' || source.length > 8192)
      throw new MathAlgebraError('unsupported', 'expression byte limit');
    const tokens = source.match(/[A-Za-z_][A-Za-z_0-9]*|\d+|[()+\-*/^]|\S/g) ?? [];
    let pos = 0,
      nodes = 0;
    const enter = (depth: number): void => {
      this.budget.tick();
      if (++nodes > 2048 || depth > 64) throw new MathAlgebraError('unsupported', 'expression AST limit');
    };
    const atom = (depth: number): RationalExpression => {
      enter(depth);
      const token = tokens[pos++];
      if (token === '(') {
        const value = sum(depth + 1);
        if (tokens[pos++] !== ')') throw new MathAlgebraError('unsupported', 'missing closing parenthesis');
        return value;
      }
      if (/^\d+$/.test(token ?? '')) {
        if (token.length > 1200) throw new MathAlgebraError('unsupported', 'integer literal limit');
        return this.number(rational(BigInt(token), BigInt(1), this.budget));
      }
      if (this.variables.includes(token)) return this.wrap(this.variable(token));
      throw new MathAlgebraError('unsupported', `unsupported token: ${token ?? '<end>'}`);
    };
    const power = (depth: number): RationalExpression => {
      let value = atom(depth + 1);
      if (tokens[pos] === '^') {
        pos++;
        const token = tokens[pos++];
        if (!/^\d{1,2}$/.test(token ?? '') || Number(token) > 16)
          throw new MathAlgebraError('unsupported', 'power must be a literal integer from 0 through 16');
        value = this.power(value, Number(token));
      }
      return value;
    };
    const unary = (depth: number): RationalExpression => {
      enter(depth);
      if (tokens[pos] === '+' || tokens[pos] === '-') {
        const sign = tokens[pos++];
        const value = unary(depth + 1);
        return sign === '-' ? this.minus(this.number(ZERO), value) : value;
      }
      return power(depth + 1);
    };
    const product = (depth: number): RationalExpression => {
      let value = unary(depth + 1);
      while (tokens[pos] === '*' || tokens[pos] === '/') {
        const op = tokens[pos++],
          right = unary(depth + 1);
        value = op === '*' ? this.times(value, right) : this.divide(value, right);
      }
      return value;
    };
    const sum = (depth: number): RationalExpression => {
      let value = product(depth + 1);
      while (tokens[pos] === '+' || tokens[pos] === '-') {
        const op = tokens[pos++],
          right = product(depth + 1);
        value = op === '+' ? this.plus(value, right) : this.minus(value, right);
      }
      return value;
    };
    const result = sum(0);
    if (pos !== tokens.length) throw new MathAlgebraError('unsupported', `unexpected token: ${tokens[pos]}`);
    return result;
  }
}

export interface LinearSolution {
  rank: number;
  particular: Rational[];
  nullspace: Rational[][];
  inconsistent: boolean;
}

/** Re-parse the restricted arithmetic language before emitting any Lean source. */
export function printMathExpressionLean(source: string, variables: string[], scalar: 'real' | 'rational'): string {
  if (
    !variables.length ||
    variables.length > 6 ||
    variables.some((v) => !/^[A-Za-z][A-Za-z0-9_]*$/.test(v)) ||
    (scalar !== 'real' && scalar !== 'rational')
  )
    throw new MathAlgebraError('unsupported', 'invalid Lean expression context');
  const algebra = new ExactAlgebra(variables),
    expression = algebra.parse(source),
    type = scalar === 'real' ? 'ℝ' : 'ℚ';
  const polynomial = (value: Polynomial): string => {
    if (!value.size) return `(0 : ${type})`;
    return `(${[...value]
      .map(([key, coefficient]) => {
        const number =
          coefficient.d === BigInt(1)
            ? `(${coefficient.n} : ${type})`
            : `((${coefficient.n} : ${type}) / (${coefficient.d} : ${type}))`;
        const factors = key
          .split(',')
          .map(Number)
          .flatMap((power, i) => (power ? [power === 1 ? `«${variables[i]}»` : `(«${variables[i]}» ^ ${power})`] : []));
        return `(${[number, ...factors].join(' * ')})`;
      })
      .join(' + ')})`;
  };
  return `(${polynomial(expression.numerator)} / ${polynomial(expression.denominator)})`;
}

export function printMathDomainLean(source: string, variables: string[], scalar: 'real' | 'rational'): string {
  const match = /^(.*?)(!=|<=|>=|=|<|>)(.*?)$/.exec(source);
  if (!match) throw new MathAlgebraError('unsupported', 'unsupported domain predicate');
  const relation = ({ '!=': '≠', '<=': '≤', '>=': '≥' } as Record<string, string>)[match[2]] ?? match[2];
  return `(${printMathExpressionLean(match[1], variables, scalar)} ${relation} ${printMathExpressionLean(match[3], variables, scalar)})`;
}

export function solveLinear(
  rows: Rational[][],
  rhs: Rational[],
  columns: number,
  budget = new AlgebraBudget()
): LinearSolution {
  if (columns > 32 || rows.length > 4096 || rows.some((r) => r.length !== columns) || rhs.length !== rows.length)
    throw new MathAlgebraError('unsupported', 'matrix dimensions outside scope');
  const matrix = rows.map((r, i) => [...r, rhs[i]]),
    pivots: number[] = [];
  for (let col = 0; col < columns && pivots.length < matrix.length; col++) {
    budget.tick();
    const index = matrix.findIndex((r, i) => i >= pivots.length && r[col].n !== BigInt(0));
    if (index < 0) continue;
    const target = pivots.length;
    [matrix[index], matrix[target]] = [matrix[target], matrix[index]];
    const scale = matrix[target][col];
    matrix[target] = matrix[target].map((v) => divR(v, scale, budget));
    for (let i = 0; i < matrix.length; i++)
      if (i !== target && matrix[i][col].n) {
        const factor = matrix[i][col];
        matrix[i] = matrix[i].map((v, j) => addR(v, negR(mulR(factor, matrix[target][j], budget)), budget));
      }
    pivots.push(col);
  }
  const particular = Array.from({ length: columns }, () => ZERO);
  pivots.forEach((col, i) => {
    particular[col] = matrix[i][columns];
  });
  const nullspace: Rational[][] = [];
  for (let col = 0; col < columns; col++)
    if (!pivots.includes(col)) {
      const v = Array.from({ length: columns }, () => ZERO);
      v[col] = ONE;
      pivots.forEach((pivot, i) => {
        v[pivot] = negR(matrix[i][col]);
      });
      nullspace.push(v);
    }
  return {
    rank: pivots.length,
    particular,
    nullspace,
    inconsistent: matrix.some((row) => row.slice(0, columns).every((v) => !v.n) && row[columns].n !== BigInt(0)),
  };
}
