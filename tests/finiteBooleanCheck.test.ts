import fs from 'node:fs';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import { describe, expect, it } from 'vitest';
import { checkFiniteBooleanConstraints, FINITE_BOOLEAN_LIMITS, type FiniteBooleanConstraints } from '../src/math/finiteBooleanCheck';
import { mathDigest } from '../src/math/mathRuntimeIo';

const constraints = (clauses: FiniteBooleanConstraints['clauses'], variables = ['A']): FiniteBooleanConstraints =>
  ({ schema: 'theorem-os.finite-boolean-cnf.v1', variables, fixed: [], clauses });
const fixture = path.resolve('examples/finite/old-b1-nine-constraints.json');

describe('finite Boolean evidence', () => {
  it('replays exactly the old nine rows, whose geometry holds but whose claimed contradiction has five witnesses', () => {
    const points: Record<string, [number, number]> = { A: [-1, 2], B: [0, 0], C: [0, 2], D: [1, -1], E: [1, 0],
      F: [1, 1], G: [2, -1], H: [2, 0], I: [2, 1], J: [2, 2] };
    const rows = [['E', 1, 'BDFGH'], ['B', 3, 'AFG'], ['F', 3, 'ABGJ'], ['F', 1, 'CEHI'], ['H', 4, 'BCJ'],
      ['I', 1, 'FHJ'], ['G', 1, 'DEH'], ['A', 7, 'DHI'], ['D', 7, 'ACI']] as const;
    const input = JSON.parse(fs.readFileSync(fixture, 'utf8')) as FiniteBooleanConstraints;
    const expected: FiniteBooleanConstraints['clauses'] = [];
    for (const [center, radius, neighbors] of rows) {
      for (const vertex of neighbors) {
        const [a, b] = points[vertex].map((coordinate, index) => coordinate - points[center][index]);
        expect(a * a + a * b + b * b).toBe(radius);
      }
      for (let i = 0; i < neighbors.length; i++) for (let j = i + 1; j < neighbors.length; j++)
        for (let k = j + 1; k < neighbors.length; k++) for (const value of [true, false])
          expected.push([{ variable: center, value }, ...[neighbors[i], neighbors[j], neighbors[k]].map(variable =>
            ({ variable, value: !value }))]);
    }
    expect(input.clauses).toEqual(expected);
    const result = checkFiniteBooleanConstraints(input);
    expect(result).toMatchObject({ verdict: 'satisfiable', trust: 'advisory', scope: 'supplied-boolean-cnf-only',
      assignmentsChecked: 256, satisfyingCount: 5, complete: true, witnessesComplete: true });
    expect(result.input).toEqual(input);
    expect(result.witnesses).toHaveLength(5);
    for (const witness of result.witnesses) {
      expect(Object.keys(witness)).toEqual(input.variables);
      expect(witness.B).toBe(false); expect(witness.E).toBe(true);
      for (const [center, , neighbors] of rows)
        expect([...neighbors].filter(vertex => witness[vertex] !== witness[center]).length).toBeLessThan(3);
    }
  });

  it('distinguishes a complete contradiction, tautology, empty domain and truncated witness output', () => {
    expect(checkFiniteBooleanConstraints(constraints([[{ variable: 'A', value: true }], [{ variable: 'A', value: false }]])))
      .toMatchObject({ verdict: 'unsatisfiable', satisfyingCount: 0, assignmentsChecked: 2, witnesses: [], complete: true });
    expect(checkFiniteBooleanConstraints(constraints([[{ variable: 'A', value: true }, { variable: 'A', value: false }]]), 1))
      .toMatchObject({ satisfyingCount: 2, witnesses: [{ A: false }], complete: true, witnessesComplete: false });
    expect(checkFiniteBooleanConstraints(constraints([], [])))
      .toMatchObject({ satisfyingCount: 1, witnesses: [{}], assignmentsChecked: 1 });
    expect(checkFiniteBooleanConstraints(constraints([[]], [])))
      .toMatchObject({ verdict: 'unsatisfiable', satisfyingCount: 0, assignmentsChecked: 1 });
    expect(checkFiniteBooleanConstraints({ ...constraints([[{ variable: 'A', value: false }]]),
      fixed: [{ variable: 'A', value: false }] })).toMatchObject({ satisfyingCount: 1, freeVariableCount: 0 });
  });

  it('binds changed constraints and fixed assignments to a new digest', () => {
    const input = constraints([[{ variable: 'A', value: true }]]), first = checkFiniteBooleanConstraints(input);
    expect(checkFiniteBooleanConstraints(JSON.parse(JSON.stringify(input)))).toEqual(first);
    expect(checkFiniteBooleanConstraints(constraints([[{ variable: 'A', value: false }]])).inputDigest).not.toBe(first.inputDigest);
    expect(checkFiniteBooleanConstraints({ ...input, fixed: [{ variable: 'A', value: true }] }).inputDigest).not.toBe(first.inputDigest);
  });

  it('rejects malformed data and reports unsupported enumeration as inconclusive', () => {
    for (const input of [constraints([], ['A', 'A']), constraints([[{ variable: 'B', value: true }]]),
      { ...constraints([]), fixed: [{ variable: 'A', value: false }, { variable: 'A', value: true }] },
      { ...constraints([]), code: 'process.exit()' }])
      expect(() => checkFiniteBooleanConstraints(input)).toThrow('math_finite_constraints_invalid');
    expect(checkFiniteBooleanConstraints(constraints([], Array.from({ length: FINITE_BOOLEAN_LIMITS.freeVariables + 1 },
      (_, index) => `X${index}`)))).toMatchObject({ verdict: 'unsupported', complete: false,
      assignmentsChecked: 0, satisfyingCount: null, witnessesComplete: false });
    expect(checkFiniteBooleanConstraints(constraints(Array.from({ length: 128 }, () => [{ variable: 'A', value: true }]),
      Array.from({ length: 20 }, (_, index) => index ? `X${index}` : 'A')))).toMatchObject({ verdict: 'unsupported', complete: false });
  });

  it('exposes reproducible CLI results with raw source identity and no proof acceptance status', () => {
    const result = spawnSync('bun', ['bin/math.ts', 'check-finite', '--input', fixture], { encoding: 'utf8', timeout: 10_000 });
    expect(result.status, result.stderr).toBe(0);
    expect(JSON.parse(result.stdout)).toMatchObject({ satisfyingCount: 5, trust: 'advisory', complete: true,
      sourceDigest: mathDigest(fs.readFileSync(fixture, 'utf8')) });
    const unsupported = spawnSync('bun', ['bin/math.ts', 'check-finite', '--json', JSON.stringify(constraints([],
      Array.from({ length: 21 }, (_, index) => `X${index}`)))], { encoding: 'utf8', timeout: 10_000 });
    expect(unsupported.status).toBe(2); expect(JSON.parse(unsupported.stdout).verdict).toBe('unsupported');
  });
});
