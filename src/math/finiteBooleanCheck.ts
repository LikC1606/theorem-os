import { z } from 'zod';
import { canonicalMathJson, mathDigest } from './mathRuntimeIo';

export const FINITE_BOOLEAN_LIMITS = Object.freeze({ variables: 64, freeVariables: 20, clauses: 4096,
  literalsPerClause: 64, literalEvaluations: 20_000_000, witnesses: 64, inputBytes: 1_000_000 });
const variable = z.string().regex(/^[A-Za-z][A-Za-z0-9_]{0,63}$/u);
const literal = z.object({ variable, value: z.boolean() }).strict();
const schema = z.object({ schema: z.literal('theorem-os.finite-boolean-cnf.v1'),
  variables: z.array(variable).max(FINITE_BOOLEAN_LIMITS.variables),
  fixed: z.array(literal).max(FINITE_BOOLEAN_LIMITS.variables).default([]),
  clauses: z.array(z.array(literal).max(FINITE_BOOLEAN_LIMITS.literalsPerClause)).max(FINITE_BOOLEAN_LIMITS.clauses),
}).strict();
export type FiniteBooleanConstraints = z.infer<typeof schema>;
export type FiniteBooleanResult = Readonly<{
  schema: 'theorem-os.finite-boolean-check.v1'; trust: 'advisory'; scope: 'supplied-boolean-cnf-only';
  method: 'exhaustive-enumeration-v1'; inputDigest: string; verdict: 'satisfiable' | 'unsatisfiable' | 'unsupported';
  input: Readonly<FiniteBooleanConstraints>;
  variableCount: number; freeVariableCount: number; constraintCount: number;
  assignmentsPlanned: number; assignmentsChecked: number; satisfyingCount: number | null;
  witnesses: readonly Readonly<Record<string, boolean>>[]; complete: boolean; witnessesComplete: boolean; reason?: string;
}>;

/** A finite replay of supplied data is evidence about those constraints, not a Lean proof. */
export function checkFiniteBooleanConstraints(value: unknown, witnessLimit = 16): FiniteBooleanResult {
  const parsed = schema.safeParse(value);
  if (!parsed.success) throw new Error('math_finite_constraints_invalid: ' + parsed.error.message);
  if (!Number.isSafeInteger(witnessLimit) || witnessLimit < 0 || witnessLimit > FINITE_BOOLEAN_LIMITS.witnesses)
    throw new Error('math_finite_witness_limit_invalid');
  const input = parsed.data, variables = new Set(input.variables);
  if (variables.size !== input.variables.length || new Set(input.fixed.map(item => item.variable)).size !== input.fixed.length ||
      [...input.fixed, ...input.clauses.flat()].some(item => !variables.has(item.variable)))
    throw new Error('math_finite_constraints_invalid: duplicate or undeclared variable');
  const fixed = new Map(input.fixed.map(item => [item.variable, item.value]));
  const free = input.variables.filter(name => !fixed.has(name));
  const assignmentsPlanned = 2 ** free.length;
  const base = { schema: 'theorem-os.finite-boolean-check.v1' as const, trust: 'advisory' as const,
    scope: 'supplied-boolean-cnf-only' as const, method: 'exhaustive-enumeration-v1' as const,
    input, inputDigest: mathDigest(canonicalMathJson(input)), variableCount: input.variables.length,
    freeVariableCount: free.length, constraintCount: input.clauses.length, assignmentsPlanned };
  const literalCount = input.clauses.reduce((count, clause) => count + Math.max(1, clause.length), 0);
  if (free.length > FINITE_BOOLEAN_LIMITS.freeVariables ||
      assignmentsPlanned * literalCount > FINITE_BOOLEAN_LIMITS.literalEvaluations)
    return { ...base, verdict: 'unsupported', assignmentsChecked: 0, satisfyingCount: null, witnesses: [],
      complete: false, witnessesComplete: false, reason: 'enumeration-size-exceeds-declared-limit' };
  const indices = new Map(free.map((name, index) => [name, index]));
  const clauses = input.clauses.map(clause => clause.map(item => ({ index: indices.get(item.variable),
    fixed: fixed.get(item.variable), value: item.value })));
  let satisfyingCount = 0;
  const witnesses: Record<string, boolean>[] = [];
  for (let mask = 0; mask < assignmentsPlanned; mask++) {
    if (!clauses.every(clause => clause.some(item =>
      (item.index === undefined ? item.fixed : Boolean(mask & (1 << item.index))) === item.value))) continue;
    satisfyingCount++;
    if (witnesses.length < witnessLimit) witnesses.push(Object.fromEntries(input.variables.map(name =>
      [name, fixed.has(name) ? fixed.get(name)! : Boolean(mask & (1 << indices.get(name)!))])));
  }
  return { ...base, verdict: satisfyingCount ? 'satisfiable' : 'unsatisfiable', assignmentsChecked: assignmentsPlanned,
    satisfyingCount, witnesses, complete: true, witnessesComplete: witnesses.length === satisfyingCount };
}
