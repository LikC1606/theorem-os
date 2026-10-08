import { z } from 'zod';

/** Shared public contract; mathematical expressions are still parsed by the exact kernel. */
const expression = z.string().min(1).max(8192);
const variable = z
  .string()
  .min(1)
  .max(32)
  .regex(/^(?!theta|constructor|prototype|toString)[A-Za-z][A-Za-z0-9_]*$/u);
const assignment = z.record(z.string(), expression);
export const mathSynthesisInputSchema = z
  .object({
    kind: z.enum(['finite_difference', 'rational_invariant']),
    scalar: z.enum(['real', 'rational']),
    variables: z.array(variable).min(1).max(6),
    basis: z.array(expression).min(1).max(32),
    denominator: expression,
    shift: assignment.optional(),
    rhs: expression.optional(),
    transition: assignment.optional(),
    domain: z.array(expression).max(32).optional(),
    seedSamples: z
      .array(z.record(z.string(), z.string().min(1).max(2400)))
      .max(256)
      .optional(),
    evidenceRefs: z.array(z.string().min(1).max(1024)).max(32).optional(),
    previousResultRef: z.string().min(1).max(1024).optional(),
  })
  .strict()
  .superRefine((value, context) => {
    const issue = (message: string) => context.addIssue({ code: 'custom', message });
    if (new TextEncoder().encode(JSON.stringify(value)).length > 65536) issue('input byte limit');
    if (new Set(value.variables).size !== value.variables.length) issue('duplicate declared variables');
    const exactKeys = (record: Record<string, string>) =>
      Object.keys(record).length === value.variables.length &&
      value.variables.every((name) => Object.hasOwn(record, name));
    const substitutions = value.kind === 'finite_difference' ? value.shift : value.transition;
    if (!substitutions || !exactKeys(substitutions))
      issue('simultaneous substitution must assign every declared variable exactly once');
    if (value.kind === 'finite_difference' && (value.rhs === undefined || value.transition !== undefined))
      issue('finite difference requires rhs and shift');
    if (value.kind === 'rational_invariant' && (value.rhs !== undefined || value.shift !== undefined))
      issue('invariant requires transition only');
    if (value.seedSamples?.some((sample) => !exactKeys(sample)))
      issue('sample must assign exactly the declared variables');
  });
export type MathSynthesisInput = z.infer<typeof mathSynthesisInputSchema>;

/** Each action has one role mapping and description; no wildcard authority is introduced. */
export const mathWorkspaceActions = [
  'describe',
  'preflight',
  'execute',
  'certify',
  'events',
  'probe',
  'search',
  'branches',
  'checkout',
  'check_connection',
  'counterexample',
  'synthesize',
  'refute_route',
  'adopt_package',
  'adopt_packages',
] as const;
type MathWorkspaceRole = 'lead' | 'researcher' | 'formalizer';
export const mathWorkspaceActionContract: Readonly<
  Record<(typeof mathWorkspaceActions)[number], Readonly<{ roles: readonly MathWorkspaceRole[]; description: string }>>
> = Object.freeze({
  describe: {
    roles: ['formalizer'],
    description: 'Describe the current Lean tool contract without executing a proof.',
  },
  preflight: {
    roles: ['formalizer'],
    description: 'Check the fixed project environment without changing proof source.',
  },
  execute: {
    roles: ['formalizer'],
    description: 'Run authorized Lean operations; only kernel-verified receipts establish proof.',
  },
  certify: {
    roles: ['formalizer'],
    description: 'Check committed source once per file and return independent per-declaration receipts.',
  },
  events: { roles: ['formalizer'], description: 'Read saved diagnostics without executing a proof.' },
  probe: {
    roles: ['formalizer'],
    description: 'Check current source or a private auxiliary span. A local probe is not original-target acceptance.',
  },
  search: {
    roles: ['formalizer'],
    description: 'Search an assignment-bound goal. Source adoption requires applyBest and the expected source hash.',
  },
  branches: { roles: ['formalizer'], description: 'Read durable proof alternatives without executing Lean.' },
  checkout: {
    roles: ['formalizer'],
    description: 'Recheck a durable branch against the expected source version before optional adoption.',
  },
  check_connection: {
    roles: ['formalizer'],
    description: 'Check a candidate lemma and its conditional connection; unresolved premises do not prove the parent.',
  },
  counterexample: {
    roles: ['researcher', 'formalizer'],
    description: 'Check explicit bounded samples; absence of a witness is not a proof.',
  },
  synthesize: {
    roles: ['lead', 'researcher', 'formalizer'],
    description:
      'Compute finite_difference or rational_invariant coefficients with exact domain obligations. Worker assignment is host-bound when unique; the Lead must select an assignment. Results are unproved candidates.',
  },
  refute_route: {
    roles: [],
    description: 'Verify an exact negation of an authorized route obligation; this never proves the original target.',
  },
  adopt_package: {
    roles: ['formalizer'],
    description: 'Adopt an eligible exact dependency only in an authorized non-frozen project.',
  },
  adopt_packages: {
    roles: ['formalizer'],
    description: 'Atomically adopt exact dependencies only in an authorized non-frozen project.',
  },
});
export function mathWorkspaceRoleActions(role: MathWorkspaceRole): readonly (typeof mathWorkspaceActions)[number][] {
  return Object.freeze(
    mathWorkspaceActions.filter((action) => mathWorkspaceActionContract[action].roles.includes(role))
  );
}
