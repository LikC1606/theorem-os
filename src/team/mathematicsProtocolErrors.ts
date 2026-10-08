/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

import type { ProtocolIssue } from "../common/types/team/mathematicsTeam";

const DISPATCH_ISSUES = {
  item: { path: 'assignments[]', code: 'invalid', message: 'Each assignment must be an object.' },
  target: {
    path: 'assignments[].target_slot_id',
    code: 'invalid',
    message: 'Use a valid Worker ID from this Team roster.',
  },
  key: {
    path: 'assignments[].idempotency_key',
    code: 'invalid',
    message: 'Use a non-empty stable ID of at most 128 characters.',
  },
  task: {
    path: 'assignments[].task',
    code: 'invalid',
    message: 'Provide exactly one full assignment or non-empty task without conflicting aliases.',
  },
  base: {
    path: 'assignments[].base_commit',
    code: 'invalid',
    message: 'The task form requires a full 40- or 64-hex Git object ID.',
  },
} as const satisfies Record<string, ProtocolIssue>;

export class MathematicsDispatchValidationError extends Error {
  readonly issues: readonly ProtocolIssue[];

  constructor(fields: ReadonlySet<keyof typeof DISPATCH_ISSUES>) {
    super('Mathematics dispatch has invalid fields. Correct every reported field across the assignment list.');
    this.name = 'MathematicsDispatchValidationError';
    // Static messages and wildcard paths group failures across a wave without
    // reflecting task text, arbitrary keys, filesystem errors, or private values.
    this.issues = Object.freeze(
      (Object.keys(DISPATCH_ISSUES) as (keyof typeof DISPATCH_ISSUES)[])
        .filter((field) => fields.has(field))
        .map((field) => Object.freeze({ ...DISPATCH_ISSUES[field] }))
    );
  }
}

export function collectMathematicsDispatchErrors(
  items: readonly unknown[],
  checks: Readonly<{
    target: (value: unknown) => unknown;
    key: (value: unknown) => unknown;
    task: (item: Record<string, unknown>) => unknown;
    base: (value: unknown) => unknown;
  }>
): void {
  const failures = new Set<keyof typeof DISPATCH_ISSUES>();
  const check = (field: keyof typeof DISPATCH_ISSUES, validate: () => unknown): void => {
    try {
      validate();
    } catch {
      failures.add(field);
    }
  };
  for (const value of items) {
    if (!value || typeof value !== 'object' || Array.isArray(value)) {
      failures.add('item');
      continue;
    }
    const item = value as Record<string, unknown>;
    check('target', () => checks.target(item.targetSlotId));
    check('key', () => checks.key(item.idempotencyKey));
    check('task', () => checks.task(item));
    if (!item.assignment || typeof item.assignment !== 'object' || Array.isArray(item.assignment)) {
      check('base', () => checks.base(item.baseCommit));
    }
  }
  if (failures.size) throw new MathematicsDispatchValidationError(failures);
}
