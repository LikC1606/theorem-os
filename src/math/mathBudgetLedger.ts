import fs from 'node:fs';
import path from 'node:path';
import { z } from 'zod';
import { assertMathCanonicalPath, isMathPathWithin } from "./mathRunBinding";
import {
  canonicalMathJson,
  mathDigest,
  readMathJson,
  withMathRuntimeLease,
  writeMathJsonDurable,
} from "./mathRuntimeIo";

export const MATH_RUN_TOKEN_LIMIT = 64_000;
const id = z.string().regex(/^[A-Za-z0-9_-]{1,128}$/u);
const count = z.number().int().nonnegative().safe();
const positive = count.positive();
const policySchema = z
  .object({
    runId: id,
    inputDigest: z.string().regex(/^[a-f0-9]{64}$/u),
    limit: positive.max(MATH_RUN_TOKEN_LIMIT),
    finalReserve: positive,
  })
  .strict()
  .refine((value) => value.finalReserve < value.limit);
export type MathBudgetPolicy = Readonly<z.infer<typeof policySchema>>;
const reservationSchema = z
  .object({
    kind: z.literal('reserve'),
    requestId: id,
    attempt: positive,
    actorId: id,
    inputTokens: count,
    outputTokens: positive,
    itemId: id.optional(),
  })
  .strict();
const usageSchema = z
  .object({
    inputTokens: count,
    outputTokens: count,
    totalTokens: count,
    cachedInputTokens: count.optional(),
    reasoningOutputTokens: count.optional(),
  })
  .strict()
  .refine(
    (value) =>
      Number.isSafeInteger(value.inputTokens + value.outputTokens) &&
      value.totalTokens === value.inputTokens + value.outputTokens &&
      (value.cachedInputTokens ?? 0) <= value.inputTokens &&
      (value.reasoningOutputTokens ?? 0) <= value.outputTokens
  );
const commandSchema = z.discriminatedUnion('kind', [
  reservationSchema,
  z.object({ kind: z.literal('settle'), requestId: id, attempt: positive, usage: usageSchema }).strict(),
  z.object({ kind: z.literal('unknown'), requestId: id, attempt: positive }).strict(),
  z.object({ kind: z.literal('open_item'), itemId: id, firstInputTokens: count }).strict(),
  z.object({ kind: z.literal('finalize') }).strict(),
]);
export type MathBudgetCommand = Readonly<z.infer<typeof commandSchema>>;
export type MathBudgetEntry = Readonly<{
  request: Readonly<z.infer<typeof reservationSchema>>;
  status: 'reserved' | 'unknown' | 'settled';
  usage?: Readonly<z.infer<typeof usageSchema>>;
}>;
type Item = Readonly<{ firstInputTokens: number; allocation: number }>;
const sum = (a: number, b: number): number => {
  if (!Number.isSafeInteger(a + b)) throw new Error('math_budget_integer_overflow');
  return a + b;
};

/** Offline accounting state machine. Only a trusted transport may supply counts or usage. */
export class MathBudgetLedger {
  readonly policy: MathBudgetPolicy;
  readonly #entries = new Map<string, MathBudgetEntry>();
  readonly #items = new Map<string, Item>();
  #finalizing = false;
  #violated = false;

  constructor(policy: MathBudgetPolicy) {
    this.policy = Object.freeze(policySchema.parse(policy));
  }

  private totals(itemId?: string) {
    let settledTokens = 0;
    let reservedTokens = 0;
    let unknownTokens = 0;
    for (const entry of this.#entries.values()) {
      if (itemId !== undefined && entry.request.itemId !== itemId) continue;
      if (entry.usage) settledTokens = sum(settledTokens, entry.usage.totalTokens);
      else {
        const reserved = sum(entry.request.inputTokens, entry.request.outputTokens);
        reservedTokens = sum(reservedTokens, reserved);
        if (entry.status === 'unknown') unknownTokens = sum(unknownTokens, reserved);
      }
    }
    return { settledTokens, reservedTokens, unknownTokens };
  }

  get snapshot() {
    const totals = this.totals();
    return Object.freeze({
      policy: this.policy,
      ...totals,
      remainingTokens: this.policy.limit - sum(totals.settledTokens, totals.reservedTokens),
      finalizing: this.#finalizing,
      controlViolation: this.#violated,
      usageComplete: [...this.#entries.values()].every((entry) => entry.status === 'settled'),
      entries: Object.freeze([...this.#entries.values()]),
      items: Object.freeze(Object.fromEntries(this.#items)),
    });
  }

  apply(value: MathBudgetCommand): void {
    const command = commandSchema.parse(value);
    const state = this.snapshot;
    const available = state.remainingTokens - (this.#finalizing ? 0 : this.policy.finalReserve);
    if (command.kind === 'finalize') {
      if (state.reservedTokens) throw new Error('math_budget_pending_requests');
      this.#finalizing = true;
      return;
    }
    if (command.kind === 'open_item') {
      const existing = this.#items.get(command.itemId);
      if (existing) {
        if (existing.firstInputTokens !== command.firstInputTokens) throw new Error('math_budget_identity_conflict');
        return;
      }
      if (this.#violated || this.#finalizing) throw new Error('math_budget_admission_closed');
      const allocation = Math.max(8000, sum(command.firstInputTokens, 1024));
      if (allocation > available) throw new Error('math_budget_exhausted');
      this.#items.set(command.itemId, Object.freeze({ firstInputTokens: command.firstInputTokens, allocation }));
      return;
    }
    const key = `${command.requestId}:${command.attempt}`;
    const existing = this.#entries.get(key);
    if (command.kind === 'reserve') {
      if (existing) {
        if (canonicalMathJson(existing.request) !== canonicalMathJson(command))
          throw new Error('math_budget_identity_conflict');
        return;
      }
      if (this.#violated) throw new Error('math_budget_admission_closed');
      const reserved = sum(command.inputTokens, command.outputTokens);
      if (reserved > available) throw new Error('math_budget_exhausted');
      if (command.itemId) {
        if (this.#finalizing) throw new Error('math_budget_admission_closed');
        const item = this.#items.get(command.itemId);
        if (!item) throw new Error('math_budget_unknown_item');
        const firstRequest = ![...this.#entries.values()].some((entry) => entry.request.itemId === command.itemId);
        if (firstRequest && (command.inputTokens !== item.firstInputTokens || command.outputTokens < 1024))
          throw new Error('math_budget_item_first_request_mismatch');
        const totals = this.totals(command.itemId);
        if (reserved > item.allocation - sum(totals.settledTokens, totals.reservedTokens))
          throw new Error('math_budget_item_exhausted');
      }
      this.#entries.set(key, Object.freeze({ request: Object.freeze(command), status: 'reserved' }));
      return;
    }
    if (!existing) throw new Error('math_budget_unknown_request');
    if (command.kind === 'unknown') {
      if (existing.status === 'reserved') this.#entries.set(key, Object.freeze({ ...existing, status: 'unknown' }));
      return;
    }
    if (existing.usage) {
      if (canonicalMathJson(existing.usage) !== canonicalMathJson(command.usage))
        throw new Error('math_budget_usage_conflict');
      return;
    }
    const reservation = existing.request;
    // Validate arithmetic before changing state; retain a provider's actual overrun.
    sum(state.settledTokens, command.usage.totalTokens);
    this.#violated ||=
      command.usage.inputTokens > reservation.inputTokens || command.usage.outputTokens > reservation.outputTokens;
    this.#entries.set(key, Object.freeze({ ...existing, status: 'settled', usage: Object.freeze(command.usage) }));
  }
}

const journalSchema = z
  .object({
    schema: z.literal('deepscientist.math.budget-journal.v1'),
    policy: policySchema,
    events: z.array(commandSchema).max(10_000),
  })
  .strict();

/** Private run storage. Admission returns only after fsync under the shared OS lease. */
export class DurableMathBudgetLedger {
  readonly #policy: MathBudgetPolicy;
  readonly #file: string;
  #pending: Promise<void> = Promise.resolve();
  constructor(
    private readonly options: Readonly<{
      directory: string;
      workspace: string;
      policy: MathBudgetPolicy;
      flockExecutable: string;
    }>
  ) {
    this.#policy = Object.freeze(policySchema.parse(options.policy));
    assertMathCanonicalPath(options.directory);
    assertMathCanonicalPath(options.workspace);
    if (
      isMathPathWithin(options.workspace, options.directory) ||
      isMathPathWithin(options.directory, options.workspace)
    )
      throw new Error('math_budget_storage_not_private');
    const stat = fs.lstatSync(options.directory);
    if (!stat.isDirectory() || (stat.mode & 0o777) !== 0o700) throw new Error('math_budget_storage_not_private');
    this.#file = path.join(options.directory, `budget-${mathDigest(this.#policy.runId)}.json`);
  }

  async transact(command?: MathBudgetCommand) {
    return this.enqueue(command, false);
  }

  async initialize() {
    return this.enqueue(undefined, true);
  }

  private enqueue(command: MathBudgetCommand | undefined, initialize: boolean) {
    const snapshot = command === undefined ? undefined : commandSchema.parse(command);
    // Actors in this process share this instance; the OS lease still excludes other processes.
    const operation = this.#pending.then(() => this.execute(snapshot, initialize));
    this.#pending = operation.then(
      () => {},
      () => {}
    );
    return operation;
  }

  private async execute(command: MathBudgetCommand | undefined, initialize: boolean) {
    assertMathCanonicalPath(path.dirname(this.#file));
    if ((fs.lstatSync(path.dirname(this.#file)).mode & 0o777) !== 0o700)
      throw new Error('math_budget_storage_not_private');
    return withMathRuntimeLease(
      { lockPath: `${this.#file}.lock`, flockExecutable: this.options.flockExecutable },
      async (lease) => {
        let events: MathBudgetCommand[] = [];
        let missing = false;
        try {
          const stat = fs.lstatSync(this.#file);
          if (!stat.isFile() || (stat.mode & 0o777) !== 0o600 || stat.size > 16 * 1024 * 1024)
            throw new Error('math_budget_storage_not_private');
          const journal = journalSchema.parse(readMathJson(this.#file));
          if (canonicalMathJson(journal.policy) !== canonicalMathJson(this.#policy))
            throw new Error('math_budget_policy_conflict');
          events = journal.events;
        } catch (error) {
          if (!initialize || (error as NodeJS.ErrnoException).code !== 'ENOENT') throw error;
          missing = true;
        }
        const ledger = new MathBudgetLedger(this.#policy);
        for (const event of events) ledger.apply(event);
        const previous = canonicalMathJson(ledger.snapshot);
        if (command) ledger.apply(command);
        const changed = canonicalMathJson(ledger.snapshot) !== previous;
        if (missing || (command && changed)) {
          if (events.length >= 10_000) throw new Error('math_budget_journal_full');
          lease.assertHeld();
          writeMathJsonDurable(this.#file, {
            schema: 'deepscientist.math.budget-journal.v1',
            policy: this.#policy,
            events: command ? [...events, commandSchema.parse(command)] : events,
          });
        }
        // Replayed or uncertain admissions must not authorize a second network attempt.
        return Object.freeze({ ...ledger.snapshot, admitted: command?.kind === 'reserve' && changed });
      }
    );
  }
}
