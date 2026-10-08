import { startMathBudgetBroker, type MathBudgetBrokerBinding, type MathBudgetBrokerHandle } from "./mathBudgetBroker";
import type { DurableMathBudgetLedger } from "./mathBudgetLedger";
type BrokerOptions = {
  socketPath: string;
  secret: string;
  binding: MathBudgetBrokerBinding;
  ledger: DurableMathBudgetLedger;
  countInput: (
    request: Readonly<{ url: string; body: Readonly<Record<string, unknown>>; signal: AbortSignal }>
  ) => Promise<number>;
  onReject?: (code: string) => void;
};
type BrokerFactory = (options: BrokerOptions) => Promise<MathBudgetBrokerHandle>;
type Entry = {
  actorId: string;
  start: Promise<MathBudgetBrokerHandle>;
  broker?: MathBudgetBrokerHandle;
  closing?: Promise<void>;
  closed: boolean;
};
type Run = { inputDigest: string; ledger: DurableMathBudgetLedger; actors: Map<string, Entry>; closing: boolean };
export class MathBudgetBrokerRegistry {
  readonly #runs = new Map<string, Run>();
  readonly #start: BrokerFactory;
  #closingAll = false;
  constructor(start: BrokerFactory = startMathBudgetBroker) {
    this.#start = start;
  }
  async open(options: BrokerOptions): Promise<MathBudgetBrokerHandle> {
    if (this.#closingAll) throw new Error('math_budget_registry_closed');
    const binding = { ...options.binding };
    let run = this.#runs.get(binding.runId);
    if (run?.closing) throw new Error('math_budget_run_closing');
    if (run && (run.inputDigest !== binding.inputDigest || run.ledger !== options.ledger))
      throw new Error('math_budget_run_identity_mismatch');
    if (!run) {
      run = { inputDigest: binding.inputDigest, ledger: options.ledger, actors: new Map(), closing: false };
      this.#runs.set(binding.runId, run);
    }
    if (run.actors.has(binding.actorId)) throw new Error('math_budget_actor_already_open');
    const entry = { actorId: binding.actorId, closed: false } as Entry;
    run.actors.set(binding.actorId, entry);
    const startOptions = { ...options, binding };
    entry.start = Promise.resolve()
      .then(() => this.#start(startOptions))
      .then((broker) => {
        entry.broker = broker;
        return broker;
      })
      .catch((error) => {
        run!.actors.delete(binding.actorId);
        if (run!.actors.size === 0 && !run!.closing) this.#runs.delete(binding.runId);
        throw error;
      });
    const broker = await entry.start;
    if (entry.closed || run.closing || this.#closingAll) {
      await this.#closeEntry(binding.runId, binding.actorId, entry);
      throw new Error('math_budget_run_closing');
    }
    return {
      getLaunchEnvironment: () => {
        if (entry.closed) throw new Error('math_budget_broker_closed');
        return broker.getLaunchEnvironment();
      },
      close: () => this.#closeEntry(binding.runId, binding.actorId, entry),
    };
  }
  get(runId: string, actorId?: string): MathBudgetBrokerHandle | undefined {
    const run = this.#runs.get(runId);
    if (!run) return undefined;
    const entry = actorId
      ? run.actors.get(actorId)
      : run.actors.size === 1
        ? run.actors.values().next().value
        : undefined;
    if (!entry || entry.closed || !entry.broker) return undefined;
    return {
      getLaunchEnvironment: () => {
        if (entry.closed) throw new Error('math_budget_broker_closed');
        return entry.broker!.getLaunchEnvironment();
      },
      close: () => this.#closeEntry(runId, entry.actorId, entry),
    };
  }
  async close(runId: string): Promise<void> {
    const run = this.#runs.get(runId);
    if (!run) return;
    run.closing = true;
    const results = await Promise.allSettled(
      [...run.actors.values()].map((entry) => this.#closeEntry(runId, entry.actorId, entry))
    );
    if (run.actors.size === 0 && this.#runs.get(runId) === run) this.#runs.delete(runId);
    const failure = results.find((r): r is PromiseRejectedResult => r.status === 'rejected');
    if (failure) throw failure.reason;
  }
  async closeAll(): Promise<void> {
    this.#closingAll = true;
    const results = await Promise.allSettled([...this.#runs.keys()].map((runId) => this.close(runId)));
    const failure = results.find((r): r is PromiseRejectedResult => r.status === 'rejected');
    if (failure) throw failure.reason;
  }
  get size(): number {
    return this.#runs.size;
  }
  #closeEntry(runId: string, actorId: string, entry: Entry): Promise<void> {
    if (entry.closing) return entry.closing;
    entry.closed = true;
    entry.closing = entry.start
      .then(async (broker) => {
        await broker.close();
        const run = this.#runs.get(runId);
        if (run?.actors.get(actorId) === entry) {
          run.actors.delete(actorId);
          if (run.actors.size === 0) this.#runs.delete(runId);
        }
      })
      .catch((error) => {
        entry.closing = undefined;
        throw error;
      });
    return entry.closing;
  }
}
