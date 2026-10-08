import type { ResearchTeamCoreEvent, ResearchTeamEventStream } from "./coreTeamEvents";

const TERMINAL_EVENTS = new Set([
  'team.runCompleted',
  'team.runFailed',
  'team.runCancelled',
  'team.childTurnCompleted',
  'team.childTurnFailed',
  'team.childTurnCancelled',
]);

const isTerminalSessionEvent = (event: ResearchTeamCoreEvent): boolean =>
  event.name === 'team.sessionStatusChanged' && ['failed', 'stopped'].includes(String(event.data.status).toLowerCase());

/** Attach before sending the initial message so immediate completions cannot be lost. */
export class ResearchTeamEventWaiter<T> {
  private pendingVersion = 0;
  private processedVersion = 0;
  private armed = false;
  private running = false;
  private closed = false;
  private heartbeatTimer?: ReturnType<typeof setInterval>;
  private pollTimer?: ReturnType<typeof setInterval>;
  private readonly seen = new Set<string>();
  private readonly unsubscribe: readonly (() => void)[];
  private readonly outcome: Promise<T>;
  private resolve!: (result: T) => void;
  private reject!: (error: unknown) => void;

  constructor(
    private readonly options: Readonly<{
      stream: ResearchTeamEventStream;
      reconcile: () => Promise<T | undefined>;
      observe?: (event: ResearchTeamCoreEvent) => void;
      startupOnly?: boolean;
      /** Reconcile periodically while a model turn is still active. */
      heartbeatMs?: number;
      signal?: AbortSignal;
      /** Optional durable reconciliation cadence for runtimes that omit idle events. */
      pollIntervalMs?: number;
    }>
  ) {
    this.outcome = new Promise<T>((resolve, reject) => {
      this.resolve = resolve;
      this.reject = reject;
    });
    // Failures before the caller awaits wait() are retained without an unhandled rejection.
    void this.outcome.catch(() => {});
    this.unsubscribe = [
      options.stream.subscribe((event) => this.event(event)),
      options.stream.subscribeInvalidation(() => this.wake()),
    ];
    options.signal?.addEventListener('abort', this.abort, { once: true });
    if (options.signal?.aborted) this.abort();
  }

  private readonly abort = (): void => this.fail(new Error('math_run_wait_interrupted'));

  private event(event: ResearchTeamCoreEvent): void {
    if (this.closed) return;
    // Background Lead turns have no run ID and emit no childTurnCompleted.
    // Their idle transition follows batch release and must trigger a fresh read.
    if (event.name === 'team.agentStatusChanged' && event.data.status === 'idle') {
      this.options.observe?.(event);
      this.wake();
      return;
    }
    const relevant =
      TERMINAL_EVENTS.has(event.name) ||
      isTerminalSessionEvent(event) ||
      (this.options.startupOnly && event.name === 'team.childTurnStarted');
    if (!relevant) return;
    const key = JSON.stringify([
      event.name,
      event.data.team_run_id,
      event.data.slot_id,
      event.data.turn_id,
      event.data.status,
    ]);
    if (this.seen.has(key)) return;
    this.seen.add(key);
    if (this.seen.size > 4096) this.seen.delete(this.seen.values().next().value!);
    this.options.observe?.(event);
    this.wake();
  }

  private wake(): void {
    if (this.closed) return;
    this.pendingVersion++;
    queueMicrotask(() => void this.pump());
  }

  private async pump(): Promise<void> {
    if (this.closed || !this.armed || this.running || !this.options.stream.ready) return;
    this.running = true;
    try {
      while (
        !this.closed &&
        this.options.stream.ready &&
        (this.pendingVersion > this.processedVersion || this.options.stream.dirty)
      ) {
        const version = this.pendingVersion;
        const invalidationVersion = this.options.stream.invalidation?.invalidationVersion ?? 0;
        const result = await this.options.reconcile();
        this.options.stream.acknowledge(invalidationVersion);
        this.processedVersion = version;
        // A gap during the read invalidates even an apparently terminal result.
        if (
          !this.closed &&
          this.options.stream.ready &&
          !this.options.stream.dirty &&
          this.pendingVersion === version &&
          result !== undefined
        ) {
          this.dispose();
          this.resolve(result);
        }
      }
    } catch (error) {
      this.fail(error);
    } finally {
      this.running = false;
    }
  }

  wait(): Promise<T> {
    this.armed = true;
    const heartbeatMs = this.options.heartbeatMs;
    if (heartbeatMs !== undefined && Number.isFinite(heartbeatMs) && heartbeatMs > 0 && !this.heartbeatTimer) {
      this.heartbeatTimer = setInterval(() => this.wake(), heartbeatMs);
    }
    if (this.options.pollIntervalMs !== undefined && !this.pollTimer) {
      if (!Number.isSafeInteger(this.options.pollIntervalMs) || this.options.pollIntervalMs <= 0) {
        this.fail(new Error('team_event_poll_interval_invalid'));
        return this.outcome;
      }
      this.pollTimer = setInterval(() => this.wake(), this.options.pollIntervalMs);
    }
    // A retained run can already be terminal before this process attaches, so
    // do one durable read even when no live event has arrived.
    if (this.pendingVersion === this.processedVersion) this.wake();
    else queueMicrotask(() => void this.pump());
    return this.outcome;
  }

  private fail(error: unknown): void {
    if (this.closed) return;
    this.dispose();
    this.reject(error);
  }

  private dispose(): void {
    this.closed = true;
    if (this.heartbeatTimer) clearInterval(this.heartbeatTimer);
    this.heartbeatTimer = undefined;
    if (this.pollTimer) clearInterval(this.pollTimer);
    this.pollTimer = undefined;
    for (const unsubscribe of this.unsubscribe) unsubscribe();
    this.options.signal?.removeEventListener('abort', this.abort);
    this.seen.clear();
  }

  close(): void {
    this.fail(new Error('math_run_wait_closed'));
  }
}
