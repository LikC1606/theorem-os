import { z } from 'zod';

export type ResearchTeamStreamInvalidation = Readonly<{
  reason: 'disconnect' | 'reconnect' | 'event_gap' | 'malformed_event' | 'handler_drop';
  connectionGeneration: number;
  invalidationVersion: number;
  observedAt: string;
}>;

export type ResearchTeamCoreEvent = Readonly<{ name: string; data: Readonly<Record<string, unknown>> }>;
export type ResearchTeamEventSocket = Pick<WebSocket, 'addEventListener' | 'removeEventListener' | 'send' | 'close'>;
const envelope = z.object({ name: z.string().min(1), data: z.unknown() }).strict();
const teamData = z.object({ team_id: z.string().min(1) }).passthrough();
const runData = teamData.extend({
  team_run_id: z.string().min(1),
  status: z.enum(['accepted', 'running', 'cancelling', 'completed', 'cancelled', 'failed']),
});
const childData = runData.extend({ slot_id: z.string().min(1), turn_id: z.string().min(1) });
const gapData = z
  .object({ skipped: z.number().int().nonnegative().safe(), observedAt: z.number().int().nonnegative().safe() })
  .strict();
const readyData = z.object({ protocolVersion: z.literal(1) }).strict();

/** Transport invalidation versions are observations, never server replay cursors. */
export class ResearchTeamEventStream {
  private generation = 0;
  private latest?: ResearchTeamStreamInvalidation;
  private acknowledgedVersion = 0;
  private readonly invalidations = new Set<(event: ResearchTeamStreamInvalidation) => void>();
  private readonly events = new Set<(event: ResearchTeamCoreEvent) => void>();
  private disconnect?: () => void;
  private reconnectTimer?: ReturnType<typeof setTimeout>;
  private closed = false;
  private startTask?: Promise<void>;
  private cancelStart?: () => void;
  private connectionReady = false;

  constructor(
    private readonly options: Readonly<{
      teamId: string;
      createSocket: () => ResearchTeamEventSocket;
      now?: () => number;
      handshakeTimeoutMs?: number;
      reconnectDelayMs?: number;
    }>
  ) {
    if (!options.teamId.trim()) throw new Error('team_event_identity_invalid');
  }

  get ready(): boolean {
    return this.connectionReady;
  }
  get invalidation(): ResearchTeamStreamInvalidation | undefined {
    return this.latest;
  }
  get dirty(): boolean {
    return (this.latest?.invalidationVersion ?? 0) > this.acknowledgedVersion;
  }

  acknowledge(version: number): void {
    if (!Number.isSafeInteger(version) || version < 0 || version > (this.latest?.invalidationVersion ?? 0))
      throw new Error('team_event_invalidation_version_invalid');
    this.acknowledgedVersion = Math.max(this.acknowledgedVersion, version);
  }

  subscribeInvalidation(listener: (event: ResearchTeamStreamInvalidation) => void): () => void {
    this.invalidations.add(listener);
    return () => this.invalidations.delete(listener);
  }

  subscribe(listener: (event: ResearchTeamCoreEvent) => void): () => void {
    this.events.add(listener);
    return () => this.events.delete(listener);
  }

  private invalidate(reason: ResearchTeamStreamInvalidation['reason']): void {
    if (this.closed) return;
    this.latest = Object.freeze({
      reason,
      connectionGeneration: this.generation,
      invalidationVersion: (this.latest?.invalidationVersion ?? 0) + 1,
      observedAt: new Date(this.options.now?.() ?? Date.now()).toISOString(),
    });
    for (const listener of this.invalidations) {
      try {
        listener(this.latest);
      } catch {
        /* State remains dirty even if an observer is unavailable. */
      }
    }
  }

  start(): Promise<void> {
    if (this.closed) return Promise.reject(new Error('team_event_stream_closed'));
    if (this.startTask) return this.startTask;
    this.startTask = this.connect();
    return this.startTask;
  }

  private connect(): Promise<void> {
    this.generation++;
    const generation = this.generation;
    let socket: ResearchTeamEventSocket;
    try {
      socket = this.options.createSocket();
    } catch {
      this.invalidate('disconnect');
      return Promise.reject(new Error('team_event_connection_failed'));
    }
    return new Promise<void>((resolve, reject) => {
      let accepted = false;
      let ended = false;
      const timeout = setTimeout(
        () => finish(new Error('team_event_subscription_unavailable')),
        this.options.handshakeTimeoutMs ?? 10_000
      );
      const finish = (error?: Error): void => {
        if (ended) return;
        ended = true;
        clearTimeout(timeout);
        socket.removeEventListener('open', open);
        socket.removeEventListener('message', message);
        socket.removeEventListener('close', close);
        socket.removeEventListener('error', close);
        socket.close();
        this.connectionReady = false;
        if (!this.closed) this.invalidate('disconnect');
        if (!accepted) reject(error ?? new Error('team_event_connection_failed'));
        if (accepted && !this.closed) this.scheduleReconnect();
      };
      this.cancelStart = () => finish(new Error('team_event_stream_closed'));
      this.disconnect = () => finish();
      const open = (): void => {
        try {
          socket.send(JSON.stringify({ name: 'runtime.subscribe', data: {} }));
        } catch {
          finish(new Error('team_event_connection_failed'));
        }
      };
      const close = (): void => finish();
      const message = (event: Event): void => {
        if (ended || this.closed || generation !== this.generation) return;
        let parsed: z.infer<typeof envelope>;
        try {
          const data = (event as MessageEvent).data;
          if (typeof data !== 'string') throw new Error('not_text');
          parsed = envelope.parse(JSON.parse(data));
        } catch {
          this.invalidate('malformed_event');
          return;
        }
        if (parsed.name === 'ping') {
          try {
            socket.send(JSON.stringify({ name: 'pong', data: {} }));
          } catch {
            finish();
          }
          return;
        }
        if (parsed.name === 'runtime.subscriptionReady') {
          if (!readyData.safeParse(parsed.data).success) {
            finish(new Error('team_event_subscription_unavailable'));
            return;
          }
          if (!accepted) {
            accepted = true;
            this.connectionReady = true;
            clearTimeout(timeout);
            if (generation > 1) this.invalidate('reconnect');
            resolve();
          }
          return;
        }
        if (parsed.name === 'runtime.eventGap') {
          this.invalidate(gapData.safeParse(parsed.data).success ? 'event_gap' : 'malformed_event');
          return;
        }
        if (!parsed.name.startsWith('team.')) return;
        const data = (
          parsed.name.startsWith('team.childTurn') ? childData : parsed.name.startsWith('team.run') ? runData : teamData
        ).safeParse(parsed.data);
        if (!data.success) {
          this.invalidate('malformed_event');
          return;
        }
        if (data.data.team_id !== this.options.teamId) return;
        const fact: ResearchTeamCoreEvent = Object.freeze({ name: parsed.name, data: Object.freeze(data.data) });
        for (const listener of this.events) {
          try {
            listener(fact);
          } catch {
            this.invalidate('handler_drop');
          }
        }
      };
      socket.addEventListener('open', open);
      socket.addEventListener('message', message);
      socket.addEventListener('close', close);
      socket.addEventListener('error', close);
    });
  }

  private scheduleReconnect(): void {
    if (this.closed || this.reconnectTimer) return;
    this.reconnectTimer = setTimeout(() => {
      this.reconnectTimer = undefined;
      if (!this.closed) void this.connect().catch(() => this.scheduleReconnect());
    }, this.options.reconnectDelayMs ?? 500);
  }

  close(): void {
    if (this.closed) return;
    this.closed = true;
    if (this.reconnectTimer) clearTimeout(this.reconnectTimer);
    this.cancelStart?.();
    this.disconnect?.();
    this.events.clear();
    this.invalidations.clear();
  }
}
