import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { randomBytes } from 'node:crypto';
import { MathBudgetBrokerRegistry } from "./mathBudgetBrokerRegistry";
import { createMathBudgetHostClient } from "./mathBudgetHostClient";
import type { DurableMathBudgetLedger } from "./mathBudgetLedger";
import type { startMathBudgetBroker } from "./mathBudgetBroker";

export type MathBudgetRole = Readonly<{ actorId: string; conversationId: string; model: string; backend: string }>;

type MathBudgetTeamOptions = Readonly<{
  runId: string;
  inputDigest: string;
  ledger: DurableMathBudgetLedger;
  countInput: Parameters<typeof startMathBudgetBroker>[0]['countInput'];
  outputTokens: number;
  onRegistrationAttempt: (conversationId: string) => void;
  onBrokerReject?: (actorId: string, code: string) => void;
}>;

/** Owns all private role bindings through the Core session-start barrier. */
export class MathBudgetTeamSession {
  readonly #registry = new MathBudgetBrokerRegistry();
  readonly #client: ReturnType<typeof createMathBudgetHostClient>;
  readonly #directory: string;
  readonly #options: MathBudgetTeamOptions;
  readonly #attempted = new Set<string>();
  readonly #abort = new AbortController();
  #work?: Promise<unknown>;
  #closing?: Promise<void>;

  constructor(options: MathBudgetTeamOptions & { coreUrl: string; hostSecret: string }) {
    this.#options = Object.freeze({ ...options });
    this.#client = createMathBudgetHostClient({ baseUrl: options.coreUrl, hostSecret: options.hostSecret });
    this.#directory = fs.mkdtempSync(path.join(fs.realpathSync(os.tmpdir()), 'mbt-'));
    fs.chmodSync(this.#directory, 0o700);
  }

  async ensure<T>(roles: readonly MathBudgetRole[], launch: (signal: AbortSignal) => Promise<T>): Promise<T> {
    if (this.#work || this.#abort.signal.aborted) throw new Error('math_budget_team_already_started');
    const roster = roles.map((role) => Object.freeze({ ...role }));
    if (
      !roster.length ||
      new Set(roster.map((role) => role.actorId)).size !== roster.length ||
      new Set(roster.map((role) => role.conversationId)).size !== roster.length ||
      roster.some(
        (role) =>
          !/^[A-Za-z0-9_-]{1,128}$/u.test(role.actorId) ||
          !/^[A-Za-z0-9][A-Za-z0-9._:-]{0,127}$/u.test(role.conversationId) ||
          role.model !== 'deepseek' ||
          role.backend !== 'codex'
      )
    ) {
      await this.close();
      throw new Error('math_budget_team_roster_invalid');
    }
    const work = Promise.resolve().then(async () => {
      for (const [index, role] of roster.entries()) {
        this.#abort.signal.throwIfAborted();
        const socketPath = path.join(this.#directory, `${index}.sock`);
        const secret = randomBytes(32).toString('hex');
        // Serialize registration so failure stops creating additional role resources.
        // eslint-disable-next-line no-await-in-loop
        await this.#registry.open({
          socketPath,
          secret,
          ledger: this.#options.ledger,
          countInput: this.#options.countInput,
          onReject: (code) => this.#options.onBrokerReject?.(role.actorId, code),
          binding: {
            runId: this.#options.runId,
            inputDigest: this.#options.inputDigest,
            actorId: role.actorId,
            provider: 'WestlakeHPC',
            model: 'deepseek',
            endpoint: 'https://hpc-api.westlake.edu.cn/v1/responses',
            outputTokens: this.#options.outputTokens,
          },
        });
        this.#abort.signal.throwIfAborted();
        // Journal only the conversation ID before POST, including uncertain writes.
        this.#options.onRegistrationAttempt(role.conversationId);
        this.#attempted.add(role.conversationId);
        // eslint-disable-next-line no-await-in-loop
        await this.#client.register(role.conversationId, {
          run_id: this.#options.runId,
          input_digest: this.#options.inputDigest,
          actor_id: role.actorId,
          socket_path: socketPath,
          secret,
          output_tokens: this.#options.outputTokens,
          provider: 'WestlakeHPC',
          model: 'deepseek',
        });
      }
      this.#abort.signal.throwIfAborted();
      return launch(this.#abort.signal);
    });
    this.#work = work;
    try {
      return await work;
    } catch {
      await this.close();
      throw new Error('math_budget_team_start_failed');
    }
  }

  close(): Promise<void> {
    this.#abort.abort();
    if (this.#closing) return this.#closing;
    this.#closing = (async () => {
      await this.#work?.catch(() => {});
      // Stop admission even when Core is unavailable. Keep durable ledger reservations.
      const brokerResults = await Promise.allSettled([this.#registry.closeAll()]);
      const results = await Promise.allSettled(
        [...this.#attempted].map(async (id) => {
          await this.#client.revoke(id);
          this.#attempted.delete(id);
        })
      );
      if ([...brokerResults, ...results].some((result) => result.status === 'rejected')) {
        throw new Error('math_budget_team_cleanup_failed');
      }
      if (fs.existsSync(this.#directory)) fs.rmdirSync(this.#directory);
    })().catch(() => {
      this.#closing = undefined;
      throw new Error('math_budget_team_cleanup_failed');
    });
    return this.#closing;
  }
}
