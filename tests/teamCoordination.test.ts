import { describe, expect, it, vi } from 'vitest';
import { createResearchCoreTeamClient } from '../src/team/coreTeamClient';
import { createResearchTeamOrchestrator } from '../src/team/orchestrator';

const baseUrl = 'http://127.0.0.1:25820';

describe('Team session cache', () => {
  it('shares an in-flight restore and reuses the restored session', async () => {
    let complete!: (response: Response) => void;
    const fetchImpl = vi.fn(() => new Promise<Response>(resolve => { complete = resolve; }));
    const client = createResearchCoreTeamClient({ baseUrl, fetchImpl });
    const first = client.ensureSession!('team');
    const second = client.ensureSession!('team');
    complete(Response.json({}));
    await Promise.all([first, second]);
    await client.ensureSession!('team');
    expect(fetchImpl).toHaveBeenCalledTimes(1);
  });

  it('evicts the least recently used session and restores a session after failure', async () => {
    const fetchImpl = vi.fn(async () => Response.json({}));
    const client = createResearchCoreTeamClient({ baseUrl, fetchImpl, retryDelaysMs: [] });
    for (let index = 0; index < 32; index++) await client.ensureSession!(`team-${index}`);
    await client.ensureSession!('team-0');
    await client.ensureSession!('team-32');
    expect(fetchImpl).toHaveBeenCalledTimes(33);
    await client.ensureSession!('team-0');
    expect(fetchImpl).toHaveBeenCalledTimes(33);
    await client.ensureSession!('team-1');
    expect(fetchImpl).toHaveBeenCalledTimes(34);
    fetchImpl.mockResolvedValueOnce(Response.json({ error: 'session lost' }, { status: 503 }));
    await expect(client.readRunState('team-0')).rejects.toThrow('session lost');
    await client.ensureSession!('team-0');
    expect(fetchImpl).toHaveBeenCalledTimes(36);
  });
});

describe('Team wait cancellation', () => {
  it('cancels a transport retry without another request and preserves the reason', async () => {
    const controller = new AbortController();
    const reason = new Error('stop retrying');
    const fetchImpl = vi.fn(async () => Response.json({}, { status: 503 }));
    const client = createResearchCoreTeamClient({ baseUrl, fetchImpl, retryDelaysMs: [60_000] });
    const result = expect(client.dispatch('team', 'worker', 'task', controller.signal, 'retry-key'))
      .rejects.toBe(reason);
    try {
      await new Promise<void>(resolve => setImmediate(resolve));
      controller.abort(reason);
      await result;
      expect(fetchImpl).toHaveBeenCalledTimes(1);
    } finally {
      controller.abort(reason);
    }
  });

  it('cancels a status wait without polling again and preserves the reason', async () => {
    const controller = new AbortController();
    const reason = new Error('stop waiting');
    const readRunState = vi.fn(async () => ({ teamId: 'team', slots: [], activeSlotIds: [], queuedIntentCount: 1 }));
    const orchestrator = createResearchTeamOrchestrator({
      validateAssignment: () => undefined,
      prepare: () => ({ message: '', detail: undefined }),
      integrate: () => undefined,
      present: event => event,
    });
    const result = orchestrator.status({ waitSeconds: 60 }, {
      teamId: 'team', reasoningConcurrency: 1, context: undefined, signal: controller.signal,
      client: { readRunState, dispatch: vi.fn() },
    });
    try {
      await new Promise<void>(resolve => setImmediate(resolve));
      controller.abort(reason);
      await expect(result).resolves.toMatchObject({ kind: 'status.error', message: reason.message });
      expect(readRunState).toHaveBeenCalledTimes(1);
    } finally {
      controller.abort(reason);
    }
  });
});
