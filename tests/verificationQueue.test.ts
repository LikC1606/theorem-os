import { afterEach, describe, expect, it, vi } from 'vitest';
import { createSolverVerificationQueue } from '../src/solver/verificationQueue';

function deferred() {
  let resolve!: () => void;
  const promise = new Promise<void>(done => { resolve = done; });
  return { promise, resolve };
}

afterEach(() => vi.restoreAllMocks());

describe('solver verification queue observability', () => {
  it('preserves arrival order and correlates separate wait and execution timings', async () => {
    let now = 100;
    vi.spyOn(performance, 'now').mockImplementation(() => now);
    const events: { event: string; details: Record<string, unknown> }[] = [];
    const run = createSolverVerificationQueue({ context: { operation: 'cooperation' },
      emit: (event, details) => events.push({ event, details }) });
    const entered = deferred(), release = deferred();
    const order: string[] = [];
    const first = run(async () => { order.push('first'); entered.resolve(); await release.promise; return 'first'; });
    await entered.promise;
    now = 110;
    const context = { workerId: 'engineer', taskId: 'original' };
    const second = run(async () => { order.push('second'); now = 170; return 'second'; }, context);
    context.taskId = 'changed';
    now = 120;
    const third = run(async () => { order.push('third'); now = 190; return 'third'; });
    expect(order).toEqual(['first']);
    now = 140;
    release.resolve();
    expect(await Promise.all([first, second, third])).toEqual(['first', 'second', 'third']);
    expect(order).toEqual(['first', 'second', 'third']);
    const waiting = events.filter(({ event }) => event === 'verification_queue_waiting');
    expect(waiting.map(({ details }) => [details.queued, details.queueDepth])).toEqual([[false, 0], [true, 1], [true, 2]]);
    expect(new Set(waiting.map(({ details }) => details.id)).size).toBe(3);
    const expectedTimings = [[0, 40], [30, 30], [50, 20]];
    for (const [index, { details: { id } }] of waiting.entries()) {
      const operation = events.filter(({ details }) => details.id === id);
      expect(operation.map(({ event }) => event)).toEqual([
        'verification_queue_waiting', 'verification_queue_acquired', 'verification_queue_finished',
      ]);
      expect(operation[1].details.waitMs).toBe(expectedTimings[index][0]);
      expect(operation[2].details).toMatchObject({ status: 'completed', acquired: true,
        waitMs: expectedTimings[index][0], executionMs: expectedTimings[index][1] });
      if (index === 1) for (const { details } of operation)
        expect(details).toMatchObject({ workerId: 'engineer', taskId: 'original', operation: 'cooperation' });
    }
  });

  it('releases the queue after a rejected verification without changing its rejection', async () => {
    const events: Record<string, unknown>[] = [];
    const run = createSolverVerificationQueue({ emit: (event, details) => {
      if (event === 'verification_queue_finished') events.push(details);
    } });
    const failure = new Error('check failed');
    const failed = run(() => { throw failure; });
    const rejection = expect(failed).rejects.toBe(failure);
    const next = run(async () => 'next');
    await rejection;
    expect(await next).toBe('next');
    expect(events.map(({ status }) => status)).toEqual(['failed', 'completed']);
  });

  it('finishes aborted waiters without acquiring or invoking their verification', async () => {
    let now = 100;
    vi.spyOn(performance, 'now').mockImplementation(() => now);
    const controller = new AbortController();
    const events: { event: string; details: Record<string, unknown> }[] = [];
    const run = createSolverVerificationQueue({ signal: controller.signal,
      emit: (event, details) => events.push({ event, details }) });
    const entered = deferred(), release = deferred();
    const active = run(async () => { entered.resolve(); await release.promise; return 'completed'; });
    await entered.promise;
    now = 110;
    const check = vi.fn(async () => 'unreachable');
    const waiting = run(check);
    const reason = new Error('stopped');
    const rejection = expect(waiting).rejects.toBe(reason);
    now = 130;
    controller.abort(reason);
    await Promise.resolve();
    expect(events.filter(({ event }) => event === 'verification_queue_finished')).toHaveLength(0);
    now = 160;
    release.resolve();
    expect(await active).toBe('completed');
    await rejection;
    expect(check).not.toHaveBeenCalled();
    const waitingId = events[2].details.id;
    const lifecycle = events.filter(({ details }) => details.id === waitingId);
    expect(lifecycle.map(({ event }) => event)).toEqual(['verification_queue_waiting', 'verification_queue_finished']);
    expect(lifecycle[1].details).toMatchObject({ status: 'aborted', acquired: false, waitMs: 50, durationMs: 50 });
    expect(lifecycle[1].details).not.toHaveProperty('executionMs');
    await expect(run(check)).rejects.toBe(reason);
    expect(check).not.toHaveBeenCalled();
  });

  it('records an abort thrown by an acquired verification', async () => {
    let now = 100;
    vi.spyOn(performance, 'now').mockImplementation(() => now);
    const controller = new AbortController();
    const events: Record<string, unknown>[] = [];
    const run = createSolverVerificationQueue({ signal: controller.signal, emit: (event, details) => {
      if (event === 'verification_queue_finished') events.push(details);
    } });
    const entered = deferred(), release = deferred();
    const pending = run(async () => { entered.resolve(); await release.promise; controller.signal.throwIfAborted(); });
    const reason = new Error('running check stopped');
    const rejection = expect(pending).rejects.toBe(reason);
    await entered.promise;
    now = 150;
    controller.abort(reason); release.resolve();
    await rejection;
    expect(events).toMatchObject([{ status: 'aborted', acquired: true, waitMs: 0, executionMs: 50, durationMs: 50 }]);
  });

  it.each(['waiting', 'acquired', 'finished'])('preserves serialization and releases after a %s observer throws', async phase => {
    const failure = new Error('observer failed');
    const run = createSolverVerificationQueue({ emit: (event, details) => {
      if (event === `verification_queue_${phase}` && details.operation === 'bad') throw failure;
    } });
    const entered = deferred(), release = deferred();
    const order: string[] = [];
    const first = run(async () => { order.push('first'); entered.resolve(); await release.promise; });
    await entered.promise;
    const failed = run(async () => { order.push('bad'); }, { operation: 'bad' });
    const rejection = expect(failed).rejects.toBe(failure);
    const next = run(async () => { order.push('next'); return 'next'; });
    await Promise.resolve();
    expect(order).toEqual(['first']);
    release.resolve();
    await Promise.all([first, rejection]);
    expect(await next).toBe('next');
    expect(order).toEqual(phase === 'finished' ? ['first', 'bad', 'next'] : ['first', 'next']);
  });
});
