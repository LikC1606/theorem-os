import { describe, expect, it, vi } from 'vitest';
import { createMathOperationLimiter } from '../src/math/concurrency';
import { deferred } from './helpers/async';

describe('verification concurrency pools', () => {
  it('limits operations and admits queued work in arrival order', async () => {
    const run = createMathOperationLimiter(() => 2);
    const blockers = Array.from({ length: 4 }, deferred);
    const started: number[] = [];
    const jobs = blockers.map((blocker, index) => run(async () => {
      started.push(index);
      await blocker.promise;
      return index;
    }));
    expect(started).toEqual([0, 1]);
    blockers[1]!.resolve();
    await jobs[1];
    expect(started).toEqual([0, 1, 2]);
    blockers[0]!.resolve();
    await jobs[0];
    expect(started).toEqual([0, 1, 2, 3]);
    blockers[2]!.resolve();
    blockers[3]!.resolve();
    expect(await Promise.all(jobs)).toEqual([0, 1, 2, 3]);
  });

  it('keeps batch and process pools independent', async () => {
    const batches = createMathOperationLimiter(() => 1);
    const processes = createMathOperationLimiter(() => 1);
    expect(await batches(() => processes(async () => 'verified'))).toBe('verified');
  });

  it('releases capacity after an operation throws', async () => {
    const run = createMathOperationLimiter(() => 1);
    const failed = run(() => { throw new Error('failed'); });
    const next = run(async () => 'next');
    await expect(failed).rejects.toThrow('failed');
    expect(await next).toBe('next');
  });

  it('rejects already aborted and queued operations without starting them', async () => {
    const run = createMathOperationLimiter(() => 1);
    const blocker = deferred();
    const first = run(() => blocker.promise);
    const controller = new AbortController();
    const operation = vi.fn(async () => 'cancelled');
    const queued = run(operation, controller.signal);
    controller.abort(new Error('cancelled'));
    await expect(queued).rejects.toThrow('cancelled');
    await expect(run(operation, controller.signal)).rejects.toThrow('cancelled');
    const next = run(async () => 'next');
    blocker.resolve();
    await first;
    expect(await next).toBe('next');
    expect(operation).not.toHaveBeenCalled();
  });

  it('passes a granted slot onward when its waiter is aborted before starting', async () => {
    const run = createMathOperationLimiter(() => 1);
    const blocker = deferred();
    const first = run(() => blocker.promise);
    const controller = new AbortController();
    const operation = vi.fn(async () => 'cancelled');
    const queued = run(operation, controller.signal);
    const next = run(async () => 'next');
    // This callback runs after slot release and before the queued operation resumes.
    const abort = blocker.promise.then(() => controller.abort(new Error('cancelled after grant')));
    blocker.resolve();
    await expect(queued).rejects.toThrow('cancelled after grant');
    expect(await next).toBe('next');
    await Promise.all([first, abort]);
    expect(operation).not.toHaveBeenCalled();
  });

  it('reserves released capacity before a new arrival can overtake a waiter', async () => {
    const run = createMathOperationLimiter(() => 1);
    const firstBlocker = deferred();
    const secondBlocker = deferred();
    const first = run(() => firstBlocker.promise);
    const order: string[] = [];
    const second = run(async () => { order.push('second'); await secondBlocker.promise; });
    const arrival = firstBlocker.promise.then(() => run(async () => { order.push('third'); }));
    firstBlocker.resolve();
    await first;
    expect(order).toEqual(['second']);
    secondBlocker.resolve();
    await Promise.all([second, arrival]);
    expect(order).toEqual(['second', 'third']);
  });
});
