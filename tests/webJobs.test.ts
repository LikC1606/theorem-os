import { afterEach, describe, expect, it, vi } from 'vitest';
import { WebJobs } from '../apps/web/jobs';
import type { WebRunner } from '../apps/web/runner';
import type { WebProvider, WebResult, WebRunInput, WorkerInput, WorkerMessage } from '../apps/web/shared';

const provider: WebProvider = { id: 'openai', name: 'OpenAI', baseUrl: 'https://api.openai.com/v1' };
const input = (apiKey = 'sk-test-job-secret'): WebRunInput => ({ providerId: provider.id, apiKey,
  model: 'gpt-6.1-sol', effort: 'xhigh', source: 'theorem example : True := by sorry',
  task: 'Prove the theorem', maxTurns: 2, maxRunSeconds: 30, workers: 1, coordination: 'cooperative' });
const result = (proof = 'theorem example : True := by trivial'): WebResult => ({
  status: 'evaluated_passed', proof, report: { acceptance: 'kernel_verified' },
});
const tick = () => new Promise<void>(resolve => setImmediate(resolve));

type Call = { input: WorkerInput; signal: AbortSignal; send(message: WorkerMessage): void;
  finish(value?: WebResult): void; end(): void; fail(error: Error): void };
class ControlledRunner implements WebRunner {
  calls: Call[] = [];
  active = 0;
  peak = 0;
  async readiness() { return { ready: true, message: 'Test worker ready' }; }
  async run(value: WorkerInput, send: (message: WorkerMessage) => void, signal: AbortSignal) {
    this.active++;
    this.peak = Math.max(this.peak, this.active);
    try {
      await new Promise<void>((resolve, reject) => {
        const abort = () => reject(new Error('Worker aborted'));
        const finish = (value = result()) => { send({ type: 'result', result: value }); resolve(); };
        this.calls.push({ input: value, signal, send, finish, end: resolve, fail: reject });
        signal.addEventListener('abort', abort, { once: true });
        if (signal.aborted) abort();
      });
    } finally { this.active--; }
  }
}

describe('web job ownership, scheduling and secret lifetime without provider calls', () => {
  const queues: WebJobs[] = [];
  const setup = (concurrency = 1, queueLimit = 8) => {
    const runner = new ControlledRunner();
    const jobs = new WebJobs(runner, { concurrency, queueLimit });
    queues.push(jobs);
    return { runner, jobs };
  };
  afterEach(async () => { await Promise.all(queues.splice(0).map(jobs => jobs.close())); });

  it('starts queued jobs in order, respects concurrency and rejects excess active work', async () => {
    const { jobs, runner } = setup(2, 4);
    const runs = Array.from({ length: 4 }, (_, index) => jobs.create('owner', { ...input(), task: `Task ${index}` }, provider));
    expect(() => jobs.create('owner', input(), provider)).toThrow(/队列已满/);
    await tick();
    expect(runner.calls.map(call => call.input.id)).toEqual(runs.slice(0, 2).map(run => run.id));
    expect(runs.map(run => run.status)).toEqual(['running', 'running', 'queued', 'queued']);
    runner.calls[0].finish();
    await tick();
    expect(runner.calls[2].input.id).toBe(runs[2].id);
    runner.calls[1].finish();
    await tick();
    expect(runner.calls[3].input.id).toBe(runs[3].id);
    runner.calls[2].finish(); runner.calls[3].finish();
    await tick();
    expect(runner.peak).toBe(2);
    expect(runner.active).toBe(0);
    expect(runs.every(run => run.status === 'completed')).toBe(true);
    expect(runner.calls.every(call => call.input.input.apiKey === '')).toBe(true);
  });

  it('prevents another owner from reading or cancelling a job', async () => {
    const { jobs, runner } = setup();
    const run = jobs.create('alice', input(), provider);
    await tick();
    expect(jobs.list('bob')).toEqual([]);
    expect(jobs.get('bob', run.id)).toBeUndefined();
    expect(jobs.cancel('bob', run.id)).toBeUndefined();
    expect(run.status).toBe('running');
    expect(runner.calls[0].signal.aborted).toBe(false);
    runner.calls[0].finish();
    await tick();
    expect(jobs.get('alice', run.id)?.result?.status).toBe('evaluated_passed');
    expect(jobs.get('bob', run.id)).toBeUndefined();
  });

  it('refuses to remove queued or running jobs without cancelling them or changing their order', async () => {
    const { jobs, runner } = setup();
    const first = jobs.create('owner', input('sk-first-active-secret'), provider);
    const second = jobs.create('owner', input('sk-second-queued-secret'), provider);
    expect(jobs.remove('owner', first.id)).toBe('active');
    expect(jobs.remove('owner', second.id)).toBe('active');
    await tick();
    expect(jobs.remove('owner', first.id)).toBe('active');
    expect(jobs.remove('owner', second.id)).toBe('active');
    expect([first.status, second.status]).toEqual(['running', 'queued']);
    expect(runner.calls).toHaveLength(1);
    expect(runner.calls[0].signal.aborted).toBe(false);
    expect(runner.calls[0].input.input.apiKey).toBe('sk-first-active-secret');
    runner.calls[0].finish();
    await tick();
    expect(runner.calls[1].input.id).toBe(second.id);
    expect(runner.calls[1].input.input.apiKey).toBe('sk-second-queued-secret');
    expect(runner.calls[1].signal.aborted).toBe(false);
    runner.calls[1].finish();
    await tick();
    expect([first.status, second.status]).toEqual(['completed', 'completed']);
  });

  it.each(['completed', 'cancelled', 'error'] as const)('removes only the owner\'s %s record and leaves other work intact', async status => {
    const { jobs, runner } = setup();
    const run = jobs.create('alice', input(), provider);
    const other = jobs.create('bob', input('sk-other-owner-secret'), provider);
    await tick();
    if (status === 'completed') runner.calls[0].finish();
    else if (status === 'error') runner.calls[0].fail(new Error('Test worker failed'));
    else jobs.cancel('alice', run.id);
    await tick();
    expect(run.status).toBe(status);
    expect(jobs.remove('bob', run.id)).toBe('missing');
    expect(jobs.remove('alice', 'unknown-run')).toBe('missing');
    expect(jobs.get('alice', run.id)).toBe(run);
    expect(jobs.remove('alice', run.id)).toBe('deleted');
    expect(jobs.remove('alice', run.id)).toBe('missing');
    expect(jobs.get('alice', run.id)).toBeUndefined();
    expect(jobs.list('alice')).toEqual([]);
    expect(jobs.list('bob')).toEqual([other]);
    expect(other.status).toBe('running');
    expect(runner.calls[1].input.id).toBe(other.id);
    expect(runner.calls[1].signal.aborted).toBe(false);
    expect(runner.calls[1].input.input.apiKey).toBe('sk-other-owner-secret');
    runner.calls[1].finish();
    await tick();
    expect(other.status).toBe('completed');
  });

  it('cleans a cancelled worker\'s credential and starts waiting work after its record is removed', async () => {
    const { jobs, runner } = setup();
    const cancelled = jobs.create('owner', input('sk-cancelled-worker-secret'), provider);
    const waiting = jobs.create('owner', input('sk-waiting-worker-secret'), provider);
    await tick();
    jobs.cancel('owner', cancelled.id);
    expect(jobs.remove('owner', cancelled.id)).toBe('deleted');
    expect(jobs.get('owner', cancelled.id)).toBeUndefined();
    expect(runner.calls[0].signal.aborted).toBe(true);
    expect(runner.active).toBe(1);
    expect(waiting.status).toBe('queued');
    await tick();
    expect(runner.calls[0].input.input.apiKey).toBe('');
    expect(runner.calls).toHaveLength(2);
    expect(runner.calls[1].input.id).toBe(waiting.id);
    expect(runner.calls[1].signal.aborted).toBe(false);
    expect(runner.calls[1].input.input.apiKey).toBe('sk-waiting-worker-secret');
    expect(runner.peak).toBe(1);
    runner.calls[1].finish();
    await tick();
    expect(waiting.status).toBe('completed');
    expect(runner.calls[1].input.input.apiKey).toBe('');
  });

  it('frees a session\'s 20-record limit by removing finished history while preserving other owners and the queue', async () => {
    const { jobs, runner } = setup();
    const history = [];
    for (let index = 0; index < 20; index++) {
      history.push(jobs.create('alice', { ...input(), task: `History ${index}` }, provider));
      await tick();
      runner.calls[index].finish();
      await tick();
    }
    expect(jobs.list('alice')).toHaveLength(20);
    expect(() => jobs.create('alice', input(), provider)).toThrow(/20.*删除已结束.*重试/);
    const other = jobs.create('bob', input('sk-other-running-secret'), provider);
    await tick();
    expect(jobs.remove('alice', history[0].id)).toBe('deleted');
    const next = jobs.create('alice', input('sk-new-history-secret'), provider);
    expect(jobs.list('alice')).toHaveLength(20);
    expect(jobs.list('alice')).not.toContain(history[0]);
    expect(jobs.list('bob')).toEqual([other]);
    expect(next.status).toBe('queued');
    expect(runner.calls[20].signal.aborted).toBe(false);
    expect(runner.calls[20].input.input.apiKey).toBe('sk-other-running-secret');
    runner.calls[20].finish();
    await tick();
    expect(runner.calls[21].input.id).toBe(next.id);
    runner.calls[21].finish();
    await tick();
    expect(next.status).toBe('completed');
    expect(runner.calls.every(call => call.input.input.apiKey === '')).toBe(true);
  });

  it('normalizes legacy jobs to the standard library and preserves explicit Mathlib in worker and public records', async () => {
    const { jobs, runner } = setup(2);
    const standard = jobs.create('owner', input(), provider);
    const mathlib = jobs.create('owner', { ...input(), environment: 'mathlib' }, provider);
    expect(standard.environment).toBe('standard');
    expect(mathlib.environment).toBe('mathlib');
    await tick();
    expect(runner.calls.map(call => call.input.input.environment)).toEqual(['standard', 'mathlib']);
    runner.calls.forEach(call => call.finish());
    await tick();
    expect(jobs.get('owner', standard.id)?.environment).toBe('standard');
    expect(jobs.list('owner').map(run => run.environment)).toEqual(['mathlib', 'standard']);
  });

  it('cancels queued work without starting it and clears the retained queued credential', async () => {
    const { jobs, runner } = setup();
    const active = jobs.create('owner', input('sk-active-credential'), provider);
    const queued = jobs.create('owner', input('sk-queued-credential'), provider);
    await tick();
    expect(queued.status).toBe('queued');
    expect(jobs.cancel('owner', queued.id)?.status).toBe('cancelled');
    // This private lifecycle check verifies that a secret cannot survive in an unstarted job.
    const records = (jobs as unknown as { jobs: Map<string, { input: WebRunInput }> }).jobs;
    expect(records.get(queued.id)?.input.apiKey).toBe('');
    expect(jobs.cancel('owner', active.id)?.status).toBe('cancelled');
    await tick();
    expect(runner.calls).toHaveLength(1);
    expect(runner.calls[0].signal.aborted).toBe(true);
    expect(runner.calls[0].input.input.apiKey).toBe('');
    expect(active.finishedAt).toBeTruthy();
    expect(queued.finishedAt).toBeTruthy();
  });

  it('keeps cancellation terminal even when a worker sends a late result', async () => {
    const { jobs, runner } = setup();
    const cancelled = jobs.create('owner', input(), provider);
    const next = jobs.create('owner', input(), provider);
    await tick();
    jobs.cancel('owner', cancelled.id);
    const eventCount = cancelled.events.length;
    runner.calls[0].send({ type: 'result', result: result() });
    runner.calls[0].send({ type: 'progress', event: 'late', message: 'Late worker output' });
    runner.calls[0].send({ type: 'progress', event: 'evaluation_started', message: 'Late evaluation' });
    runner.calls[0].send({ type: 'artifact', artifact: { source: 'by trivial', workerId: 'solver',
      capturedAt: '2026-10-17T00:00:00.000Z', status: 'candidate' } });
    await tick();
    expect(cancelled.status).toBe('cancelled');
    expect(cancelled.result).toBeUndefined();
    expect(cancelled.artifact).toBeUndefined();
    expect(cancelled.events).toHaveLength(eventCount);
    expect(cancelled.timings?.evaluating).toBeUndefined();
    expect(runner.calls[1].input.id).toBe(next.id);
    runner.calls[1].finish();
    await tick();
    expect(next.status).toBe('completed');
  });

  it('keeps only the latest redacted candidate without changing phase or proof acceptance', async () => {
    const { jobs, runner } = setup();
    const key = 'sk-live-source-secret';
    const run = jobs.create('owner', input(key), provider);
    await tick();
    runner.calls[0].send({ type: 'progress', event: 'proof_check_started', message: 'Checking candidate' });
    const count = run.events.length;
    const first = { source: `-- ${key}\nby sorry`, workerId: 'solver',
      capturedAt: '2026-10-17T00:00:00.000Z', status: 'candidate' as const };
    runner.calls[0].send({ type: 'artifact', artifact: first });
    expect(run.artifact).toEqual({ ...first, source: '-- [REDACTED]\nby sorry' });
    expect(run.status).toBe('running');
    expect(run.phase).toBe('proof_check_started');
    expect(run.result).toBeUndefined();
    expect(run.events).toHaveLength(count);
    const second = { ...first, source: 'by trivial', workerId: 'engineer', capturedAt: '2026-10-17T00:00:01.000Z' };
    runner.calls[0].send({ type: 'artifact', artifact: second });
    expect(jobs.get('owner', run.id)?.artifact).toEqual(second);
    expect(jobs.get('other-owner', run.id)).toBeUndefined();
    runner.calls[0].finish({ status: 'evaluated_rejected', proof: 'by trivial', report: { accepted: false } });
    await tick();
    runner.calls[0].send({ type: 'artifact', artifact: first });
    expect(run.artifact).toEqual(second);
    expect(run.status).toBe('completed');
    expect(run.result?.status).toBe('evaluated_rejected');
    expect(JSON.stringify(run)).not.toContain(key);
  });

  it('retains first phase boundaries after activity-log rotation and repeated progress events', async () => {
    const { jobs, runner } = setup();
    vi.useFakeTimers({ toFake: ['Date'] });
    try {
      vi.setSystemTime('2026-10-16T00:00:00.000Z');
      const run = jobs.create('owner', { ...input(), environment: 'mathlib' }, provider);
      vi.setSystemTime('2026-10-16T00:00:10.000Z');
      await tick();
      vi.setSystemTime('2026-10-16T00:02:10.000Z');
      runner.calls[0].send({ type: 'progress', event: 'solve_started', message: 'Solving' });
      vi.setSystemTime('2026-10-16T00:02:20.000Z');
      for (let index = 0; index < 210; index++) runner.calls[0].send({ type: 'progress', event: 'worker_activity', message: 'Working' });
      expect(run.events).toHaveLength(200);
      expect(run.events.some(event => event.type === 'solve_started')).toBe(false);
      runner.calls[0].send({ type: 'progress', event: 'solve_started', message: 'Repeated progress' });
      vi.setSystemTime('2026-10-16T00:02:40.000Z');
      runner.calls[0].send({ type: 'progress', event: 'evaluation_started', message: 'Evaluating' });
      runner.calls[0].finish();
      await tick();
      expect(jobs.get('owner', run.id)?.timings).toEqual({ preparing: '2026-10-16T00:00:10.000Z',
        solving: '2026-10-16T00:02:10.000Z', evaluating: '2026-10-16T00:02:40.000Z' });
      expect(run.status).toBe('completed');
    } finally { vi.useRealTimers(); }
  });

  it('redacts credentials from submitted text, worker events, nested reports and proof output', async () => {
    const { jobs, runner } = setup();
    const key = 'sk-quote-"-slash-\\-test';
    const run = jobs.create('owner', { ...input(key), task: `Test ${key}`, source: `-- ${key}\ntheorem example : True := by sorry` }, provider);
    expect(JSON.stringify(run)).not.toContain(key);
    expect(run).not.toHaveProperty('apiKey');
    await tick();
    expect(runner.calls[0].input.input.apiKey).toBe(key);
    runner.calls[0].send({ type: 'progress', event: `check-${key}`, message: `Provider says ${key}` });
    runner.calls[0].finish({ status: 'evaluated_passed', proof: `-- ${key}\nby trivial`,
      report: { message: `Receipt ${key}`, nested: [{ token: key }] } });
    await tick();
    const serialized = JSON.stringify(jobs.list('owner'));
    expect(serialized).not.toContain(JSON.stringify(key).slice(1, -1));
    expect(run.task).toBe('Test [REDACTED]');
    expect(run.source).toContain('-- [REDACTED]');
    expect(run.events.some(event => event.message.includes('[REDACTED]'))).toBe(true);
    expect(run.result?.report).toEqual({ message: 'Receipt [REDACTED]', nested: [{ token: '[REDACTED]' }] });
    expect(run.result?.proof).toContain('[REDACTED]');
    expect(runner.calls[0].input.input.apiKey).toBe('');
  });

  it('redacts a long key pasted into task text before deriving its truncated public title', async () => {
    const { jobs } = setup();
    const key = 'sk-long-credential-' + '1234567890abcdef'.repeat(10);
    const run = jobs.create('owner', { ...input(key), task: `${key} prove this theorem` }, provider);
    expect(run.title).toBe('[REDACTED] prove this theorem');
    expect(JSON.stringify(run)).not.toContain(key.slice(0, 60));
    expect(jobs.list('owner')[0].title).toBe(run.title);
    expect(jobs.get('owner', run.id)?.task).toBe('[REDACTED] prove this theorem');
    jobs.cancel('owner', run.id);
  });

  it.each(['throw', 'message'] as const)('redacts %s failures and clears credentials after a failed worker', async mode => {
    const { jobs, runner } = setup();
    const key = 'sk-failure-secret';
    const run = jobs.create('owner', input(key), provider);
    await tick();
    if (mode === 'throw') runner.calls[0].fail(new Error(`Request failed with ${key}`));
    else {
      runner.calls[0].send({ type: 'error', message: `Request failed with ${key}` });
      runner.calls[0].end();
    }
    await tick();
    expect(run.status).toBe('error');
    expect(run.error).toContain('[REDACTED]');
    expect(JSON.stringify(run)).not.toContain(key);
    expect(runner.calls[0].input.input.apiKey).toBe('');
  });

  it('distinguishes a terminal runtime error from a completed proof attempt', async () => {
    const { jobs, runner } = setup();
    const failed = jobs.create('owner', input(), provider);
    await tick();
    runner.calls[0].finish({ status: 'runtime_error', proof: '', report: { reason: 'worker unavailable' } });
    await tick();
    expect(failed.status).toBe('error');
    expect(failed.result?.status).toBe('runtime_error');
    const unproved = jobs.create('owner', input(), provider);
    await tick();
    runner.calls[1].finish({ status: 'evaluated_rejected', proof: 'by sorry', report: { accepted: false } });
    await tick();
    expect(unproved.status).toBe('completed');
    expect(unproved.result?.status).toBe('evaluated_rejected');
    expect(unproved.events.at(-1)?.message).not.toContain('通过独立 Lean 验收');
  });

  it('forgets expired owners and shuts down without starting waiting work', async () => {
    const { jobs, runner } = setup();
    const expired = jobs.create('expired-owner', input(), provider);
    const waiting = jobs.create('remaining-owner', input(), provider);
    await tick();
    jobs.forget('expired-owner');
    expect(jobs.get('expired-owner', expired.id)).toBeUndefined();
    expect(runner.calls[0].signal.aborted).toBe(true);
    await jobs.close();
    expect(runner.calls).toHaveLength(1);
    expect(waiting.status).toBe('cancelled');
    expect(runner.calls[0].input.input.apiKey).toBe('');
    expect(jobs.list('remaining-owner')).toEqual([]);
    expect(() => jobs.create('owner', input(), provider)).toThrow(/服务正在停止/);
  });
});
