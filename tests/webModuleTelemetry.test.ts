import { describe, expect, it } from 'vitest';
import { isWebEventDetails, recordWebModuleEvent, sanitizeWebEventDetails, webEventModule, webModuleSnapshots } from '../apps/web/moduleTelemetry';
import { translateWebProgress } from '../apps/web/progress';
import { parseWorkerMessage } from '../apps/web/runner';
import type { WebEvent, WebEventDetails, WebRun } from '../apps/web/shared';

const run = (overrides: Partial<WebRun> = {}): WebRun => ({
  id: 'run-modules', title: 'Test modules', status: 'running', phase: 'solve_started',
  createdAt: '2026-10-18T00:00:00.000Z', updatedAt: '2026-10-18T00:00:00.000Z',
  providerId: 'openai', model: 'fixture', effort: 'high', environment: 'standard',
  source: 'theorem example : True := by sorry', task: 'Prove example', maxTurns: 4, maxRunSeconds: 60,
  workers: 4, coordination: 'cooperative', events: [], ...overrides,
});
const event = (type: string, sequence: number, details?: WebEventDetails): WebEvent => ({
  sequence, at: new Date(Date.parse('2026-10-18T00:00:00.000Z') + sequence * 1_000).toISOString(),
  type, message: type, ...(details ? { details } : {}),
});
const append = (value: WebRun, type: string, details?: WebEventDetails) => {
  const next = event(type, (value.events.at(-1)?.sequence ?? 0) + 1, details);
  recordWebModuleEvent(value, next);
  value.events.push(next);
  if (value.events.length > 200) value.events.shift();
  return next;
};

describe('bounded web module observations', () => {
  it.each([
    ['turn_started', 'M1'], ['worker_activity', 'M1'], ['turn_checkpoint', 'M1'],
    ['proof_checked', 'M2'], ['task_checked', 'M2'], ['lemma_checked', 'M2'],
    ['research_action', 'M3'], ['turn_retry', 'M3'], ['context_compiled', 'M4'],
    ['context_restarted', 'M4'], ['task_assigned', 'M5'], ['review_completed', 'M5'],
    ['evaluation_started', 'S3'], ['evaluation_finished', 'S3'],
  ])('maps the actual %s event to %s', (type, module) => {
    expect(webEventModule(type)).toBe(module);
  });

  it('does not invent archive, preparation, acceptance or inherited module events', () => {
    for (const type of ['ready', 'finished', 'queued', 'S1', 'S2', 'constructor', 'toString', 'unknown'])
      expect(webEventModule(type)).toBeUndefined();
  });

  it('keeps concurrent model and checker intervals separate by worker identity', () => {
    const value = run();
    append(value, 'turn_started', { workerId: 'solver', turn: 1 });
    append(value, 'turn_started', { workerId: 'researcher-1', turn: 1 });
    append(value, 'proof_check_started', { workerId: 'solver', turn: 1 });
    expect(value.modules?.M1?.activeWorkers).toEqual(['researcher-1']);
    expect(value.modules?.M2?.activeWorkers).toEqual(['solver']);
    append(value, 'proof_check_started', { workerId: 'researcher-1', turn: 1 });
    expect(value.modules?.M1?.activeWorkers).toEqual([]);
    expect(value.modules?.M2?.activeWorkers).toEqual(['solver', 'researcher-1']);
    append(value, 'proof_checked', { workerId: 'solver', passed: false });
    expect(value.modules?.M2?.activeWorkers).toEqual(['researcher-1']);
    append(value, 'proof_checked', { workerId: 'researcher-1', passed: true });
    expect(value.modules?.M2?.activeWorkers).toEqual([]);
    expect(value.status).toBe('running');
    expect(value.result).toBeUndefined();
  });

  it('does not clear other workers when an old event has no structured identity', () => {
    const value = run();
    append(value, 'turn_started', { workerId: 'solver' });
    append(value, 'turn_started', { workerId: 'engineer' });
    append(value, 'turn_checkpoint', { workerId: 'solver' });
    append(value, 'task_checked', { taskId: 'goal-1', passed: true, conditional: true });
    append(value, 'turn_failed');
    expect(value.modules?.M1?.activeWorkers).toEqual(['engineer']);
    expect(value.modules?.M2?.activeWorkers).toEqual([]);
    expect(value.modules?.M2?.lastEvent.details).toEqual({ taskId: 'goal-1', passed: true, conditional: true });
  });

  it('records decisions, context and assignment as observations rather than running intervals', () => {
    const value = run();
    append(value, 'research_action', { workerId: 'solver', operation: 'decompose' });
    append(value, 'context_compiled', { workerId: 'solver', usedBytes: 1_024, maxBytes: 8_192 });
    append(value, 'task_assigned', { workerId: 'engineer', taskId: 'goal-1' });
    expect(value.modules?.M3?.activeWorkers).toEqual([]);
    expect(value.modules?.M4?.activeWorkers).toEqual([]);
    expect(value.modules?.M5?.activeWorkers).toEqual([]);
    expect(value.modules?.M1).toBeUndefined();
  });

  it('ends research intervals at independent evaluation and retains its separate outcome', () => {
    const value = run();
    append(value, 'ready');
    expect(value.modules?.S3).toBeUndefined();
    append(value, 'turn_started', { workerId: 'solver' });
    append(value, 'proof_check_started', { workerId: 'engineer' });
    append(value, 'evaluation_started', { workerId: 'solver' });
    expect(value.modules?.M1?.activeWorkers).toEqual([]);
    expect(value.modules?.M2?.activeWorkers).toEqual([]);
    expect(value.modules?.S3?.activeWorkers).toEqual(['solver']);
    append(value, 'evaluation_finished', { status: 'passed' });
    expect(value.modules?.S3?.activeWorkers).toEqual([]);
    expect(value.modules?.S3?.lastEvent.details?.status).toBe('passed');
    expect(value.status).toBe('running');
    expect(value.result).toBeUndefined();
  });

  it.each(['finished', 'cancelled', 'error'])('clears outstanding activity on %s without creating a proof outcome', type => {
    const value = run();
    append(value, 'turn_started', { workerId: 'solver' });
    append(value, 'proof_check_started', { workerId: 'engineer' });
    append(value, type);
    expect(value.modules?.M1?.activeWorkers).toEqual([]);
    expect(value.modules?.M2?.activeWorkers).toEqual([]);
    expect(value.modules?.M1?.lastEvent.type).toBe('turn_started');
    expect(value.result).toBeUndefined();
  });

  it('retains first observation and total observation count when the activity window rotates', () => {
    const value = run();
    const first = append(value, 'context_compiled', { workerId: 'solver', usedBytes: 0, maxBytes: 1_024 });
    for (let index = 0; index < 220; index++) append(value, 'worker_activity', { workerId: 'solver' });
    append(value, 'context_compiled', { workerId: 'solver', usedBytes: 512, maxBytes: 1_024 });
    expect(value.events).toHaveLength(200);
    expect(value.events.some(item => item.sequence === first.sequence)).toBe(false);
    expect(value.modules?.M4?.firstAt).toBe(first.at);
    expect(value.modules?.M4?.eventCount).toBe(2);
    expect(value.modules?.M1?.eventCount).toBe(220);
    expect(webModuleSnapshots(value)).toBe(value.modules);
  });

  it('reconstructs older runs only from retained events without mutating their records', () => {
    const value = run({ events: [event('turn_started', 5, { workerId: 'solver' }),
      event('proof_check_started', 6, { workerId: 'solver' }), event('proof_checked', 7, { workerId: 'solver', passed: false })] });
    const before = JSON.stringify(value);
    const snapshots = webModuleSnapshots(value);
    expect(snapshots.M1).toMatchObject({ eventCount: 1, firstAt: value.events[0].at, activeWorkers: [] });
    expect(snapshots.M2).toMatchObject({ eventCount: 2, firstAt: value.events[1].at, activeWorkers: [] });
    expect(JSON.stringify(value)).toBe(before);
    expect(value.modules).toBeUndefined();
  });

  it.each(['completed', 'cancelled', 'error'] as const)('does not revive activity when reconstructing %s legacy runs', status => {
    const value = run({ status, events: [event('turn_started', 1, { workerId: 'solver' })] });
    expect(webModuleSnapshots(value).M1?.activeWorkers).toEqual([]);
  });

  it('bounds active identities and counters, and copies structured evidence into the summary', () => {
    const value = run();
    const details = { workerId: 'solver', turn: 1 };
    append(value, 'turn_started', details);
    details.turn = 99;
    expect(value.modules?.M1?.lastEvent.details?.turn).toBe(1);
    for (let index = 0; index < 12; index++) append(value, 'turn_started', { workerId: `worker-${index}` });
    expect(value.modules?.M1?.activeWorkers).toHaveLength(4);
    value.modules!.M1!.eventCount = Number.MAX_SAFE_INTEGER;
    append(value, 'worker_activity', { workerId: 'solver' });
    expect(value.modules?.M1?.eventCount).toBe(Number.MAX_SAFE_INTEGER);
  });
});

describe('allowlisted web progress translation', () => {
  it('preserves real context identity and size but discards private and unneeded fields', () => {
    const message = translateWebProgress({ event: 'context_compiled', workerId: 'researcher-1',
      taskId: 'lemma-1', usedBytes: 4_096, maxBytes: 16_384, included: 4, omitted: 2,
      contentDigest: 'private-digest', worktree: '/work/run-1', instructions: 'private instructions',
      apiKey: 'sk-private', sections: ['private-section'], threadId: 'private-thread' });
    expect(message).toEqual({ type: 'progress', event: 'context_compiled',
      message: '本轮上下文已整理 · researcher-1', details: { workerId: 'researcher-1', usedBytes: 4_096, maxBytes: 16_384 } });
    expect(parseWorkerMessage(JSON.stringify(message))).toEqual(message);
    expect(JSON.stringify(message)).not.toMatch(/private|worktree|sections|instructions|threadId/);
  });

  it('forwards only exact event evidence and keeps conditional proof and model outcomes separate', () => {
    const task = translateWebProgress({ event: 'task_checked', taskId: 'goal-1', passed: true, conditional: true,
      commit: 'private-commit', verification: { status: 'kernel_verified' } });
    expect(task?.details).toEqual({ taskId: 'goal-1', passed: true, conditional: true });
    const lemma = translateWebProgress({ event: 'lemma_checked', workerId: 'solver', bridge: true, lemma: false,
      passed: true, status: 'evaluated_passed', error: 'private-lean-error' });
    expect(lemma?.details).toEqual({ workerId: 'solver' });
    const model = translateWebProgress({ event: 'worker_activity', workerId: 'solver', status: 'completed', passed: true });
    expect(model?.details).toEqual({ workerId: 'solver' });
    expect(translateWebProgress({ event: 'proof_checked', workerId: 'solver', passed: false, reused: false })?.details)
      .toEqual({ workerId: 'solver', passed: false, reused: false });
    expect(translateWebProgress({ event: 'evaluation_finished', status: 'failed', durationMs: 100 })?.details)
      .toEqual({ status: 'failed' });
  });

  it('translates genuine search and cooperation events with bounded role and task identifiers', () => {
    expect(translateWebProgress({ event: 'research_action', workerId: 'solver', operation: 'decompose',
      reason: 'private strategy', estimates: [{ private: true }] })?.details)
      .toEqual({ workerId: 'solver', operation: 'decompose' });
    expect(translateWebProgress({ event: 'task_assigned', workerId: 'engineer', taskId: 'goal-1',
      kind: 'goal', seedCommit: 'private-commit' })?.details).toEqual({ workerId: 'engineer', taskId: 'goal-1' });
    expect(translateWebProgress({ event: 'review_assigned', workerId: 'researcher-1', role: 'reviewer' })?.details)
      .toEqual({ workerId: 'researcher-1', role: 'reviewer' });
  });

  it('uses fixed failure descriptions and drops malformed details instead of exposing raw logs', () => {
    const message = translateWebProgress({ event: 'turn_failed', workerId: '../secret', turn: -1,
      reason: 'math_model_authentication_failed', error: 'sk-private', message: 'private log' });
    expect(message).toEqual({ type: 'progress', event: 'turn_failed', message: 'API Key 认证失败，请检查密钥和服务商' });
    expect(translateWebProgress({ event: 'research_action', operation: 'run-shell', workerId: 'x'.repeat(65) })?.details).toBeUndefined();
    expect(translateWebProgress({ event: 'context_compiled', usedBytes: Infinity, maxBytes: 0 })?.details).toEqual({ maxBytes: 0 });
  });

  it.each([null, [], 'private log', {}, { event: 'unknown' }, { event: 'constructor' }, { event: 'toString' }])
    ('ignores unrecognized or unstructured runtime output (%#)', value => {
      expect(translateWebProgress(value)).toBeUndefined();
    });

  it('validates safe scalar metadata and rejects malformed protocol detail objects', () => {
    const valid = { workerId: 'solver', taskId: 'goal-1', turn: 0, passed: false, conditional: true, reused: false,
      operation: 'direct', usedBytes: 0, maxBytes: 1_024, status: 'changes_requested', role: 'reviewer' };
    expect(isWebEventDetails(valid)).toBe(true);
    expect(sanitizeWebEventDetails({ ...valid, instructions: 'private', nested: {} })).toEqual(valid);
    for (const invalid of [null, [], 'private', { workerId: '/work/private' }, { taskId: 'x'.repeat(65) },
      { usedBytes: -1 }, { maxBytes: Number.MAX_SAFE_INTEGER + 1 }, { turn: 1.5 }, { passed: 'true' },
      { status: 'private log' }, { operation: 'shell' }, { role: 'admin' }, { arbitrary: 'private' },
      { workerId: 'solver', nested: { apiKey: 'sk-private' } }]) expect(isWebEventDetails(invalid)).toBe(false);
    expect(isWebEventDetails({})).toBe(true);
    expect(sanitizeWebEventDetails(Object.create({ workerId: 'private-inherited' }))).toBeUndefined();
  });
});
