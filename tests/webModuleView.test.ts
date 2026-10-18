import { describe, expect, it } from 'vitest';
import { latestModuleActivity, moduleState } from '../apps/web/client/moduleView';
import type { WebEvent, WebModuleId, WebModuleSnapshot, WebRun } from '../apps/web/shared';

const at = '2026-10-18T08:00:00.000Z';
const run = (overrides: Partial<WebRun> = {}): WebRun => ({
  id: 'module-fixture', title: 'A theorem', status: 'running', phase: 'turn_started', createdAt: at, updatedAt: at,
  timings: { preparing: at, solving: at }, providerId: 'openai', model: 'fixture', effort: 'high', environment: 'mathlib',
  source: 'theorem example : True := by sorry', task: 'Prove the theorem',
  maxTurns: 3, maxRunSeconds: 60, workers: 2, coordination: 'cooperative', events: [], ...overrides,
});
const snapshot = (type: string, details?: WebEvent['details'], activeWorkers: string[] = []): WebModuleSnapshot => ({
  eventCount: 1, firstAt: at, lastEvent: { sequence: 1, at, type, message: 'Actual module event', ...(details ? { details } : {}) }, activeWorkers,
});
const researchModules: WebModuleId[] = ['M1', 'M2', 'M3', 'M4', 'M5'];

describe('latest module activity', () => {
  it('has no destination until a module event has been observed', () => {
    expect(latestModuleActivity({})).toBeUndefined();
  });

  it('uses event sequence when modules share a timestamp or arrive in a different display order', () => {
    const context = snapshot('context_compiled'), construction = snapshot('turn_started');
    context.lastEvent.sequence = 8;
    construction.lastEvent.sequence = 9;
    context.lastEvent.at = '2026-10-18T08:00:01.000Z';
    expect(latestModuleActivity({ M1: construction, M4: context })).toEqual({ id: 'M1', event: construction.lastEvent });
  });

  it('can locate a module from its retained summary after its events have rotated out', () => {
    const evidence = snapshot('evaluation_finished', { status: 'evaluated_passed' });
    const value = run({ modules: { S3: evidence }, events: [] });
    expect(latestModuleActivity(value.modules!)).toEqual({ id: 'S3', event: evidence.lastEvent });
    expect(moduleState('S3', value, evidence).tone).not.toBe('passed');
  });
});

describe('module visualization evidence boundaries', () => {
  it.each([...researchModules, 'S3'] as WebModuleId[])('shows %s without inventing activity in a draft or queued run', id => {
    expect(moduleState(id)).toEqual({ tone: 'pending', label: '未运行' });
    expect(moduleState(id, run({ status: 'queued', phase: 'queued', timings: {} })).tone).toBe('pending');
  });

  it('shows parallel construction until all observed worker intervals end', () => {
    expect(moduleState('M1', run(), snapshot('turn_checkpoint', { workerId: 'worker-1' }, ['worker-2']))).toEqual({ tone: 'active', label: '构造中' });
    expect(moduleState('M1', run(), snapshot('turn_checkpoint', { workerId: 'worker-2' }))).toEqual({ tone: 'observed', label: '已有执行记录' });
  });

  it('distinguishes candidate, conditional and failed local checks from independent acceptance', () => {
    expect(moduleState('M2', run(), snapshot('proof_checked', { passed: true }))).toEqual({ tone: 'observed', label: '候选通过' });
    expect(moduleState('M2', run(), snapshot('task_checked', { passed: true, conditional: true }))).toEqual({ tone: 'observed', label: '条件性通过' });
    expect(moduleState('M2', run(), snapshot('task_checked', { passed: true }))).toEqual({ tone: 'observed', label: '局部通过' });
    expect(moduleState('M2', run(), snapshot('task_checked', { passed: false }))).toEqual({ tone: 'feedback', label: '待修复' });
    expect(moduleState('M2', run(), snapshot('lemma_checked'))).toEqual({ tone: 'observed', label: '已有检查记录' });
    expect(moduleState('S3', run()).tone).toBe('pending');
  });

  it('keeps unknown check results unknown and source rejections visible', () => {
    expect(moduleState('M2', run(), snapshot('proof_checked')).label).toBe('已有检查记录');
    expect(moduleState('M2', run(), snapshot('source_rejected')).label).toBe('约束拒绝');
  });

  it('does not treat a compiler or scheduler observation as an active model call', () => {
    expect(moduleState('M4', run(), snapshot('context_compiled')).tone).toBe('observed');
    expect(moduleState('M3', run(), snapshot('research_action')).tone).toBe('observed');
    expect(moduleState('M5', run(), snapshot('task_assigned')).tone).toBe('observed');
    expect(moduleState('M1', run()).label).toBe('无活动记录');
    expect(moduleState('M5', run(), snapshot('plan_rejected'))).toEqual({ tone: 'feedback', label: '计划待调整' });
  });

  it('waits for the completed final result even after an evaluation finished event says passed', () => {
    const evidence = snapshot('evaluation_finished', { status: 'evaluated_passed' });
    const value = run({ phase: 'evaluation_finished', timings: { evaluating: at } });
    expect(moduleState('S3', value, evidence)).toEqual({ tone: 'observed', label: '等待结果确认' });
    expect(moduleState('S3', { ...value, result: { status: 'evaluated_passed', proof: 'by trivial', report: {} } }, evidence).tone).not.toBe('passed');
    expect(moduleState('S3', { ...value, status: 'completed', result: { status: 'evaluated_passed', proof: 'by trivial', report: {} } }, evidence))
      .toEqual({ tone: 'passed', label: '验收通过' });
  });

  it.each(['cancelled', 'error', 'running', 'queued'] as const)('never shows acceptance for a %s run containing a late passed result', status => {
    const value = run({ status, result: { status: 'evaluated_passed', proof: 'by trivial', report: {} } });
    expect(moduleState('S3', value, snapshot('evaluation_finished', { status: 'evaluated_passed' })).tone).not.toBe('passed');
  });

  it.each(['evaluated_failed', 'evaluated_rejected'])('shows %s only as failed final acceptance', status => {
    const value = run({ status: 'completed', result: { status, proof: 'by sorry', report: {} } });
    expect(moduleState('S3', value).tone).toBe('failed');
    for (const id of researchModules) expect(moduleState(id, value).tone).not.toBe('passed');
  });

  it('does not keep research active after evaluation starts or cancellation arrives', () => {
    const evidence = snapshot('turn_started', { workerId: 'worker-1' }, ['worker-1']);
    expect(moduleState('M1', run({ phase: 'evaluation_started', timings: { evaluating: at } }), evidence).tone).not.toBe('active');
    expect(moduleState('M1', run({ status: 'cancelled' }), evidence)).toEqual({ tone: 'stopped', label: '已停止' });
    expect(moduleState('S3', run({ status: 'cancelled', timings: { evaluating: at } }), snapshot('evaluation_started')).label).toBe('验收已中断');
  });

  it('keeps unobserved modules neutral when a run ends before evaluation', () => {
    const value = run({ status: 'completed', result: { status: 'incomplete', proof: '', report: {} } });
    for (const id of researchModules) expect(moduleState(id, value)).toEqual({ tone: 'pending', label: '无活动记录' });
    expect(moduleState('S3', value)).toEqual({ tone: 'pending', label: '无验收记录' });
  });
});
