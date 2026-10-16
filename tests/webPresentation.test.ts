import { describe, expect, it } from 'vitest';
import { formatDuration, isAcceptedRun, resultDescription, runProgress } from '../apps/web/presentation';
import type { WebRun } from '../apps/web/shared';

const at = (seconds: number) => new Date(Date.UTC(2026, 9, 16) + seconds * 1000).toISOString();
const run = (changes: Partial<WebRun> = {}): WebRun => ({
  id: 'run', title: 'Square expansion', status: 'running', phase: 'proof_environment',
  createdAt: at(0), updatedAt: at(10), timings: { preparing: at(10) },
  providerId: 'openai', model: 'test-model', effort: 'high', environment: 'mathlib',
  source: 'theorem example : True := by sorry', task: 'Prove the theorem',
  maxTurns: 5, maxRunSeconds: 30, workers: 1, coordination: 'independent', events: [],
  ...changes,
});

describe('workbench phase and elapsed-time presentation', () => {
  it('requires a completed job before showing an accepted result', () => {
    const result = { status: 'evaluated_passed', proof: 'by trivial', report: {} };
    for (const status of ['queued', 'running', 'cancelled', 'error'] as const) {
      const value = run({ status, result, phase: 'evaluated_passed' });
      expect(isAcceptedRun(value)).toBe(false);
      expect(runProgress(value).phaseLabel).not.toBe('验收通过');
      expect(resultDescription(value)).not.toBe('完整原题通过独立 Lean 验收。');
    }
    expect(isAcceptedRun(run({ status: 'completed', result }))).toBe(true);
  });

  it('keeps queue and Mathlib preparation separate from the solving clock', () => {
    const queued = runProgress(run({ status: 'queued', phase: 'queued', timings: {} }), Date.parse(at(9)));
    expect(queued.index).toBe(0);
    expect(queued.elapsed).toBe(9000);
    expect(queued.solvingElapsed).toBeNull();
    const preparing = runProgress(run(), Date.parse(at(120)));
    expect(preparing.index).toBe(1);
    expect(preparing.elapsed).toBe(120000);
    expect(preparing.steps[1].elapsed).toBe(110000);
    expect(preparing.solvingElapsed).toBeNull();
    expect(resultDescription(run())).toContain('解题尚未开始');
    const solving = runProgress(run({ phase: 'proof_check_started',
      timings: { preparing: at(10), solving: at(130) } }), Date.parse(at(150)));
    expect(solving.steps[0].elapsed).toBe(10000);
    expect(solving.steps[1].elapsed).toBe(120000);
    expect(solving.solvingElapsed).toBe(20000);
    expect(solving.phaseLabel).toBe('检查候选证明');
  });

  it('stops the solving clock at independent evaluation and freezes completed durations', () => {
    const value = run({ phase: 'evaluation_started', timings: { preparing: at(10), solving: at(130), evaluating: at(160) } });
    const evaluating = runProgress(value, Date.parse(at(170)));
    expect(evaluating.solvingElapsed).toBe(30000);
    expect(evaluating.steps[3].elapsed).toBe(10000);
    const completed = runProgress({ ...value, status: 'completed', finishedAt: at(180),
      result: { status: 'evaluated_passed', proof: 'by trivial', report: {} } }, Date.parse(at(1000)));
    expect(completed.phaseLabel).toBe('验收通过');
    expect(completed.elapsed).toBe(180000);
    expect(completed.solvingElapsed).toBe(30000);
    expect(completed.steps[3].elapsed).toBe(20000);
    expect(completed.steps.every(step => step.state === 'done')).toBe(true);
  });

  it.each(['cancelled', 'error', 'completed'] as const)('shows unexecuted evaluation after a %s solve', status => {
    const value = run({ status, phase: status, finishedAt: at(150), timings: { preparing: at(10), solving: at(130) },
      ...(status === 'completed' ? { result: { status: 'incomplete', proof: 'by sorry', report: {} } } : {}) });
    const progress = runProgress(value, Date.parse(at(1000)));
    expect(progress.elapsed).toBe(150000);
    expect(progress.solvingElapsed).toBe(20000);
    expect(progress.steps[2].state).toBe(status === 'error' ? 'error' : 'stopped');
    expect(progress.steps[3].state).toBe('skipped');
    expect(progress.steps[3].elapsed).toBeNull();
    expect(progress.phaseLabel).not.toBe('验收通过');
  });

  it('does not mark skipped work complete when a queued task is cancelled', () => {
    const progress = runProgress(run({ status: 'cancelled', phase: 'cancelled', timings: {}, finishedAt: at(9) }), Date.parse(at(1000)));
    expect(progress.steps.map(step => step.state)).toEqual(['stopped', 'skipped', 'skipped', 'skipped']);
    expect(progress.solvingElapsed).toBeNull();
  });

  it.each(['evaluated_failed', 'evaluated_rejected'])('keeps %s distinct from successful acceptance', status => {
    const value = run({ status: 'completed', phase: status, finishedAt: at(180), result: { status, proof: 'by sorry', report: {} } });
    expect(runProgress(value).phaseLabel).toBe('验收未通过');
    expect(runProgress(value).steps[3].state).toBe('error');
    expect(resultDescription(value)).not.toBe('完整原题通过独立 Lean 验收。');
  });

  it('falls back to legacy events and terminal update time without requiring a new archive schema', () => {
    const value = run({ timings: undefined, phase: 'finished', status: 'completed', updatedAt: at(180),
      events: [{ sequence: 1, at: at(10), type: 'preparing', message: '' },
        { sequence: 2, at: at(130), type: 'solve_started', message: '' },
        { sequence: 3, at: at(160), type: 'evaluation_started', message: '' }],
      result: { status: 'evaluated_passed', proof: 'by trivial', report: {} } });
    const progress = runProgress(value);
    expect(progress.elapsed).toBe(180000);
    expect(progress.steps.map(step => step.elapsed)).toEqual([10000, 120000, 30000, 20000]);
  });

  it('formats long, unknown and skewed durations without invalid or negative clocks', () => {
    expect(formatDuration(89999)).toBe('01:29');
    expect(formatDuration(3661000)).toBe('01:01:01');
    expect(formatDuration(null)).toBe('--:--');
    expect(formatDuration(Number.NaN)).toBe('--:--');
    expect(runProgress(run(), Date.parse(at(-10))).elapsed).toBe(0);
    expect(runProgress(run({ createdAt: 'invalid' })).elapsed).toBeNull();
  });
});
