import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, describe, expect, it } from 'vitest';
import {
  createMathProofProgressMonitor,
  finalizeMathRunReceipt,
  mathRunExitCode,
  recoverMathRunReceiptCleanup,
  type MathCleanupOutcome,
} from '../src/math/mathRunLifecycle';

const completed: MathCleanupOutcome = {
  status: 'completed',
  reason: 'resources_removed',
  resourcesRemoved: true,
  manifestRetained: false,
};
const pending: MathCleanupOutcome = {
  status: 'pending',
  reason: 'remove_resources',
  resourcesRemoved: false,
  manifestRetained: true,
};
const roots: string[] = [];
const output = () => {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), 'math-run-lifecycle-'));
  roots.push(root);
  return path.join(root, 'result.json');
};
afterEach(() => {
  for (const root of roots.splice(0)) fs.rmSync(root, { recursive: true, force: true });
});

describe('math result and resource lifecycle', () => {
  it('recovers interrupted cleanup without changing proof evidence and rejects another run', () => {
    const file = output();
    const identity = {
      run_id: 'run',
      team_id: 'team',
      run_inputs_digest: 'a'.repeat(64),
      run_binding_ref: '/binding.json',
      run_binding_digest: 'b'.repeat(64),
    };
    const saved = {
      schema: 'deepscientist.mathematics.proof-team-run.v2',
      ...identity,
      status: 'evaluated_passed',
      evaluator: { status: 'passed' },
      cleanup: pending,
      finalized_at: null as string | null,
    };
    fs.writeFileSync(file, JSON.stringify(saved));
    expect(() => recoverMathRunReceiptCleanup({ output: file, identity: { ...identity, run_id: 'other' } })).toThrow(
      'math_cleanup_receipt_identity_mismatch'
    );
    recoverMathRunReceiptCleanup({ output: file, identity });
    const first = fs.readFileSync(file, 'utf8');
    recoverMathRunReceiptCleanup({ output: file, identity });
    expect(fs.readFileSync(file, 'utf8')).toBe(first);
    expect(JSON.parse(first)).toMatchObject({
      ...identity,
      status: 'evaluated_passed',
      evaluator: { status: 'passed' },
      cleanup: completed,
    });
  });
  it('preserves proof success while making cleanup failures a distinct unsuccessful exit', async () => {
    const file = output();
    const result = await finalizeMathRunReceipt({
      output: file,
      receipt: { status: 'evaluated_passed', run_id: 'run' },
      pending,
      cleanup: async () => {
        expect(JSON.parse(fs.readFileSync(file, 'utf8'))).toMatchObject({
          cleanup: { status: 'pending' },
          finalized_at: null,
        });
        throw new Error('secret transport failure');
      },
    });
    expect(result).toMatchObject({ status: 'evaluated_passed', cleanup: { status: 'failed', manifestRetained: true } });
    expect(fs.readFileSync(file, 'utf8')).not.toContain('secret');
    expect(
      mathRunExitCode({
        startupOnly: false,
        completionSignalValid: true,
        evaluatorStatus: 'passed',
        cleanup: result.cleanup,
      })
    ).toBe(3);
  });

  it('finishes only after actual cleanup and refuses to overwrite an existing result', async () => {
    const file = output();
    const result = await finalizeMathRunReceipt({
      output: file,
      receipt: { run_id: 'run' },
      pending,
      cleanup: async () => completed,
    });
    expect(result.cleanup).toEqual(completed);
    expect(JSON.parse(fs.readFileSync(file, 'utf8')).finalized_at).toEqual(expect.any(String));
    await expect(
      finalizeMathRunReceipt({ output: file, receipt: { run_id: 'other' }, pending, cleanup: async () => completed })
    ).rejects.toThrow();
  });

  it('does not overwrite a concurrently replaced result', async () => {
    const file = output();
    await expect(
      finalizeMathRunReceipt({
        output: file,
        receipt: { run_id: 'run' },
        pending,
        cleanup: async () => {
          fs.writeFileSync(file, JSON.stringify({ run_id: 'other' }));
          return completed;
        },
      })
    ).rejects.toThrow('math_final_receipt_changed');
    expect(JSON.parse(fs.readFileSync(file, 'utf8'))).toEqual({ run_id: 'other' });
  });

  it('keeps runtime failure, limits, incomplete proof and successful cleanup distinct', () => {
    const base = { startupOnly: false, completionSignalValid: true, evaluatorStatus: 'passed', cleanup: completed };
    expect(mathRunExitCode(base)).toBe(0);
    expect(mathRunExitCode({ ...base, runtimeError: 'failure' })).toBe(1);
    expect(mathRunExitCode({ ...base, evaluatorStatus: 'failed' })).toBe(2);
    expect(mathRunExitCode({ ...base, limitReached: 'math_run_wall_limit' })).toBe(4);
    expect(mathRunExitCode({ ...base, cleanup: pending })).toBe(3);
  });
});

describe('checked proof progress and explicit limits', () => {
  it('does not infer no progress after the bounded evidence history fills', () => {
    let time = 1;
    const monitor = createMathProofProgressMonitor({ runId: 'run', startedAt: 1, now: () => time });
    const observation = {
      checkedEvidenceIds: Array.from({ length: 4097 }, (_, index) => index.toString(16).padStart(64, '0')),
      activityFingerprint: 'a'.repeat(64),
      pendingProofAssignments: 1,
      solverReady: false,
    };
    monitor.observe(observation);
    time = 100_000;
    const restored = createMathProofProgressMonitor({
      runId: 'run',
      startedAt: 1,
      retained: monitor.state(),
      now: () => time,
    });
    expect(restored.snapshot().evidenceCoverage).toBe('bounded');
    expect(restored.limitReason({ noProgressSeconds: 1 }, true)).toBeUndefined();
    expect(restored.limitReason({ maxRunSeconds: 1 }, true)).toBe('math_run_wall_limit');
  });
  it('does not reset progress on heartbeats, source activity or repeated old evidence after restart', () => {
    let time = 1000;
    const monitor = createMathProofProgressMonitor({ runId: 'run', startedAt: 1000, now: () => time });
    const event = {
      checkedEvidenceIds: ['a'.repeat(64)],
      activityFingerprint: 'b'.repeat(64),
      pendingProofAssignments: 1,
      solverReady: false,
    };
    time = 2000;
    monitor.observe(event);
    time = 5000;
    monitor.observe({ ...event, activityFingerprint: 'c'.repeat(64) });
    const restored = createMathProofProgressMonitor({
      runId: 'run',
      startedAt: 1000,
      retained: monitor.state(),
      now: () => time,
    });
    time = 8000;
    restored.observe(event);
    expect(restored.snapshot()).toMatchObject({
      lastCheckedEvidenceAt: 2000,
      noNewCheckedEvidenceMs: 6000,
      distinctCheckedEvidenceCount: 1,
      originalObligationsRemaining: null,
    });
    expect(restored.limitReason({ noProgressSeconds: 5 }, false)).toBe('math_run_no_progress_limit');
    expect(restored.limitReason({ noProgressSeconds: 5 }, true)).toBe('math_run_no_progress_limit');
    expect(restored.limitReason({ maxRunSeconds: 7 }, false)).toBe('math_run_wall_limit');
  });
  it('enforces an explicit no-progress budget while unrelated Team work is running', () => {
    let time = 1000;
    const monitor = createMathProofProgressMonitor({ runId: 'run', startedAt: 1000, now: () => time });
    monitor.observe({
      checkedEvidenceIds: [],
      activityFingerprint: 'a'.repeat(64),
      pendingProofAssignments: 1,
      solverReady: false,
    });
    time = 7000;
    expect(monitor.limitReason({ noProgressSeconds: 5 }, false)).toBe('math_run_no_progress_limit');
  });

  it('leaves long proof turns unlimited unless a limit was specified', () => {
    const monitor = createMathProofProgressMonitor({ runId: 'run', startedAt: 0, now: () => 10_000_000 });
    expect(monitor.limitReason({}, true)).toBeUndefined();
    expect(monitor.snapshot()).toMatchObject({ lastCheckedEvidenceAt: null, pendingProofAssignments: null });
  });

  it('rejects cross-run or malformed progress instead of silently resetting the budget', () => {
    const initial = createMathProofProgressMonitor({ runId: 'run', startedAt: 1, now: () => 100 });
    expect(() =>
      createMathProofProgressMonitor({ runId: 'other', startedAt: 1, retained: initial.state(), now: () => 100 })
    ).toThrow('math_progress_state_invalid');
    expect(() =>
      createMathProofProgressMonitor({
        runId: 'run',
        startedAt: 1,
        retained: { ...initial.state(), lastEvidenceAt: 1000 },
        now: () => 100,
      })
    ).toThrow();
  });
});
