import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, describe, expect, it } from 'vitest';
import { readSolverRunState, writeSolverRunState, type SolverRunState } from '../src/solver/archive';
import { buildRunInspection, renderRunInspection } from '../src/solver/inspection';
import { captureObligationSnapshot, diffObligationProgress } from '../src/solver/obligationProgress';
import { finalCandidateReviewReady } from '../src/solver/modules/search';
import { taskVersion, type TaskRecord } from '../src/solver/tasks';
import type { TaskProof } from '../src/solver/cooperativeProof';

const roots: string[] = [];
afterEach(() => { for (const root of roots.splice(0)) fs.rmSync(root, { recursive: true, force: true }); });
function fixture() {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), 'obligation-archive-')); roots.push(root);
  const goal: TaskRecord = { task: { id: 'goal', kind: 'goal', objective: 'Prove the original claim', dependsOn: [],
    revision: 0, proofPath: 'Submission.lean', theoremName: 'original', type: 'True' }, status: 'pending', attempts: 0 };
  const before = captureObligationSnapshot([goal], { environmentDigest: 'environment' });
  goal.status = 'integrated';
  goal.integratedCheck = { taskDigest: taskVersion(goal.task), passed: true, commit: 'canonical', sourceDigest: 'source',
    seedCommit: 'seed', changes: [], verification: { status: 'kernel_verified', targetCommit: 'projection', results: [
      { status: 'kernel_verified', targetCommit: 'projection', receiptId: 'receipt' },
    ] }, references: { environmentDigest: 'environment', sourceCommit: 'projection', contextDigest: 'context',
      root: { file: 'Submission.lean', name: 'original' }, inputs: [], tasks: [], statement: [], proof: [] } } as TaskProof;
  const after = captureObligationSnapshot([goal], { environmentDigest: 'environment' });
  const state = { schema: 'deepscientist.math.solver.v1', runId: 'fixture', worktree: root, phase: 'running', turns: 1,
    model: 'fixture', effort: 'xhigh', taskDigest: 'task', buildDigest: 'build', environmentDigest: 'environment',
    evaluatorDigest: 'evaluator', problem: { workspace: root, receiptDigest: 'problem', targets: [],
      contract: { problemId: 'fixture', informalStatement: 'Prove True', formalStatement: 'True', assumptions: [] } },
    cooperation: { tasks: [goal], progressSnapshot: after, progressReceipts: [diffObligationProgress(before, after, 10)!] },
  } as unknown as SolverRunState;
  const file = path.join(root, 'state.json');
  return { state, file, read: () => { writeSolverRunState(file, state); return readSolverRunState(file); } };
}

describe('persisted mathematical progress', () => {
  it('restores and renders recorded transitions without granting fresh acceptance', () => {
    const { read } = fixture(), restored = read();
    const report = buildRunInspection(restored);
    expect(report.mathematics.recentChanges[0].obligations.closed[0].after.taskId).toBe('goal');
    expect(renderRunInspection(report)).toContain('Mathematical changes');
    expect(diffObligationProgress(restored.cooperation!.progressSnapshot,
      captureObligationSnapshot(restored.cooperation!.tasks, { environmentDigest: 'environment' }))).toBeUndefined();
    expect(finalCandidateReviewReady(restored.cooperation!.tasks)).toBe(false);
  });

  it('keeps legacy checkpoints without mathematical progress readable', () => {
    const { state, read } = fixture();
    delete state.cooperation!.progressSnapshot; delete state.cooperation!.progressReceipts;
    expect(read().cooperation!.progressSnapshot).toBeUndefined();
  });

  it.each(['closed', 'reopened', 'changed'] as const)('rejects malformed %s changes before inspection can dereference them', kind => {
    const { state, read } = fixture();
    state.cooperation!.progressReceipts![0].obligations[kind] = [{}] as never;
    expect(read).toThrow(`math_resume_state_invalid:cooperation.progressReceipts.0.obligations.${kind}.0.before`);
  });

  it('rejects a malformed original-goal frontier before diffing the restored snapshot', () => {
    const { state, read } = fixture();
    delete (state.cooperation!.progressSnapshot!.goals[0] as Partial<typeof state.cooperation.progressSnapshot.goals[number]>).frontier;
    expect(read).toThrow('math_resume_state_invalid:cooperation.progressSnapshot.goals.0.frontier');
  });

  it('rejects incomplete proof-reference records instead of crashing in context or progress compilation', () => {
    const { state, read } = fixture();
    delete (state.cooperation!.tasks[0].integratedCheck!.references as Partial<NonNullable<TaskProof['references']>>).inputs;
    expect(read).toThrow('math_resume_state_invalid:cooperation.tasks.0.integratedCheck.references.inputs');
  });
});
