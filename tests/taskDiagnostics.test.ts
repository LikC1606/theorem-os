import { describe, expect, it } from 'vitest';
import type { TaskProof } from '../src/solver/cooperativeProof';
import { clearTaskDiagnostic, currentTaskFeedback, setTaskDiagnostic } from '../src/solver/taskDiagnostics';
import { taskVersion, type CooperativeTask, type TaskRecord } from '../src/solver/tasks';

const task: CooperativeTask = { id: 'helper', kind: 'lemma', objective: 'Prove the helper', dependsOn: [],
  revision: 0, proofPath: 'Submission.lean', theoremName: 'Submission.helper', type: 'True' };
const node = (): TaskRecord => ({ task, status: 'blocked', attempts: 1,
  assignment: { taskId: task.id, taskDigest: taskVersion(task), workerId: 'engineer', seedCommit: 'assignment-seed' } });
const proof = (passed = false): TaskProof => ({ commit: 'proof-commit', sourceDigest: 'proof-source', seedCommit: 'seed',
  passed, taskDigest: taskVersion(task), changes: [],
  verification: { schema: 'deepscientist.mathematics.verification-batch/v1',
    status: passed ? 'kernel_verified' : 'failed', results: [] },
  references: { sourceCommit: 'proof-commit', environmentDigest: 'env', contextDigest: 'proof-context',
    root: { file: 'Submission.lean', name: 'Submission.helper' }, statement: [], proof: [], inputs: [] } });

describe('task diagnostic lifecycle', () => {
  it('clears a successful task current error while retaining the attempted version in history', () => {
    const record = node();
    setTaskDiagnostic(record, 'M4: application failed', 'env', proof());
    const failedAttempt = structuredClone(record.diagnostic);
    record.status = 'integrated'; record.integratedCheck = proof(true);
    clearTaskDiagnostic(record);
    expect(record.feedback).toBeUndefined();
    expect(record.diagnostic).toBeUndefined();
    expect(record.diagnosticHistory).toEqual([failedAttempt]);
    expect(currentTaskFeedback(record, 'env')).toBeUndefined();
    clearTaskDiagnostic(record);
    expect(record.diagnosticHistory).toEqual([failedAttempt]);
  });

  it('hides a legacy M4 error beside an archived successful integrated proof', () => {
    const record = node();
    record.status = 'integrated'; record.feedback = 'M4: stale failure'; record.integratedCheck = proof(true);
    const archived = JSON.parse(JSON.stringify(record)) as TaskRecord;
    expect(currentTaskFeedback(archived, 'env')).toBeUndefined();
    expect(archived.feedback).toBe('M4: stale failure');
    clearTaskDiagnostic(archived);
    expect(archived.diagnosticHistory).toMatchObject([{ message: 'M4: stale failure',
      taskDigest: taskVersion(task), legacy: true }]);
  });

  it('hides a diagnostic after its task or environment version changes', () => {
    const record = node();
    setTaskDiagnostic(record, 'M4: version-bound failure', 'env', proof());
    expect(currentTaskFeedback(record, 'env')).toBe('M4: version-bound failure');
    expect(currentTaskFeedback(record, 'new-env')).toBeUndefined();
    record.task = { ...task, revision: 1 };
    expect(currentTaskFeedback(record, 'env')).toBeUndefined();
    expect(record.diagnostic?.taskDigest).toBe(taskVersion(task));
  });

  it('shows a new blocked failure even when a previous successful proof remains', () => {
    const record = node();
    record.integratedCheck = proof(true);
    setTaskDiagnostic(record, 'M4: latest integration failed', 'env', proof());
    expect(currentTaskFeedback(record, 'env')).toBe('M4: latest integration failed');
    record.status = 'integrated'; record.task = { ...task, revision: 1 };
    setTaskDiagnostic(record, 'M4: revised task failed', 'env');
    expect(currentTaskFeedback(record, 'env')).toBe('M4: revised task failed');
  });

  it('binds failures to their attempted proof and keeps only the eight most recent history entries', () => {
    const record = node();
    setTaskDiagnostic(record, 'proof failed', 'env', proof());
    expect(record.diagnostic).toMatchObject({ taskDigest: taskVersion(task), environmentDigest: 'env',
      commit: 'proof-commit', sourceDigest: 'proof-source', contextDigest: 'proof-context', verificationStatus: 'failed' });
    setTaskDiagnostic(record, 'explicit attempt failed', 'env', proof(), 'explicit-commit');
    expect(record.diagnostic?.commit).toBe('explicit-commit');
    setTaskDiagnostic(record, 'assignment failed', 'env');
    expect(record.diagnostic?.commit).toBe('assignment-seed');
    for (let index = 0; index < 10; index++) setTaskDiagnostic(record, `attempt-${index}`, 'env');
    expect(record.diagnosticHistory?.map(item => item.message)).toEqual([
      'attempt-1', 'attempt-2', 'attempt-3', 'attempt-4', 'attempt-5', 'attempt-6', 'attempt-7', 'attempt-8',
    ]);
    clearTaskDiagnostic(record);
    expect(record.diagnosticHistory?.map(item => item.message)).toEqual([
      'attempt-2', 'attempt-3', 'attempt-4', 'attempt-5', 'attempt-6', 'attempt-7', 'attempt-8', 'attempt-9',
    ]);
  });
});
