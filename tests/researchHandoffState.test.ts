import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, expect, it } from 'vitest';
import { readSolverRunState, writeSolverRunState, type SolverRunState } from '../src/solver/archive';

const roots: string[] = [];
afterEach(() => { for (const root of roots.splice(0)) fs.rmSync(root, { recursive: true, force: true }); });
const reference = { taskId: 'needed', taskDigest: 'a'.repeat(64) };
const deferred = { id: 'handoff', deliveryId: 'delivery', status: 'deferred', reason: 'Await the exact checked estimate.', waitsOn: [reference] };
function stateFile(decision: unknown): string {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), 'handoff-state-test-')); roots.push(root);
  const file = path.join(root, 'state.json');
  writeSolverRunState(file, { schema: 'deepscientist.math.solver.v1', runId: 'fixture-run',
    problem: { workspace: '/fixture', receiptDigest: 'fixture-receipt' },
    taskDigest: 'task', buildDigest: 'build', environmentDigest: 'environment', evaluatorDigest: 'evaluator',
    model: 'fixture', effort: 'fixture', worktree: '/fixture', phase: 'prepared', turns: 0,
    cooperation: { tasks: [], researchDecisions: [decision] },
  } as SolverRunState);
  return file;
}

it('preserves exact waiting contracts through the actual durable state reader and writer', () => {
  const restored = readSolverRunState(stateFile(deferred));
  expect(restored.cooperation!.researchDecisions).toEqual([deferred]);
  expect(restored.cooperation!.tasks).toEqual([]);
});

it('keeps historical deferred decisions without a waiting condition readable', () => {
  const { waitsOn: _waits, ...legacy } = deferred;
  expect(readSolverRunState(stateFile(legacy)).cooperation!.researchDecisions).toEqual([legacy]);
});

it.each([
  { waitsOn: [] }, { waitsOn: [reference, reference] }, { waitsOn: ['needed'] },
  { waitsOn: [{ ...reference, taskDigest: 'unbound-version' }] },
  { waitsOn: [{ ...reference, taskId: '../other-task' }] },
  { waitsOn: [{ ...reference, accepted: true }] },
  { status: 'adopted' }, { status: 'rejected' },
])('rejects malformed persisted waiting conditions instead of silently weakening them: %j', change => {
  expect(() => readSolverRunState(stateFile({ ...deferred, ...change })))
    .toThrow('math_resume_state_invalid:cooperation.researchDecisions');
});
