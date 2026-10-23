import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it } from 'vitest';
import { readSolverRunState, writeSolverRunState, type SolverRunState } from '../src/solver/archive';
import { captureResearchBasis, settleResearch } from '../src/solver/researchRecords';
import { taskVersion, type CooperativeTask } from '../src/solver/tasks';

const task: CooperativeTask = { id: 'route', kind: 'research', objective: 'Investigate an exact estimate', dependsOn: [], revision: 0 };
const finding = 'A diagonal family refutes the scoped estimate.';

describe('research completion archive schema', () => {
  let root: string, state: SolverRunState;
  beforeEach(() => {
    root = fs.mkdtempSync(path.join(os.tmpdir(), 'research-archive-'));
    const basis = captureResearchBasis(task, { problemReceiptDigest: 'fixture-receipt', environmentDigest: 'fixture-environment',
      sourceDigest: 'fixture-source', tasks: [] });
    const assignment = { taskId: task.id, taskDigest: taskVersion(task), seedCommit: 'fixture-seed',
      workerId: 'researcher', assignmentId: 'fixture-assignment', researchBasis: basis };
    const completion = settleResearch({ id: 'publication', assignment, basis, commit: 'fixture-delivery', finding, complete: true })!;
    state = { schema: 'deepscientist.math.solver.v1', runId: 'fixture', worktree: root, phase: 'running', turns: 0,
      model: 'fixture', effort: 'fixture', taskDigest: 'task', buildDigest: 'build', environmentDigest: 'fixture-environment',
      evaluatorDigest: 'fixture-evaluator', problem: { workspace: root, receiptDigest: 'fixture-receipt' },
      cooperation: { tasks: [{ task, status: 'completed', attempts: 1, assignment, finding, researchCompletion: completion }],
        deliveries: [{ id: completion.id, producer: 'researcher', taskId: task.id, taskDigest: taskVersion(task),
          kind: 'research', status: 'advisory', statement: task.objective, premises: [], dependencies: [], remainingObligations: [],
          summary: finding, evidenceRefs: [], createdAt: 1, finding, findingDigest: completion.findingDigest, researchRecord: structuredClone(completion) }],
        history: [{ task, status: 'completed', finding, researchCompletion: structuredClone(completion) }] } } as unknown as SolverRunState;
  });
  afterEach(() => fs.rmSync(root, { recursive: true, force: true }));
  const read = () => {
    const file = path.join(root, 'state.json'); writeSolverRunState(file, state); return readSolverRunState(file);
  };

  it('preserves the same immutable record in the node, delivery and history without creating proof evidence', () => {
    const restored = read(), node = restored.cooperation!.tasks[0]!;
    expect(node.assignment?.researchBasis).toEqual(state.cooperation!.tasks[0]!.assignment?.researchBasis);
    expect(node.researchCompletion).toEqual(state.cooperation!.tasks[0]!.researchCompletion);
    expect(restored.cooperation!.deliveries).toEqual(state.cooperation!.deliveries);
    expect(restored.cooperation!.history).toEqual(state.cooperation!.history);
    expect(node.status).toBe('completed');
    expect(node.finding).toBe(finding);
    expect(node.proof).toBeUndefined();
    expect(node.integratedCheck).toBeUndefined();
  });

  it('reads legacy checkpoints without inventing a completion record or a frozen assignment basis', () => {
    delete state.cooperation!.tasks[0]!.assignment!.researchBasis;
    delete state.cooperation!.tasks[0]!.researchCompletion;
    delete state.cooperation!.deliveries![0]!.researchRecord;
    delete state.cooperation!.history![0]!.researchCompletion;
    const restored = read();
    expect(restored.cooperation!.tasks[0]!.assignment?.researchBasis).toBeUndefined();
    expect(restored.cooperation!.tasks[0]!.researchCompletion).toBeUndefined();
    expect(restored.cooperation!.deliveries![0]!.researchRecord).toBeUndefined();
    expect(restored.cooperation!.history![0]!.researchCompletion).toBeUndefined();
    expect(restored.cooperation!.tasks[0]!.finding).toBe(finding);
    expect(restored.cooperation!.history![0]!.finding).toBe(finding);
  });

  it('rejects a malformed assignment basis instead of treating it as a legacy checkpoint', () => {
    state = structuredClone(state);
    Object.assign(state.cooperation!.tasks[0]!.assignment!.researchBasis!, { schema: 'unknown-research-basis' });
    expect(read).toThrow('math_resume_state_invalid:cooperation.tasks.0.assignment.researchBasis.schema');
  });

  it('rejects a malformed current completion content hash', () => {
    state = structuredClone(state);
    Object.assign(state.cooperation!.tasks[0]!.researchCompletion!, { findingDigest: 'not-a-content-digest' });
    expect(read).toThrow('math_resume_state_invalid:cooperation.tasks.0.researchCompletion.findingDigest');
  });

  it('validates research records embedded in deliveries', () => {
    state = structuredClone(state);
    Object.assign(state.cooperation!.deliveries![0]!.researchRecord!.basis, { environmentDigest: '' });
    expect(read).toThrow('math_resume_state_invalid:cooperation.deliveries.0.researchRecord.basis.environmentDigest');
  });

  it('validates research records retained in task history', () => {
    state = structuredClone(state);
    Object.assign(state.cooperation!.history![0]!.researchCompletion!, { taskId: 'another-task' });
    expect(read).toThrow('math_resume_state_invalid:cooperation.history.0.researchCompletion');
  });

  it('rejects duplicated full finding text in the research record schema', () => {
    state = structuredClone(state);
    Object.assign(state.cooperation!.tasks[0]!.researchCompletion!, { finding });
    expect(read).toThrow('math_resume_state_invalid:cooperation.tasks.0.researchCompletion');
  });
});
