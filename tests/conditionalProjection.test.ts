import { describe, expect, it } from 'vitest';
import type { TaskProof } from '../src/solver/cooperativeProof';
import { describeProofRoutes, proofRouteReady, type ProofRoute } from '../src/solver/proofRoutes';
import { createProofRoutePriority } from '../src/solver/routePriority';
import { hasTaskAcceptance, markTaskAcceptance, taskVersion, type TaskRecord } from '../src/solver/tasks';

function fixture() {
  const premise: TaskRecord = { task: { id: 'premise', kind: 'lemma', objective: 'Prove the premise',
    dependsOn: [], revision: 0, proofPath: 'Submission.lean', theoremName: 'Submission.premise', type: 'True' },
  status: 'pending', attempts: 0 };
  const closing: TaskRecord = { task: { id: 'closing', kind: 'lemma', objective: 'Connect the premise',
    dependsOn: ['premise'], revision: 0, proofPath: 'Submission.lean', theoremName: 'Submission.closing',
    type: 'True', conditional: true }, status: 'conditional', attempts: 1 };
  const route: ProofRoute = { id: 'connection', targetTaskId: 'goal', prerequisiteTaskIds: ['premise'], closingTaskId: 'closing' };
  const goal: TaskRecord = { task: { id: 'goal', kind: 'goal', objective: 'Prove the original goal',
    dependsOn: [], revision: 0, proofPath: 'Submission.lean', theoremName: 'Submission.goal' },
  status: 'pending', attempts: 0, alternativeRoutes: [route] };
  const proof: TaskProof = { taskDigest: taskVersion(closing.task), commit: 'draft', seedCommit: 'seed',
    sourceDigest: 'draft-source', passed: true, changes: [],
    projection: { environmentDigest: 'environment', problemReceiptDigest: 'problem', sourceDigest: 'projected-sources' },
    conditions: [{ taskId: premise.task.id, taskDigest: taskVersion(premise.task) }],
    verification: { status: 'kernel_verified', targetCommit: 'projection', results: [{ status: 'kernel_verified',
      targetCommit: 'projection', receiptId: 'receipt', proofPath: closing.task.proofPath,
      theoremName: closing.task.theoremName, statementHash: taskVersion(closing.task) }] } } as TaskProof;
  closing.proof = proof;
  markTaskAcceptance(proof);
  return { premise, closing, goal, proof, route, tasks: [premise, closing, goal] };
}

describe('conditional projection identity', () => {
  it('shares host-verified conditional evidence between scheduler and environment-specific context', () => {
    const { goal, premise, proof, route, tasks } = fixture();
    expect(proof.references).toBeUndefined();
    const scheduled = createProofRoutePriority(tasks).routes[0];
    const contextual = createProofRoutePriority(tasks, { environmentDigest: 'environment' }).routes[0];
    expect(contextual).toEqual(scheduled);
    expect(contextual).toMatchObject({ closingStatus: 'conditional', closingEvidence: 'conditional', checkedInputIds: [] });
    expect(describeProofRoutes([route], tasks, 'environment').routes[0]).toMatchObject({
      closingStatus: 'conditional', ready: false, connection: 'awaiting-original-check',
    });
    expect(proofRouteReady(route, tasks, 'environment')).toBe(false);
    expect(premise.status).toBe('pending');
    expect(goal.status).toBe('pending');
    expect(goal.integratedCheck).toBeUndefined();
  });

  it('rejects conditional evidence checked in another environment', () => {
    const { route, tasks } = fixture();
    expect(describeProofRoutes([route], tasks, 'other').routes[0].closingStatus).toBe('stale');
    expect(createProofRoutePriority(tasks, { environmentDigest: 'other' }).routes[0].closingEvidence).toBe('none');
    expect(proofRouteReady(route, tasks, 'other')).toBe(false);
  });

  it('does not infer an environment from old conditional records lacking projection identity', () => {
    const { proof, route, tasks } = fixture();
    delete proof.projection;
    markTaskAcceptance(proof);
    expect(describeProofRoutes([route], tasks, 'environment').routes[0].closingStatus).toBe('unverified');
    expect(createProofRoutePriority(tasks, { environmentDigest: 'environment' }).routes[0].closingEvidence).toBe('none');
  });

  it('preserves unconditional reference coverage requirements despite a host projection identity', () => {
    const { closing, proof, route, tasks } = fixture();
    closing.task = { ...closing.task, dependsOn: [] };
    proof.taskDigest = taskVersion(closing.task);
    proof.verification.results[0]!.statementHash = proof.taskDigest;
    delete proof.conditions;
    closing.status = 'integrated'; closing.integratedCheck = proof;
    route.prerequisiteTaskIds = [];
    markTaskAcceptance(proof);
    expect(describeProofRoutes([route], tasks, 'environment').routes[0].closingStatus).toBe('unverified');
    expect(createProofRoutePriority(tasks, { environmentDigest: 'environment' }).routes[0].closingEvidence).toBe('none');
    expect(proofRouteReady(route, tasks, 'environment')).toBe(false);
  });

  it.each(['changed', 'missing'] as const)('invalidates recorded and fresh conditional evidence for a %s premise', change => {
    const { premise, route, tasks } = fixture();
    if (change === 'changed') premise.task = { ...premise.task, type: 'False' };
    else tasks.splice(tasks.indexOf(premise), 1);
    expect(describeProofRoutes([route], tasks, 'environment').routes[0].closingStatus).toBe('stale');
    expect(createProofRoutePriority(tasks).routes[0].closingEvidence).toBe('none');
    expect(createProofRoutePriority(tasks, { environmentDigest: 'environment' }).routes[0].closingEvidence).toBe('none');
  });

  it('rejects contradictory projection and reference environments', () => {
    const { closing, proof, route, tasks } = fixture();
    proof.references = { sourceCommit: 'draft', environmentDigest: 'other', contextDigest: 'context',
      root: { file: closing.task.proofPath!, name: closing.task.theoremName! }, inputs: [], tasks: [], statement: [], proof: [] };
    markTaskAcceptance(proof);
    expect(describeProofRoutes([route], tasks).routes[0].closingStatus).toBe('unverified');
    expect(createProofRoutePriority(tasks).routes[0].closingEvidence).toBe('none');
  });

  it('rejects malformed duplicate conditional inputs', () => {
    const { proof, route, tasks } = fixture();
    proof.conditions = [...proof.conditions!, ...proof.conditions!];
    markTaskAcceptance(proof);
    expect(describeProofRoutes([route], tasks, 'environment').routes[0].closingStatus).toBe('unverified');
    expect(createProofRoutePriority(tasks).routes[0].closingEvidence).toBe('none');
  });

  it('retains recorded identity after JSON restore without restoring fresh acceptance', () => {
    const { route, tasks } = fixture();
    const restored = JSON.parse(JSON.stringify(tasks)) as TaskRecord[];
    const restoredProof = restored.find(node => node.task.id === 'closing')!.proof!;
    expect(restoredProof.projection?.environmentDigest).toBe('environment');
    expect(hasTaskAcceptance(restoredProof)).toBe(false);
    expect(describeProofRoutes([route], restored, 'environment').routes[0].closingStatus).toBe('conditional');
    expect(createProofRoutePriority(restored).routes[0].closingEvidence).toBe('none');
    expect(createProofRoutePriority(restored, { environmentDigest: 'environment' }).routes[0].closingEvidence).toBe('none');
    expect(proofRouteReady(route, restored, 'environment')).toBe(false);
  });

  it.each(['environmentDigest', 'problemReceiptDigest', 'sourceDigest'] as const)(
    'drops fresh acceptance if the host projection %s changes', field => {
      const { proof, tasks } = fixture();
      expect(hasTaskAcceptance(proof)).toBe(true);
      proof.projection = { ...proof.projection!, [field]: 'changed' };
      expect(hasTaskAcceptance(proof)).toBe(false);
      expect(createProofRoutePriority(tasks).routes[0].closingEvidence).toBe('none');
    });
});
