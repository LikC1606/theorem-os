import { describe, expect, it } from 'vitest';
import { canonicalMathJson } from '../src/math/mathRuntimeIo';
import type { DeliveryRecord } from '../src/solver/deliveries';
import { buildProofContinuation } from '../src/solver/progress';
import { researchHandoffs, resolveResearchHandoffs, type ResearchHandoff, type ResearchHandoffDecision } from '../src/solver/researchHandoffs';
import { hasTaskAcceptance, taskVersion, type TaskRecord } from '../src/solver/tasks';
import { integratedProof } from './helpers/taskProof';

const node = (id: string, kind: TaskRecord['task']['kind'] = 'lemma', dependsOn: string[] = []): TaskRecord => ({
  task: { id, kind, objective: id, dependsOn, revision: 0,
    ...(['lemma', 'goal'].includes(kind) ? { theoremName: `Original.${id}`, proofPath: 'Submission.lean', type: 'True' } : {}) },
  status: 'pending', attempts: 0,
});
function checked(item: TaskRecord, inputs: TaskRecord[] = [], statementOnly = false) {
  return integratedProof(item, { uses: inputs, statementOnly });
}
type State = { tasks: TaskRecord[]; deliveries: DeliveryRecord[]; researchDecisions: ResearchHandoffDecision[] };
function fixture() {
  const source = node('investigation', 'research'), adopted = node('bridge'), goal = node('goal', 'goal');
  source.status = 'completed';
  const delivery: DeliveryRecord = { id: 'research-delivery', producer: 'researcher', taskId: source.task.id,
    taskDigest: taskVersion(source.task), kind: 'research', status: 'advisory', summary: 'An exact bridge is worth proving.',
    statement: '', premises: [], dependencies: [], remainingObligations: [], evidenceRefs: [], createdAt: 1,
    commit: 'a'.repeat(40), lemmaRequests: [adopted.task] };
  const state: State = { tasks: [source, adopted, goal], deliveries: [delivery], researchDecisions: [] };
  const handoff = researchHandoffs(state)[0]!;
  state.researchDecisions = resolveResearchHandoffs(state, [handoff.id], state.tasks.map(item => item.task), undefined);
  return { state, source, adopted, goal, handoffId: handoff.id };
}
const report = (state: State, handoffs = researchHandoffs(state)) => buildProofContinuation(state.tasks, {
  environmentDigest: 'environment', researchHandoffs: handoffs,
});

describe('adopted research continuation', () => {
  it('keeps an unproved and unconnected adopted proposal visible without promoting its proof status', () => {
    const { state, adopted, source, goal, handoffId } = fixture(), before = canonicalMathJson(state);
    const continuation = report(state);

    expect(continuation.adoptedResearch).toEqual([{
      adoption: 'adopted', handoffId, sourceTaskId: source.task.id, taskId: adopted.task.id,
      taskDigest: taskVersion(adopted.task), recordedProof: 'none', plannedConsumers: [], plannedGoalIds: [],
      proofConsumers: [], statementConsumers: [], conditionalConsumers: [],
      referenceCoverage: 'unknown', missingReferenceTaskIds: [adopted.task.id],
    }]);
    expect(continuation.unconnectedTasks).toContain(adopted.task.id);
    expect(continuation.goals[0]).toMatchObject({ taskId: goal.task.id, recordedProof: 'none', frontier: [goal.task.id] });
    expect(continuation.evidence).toBe('recorded-not-replayed');
    expect(canonicalMathJson(state)).toBe(before);
  });

  it('reports a planned original-goal connection independently from actual Lean use', () => {
    const { state, adopted, goal } = fixture();
    goal.task = { ...goal.task, dependsOn: [adopted.task.id] };
    const continuation = report(state);

    expect(continuation.adoptedResearch[0]).toMatchObject({ adoption: 'adopted', recordedProof: 'none',
      plannedConsumers: [goal.task.id], plannedGoalIds: [goal.task.id], proofConsumers: [], referenceCoverage: 'unknown' });
    expect(continuation.goals[0]!.frontier).toEqual([adopted.task.id]);
    expect(continuation.unconnectedTasks).not.toContain(adopted.task.id);
    expect(continuation.reuse).toEqual([]);
  });

  it('uses the existing alternative-route path for planned consumers', () => {
    const { state, adopted, goal } = fixture(), closing = node('closing', 'lemma', [adopted.task.id]);
    state.tasks.push(closing);
    const continuation = buildProofContinuation(state.tasks, { researchHandoffs: researchHandoffs(state), proofRoutes: [
      { id: 'route', targetTaskId: goal.task.id, prerequisiteTaskIds: [adopted.task.id], closingTaskId: closing.task.id },
    ] });

    expect(continuation.adoptedResearch[0]).toMatchObject({ plannedConsumers: [goal.task.id, closing.task.id],
      plannedGoalIds: [goal.task.id], proofConsumers: [], referenceCoverage: 'unknown' });
  });

  it('separates recorded proof, statement and conditional consumers from planned edges', () => {
    const { state, adopted, goal } = fixture(); checked(adopted); checked(goal, [adopted]);
    const statement = node('statement'), conditional = node('conditional', 'lemma', [adopted.task.id]);
    checked(statement, [adopted], true);
    const proof = checked(conditional, [adopted]);
    conditional.status = 'conditional'; proof.conditions = [{ taskId: 'open-premise', taskDigest: 'open-version' }];
    state.tasks.push(statement, conditional);
    const continuation = report(state);

    expect(continuation.adoptedResearch[0]).toMatchObject({ recordedProof: 'checked', plannedConsumers: [conditional.task.id],
      plannedGoalIds: [], proofConsumers: [goal.task.id], statementConsumers: [statement.task.id],
      conditionalConsumers: [conditional.task.id], referenceCoverage: 'recorded', missingReferenceTaskIds: [] });
    expect(continuation.adoptedResearch[0]!.proofConsumers).toEqual(continuation.reuse[0]!.proofConsumers);
    expect(continuation.adoptedResearch[0]!.statementConsumers).toEqual(continuation.reuse[0]!.statementConsumers);
    expect(continuation.adoptedResearch[0]!.conditionalConsumers).toEqual(continuation.reuse[0]!.conditionalConsumers);
  });

  it.each(['producer', 'consumer'] as const)('keeps missing %s reference coverage unknown even when no use is recorded', missing => {
    const { state, adopted, goal } = fixture();
    const producerProof = checked(adopted), consumerProof = checked(goal, [adopted]);
    delete (missing === 'producer' ? producerProof : consumerProof).references;
    const item = report(state).adoptedResearch[0]!;

    expect(item.referenceCoverage).toBe('unknown');
    expect(item.missingReferenceTaskIds).toContain(missing === 'producer' ? adopted.task.id : goal.task.id);
    if (missing === 'consumer') expect(item.proofConsumers).toEqual([]);
    expect(item.recordedProof).toBe('checked');
  });

  it.each(['tasks', 'proof', 'statement'] as const)('does not report complete coverage when a checked consumer lacks %s references', field => {
    const { state, adopted, goal } = fixture(); checked(adopted);
    const proof = checked(goal, [adopted]);
    // Incomplete older snapshots preserve known use while leaving the missing channel unknown.
    delete (proof.references as unknown as Record<string, unknown>)[field];
    const item = report(state).adoptedResearch[0]!;

    expect(item).toMatchObject({ proofConsumers: field === 'statement' ? [goal.task.id] : [],
      referenceCoverage: 'unknown', missingReferenceTaskIds: [goal.task.id] });
  });

  it('retains adoption while exposing a stale producer proof and withholding recorded consumers', () => {
    const { state, adopted, goal } = fixture();
    const proof = checked(adopted); checked(goal, [adopted]);
    proof.references!.environmentDigest = 'old-environment';
    const item = report(state).adoptedResearch[0]!;

    expect(item).toMatchObject({ adoption: 'adopted', recordedProof: 'stale', proofConsumers: [],
      referenceCoverage: 'unknown', missingReferenceTaskIds: [adopted.task.id] });
    expect(researchHandoffs(state)[0]!.status).toBe('adopted');
  });

  it('does not count a stale task reference as actual use', () => {
    const { state, adopted, goal } = fixture(); checked(adopted);
    const proof = checked(goal, [adopted]); proof.references!.tasks![0]!.taskDigest = 'old-version';
    expect(report(state).adoptedResearch[0]).toMatchObject({ proofConsumers: [], referenceCoverage: 'unknown',
      missingReferenceTaskIds: [goal.task.id] });
  });

  it.each(['source-version', 'source-scope', 'target-version', 'target-scope'] as const)('rejects a previously resolved handoff after %s changes', change => {
    const { state, source, adopted } = fixture(), handoffs = researchHandoffs(state);
    if (change === 'source-version') source.task = { ...source.task, revision: 1 };
    if (change === 'target-version') adopted.task = { ...adopted.task, type: 'False', revision: 1 };
    if (change === 'source-scope') state.tasks = state.tasks.filter(item => item !== source);
    if (change === 'target-scope') state.tasks = state.tasks.filter(item => item !== adopted);

    expect(report(state, handoffs).adoptedResearch).toEqual([]);
    expect(report(state).adoptedResearch).toEqual([]);
  });

  it.each(['pending', 'rejected', 'deferred'] as const)('does not label a %s handoff as adopted', status => {
    const { state } = fixture(), handoff = researchHandoffs(state)[0]!;
    expect(report(state, [{ ...handoff, status }]).adoptedResearch).toEqual([]);
  });

  it('requires a matching adoption decision without inferring one from an existing task or proposal', () => {
    const { state } = fixture(), handoff = researchHandoffs(state)[0]!;
    const cases: ResearchHandoff[] = [
      { ...handoff, decision: undefined },
      { ...handoff, decision: { ...handoff.decision!, status: 'deferred' } },
      { ...handoff, decision: { ...handoff.decision!, taskDigest: 'old-task' } },
      { ...handoff, decision: { ...handoff.decision!, taskId: undefined } },
    ];
    for (const value of cases) expect(report(state, [value]).adoptedResearch).toEqual([]);
  });

  it('does not promote restored recorded receipts to fresh acceptance or change ordinary continuation behavior', () => {
    const { state, adopted, goal } = fixture(); checked(adopted); checked(goal, [adopted]);
    const restored = JSON.parse(JSON.stringify(state)) as State;
    const restoredProof = restored.tasks.find(item => item.task.id === adopted.task.id)!.integratedCheck!;
    const before = canonicalMathJson(restored), baseline = buildProofContinuation(restored.tasks, { environmentDigest: 'environment' });
    expect(hasTaskAcceptance(restoredProof)).toBe(false);
    const { adoptedResearch, ...ordinary } = report(restored);
    const { adoptedResearch: _empty, ...expected } = baseline;

    expect(adoptedResearch[0]).toMatchObject({ adoption: 'adopted', recordedProof: 'checked', proofConsumers: [goal.task.id] });
    expect(ordinary).toEqual(expected);
    expect(hasTaskAcceptance(restoredProof)).toBe(false);
    expect(canonicalMathJson(restored)).toBe(before);
  });

  it('returns no adoption rows when callers supply no resolved handoffs', () => {
    const { state } = fixture();
    expect(buildProofContinuation(state.tasks).adoptedResearch).toEqual([]);
  });
});
