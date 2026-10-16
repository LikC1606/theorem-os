import { describe, expect, it } from 'vitest';
import { canonicalMathJson, mathDigest } from '../src/math/mathRuntimeIo';
import type { SolverProblem } from '../src/solver/problem';
import type { TaskProof } from '../src/solver/cooperativeProof';
import { invalidatedTaskIds, markTaskReferences, parseCooperationPlan, taskVersion,
  type CooperativeTask, type TaskRecord } from '../src/solver/tasks';
import { buildTaskObligationSummary, type TaskVersionReference } from '../src/solver/taskObligations';
import { readyResearchTasks } from '../src/solver/modules/search';

const problem = { ownedFiles: ['Submission.lean'], declarations: {
  'Submission.lean': [{ name: 'Submission.target', header: 'theorem target : True' }],
}, targets: [{ proofPath: 'Submission.lean', theoremName: 'Submission.target' }] } as unknown as SolverProblem;
const helper = (id: string, type = 'True'): CooperativeTask => ({ id, kind: 'lemma', objective: `Prove ${id}`,
  dependsOn: [], revision: 0, proofPath: 'Submission.lean', theoremName: `Submission.${id}`, type });
const goal: CooperativeTask = { id: 'goal', kind: 'goal', objective: 'Prove the original target',
  dependsOn: ['helper'], revision: 0, proofPath: 'Submission.lean', theoremName: 'Submission.target' };
const ref = (task: CooperativeTask): TaskVersionReference => ({ taskId: task.id, taskDigest: taskVersion(task) });
const parse = (tasks: CooperativeTask[], groups?: unknown[]) => parseCooperationPlan(problem, { tasks, ...(groups ? { groups } : {}) });
const node = (task: CooperativeTask): TaskRecord => ({ task, status: 'pending', attempts: 0 });
const contracted = () => {
  const producer = helper('helper'), application = { ...helper('apply', '∀ (n : Nat), n = n'), dependsOn: ['helper'] };
  return [{ ...producer, applications: [{ id: 'use-in-goal', consumer: ref(goal), type: application.type, proofTask: ref(application) }] },
    application, goal];
};

function checked(task: CooperativeTask, used: CooperativeTask[] = []): TaskRecord {
  const proof = { commit: `source-${task.id}`, seedCommit: 'seed', sourceDigest: 'source-digest', passed: true,
    taskDigest: taskVersion(task), changes: [], references: { sourceCommit: `source-${task.id}`, environmentDigest: 'env',
      contextDigest: 'context', root: { file: task.proofPath!, name: task.theoremName! },
      statement: [], proof: used.map(task => ({ file: task.proofPath!, name: task.theoremName! })),
      inputs: [{ file: task.proofPath!, name: task.theoremName!, digest: 'declaration' }], tasks: used.map(ref) },
    verification: { schema: 'deepscientist.mathematics.verification-batch/v1', status: 'kernel_verified',
      targetCommit: `projection-${task.id}`, results: [{ status: 'kernel_verified', targetCommit: `projection-${task.id}`,
        theoremName: task.theoremName!, proofPath: task.proofPath!, statementHash: taskVersion(task),
        leanStatementHash: taskVersion(task), claim: 'statement', sourceDeclarationHash: 'declaration',
        receiptId: `receipt-${task.id}`, sorryCount: 0, admitCount: 0, goalsRemaining: 0 }] },
  } as TaskProof;
  markTaskReferences(proof);
  return { task, status: 'integrated', attempts: 1, integratedCheck: proof };
}
const summary = (records: TaskRecord[]) => buildTaskObligationSummary(records, { environmentDigest: 'env' });

describe('declared task applications and premise sources', () => {
  it('preserves historical task identities, actual dependencies and readiness when adding metadata', () => {
    const original = helper('helper'), tasks = contracted();
    const originalDigest = mathDigest(canonicalMathJson(original));
    const annotated = { ...tasks[0], obligations: [{ id: 'context-premise', type: 'True',
      source: { kind: 'original-context' as const, file: 'Submission.lean', declaration: 'Submission.target' } }] };
    const parsed = parse([annotated, ...tasks.slice(1)]).tasks;
    expect(taskVersion(parsed[0])).toBe(originalDigest);
    expect(taskVersion(parsed[0])).toBe(taskVersion(original));
    expect([...invalidatedTaskIds([node(original)], parsed, new Set(), new Map())]).toEqual([]);
    expect(readyResearchTasks(parsed.map(node)).map(item => item.task.id)).toEqual(['helper']);
    expect(taskVersion({ ...parsed[0], dependsOn: ['apply'] })).not.toBe(originalDigest);
    expect(taskVersion({ ...parsed[0], type: 'False' })).not.toBe(originalDigest);
    expect(parsed[0].applications[0].consumer).toEqual(ref(goal));
    expect(parsed[0].obligations[0].source.kind).toBe('original-context');
  });

  it('records local, producer, original-context and unassigned premises without inferring a telescope', () => {
    const producer = helper('helper');
    const consumer = { ...goal, obligations: [
      { id: 'known', type: 'True', source: { kind: 'task' as const, ...ref(producer) } },
      { id: 'local-bridge', type: 'True', source: { kind: 'local' as const, ...ref(producer) } },
      { id: 'hypothesis', type: 'True', source: { kind: 'original-context' as const,
        file: 'Submission.lean', declaration: 'Submission.target' } },
      { id: 'open', type: '∀ (p : Prop), p → p', source: { kind: 'unassigned' as const } },
    ] };
    const parsed = parse([producer, consumer]);
    const before = structuredClone(parsed);
    const view = summary(parsed.tasks.map(node));
    expect(view.evidence).toBe('advisory-contracts');
    expect(view.tasks[0].obligations.map(item => item.status)).toEqual([
      'awaiting-proof', 'awaiting-proof', 'declared-original-context', 'unassigned',
    ]);
    expect(parsed).toEqual(before);
    expect(JSON.stringify(view)).not.toContain('closed');
  });

  it.each([
    ['missing task', { consumer: { taskId: 'missing', taskDigest: 'a'.repeat(64) } }, 'missing_task'],
    ['old version', { consumer: { ...ref(goal), taskDigest: 'a'.repeat(64) } }, 'stale_reference'],
    ['missing version', { consumer: { taskId: 'goal' } }, 'invalid_reference'],
    ['empty type', { type: ' ' }, 'invalid_type'],
    ['placeholder', { type: 'FULL_CLOSED_LEAN_TYPE' }, 'invalid_type'],
    ['claimed completion', { status: 'closed' }, 'invalid_fields'],
  ])('rejects %s in an application contract', (_name, change, reason) => {
    const tasks = contracted();
    tasks[0] = { ...tasks[0], applications: [{ ...tasks[0].applications[0], ...change }] } as CooperativeTask;
    expect(() => parse(tasks)).toThrow(`math_plan_obligation_${reason}`);
  });

  it('requires a separate exact typed application task and checks original-context origins', () => {
    const tasks = contracted();
    tasks[0] = { ...tasks[0], applications: [{ ...tasks[0].applications[0], type: 'False' }] };
    expect(() => parse(tasks)).toThrow('math_plan_obligation_invalid_application_task');
    const producer = helper('helper');
    expect(() => parse([producer, { ...goal, obligations: [{ id: 'bad-origin', type: 'True',
      source: { kind: 'original-context', file: '../outside.lean', declaration: 'Submission.target' } }] }]))
      .toThrow('math_plan_obligation_unknown_original_context');
    expect(() => parse([producer, { ...goal, obligations: [{ id: 'bad-type', type: 'False',
      source: { kind: 'task', ...ref(producer) } }] }])).toThrow('math_plan_obligation_producer_type_mismatch');
  });

  it('rejects duplicate obligation ids and fabricated closed premise sources', () => {
    const premise = { id: 'same', type: 'True', source: { kind: 'unassigned' as const } };
    expect(() => parse([helper('helper'), { ...goal, obligations: [premise, premise] }]))
      .toThrow('math_plan_obligation_duplicate_id');
    expect(() => parse([helper('helper'), { ...goal, obligations: [{ ...premise,
      source: { kind: 'unassigned', closed: true } } as never] }])).toThrow('math_plan_obligation_invalid_fields');
  });

  it('rejects private cross-group producers for both applications and premise metadata', () => {
    const groups = [{ id: 'a', objective: 'First route' }, { id: 'b', objective: 'Second route' }];
    const producer = { ...helper('helper'), groupId: 'a', sharing: 'group' as const };
    const consumer = { ...goal, dependsOn: [], groupId: 'b', sharing: 'problem' as const };
    expect(() => parse([{ ...producer, applications: [{ id: 'cross', consumer: ref(consumer), type: 'True' }] }, consumer], groups))
      .toThrow('math_plan_obligation_not_shared');
    expect(() => parse([producer, { ...consumer, obligations: [{ id: 'cross', type: 'True',
      source: { kind: 'task', ...ref(producer) } }] }], groups)).toThrow('math_plan_obligation_not_shared');
    const shared = { ...producer, sharing: 'problem' as const };
    expect(() => parse([{ ...shared, applications: [{ id: 'cross', consumer: ref(consumer), type: 'True' }] }, consumer], groups))
      .not.toThrow();
    const privateConsumer = { ...consumer, sharing: 'group' as const };
    expect(() => parse([{ ...shared, applications: [{ id: 'private', consumer: ref(privateConsumer), type: 'True' }] },
      privateConsumer], groups)).toThrow('math_plan_obligation_not_shared');
  });

  it('rejects cycles combining declared use, premise sources and real dependencies', () => {
    const producer = helper('helper'), consumer = { ...helper('other'), dependsOn: ['helper'] };
    expect(() => parse([{ ...producer, obligations: [{ id: 'circular', type: 'True',
      source: { kind: 'local', ...ref(consumer) } }] }, consumer, goal])).toThrow('math_plan_obligation_cycle');
    const app = { ...producer, applications: [{ id: 'use', consumer: ref(consumer), type: 'True' }] };
    const circular = { ...app, obligations: [{ id: 'back', type: 'True', source: { kind: 'task' as const, ...ref(consumer) } }] };
    expect(() => parse([circular, { ...consumer, dependsOn: [] }, goal])).toThrow('math_plan_obligation_stale_reference');
    const independent = { ...consumer, dependsOn: [] };
    expect(() => parse([{ ...producer, applications: [{ id: 'use', consumer: ref(independent), type: 'True' }],
      obligations: [{ id: 'back', type: 'True', source: { kind: 'task', ...ref(independent) } }] }, independent, goal]))
      .toThrow('math_plan_obligation_cycle');
  });
});

describe('application evidence summaries', () => {
  it('keeps the proposed application unverified until the consumer has a real checked proof reference', () => {
    const tasks = parse(contracted()).tasks, producer = checked(tasks[0]), consumer = checked(tasks[2]);
    const records = [producer, node(tasks[1]), consumer];
    expect(summary(records).tasks[0].applications[0].status).toBe('declared');
    consumer.integratedCheck.references.tasks = [ref(tasks[0])];
    consumer.integratedCheck.references.statement = [{ file: tasks[0].proofPath, name: tasks[0].theoremName }];
    expect(summary(records).tasks[0].applications[0].status).toBe('declared');
    consumer.integratedCheck.references.proof = [{ file: tasks[0].proofPath, name: tasks[0].theoremName }];
    expect(summary(records).tasks[0].applications[0].status).toBe('checked-reference');
    expect(summary(records).tasks[0].applications[0].typeEvidence).toBe('declared-not-elaborated');
    consumer.integratedCheck.references.tasks[0].taskDigest = 'f'.repeat(64);
    expect(summary(records).tasks[0].applications[0].status).toBe('declared');
  });

  it('does not promote archived receipts, wrong receipt identities, conditions or old environments', () => {
    const tasks = parse(contracted()).tasks;
    const records = [checked(tasks[0]), node(tasks[1]), checked(tasks[2], [tasks[0]])];
    const status = () => summary(records).tasks[0].applications[0];
    expect(status().status).toBe('checked-reference');
    records[2] = structuredClone(records[2]);
    expect(status().status).toBe('declared');
    expect(status().consumerProof.status).toBe('recorded-unverified');
    markTaskReferences(records[2].integratedCheck);
    records[2].integratedCheck.verification.results[0].theoremName = 'Submission.wrong';
    expect(status().status).toBe('declared');
    records[2] = checked(tasks[2], [tasks[0]]);
    records[2].integratedCheck.conditions = [ref(tasks[0])];
    expect(status().consumerProof.status).toBe('conditional');
    records[2] = checked(tasks[2], [tasks[0]]);
    records[2].integratedCheck.references.environmentDigest = 'old-env';
    expect(status().consumerProof.status).toBe('stale');
    expect(status().status).toBe('declared');
  });

  it('distinguishes a formal application lemma from actual consumer use and preserves the open original goal', () => {
    const tasks = parse(contracted()).tasks;
    const records = [checked(tasks[0]), checked(tasks[1], [tasks[0]]), node(tasks[2])];
    const view = summary(records).tasks[0].applications[0];
    expect(view.status).toBe('checked-application-task');
    expect(view.typeEvidence).toBe('checked-application-task');
    expect(view.applicationProof.status).toBe('checked-at-source');
    expect(view.consumerProof.status).toBe('unchecked');
    expect(records[2].status).toBe('pending');
    records[1] = checked(tasks[1]);
    expect(summary(records).tasks[0].applications[0].status).toBe('declared');
    records[1] = checked(tasks[1], [tasks[0]]);
    records[0].task = { ...records[0].task, type: 'False' };
    expect(summary(records).tasks[0].applications[0].status).toBe('declared');
    records[0] = checked(tasks[0]);
    records[1].task = { ...records[1].task, type: 'False' };
    expect(summary(records).tasks[0].applications[0].status).toBe('stale-or-unavailable');
  });

  it('omits out-of-scope producer details while preserving visible producer type/version changes', () => {
    const producer = helper('helper'), consumer = { ...goal, obligations: [{ id: 'needed', type: 'True',
      source: { kind: 'task' as const, ...ref(producer) } }] };
    const records = [checked(producer), node(consumer)];
    expect(summary(records).tasks[0].obligations[0].status).toBe('checked-producer');
    expect(summary(records.slice(1)).tasks[0].obligations).toEqual([]);
    records[0].task = { ...producer, type: 'False' };
    expect(summary(records).tasks[0].obligations[0].status).toBe('stale-or-unavailable');
  });

  it('omits private consumers and application proofs from a scoped exported helper summary', () => {
    const groups = [{ id: 'a', objective: 'First route' }, { id: 'b', objective: 'Second route' }];
    const producer = { ...helper('helper'), groupId: 'a', sharing: 'problem' as const };
    const consumer = { ...goal, groupId: 'a', sharing: 'group' as const };
    const application = { ...helper('apply', '∀ (n : Nat), n = n'), groupId: 'a', sharing: 'group' as const };
    const tasks = parse([{ ...producer, applications: [{ id: 'use-in-goal', consumer: ref(consumer),
      type: application.type, proofTask: ref(application) }] }, application, consumer], groups).tasks;
    const records = tasks.map(node);
    const withoutConsumer = summary(records.slice(0, 2));
    expect(withoutConsumer.tasks[0].applications).toEqual([]);
    expect(JSON.stringify(withoutConsumer)).not.toContain('use-in-goal');
    expect(JSON.stringify(withoutConsumer)).not.toContain(tasks[0].applications[0].type);
    const withoutApplication = summary([records[0], records[2]]);
    expect(withoutApplication.tasks[0].applications).toEqual([]);
    expect(JSON.stringify(withoutApplication)).not.toContain('use-in-goal');
    records[2].task = { ...records[2].task, revision: 1 };
    expect(summary(records).tasks[0].applications[0].status).toBe('stale-or-unavailable');
  });

  it('keeps conditional status while omitting hidden condition references', () => {
    const hidden = helper('private-condition'), visible = helper('visible-condition');
    const producer = { ...helper('helper'), applications: [{ id: 'use', consumer: ref(goal), type: 'True' }] };
    const record = checked(producer);
    record.integratedCheck.conditions = [ref(hidden), ref(visible)];
    const view = summary([record, node(goal), node(visible)]).tasks[0].applications[0];
    expect(view.producerProof.status).toBe('conditional');
    expect(view.producerProof).toMatchObject({ conditions: [ref(visible)] });
    expect(JSON.stringify(view)).not.toContain(hidden.id);
    expect(JSON.stringify(view)).not.toContain(taskVersion(hidden));
    expect(view.status).toBe('declared');
  });

  it.each(['task', 'local'] as const)('omits hidden %s premise identifiers and types', kind => {
    const privateProducer = helper('private-source', '∀ (p : Prop), p → p');
    const shared = { ...helper('shared'), obligations: [{ id: 'private-premise', type: privateProducer.type,
      source: { kind, ...ref(privateProducer) } }] };
    const view = summary([node(shared)]);
    expect(view.tasks[0].obligations).toEqual([]);
    expect(JSON.stringify(view)).not.toContain(privateProducer.id);
    expect(JSON.stringify(view)).not.toContain(privateProducer.type);
  });
});
