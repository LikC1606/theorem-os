import fs from 'node:fs';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import type { MathematicsVerifierBatchRequest } from '../src/math/verifier';
import { readSolverRunState, writeSolverRunState, type SolverRunState } from '../src/solver/archive';
import { parseCooperationPlan, type CooperativeResearch } from '../src/solver/cooperation';
import { directSolverModules } from '../src/solver/modules';
import { taskDependenciesReady } from '../src/solver/modules/search';
import type { ResearchWorker } from '../src/solver/modules/organization';
import { commitSolverSources, type SolverProblem } from '../src/solver/problem';
import { assignmentDeliveryFile, type CooperativeAction, type CooperativeTask } from '../src/solver/tasks';
import { deferred } from './helpers/async';
import { cooperativeResearch } from './helpers/cooperation';
import { leadWorker, localExample, peerWorker, solverState } from './helpers/solver';
import { verifiedBatch } from './helpers/verifier';

const host = vi.hoisted(() => ({ verify: vi.fn(), createSession: vi.fn() }));
vi.mock('../src/math/verifier', async importOriginal => ({
  ...await importOriginal<typeof import('../src/math/verifier')>(),
  checkManyFormalVerifications: host.verify,
  resolveMathematicsLakePackagesCache: () => undefined,
}));
vi.mock('../src/runtime/codexSession', () => ({ createCodexMathSession: host.createSession }));

const verified = (request: MathematicsVerifierBatchRequest) => verifiedBatch(request, { sessionId: 'delivery-identity-fixture' });

type TaskAction = Extract<CooperativeAction, { kind: 'task' }>;
type Log = 'scoped' | 'legacy';
const budget = { maxTurns: Infinity, remainingMs: Infinity };

describe('assignment-bound worker delivery identities', () => {
  let directory: string, problem: SolverProblem, state: SolverRunState;
  let lead: ResearchWorker, peer: ResearchWorker, other: ResearchWorker, cooperative: CooperativeResearch;
  let instances: { cooperative: CooperativeResearch; controller: AbortController }[];
  let events: { event: string; details?: Record<string, unknown> }[];
  let edits: number;

  const create = () => {
    const controller = new AbortController();
    let queue = Promise.resolve();
    const instance = cooperativeResearch({ state, workers: [lead, peer, other], retrievalRoot: directory,
      signal: controller.signal, emit: (event, details) => events.push({ event, details }),
      modules: directSolverModules,
      exclusiveCheck: async check => {
        const previous = queue;
        let release!: () => void;
        queue = new Promise<void>(resolve => { release = resolve; });
        await previous;
        try { return await check(); } finally { release(); }
      } });
    instances.push({ cooperative: instance, controller });
    return instance;
  };
  const start = async (id: string) => {
    const action = await cooperative.next(peer, budget);
    if (action?.kind !== 'task') throw new Error('missing_delivery_assignment');
    expect(action.task.id).toBe(id);
    expect(cooperative.started(peer, action)).toBe(true);
    cooperative.activate(peer, action, async () => {}, async () => {});
    return action;
  };
  const logName = (action: TaskAction, log: Log) => log === 'scoped' ? assignmentDeliveryFile(action.assignment) : 'DELIVERIES.jsonl';
  const cursorKey = (action: TaskAction, log: Log) => log === 'scoped' ? `${peer.id}/${logName(action, log)}` : peer.id;
  const append = (action: TaskAction, log: Log, value: Record<string, unknown>) => fs.appendFileSync(
    path.join(peer.worktree, logName(action, log)), JSON.stringify(log === 'scoped' ? value : {
      taskId: action.task.id, taskDigest: action.assignment.taskDigest, ...value,
    }) + '\n');
  const saveProof = (action: TaskAction) => {
    const file = path.join(peer.worktree, problem.projectRelative, 'Submission.lean');
    const source = fs.readFileSync(file, 'utf8');
    const declaration = `lemma ${action.task.id} : True := by trivial\n`;
    if (!source.includes(declaration)) fs.writeFileSync(file, source.replace('end Tutorial', declaration + 'end Tutorial'));
    return commitSolverSources(problem, peer.worktree);
  };
  const applyEdit = async (change: (task: CooperativeTask) => CooperativeTask) => {
    const id = `edit-${++edits}`;
    fs.appendFileSync(path.join(directory, 'edits.jsonl'), JSON.stringify({ id,
      baseVersion: state.cooperation!.planVersion, tasks: state.cooperation!.tasks.map(node => change(node.task)) }) + '\n');
    await cooperative.pulse(lead.id);
    expect(state.cooperation!.edits?.find(record => record.id === id)?.status).toBe('applied');
  };
  const reassign = async () => {
    await applyEdit(task => task.id === 'a' ? { ...task, ownerId: other.id } : task);
    await applyEdit(task => task.id === 'a' ? { ...task, ownerId: peer.id } : task);
  };
  const restart = async () => {
    const instance = instances.find(item => item.cooperative === cooperative)!;
    instance.controller.abort();
    await cooperative.stop();
    const file = path.join(directory, 'state.json');
    writeSolverRunState(file, state);
    state = readSolverRunState(file);
    cooperative = create();
    await cooperative.restore();
  };

  beforeEach(() => {
    const example = localExample('worker-delivery-identity-', 'lead');
    ({ directory, problem } = example);
    [peer, other] = ['peer', 'other'].map(id => peerWorker(example, id));
    lead = leadWorker(problem, example.workspace);
    const plan = parseCooperationPlan(problem, { tasks: [
      ...problem.targets.map((target, index) => ({ id: `goal_${index}`, kind: 'goal', objective: `Prove ${target.theoremName}.`,
        proofPath: target.proofPath, theoremName: target.theoremName, status: 'paused' })),
      ...['a', 'b'].map(id => ({ id, kind: 'lemma', objective: `Prove helper ${id}.`, proofPath: 'Submission.lean',
        theoremName: `Tutorial.${id}`, type: 'True', ownerId: peer.id })),
    ] });
    state = solverState(problem, example.workspace, { runId: 'delivery-identity-fixture', phase: 'running', failures: [],
      cooperation: { canonicalCommit: problem.baseCommit,
        tasks: plan.tasks.map(task => ({ task, status: 'pending', attempts: 0 })),
        groups: plan.groups.map(group => ({ group, turns: 0 })) } });
    host.verify.mockReset().mockImplementation(async request => verified(request));
    host.createSession.mockReset().mockImplementation(() => { throw new Error('real_models_are_not_used_in_delivery_tests'); });
    instances = []; events = []; edits = 0;
    cooperative = create();
  });
  afterEach(async () => {
    for (const instance of instances) { instance.controller.abort(); await instance.cooperative.stop(); }
    expect(host.createSession).not.toHaveBeenCalled();
    vi.restoreAllMocks();
    fs.rmSync(directory, { recursive: true, force: true });
  });

  it.each(['scoped', 'legacy'] as const)('accepts reused explicit ids for different assignments in %s logs and checks each proof once', async log => {
    for (const [index, id] of ['a', 'b'].entries()) {
      const action = await start(id), commit = saveProof(action);
      const value = { id: 'ready', kind: 'proof', commit, summary: `${id} proved.` };
      append(action, log, value); append(action, log, value);
      await cooperative.pulse(peer.id);
      const node = state.cooperation!.tasks.find(node => node.task.id === id)!;
      expect(node.status).toBe('integrated');
      expect(node.proof).toMatchObject({ taskDigest: action.assignment.taskDigest, seedCommit: action.assignment.seedCommit });
      expect(node.integratedCheck?.verification).toEqual(node.proof!.verification);
      expect(node.integratedCheck?.verification.targetCommit).toBe(host.verify.mock.calls[index][0].targetCommit);
      expect(state.cooperation!.cursors?.[cursorKey(action, log)]).toBe(fs.statSync(path.join(peer.worktree, logName(action, log))).size);
      expect(state.cooperation!.deliveries?.filter(record => record.taskId === id && record.submissionId === 'ready'))
        .toMatchObject([{ status: 'verified', taskDigest: action.assignment.taskDigest, assignmentKey: assignmentDeliveryFile(action.assignment) }]);
      await cooperative.pulse(peer.id);
      expect(host.verify).toHaveBeenCalledTimes(index + 1);
      cooperative.deactivate(peer);
    }
    expect(host.verify.mock.calls.map(([request]) => request.items.map((item: { theoremName: string }) => item.theoremName)))
      .toEqual([['Tutorial.a'], ['Tutorial.b']]);
    expect(events.some(item => item.event === 'delivery_rejected')).toBe(false);
  });

  it.each(['scoped', 'legacy'] as const)('isolates reused ids after a mathematical task revision in %s logs', async log => {
    const first = await start('a');
    append(first, log, { id: 'ready', kind: 'proof', commit: saveProof(first) });
    await cooperative.pulse(peer.id); cooperative.deactivate(peer);
    const firstVerification = state.cooperation!.tasks.find(node => node.task.id === 'a')!.integratedCheck!.verification;
    expect(host.verify).toHaveBeenCalledOnce();
    await applyEdit(task => task.id === 'a' ? { ...task, revision: 1, premises: ['Revised mathematical premise'] } : task);
    const revised = await start('a');
    expect(revised.assignment.taskDigest).not.toBe(first.assignment.taskDigest);
    append(revised, log, { id: 'ready', kind: 'proof', commit: saveProof(revised) });
    await cooperative.pulse(peer.id); cooperative.deactivate(peer);
    const node = state.cooperation!.tasks.find(node => node.task.id === 'a')!;
    expect(node).toMatchObject({ task: { revision: 1 }, status: 'integrated', proof: { taskDigest: revised.assignment.taskDigest } });
    expect(node.integratedCheck?.verification).toEqual(node.proof!.verification);
    expect(state.cooperation!.deliveries?.filter(record => record.submissionId === 'ready')).toMatchObject([
      { status: 'superseded', taskDigest: first.assignment.taskDigest, assignmentKey: assignmentDeliveryFile(first.assignment) },
      { status: 'verified', taskDigest: revised.assignment.taskDigest, assignmentKey: assignmentDeliveryFile(revised.assignment) },
    ]);
    expect(host.verify).toHaveBeenCalledTimes(2);
    expect(host.verify.mock.calls.map(([request]) => request.items[0].statementHash))
      .toEqual([first.assignment.taskDigest, revised.assignment.taskDigest]);
    expect(host.verify.mock.calls[0][0].items[0].expectedSourceDeclarationHash)
      .toBe(host.verify.mock.calls[1][0].items[0].expectedSourceDeclarationHash);
    expect(firstVerification.results[0].statementHash).toBe(first.assignment.taskDigest);
    expect(node.integratedCheck?.verification.results[0].statementHash).toBe(revised.assignment.taskDigest);
  });

  it.each(['passed', 'failed', 'unavailable'] as const)('allows independent work and isolates consumers while descriptive source revalidation is %s', async outcome => {
    const first = await start('a');
    append(first, 'scoped', { id: 'ready', kind: 'proof', commit: saveProof(first) });
    await cooperative.pulse(peer.id); cooperative.deactivate(peer);
    expect(state.cooperation!.tasks.find(node => node.task.id === 'a')?.status).toBe('integrated');
    const unrelated = await cooperative.next(peer, budget);
    if (unrelated?.kind !== 'task') throw new Error('missing_unrelated_assignment');
    expect(unrelated.task.id).toBe('b');
    expect(cooperative.current(unrelated)).toBe(true);
    const { promise: checking, resolve: entered } = deferred(), { promise: blocked, resolve: release } = deferred();
    host.verify.mockImplementationOnce(async request => {
      expect(request.items.map((item: { theoremName: string }) => item.theoremName)).toEqual(['Tutorial.a']);
      entered(); await blocked;
      const result = verified(request);
      const status = outcome === 'unavailable' ? 'unavailable' : 'failed';
      return outcome === 'passed' ? result : { ...result, status, results: result.results.map(item => ({
        ...item, status, stdoutPreview: 'Submission.lean:1:1: error: revalidation rejected the proof',
      })) };
    });
    const consumer: CooperativeTask = { id: 'consumer', kind: 'lemma', objective: 'Use the revalidated helper a.',
      proofPath: 'Submission.lean', theoremName: 'Tutorial.consumer', type: 'True', dependsOn: ['a'],
      ownerId: other.id, revision: 0 };
    fs.appendFileSync(path.join(directory, 'edits.jsonl'), JSON.stringify({ id: 'describe-and-consume',
      baseVersion: state.cooperation!.planVersion,
      tasks: [...state.cooperation!.tasks.map(node => node.task.id === 'a'
        ? { ...node.task, objective: 'Clarify the existing helper a.', revision: 1 } : node.task), consumer],
    }) + '\n');
    const pendingEdit = cooperative.pulse(lead.id);
    const controller = instances.find(instance => instance.cooperative === cooperative)!.controller;
    let synchronization: Promise<void> | undefined;
    let pendingAssignment: Promise<CooperativeAction | undefined> | undefined;
    let assigned = false;
    try {
      await checking;
      await pendingEdit;
      synchronization = (cooperative as any).schedulePlanSynchronization() as Promise<void>;
      void synchronization.catch(() => {});
      expect(state.cooperation!.tasks.find(node => node.task.id === 'a')?.pendingValidation).toBeDefined();
      expect(taskDependenciesReady(consumer, state.cooperation!.tasks)).toBe(false);
      expect(cooperative.current(unrelated)).toBe(true);
      expect(cooperative.started(peer, unrelated)).toBe(true);
      expect(state.cooperation!.tasks.find(node => node.task.id === 'b')?.attempts).toBe(1);
      pendingAssignment = cooperative.next(other, budget).then(action => { assigned = true; return action; });
      void pendingAssignment.catch(() => {});
      await Promise.resolve(); await Promise.resolve();
      expect(assigned).toBe(false);
      expect(events.some(item => item.event === 'task_assigned' && item.details?.taskId === 'consumer')).toBe(false);
      release();
      if (outcome === 'unavailable') await expect(synchronization).rejects.toThrow('math_verifier_unavailable');
      else {
        await synchronization;
        expect(state.cooperation!.tasks.find(node => node.task.id === 'a')?.status)
          .toBe(outcome === 'passed' ? 'integrated' : 'blocked');
        expect(state.cooperation!.tasks.find(node => node.task.id === 'a')?.pendingValidation).toBeUndefined();
      }
      expect(state.cooperation!.tasks.find(node => node.task.id === 'b')).toMatchObject({ status: 'running', attempts: 1 });
      if (outcome === 'passed') {
        expect(taskDependenciesReady(consumer, state.cooperation!.tasks)).toBe(true);
        const action = await pendingAssignment;
        expect(action?.kind).toBe('task');
        if (action?.kind !== 'task') throw new Error('missing_revalidated_consumer');
        expect(action.task.id).toBe('consumer');
        expect(cooperative.started(other, action)).toBe(true);
      } else {
        await Promise.resolve(); await Promise.resolve();
        expect(taskDependenciesReady(consumer, state.cooperation!.tasks)).toBe(false);
        expect(assigned).toBe(false);
        if (outcome === 'unavailable') expect(cooperative.started(peer, unrelated)).toBe(false);
        expect(events.some(item => item.event === 'task_assigned' && item.details?.taskId === 'consumer')).toBe(false);
        expect(state.cooperation!.tasks.find(node => node.task.id === 'consumer')).toMatchObject({ status: 'pending', attempts: 0 });
        if (outcome === 'unavailable') await expect(pendingAssignment).rejects.toThrow('math_verifier_unavailable');
        else {
          controller.abort();
          await expect(pendingAssignment).rejects.toThrow();
        }
      }
    } finally {
      release(); await pendingEdit.catch(() => {}); await synchronization?.catch(() => {});
      controller.abort(); await pendingAssignment?.catch(() => {});
    }
  });

  it.each([
    { log: 'scoped', legacyRecord: false }, { log: 'legacy', legacyRecord: false },
    { log: 'scoped', legacyRecord: true }, { log: 'legacy', legacyRecord: true },
  ] as const)('accepts the same task version from a new seed after restore ($log, old record: $legacyRecord)', async ({ log, legacyRecord }) => {
    const first = await start('a');
    append(first, log, { id: 'ready', kind: 'progress', summary: 'First assignment evidence.' });
    await cooperative.pulse(peer.id); cooperative.deactivate(peer);
    if (legacyRecord) delete state.cooperation!.deliveries![0].assignmentKey;
    await reassign();
    fs.writeFileSync(path.join(peer.worktree, 'RESEARCH.md'), 'A new assignment checkpoint.');
    commitSolverSources(problem, peer.worktree);
    await restart();
    const next = await start('a');
    expect(next.assignment.taskDigest).toBe(first.assignment.taskDigest);
    expect(next.assignment.seedCommit).not.toBe(first.assignment.seedCommit);
    const value = { id: 'ready', kind: 'progress', summary: 'Current assignment evidence.' };
    append(next, log, value); append(next, log, value);
    await cooperative.pulse(peer.id); cooperative.deactivate(peer);
    expect(state.cooperation!.deliveries?.filter(record => record.submissionId === 'ready')).toMatchObject([
      { summary: 'First assignment evidence.' },
      { summary: 'Current assignment evidence.', assignmentKey: assignmentDeliveryFile(next.assignment) },
    ]);
    expect(host.verify).not.toHaveBeenCalled();
  });

  it.each(['scoped', 'legacy'] as const)('accepts reused ids after the same-version assignment is replaced without a new seed in %s logs', async log => {
    const first = await start('a');
    append(first, log, { id: 'ready', kind: 'progress', summary: 'First assignment evidence.' });
    await cooperative.pulse(peer.id); cooperative.deactivate(peer);
    await reassign();
    const next = await start('a');
    expect(next.assignment).not.toBe(first.assignment);
    expect(next.assignment.taskDigest).toBe(first.assignment.taskDigest);
    expect(next.assignment.seedCommit).toBe(first.assignment.seedCommit);
    expect(next.assignment.assignmentId).not.toBe(first.assignment.assignmentId);
    expect(assignmentDeliveryFile(next.assignment)).not.toBe(assignmentDeliveryFile(first.assignment));
    append(next, log, { id: 'ready', kind: 'progress', summary: 'Replacement assignment evidence.' });
    await cooperative.pulse(peer.id); cooperative.deactivate(peer);
    expect(state.cooperation!.deliveries?.filter(record => record.submissionId === 'ready').map(record => record.summary))
      .toEqual(['First assignment evidence.', 'Replacement assignment evidence.']);
    expect(host.verify).not.toHaveBeenCalled();
  });

  it('does not attribute a late old scoped log to a replacement assignment with the same task and seed', async () => {
    const first = await start('a');
    append(first, 'scoped', { id: 'ready', kind: 'progress', summary: 'First assignment evidence.' });
    await cooperative.pulse(peer.id); cooperative.deactivate(peer);
    await reassign();
    const next = await start('a');
    expect(next.assignment.seedCommit).toBe(first.assignment.seedCommit);
    append(first, 'scoped', { id: 'late', kind: 'proof', commit: saveProof(next), summary: 'Late old assignment proof.' });
    append(next, 'scoped', { id: 'ready', kind: 'progress', summary: 'Replacement assignment evidence.' });
    await cooperative.pulse(peer.id); cooperative.deactivate(peer);
    expect(state.cooperation!.deliveries?.map(record => record.summary))
      .toEqual(['First assignment evidence.', 'Replacement assignment evidence.']);
    expect(state.cooperation!.tasks.find(node => node.task.id === 'a')?.proof).toBeUndefined();
    expect(host.verify).not.toHaveBeenCalled();
  });

  it.each(['scoped', 'legacy'] as const)('keeps a stale asynchronous proof out of the revised task in %s logs', async log => {
    const { promise: checking, resolve: entered } = deferred(), { promise: blocked, resolve: release } = deferred();
    host.verify.mockImplementationOnce(async request => { entered(); await blocked; return verified(request); });
    const old = await start('a');
    append(old, log, { id: 'ready', kind: 'proof', commit: saveProof(old) });
    const pending = cooperative.pulse(peer.id);
    try {
      await checking;
      await cooperative.pulse(lead.id);
      await applyEdit(task => task.id === 'a' ? { ...task, revision: 1 } : task);
      expect(cooperative.current(old)).toBe(false);
    } finally { release(); await pending; }
    cooperative.deactivate(peer);
    expect(state.cooperation!.tasks.find(node => node.task.id === 'a')).toMatchObject({ task: { revision: 1 }, status: 'pending' });
    expect(state.cooperation!.tasks.find(node => node.task.id === 'a')?.proof).toBeUndefined();
    expect(host.verify).toHaveBeenCalledOnce();
    const next = await start('a');
    expect(next.assignment.taskDigest).not.toBe(old.assignment.taskDigest);
    append(next, log, { id: 'ready', kind: 'proof', commit: saveProof(next) });
    await cooperative.pulse(peer.id); cooperative.deactivate(peer);
    expect(state.cooperation!.deliveries?.filter(record => record.submissionId === 'ready')).toMatchObject([
      { status: 'superseded', taskDigest: old.assignment.taskDigest, assignmentKey: assignmentDeliveryFile(old.assignment) },
      { status: 'verified', taskDigest: next.assignment.taskDigest, assignmentKey: assignmentDeliveryFile(next.assignment) },
    ]);
    const node = state.cooperation!.tasks.find(node => node.task.id === 'a')!;
    expect(node).toMatchObject({ status: 'integrated', proof: { taskDigest: next.assignment.taskDigest } });
    expect(node.integratedCheck?.verification).toEqual(node.proof!.verification);
    expect(host.verify).toHaveBeenCalledTimes(2);
    expect(host.verify.mock.calls.map(([request]) => request.items[0].statementHash))
      .toEqual([old.assignment.taskDigest, next.assignment.taskDigest]);
    expect(node.integratedCheck?.verification.targetCommit).toBe(host.verify.mock.calls[1][0].targetCommit);
  });

  it.each(['scoped', 'legacy'] as const)('deduplicates a persisted assignment after replaying a %s cursor', async log => {
    const first = await start('a');
    const value = { id: 'ready', kind: 'progress', summary: 'Saved assignment evidence.' };
    append(first, log, value); append(first, log, value);
    await cooperative.pulse(peer.id); cooperative.deactivate(peer);
    state.cooperation!.cursors![cursorKey(first, log)] = 0;
    await restart();
    const resumed = await start('a');
    expect(resumed.assignment.assignmentId).toBe(first.assignment.assignmentId);
    expect(assignmentDeliveryFile(resumed.assignment)).toBe(assignmentDeliveryFile(first.assignment));
    await cooperative.pulse(peer.id); cooperative.deactivate(peer);
    expect(state.cooperation!.deliveries).toHaveLength(1);
    expect(host.verify).not.toHaveBeenCalled();
  });

  it('preserves assignment-bound automatic id deduplication for old scoped records', async () => {
    const first = await start('a');
    delete first.assignment.assignmentId;
    append(first, 'scoped', { summary: 'Automatic assignment evidence.' });
    await cooperative.pulse(peer.id); cooperative.deactivate(peer);
    delete state.cooperation!.deliveries![0].assignmentKey;
    state.cooperation!.cursors![cursorKey(first, 'scoped')] = 0;
    await restart();
    await start('a');
    await cooperative.pulse(peer.id); cooperative.deactivate(peer);
    expect(state.cooperation!.deliveries).toHaveLength(1);
    expect(host.verify).not.toHaveBeenCalled();
  });
});
