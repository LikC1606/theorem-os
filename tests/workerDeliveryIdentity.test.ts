import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { bootstrapLocalExample } from '../src/math/localExample';
import type { MathematicsVerifierBatchRequest, MathematicsVerifierBatchResult } from '../src/math/verifier';
import { readSolverRunState, writeSolverRunState, type SolverRunState } from '../src/solver/archive';
import { CooperativeResearch, parseCooperationPlan } from '../src/solver/cooperation';
import { directSolverModules } from '../src/solver/modules';
import type { ResearchWorker } from '../src/solver/modules/organization';
import { commitSolverSources, git, readSolverProblem, type SolverProblem } from '../src/solver/problem';
import { assignmentDeliveryFile, type CooperativeAction, type CooperativeTask } from '../src/solver/tasks';

const host = vi.hoisted(() => ({ verify: vi.fn(), createSession: vi.fn() }));
vi.mock('../src/math/verifier', async importOriginal => ({
  ...await importOriginal<typeof import('../src/math/verifier')>(),
  checkManyFormalVerifications: host.verify,
  resolveMathematicsLakePackagesCache: () => undefined,
}));
vi.mock('../src/runtime/codexSession', () => ({ createCodexMathSession: host.createSession }));

function verified(request: MathematicsVerifierBatchRequest): MathematicsVerifierBatchResult {
  return { schema: 'deepscientist.mathematics.verification-batch/v1', status: 'kernel_verified',
    targetCommit: request.targetCommit!, sessionId: 'delivery-identity-fixture', events: [], startedAt: 1, checkedAt: 2, durationMs: 1,
    results: request.items.map(item => ({ ...item, sourceDeclarationHash: item.expectedSourceDeclarationHash,
      receiptId: `fixture-${request.targetCommit}-${item.theoremName}`, targetCommit: request.targetCommit,
      status: 'kernel_verified', claim: 'statement' })) as MathematicsVerifierBatchResult['results'] };
}

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
    const instance = new CooperativeResearch({ state, workers: [lead, peer, other],
      access: new Map([lead, peer, other].map(worker => [worker.id, { environment: {}, retrievalRoot: directory }])),
      signal: controller.signal, save: () => {}, emit: (event, details) => events.push({ event, details }),
      modules: { ...directSolverModules, M5: { ...directSolverModules.M5, primaryLed: true } },
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
    directory = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'worker-delivery-identity-')));
    const workspace = path.join(directory, 'lead');
    const receipt = bootstrapLocalExample(workspace);
    problem = readSolverProblem(workspace, receipt.activeProblemPath);
    const workers = ['peer', 'other'].map(id => {
      const worktree = path.join(directory, id);
      git(workspace, ['worktree', 'add', '--quiet', '--detach', worktree, problem.baseCommit]);
      return { id, role: 'researcher' as const, worktree, ownedFiles: problem.ownedFiles };
    });
    lead = { id: 'solver', role: 'lead', worktree: workspace, ownedFiles: problem.ownedFiles };
    [peer, other] = workers;
    const plan = parseCooperationPlan(problem, { tasks: [
      ...problem.targets.map((target, index) => ({ id: `goal_${index}`, kind: 'goal', objective: `Prove ${target.theoremName}.`,
        proofPath: target.proofPath, theoremName: target.theoremName, status: 'paused' })),
      ...['a', 'b'].map(id => ({ id, kind: 'lemma', objective: `Prove helper ${id}.`, proofPath: 'Submission.lean',
        theoremName: `Tutorial.${id}`, type: 'True', ownerId: peer.id })),
    ] });
    state = { schema: 'deepscientist.math.solver.v1', runId: 'delivery-identity-fixture', problem,
      taskDigest: 'task', buildDigest: 'build', environmentDigest: 'environment', evaluatorDigest: 'evaluator',
      model: 'unused', effort: 'unused', worktree: workspace, phase: 'running', turns: 0, failures: [],
      cooperation: { canonicalCommit: problem.baseCommit,
        tasks: plan.tasks.map(task => ({ task, status: 'pending', attempts: 0 })),
        groups: plan.groups.map(group => ({ group, turns: 0 })) } };
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
    for (const id of ['a', 'b']) {
      const action = await start(id), commit = saveProof(action);
      const value = { id: 'ready', kind: 'proof', commit, summary: `${id} proved.` };
      append(action, log, value); append(action, log, value);
      await cooperative.pulse(peer.id);
      expect(state.cooperation!.tasks.find(node => node.task.id === id)?.status).toBe('integrated');
      expect(state.cooperation!.cursors?.[cursorKey(action, log)]).toBe(fs.statSync(path.join(peer.worktree, logName(action, log))).size);
      expect(state.cooperation!.deliveries?.filter(record => record.taskId === id && record.submissionId === 'ready'))
        .toMatchObject([{ status: 'verified', assignmentKey: assignmentDeliveryFile(action.assignment) }]);
      await cooperative.pulse(peer.id);
      cooperative.deactivate(peer);
    }
    expect(host.verify).toHaveBeenCalledTimes(4);
    expect(events.some(item => item.event === 'delivery_rejected')).toBe(false);
  });

  it.each(['scoped', 'legacy'] as const)('isolates reused ids after a mathematical task revision in %s logs', async log => {
    const first = await start('a');
    append(first, log, { id: 'ready', kind: 'proof', commit: saveProof(first) });
    await cooperative.pulse(peer.id); cooperative.deactivate(peer);
    await applyEdit(task => task.id === 'a' ? { ...task, revision: 1 } : task);
    const revised = await start('a');
    expect(revised.assignment.taskDigest).not.toBe(first.assignment.taskDigest);
    append(revised, log, { id: 'ready', kind: 'proof', commit: saveProof(revised) });
    await cooperative.pulse(peer.id); cooperative.deactivate(peer);
    expect(state.cooperation!.tasks.find(node => node.task.id === 'a')).toMatchObject({ task: { revision: 1 }, status: 'integrated' });
    expect(state.cooperation!.deliveries?.filter(record => record.submissionId === 'ready').map(record => record.status))
      .toEqual(['superseded', 'verified']);
    expect(host.verify).toHaveBeenCalledTimes(4);
  });

  it.each([
    { log: 'scoped', legacyRecord: false }, { log: 'legacy', legacyRecord: false },
    { log: 'scoped', legacyRecord: true }, { log: 'legacy', legacyRecord: true },
  ] as const)('accepts the same task version from a new seed after restore ($log, old record: $legacyRecord)', async ({ log, legacyRecord }) => {
    const first = await start('a');
    append(first, log, { id: 'ready', kind: 'progress', summary: 'First assignment evidence.' });
    await cooperative.pulse(peer.id); cooperative.deactivate(peer);
    if (legacyRecord) delete state.cooperation!.deliveries![0].assignmentKey;
    await applyEdit(task => task.id === 'a' ? { ...task, ownerId: other.id } : task);
    await applyEdit(task => task.id === 'a' ? { ...task, ownerId: peer.id } : task);
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
    await applyEdit(task => task.id === 'a' ? { ...task, ownerId: other.id } : task);
    await applyEdit(task => task.id === 'a' ? { ...task, ownerId: peer.id } : task);
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
    await applyEdit(task => task.id === 'a' ? { ...task, ownerId: other.id } : task);
    await applyEdit(task => task.id === 'a' ? { ...task, ownerId: peer.id } : task);
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
    let entered!: () => void, release!: () => void;
    const checking = new Promise<void>(resolve => { entered = resolve; });
    const blocked = new Promise<void>(resolve => { release = resolve; });
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
    const next = await start('a');
    append(next, log, { id: 'ready', kind: 'proof', commit: saveProof(next) });
    await cooperative.pulse(peer.id); cooperative.deactivate(peer);
    expect(state.cooperation!.deliveries?.filter(record => record.submissionId === 'ready').map(record => record.status))
      .toEqual(['superseded', 'verified']);
    expect(state.cooperation!.tasks.find(node => node.task.id === 'a')?.status).toBe('integrated');
    expect(host.verify).toHaveBeenCalledTimes(3);
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
