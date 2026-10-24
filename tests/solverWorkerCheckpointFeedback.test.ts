import fs from 'node:fs';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { mathDigest } from '../src/math/mathRuntimeIo';
import { readSolverRunState, writeSolverRunState, type SolverRunState } from '../src/solver/archive';
import type { CooperativeResearch } from '../src/solver/cooperation';
import { directSolverModules } from '../src/solver/modules';
import type { ResearchWorker } from '../src/solver/modules/organization';
import type { SolverProblem } from '../src/solver/problem';
import { assignmentDeliveryFile, parseCooperationPlan, type CooperativeAction } from '../src/solver/tasks';
import { cooperativeResearch } from './helpers/cooperation';
import { leadWorker, localExample, peerWorker, solverState } from './helpers/solver';

type Task = Extract<CooperativeAction, { kind: 'task' }>;
type Notice = ReturnType<typeof vi.fn<(message: string) => Promise<void>>>;

describe('task worker checkpoint correction feedback', () => {
  const budget = { maxTurns: Infinity, remainingMs: Infinity };
  let directory: string, problem: SolverProblem, state: SolverRunState, workers: ResearchWorker[];
  let cooperative: CooperativeResearch, controller: AbortController;
  let notices: Map<string, Notice>, releases: (() => void)[];
  let events: { event: string; details?: Record<string, unknown> }[];
  const savedFile = () => path.join(directory, 'state.json');
  const research = (worker: ResearchWorker) => state.workers!.find(record => record.id === worker.id)!;
  const node = (action: Task) => state.cooperation!.tasks.find(record => record.task.id === action.task.id)!;
  const log = (action: Task) => assignmentDeliveryFile(action.assignment);
  const key = (worker: ResearchWorker, action: Task) => `${worker.id}/${log(action)}`;
  const json = (worker: ResearchWorker) => JSON.parse(fs.readFileSync(path.join(worker.worktree, 'COOPERATION.json'), 'utf8'));
  const notice = (worker: ResearchWorker) => notices.get(worker.id)!;
  const request = (worker: ResearchWorker) => {
    const record = research(worker);
    record.threadId = `${worker.id}-thread`;
    record.contextCheckpoint = { threadId: record.threadId, requestId: `${worker.id}-request`, requestedAt: 1 };
    fs.writeFileSync(path.join(worker.worktree, 'RESEARCH.md'),
      `The exact ${worker.id} argument and missing construction remain saved before handing back writing.\n`);
    return record.contextCheckpoint;
  };
  const checkpoint = (worker: ResearchWorker, correct = false) => ({ kind: 'checkpoint',
    requestId: research(worker).contextCheckpoint!.requestId,
    notesDigest: correct ? mathDigest(fs.readFileSync(path.join(worker.worktree, 'RESEARCH.md'))) : '0'.repeat(64) });
  const append = (worker: ResearchWorker, action: Task, value: unknown) => fs.appendFileSync(
    path.join(worker.worktree, log(action)), JSON.stringify(value) + '\n');
  const publish = async (worker: ResearchWorker, action: Task, value = checkpoint(worker)) => {
    append(worker, action, value); await cooperative.pulse(worker.id);
  };
  const start = async (worker: ResearchWorker) => {
    const action = await cooperative.next(worker, budget);
    if (action?.kind !== 'task' || action.task.kind !== 'research') throw new Error('fixture_expected_research_assignment');
    expect(cooperative.started(worker, action)).toBe(true);
    cooperative.activate(worker, action, async () => {}, notice(worker));
    return action;
  };
  const context = (worker: ResearchWorker, action: Task) => directSolverModules.M4.build(problem,
    { ...state, cooperation: cooperative.contextState(action, worker) },
    { root: directory, worktree: worker.worktree, retrievalRoot: directory, environment: {},
      taskText: 'Resolve the exact assigned mathematical question.', assignment: action, maxOptionalContextBytes: 0 });
  const expectCorrection = (message: string, worker: ResearchWorker, action: Task, notification = true) => {
    for (const detail of [research(worker).contextCheckpoint!.requestId!, log(action), 'notesDigest', '"kind":"checkpoint"'])
      expect(message).toContain(detail);
    expect(message).toMatch(/append/iu);
    if (notification) {
      expect(message).not.toContain('replacesReceipt');
      expect(message).not.toContain('dispatchNonce');
    }
  };

  beforeEach(() => {
    const example = localExample('solver-worker-checkpoint-feedback-', 'lead');
    ({ directory, problem } = example);
    workers = [leadWorker(problem, example.workspace), peerWorker(example, 'researcher-a'), peerWorker(example, 'researcher-b')];
    const plan = parseCooperationPlan(problem, { tasks: [
      ...workers.slice(1).map(worker => ({ id: `${worker.id}-question`, kind: 'research', ownerId: worker.id,
        objective: `Identify the exact ${worker.id} construction.`, dependsOn: [] })),
      ...problem.targets.map((target, index) => ({ id: `goal_${index}`, kind: 'goal',
        objective: `Prove ${target.theoremName}.`, ...target, status: 'paused' })),
    ] });
    state = solverState(problem, example.workspace, { runId: 'worker-checkpoint-feedback-fixture', phase: 'running',
      workers: workers.map(worker => ({ id: worker.id, role: worker.role, worktree: worker.worktree, phase: 'checking', turns: 0 })),
      cooperation: { canonicalCommit: problem.baseCommit,
        tasks: plan.tasks.map(task => ({ task, status: 'pending', attempts: 0 })),
        groups: plan.groups.map(group => ({ group, turns: 0 })) } });
    events = []; releases = []; notices = new Map(workers.map(worker => [worker.id, vi.fn(async (_message: string) => {})]));
    controller = new AbortController();
    cooperative = cooperativeResearch({ state, workers, retrievalRoot: directory, signal: controller.signal,
      save: () => writeSolverRunState(savedFile(), state), emit: (event, details) => events.push({ event, details }) });
  });
  afterEach(async () => {
    controller.abort(); releases.forEach(release => release());
    await cooperative.stop();
    vi.restoreAllMocks(); fs.rmSync(directory, { recursive: true, force: true });
  });

  it('repairs a bad worker ACK through its notice without creating mathematical correction or replacing task feedback', async () => {
    const worker = workers[1], action = await start(worker), checkpointRequest = request(worker);
    const mathematicalFeedback = 'Use the exact saved coercion gap before another library search.';
    node(action).feedback = mathematicalFeedback;
    cooperative.activate(worker, action, async () => {}, notice(worker));
    const before = structuredClone({ task: node(action).task, status: node(action).status,
      assignment: node(action).assignment, planVersion: state.cooperation!.planVersion });
    let notifiedState: SolverRunState | undefined;
    notice(worker).mockImplementation(async message => {
      expectCorrection(message, worker, action);
      notifiedState = readSolverRunState(savedFile());
      const saved = notifiedState.workers!.find(record => record.id === worker.id)!.contextCheckpoint!.rejection!;
      expect(saved).toMatchObject({ file: log(action), reason: 'math_delivery_invalid' });
      expect(notifiedState.cooperation!.cursors![key(worker, action)]).toBe(saved.offset);
      append(worker, action, checkpoint(worker, true));
    });
    await publish(worker, action);
    expect(checkpointRequest.rejection).toMatchObject({ file: log(action), reason: 'math_delivery_invalid' });
    expect(notice(worker)).toHaveBeenCalledOnce();
    expect(notifiedState).toBeDefined();
    expect(state.cooperation!.deliveryReceipts ?? []).toEqual([]);
    expect(node(action).feedback).toBe(mathematicalFeedback);
    const rejection = cooperative.contextState(action, worker).contextCheckpointRejection;
    expect(rejection).toMatchObject({ threadId: checkpointRequest.threadId, requestId: checkpointRequest.requestId });
    expect(json(worker).contextCheckpointRejection).toEqual(rejection);
    for (const other of [workers[0], workers[2]]) {
      expect(cooperative.contextState(undefined, other).contextCheckpointRejection).toBeUndefined();
      expect(json(other).contextCheckpointRejection).toBeUndefined();
      expect(notice(other)).not.toHaveBeenCalled();
    }
    const compiled = context(worker, action);
    expect(compiled.manifest!.included).toContainEqual(expect.objectContaining({ id: 'context-checkpoint-rejection', required: true }));
    expect(compiled.manifest).toMatchObject({ maxOptionalBytes: 0, optionalBytes: 0 });
    for (const message of [compiled.message, compiled.continuationMessage!]) {
      expectCorrection(message, worker, action, false);
      expect(message).toContain(mathematicalFeedback);
    }
    await cooperative.pulse(worker.id);
    expect(checkpointRequest.publishedNotesDigest).toBe(checkpoint(worker, true).notesDigest);
    expect(checkpointRequest.rejection).toBeUndefined();
    expect(json(worker).contextCheckpointRejection).toBeUndefined();
    expect(node(action).feedback).toBe(mathematicalFeedback);
    expect({ task: node(action).task, status: node(action).status,
      assignment: node(action).assignment, planVersion: state.cooperation!.planVersion }).toEqual(before);
    expect(state.check).toBeUndefined();
    expect(state.cooperation!.deliveries ?? []).toEqual([]);
    expect(state.cooperation!.tasks.every(record => !record.proof && !record.integratedCheck)).toBe(true);
  });

  it('clears a repaired ACK while preserving an independent rejected research finding and its correction receipt', async () => {
    const worker = workers[1], action = await start(worker), checkpointRequest = request(worker);
    append(worker, action, { kind: 'research', finding: { summary: 42 } });
    await cooperative.pulse(worker.id);
    expect(state.cooperation!.deliveryReceipts).toHaveLength(1);
    const receipt = structuredClone(state.cooperation!.deliveryReceipts![0]), mathematicalFeedback = node(action).feedback;
    expect(receipt).toMatchObject({ status: 'needs-correction', code: 'math_research_delivery_invalid' });
    expect(notice(worker)).toHaveBeenCalledOnce();
    notice(worker).mockClear();
    await publish(worker, action);
    expect(checkpointRequest.rejection).toBeDefined();
    expect(state.cooperation!.deliveryReceipts).toEqual([receipt]);
    expect(node(action).feedback).toBe(mathematicalFeedback);
    expect(notice(worker)).toHaveBeenCalledOnce();
    expectCorrection(notice(worker).mock.calls[0][0], worker, action);
    await publish(worker, action, checkpoint(worker, true));
    expect(checkpointRequest.rejection).toBeUndefined();
    expect(checkpointRequest.publishedNotesDigest).toBe(checkpoint(worker, true).notesDigest);
    expect(state.cooperation!.deliveryReceipts).toEqual([receipt]);
    expect(node(action).feedback).toBe(mathematicalFeedback);
    expect(context(worker, action).continuationMessage).toContain(receipt.id);
  });

  it('accepts a later corrected ACK while its diagnostic notification is still pending', async () => {
    const worker = workers[1], action = await start(worker), checkpointRequest = request(worker);
    let release!: () => void;
    const held = new Promise<void>(resolve => { release = resolve; });
    releases.push(release);
    notice(worker).mockImplementation(() => held);
    let settled = false;
    const first = publish(worker, action).then(() => { settled = true; });
    try {
      await vi.waitFor(() => expect(settled).toBe(true), { timeout: 500 });
      expect(notice(worker)).toHaveBeenCalledOnce();
      const saved = readSolverRunState(savedFile());
      expect(saved.workers!.find(record => record.id === worker.id)!.contextCheckpoint!.rejection).toBeDefined();
      await publish(worker, action, checkpoint(worker, true));
      expect(checkpointRequest.publishedNotesDigest).toBe(checkpoint(worker, true).notesDigest);
      expect(checkpointRequest.rejection).toBeUndefined();
      expect(state.cooperation!.deliveryReceipts ?? []).toEqual([]);
      expect(notice(worker)).toHaveBeenCalledOnce();
    } finally { release(); await first; }
  });

  it('retries failures independently for two simultaneous peer requests without replaying their intake or leaking diagnostics', async () => {
    const peers = workers.slice(1), actions: Task[] = [];
    for (const worker of peers) {
      const action = await start(worker); actions.push(action); request(worker);
      notice(worker).mockRejectedValueOnce(new Error('transport unavailable'));
      append(worker, action, checkpoint(worker));
    }
    await cooperative.pulse();
    expect(events.filter(item => item.event === 'delivery_rejected')).toHaveLength(2);
    for (const [index, worker] of peers.entries()) {
      expect(research(worker).contextCheckpoint!.rejection).toMatchObject({ file: log(actions[index]) });
      expect(notice(worker)).toHaveBeenCalledOnce();
    }
    await cooperative.pulse();
    await cooperative.pulse();
    for (const [index, worker] of peers.entries()) {
      expect(notice(worker)).toHaveBeenCalledTimes(2);
      expectCorrection(notice(worker).mock.calls[1][0], worker, actions[index]);
      const other = peers[1 - index];
      expect(notice(worker).mock.calls[1][0]).not.toContain(research(other).contextCheckpoint!.requestId!);
      expect(json(worker).contextCheckpointRejection.requestId).toBe(research(worker).contextCheckpoint!.requestId);
      expect(state.cooperation!.cursors![key(worker, actions[index])]).toBe(fs.statSync(path.join(worker.worktree, log(actions[index]))).size);
    }
    expect(json(workers[0]).contextCheckpointRejection).toBeUndefined();
    expect(notice(workers[0])).not.toHaveBeenCalled();
    expect(events.filter(item => item.event === 'delivery_rejected')).toHaveLength(2);
    expect(state.cooperation!.deliveryReceipts ?? []).toEqual([]);
  });

  it('drops old request and thread diagnostics and does not notify an inactive assignment', async () => {
    const worker = workers[1], action = await start(worker), record = research(worker);
    request(worker);
    for (const change of ['request', 'thread', 'inactive'] as const) {
      if (change === 'inactive') record.contextCheckpoint = { threadId: record.threadId!, requestId: 'active-again-request', requestedAt: 3 };
      notice(worker).mockRejectedValueOnce(new Error('transport unavailable'));
      await publish(worker, action);
      expect(record.contextCheckpoint!.rejection).toBeDefined();
      notice(worker).mockClear();
      if (change === 'request') record.contextCheckpoint = { threadId: record.threadId!, requestId: 'replacement-request', requestedAt: 2 };
      else if (change === 'thread') record.threadId = 'replacement-thread';
      else cooperative.deactivate(worker);
      if (change !== 'inactive') cooperative.activate(worker, action, async () => {}, notice(worker));
      await cooperative.pulse(worker.id);
      expect(notice(worker)).not.toHaveBeenCalled();
      if (change !== 'inactive') {
        expect(cooperative.contextState(action, worker).contextCheckpointRejection).toBeUndefined();
        expect(json(worker).contextCheckpointRejection).toBeUndefined();
        const compiled = context(worker, action);
        expect(compiled.manifest!.included).not.toContainEqual(expect.objectContaining({ id: 'context-checkpoint-rejection' }));
        expect(compiled.continuationMessage).not.toContain('math_delivery_invalid');
      }
    }
    expect(state.cooperation!.deliveryReceipts ?? []).toEqual([]);
  });

  it('retargets unresolved checkpoint feedback to a new active assignment without retrying its old callback', async () => {
    const worker = workers[1], oldAction = await start(worker), checkpointRequest = request(worker);
    const oldNotice = notice(worker);
    oldNotice.mockRejectedValueOnce(new Error('transport unavailable'));
    await publish(worker, oldAction);
    expect(checkpointRequest.rejection).toMatchObject({ file: log(oldAction) });
    expect(oldNotice).toHaveBeenCalledOnce();
    cooperative.deactivate(worker); cooperative.interrupted(worker, oldAction);
    node(oldAction).assignment = undefined;
    const currentNotice = vi.fn(async (_message: string) => {});
    notices.set(worker.id, currentNotice);
    const currentAction = await start(worker);
    expect(log(currentAction)).not.toBe(log(oldAction));
    await cooperative.pulse(worker.id);
    expect(oldNotice).toHaveBeenCalledOnce();
    expect(currentNotice).toHaveBeenCalledOnce();
    expectCorrection(currentNotice.mock.calls[0][0], worker, currentAction);
    for (const message of [context(worker, currentAction).message, context(worker, currentAction).continuationMessage!])
      expect(message).toContain('Append one complete corrected JSON line to ' + log(currentAction));
    await publish(worker, currentAction, checkpoint(worker, true));
    expect(checkpointRequest.rejection).toBeUndefined();
    expect(checkpointRequest.publishedNotesDigest).toBe(checkpoint(worker, true).notesDigest);
    expect(state.cooperation!.deliveryReceipts ?? []).toEqual([]);
  });
});
