import fs from 'node:fs';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { mathDigest } from '../src/math/mathRuntimeIo';
import { readSolverRunState, writeSolverRunState, type SolverRunState } from '../src/solver/archive';
import type { CooperativeResearch } from '../src/solver/cooperation';
import { directSolverModules } from '../src/solver/modules';
import type { ResearchWorker } from '../src/solver/modules/organization';
import type { SolverProblem } from '../src/solver/problem';
import { leadPlanDeliveryFile, parseCooperationPlan, taskVersion, type CooperativeAction, type CooperativeTask } from '../src/solver/tasks';
import { cooperativeResearch } from './helpers/cooperation';
import { leadWorker, localExample, peerWorker, solverState } from './helpers/solver';

type Lead = Extract<CooperativeAction, { kind: 'lead' }>;
type Publication = 'initial' | 'replacement' | 'handoff' | 'assessment';

describe('live Lead publication correction feedback', () => {
  const budget = { maxTurns: Infinity, remainingMs: Infinity };
  let directory: string, problem: SolverProblem, state: SolverRunState, workers: ResearchWorker[];
  let cooperative: CooperativeResearch, completePlan: ReturnType<typeof parseCooperationPlan>;
  let instances: { cooperative: CooperativeResearch; controller: AbortController }[];
  let events: { event: string; details?: Record<string, unknown> }[];
  let notify: ReturnType<typeof vi.fn<(message: string) => Promise<void>>>;
  const savedFile = () => path.join(directory, 'state.json');
  const json = (worker = workers[0]) => JSON.parse(fs.readFileSync(path.join(worker.worktree, 'COOPERATION.json'), 'utf8'));
  const nonce = (action: Lead) => action.initialPlanNonce ?? action.planNonce!;
  const log = (action: Lead) => leadPlanDeliveryFile(action)!;
  const cursor = (action: Lead) => `${workers[0].id}/${log(action)}`;
  const rejected = () => events.filter(item => ['initial_plan_rejected', 'plan_publication_rejected'].includes(item.event));
  const helper: CooperativeTask = { id: 'bridge', kind: 'lemma', objective: 'Prove the exact independent bridge.',
    theoremName: 'Tutorial.bridge', proofPath: 'Submission.lean', type: 'True', dependsOn: [], revision: 0 };
  const create = () => {
    const controller = new AbortController(), currentState = state;
    const instance = cooperativeResearch({ state: currentState, workers, retrievalRoot: directory, signal: controller.signal,
      save: () => writeSolverRunState(savedFile(), currentState), emit: (event, details) => events.push({ event, details }) });
    instances.push({ cooperative: instance, controller });
    return instance;
  };
  const prepare = (kind: Publication = 'replacement') => {
    state.cooperation = { canonicalCommit: problem.baseCommit,
      tasks: kind === 'initial' ? [] : completePlan.tasks.map(task => ({ task, attempts: 0,
        status: kind === 'handoff' && task.id === 'question' ? 'completed' : 'pending' })),
      groups: completePlan.groups.map(group => ({ group, turns: 0 })),
      ...(kind === 'initial' ? {} : { error: 'fixture_request_new_plan' }),
      ...(kind === 'handoff' ? { deliveries: [{ id: 'bridge-proposal', producer: workers[2].id, taskId: 'question',
        taskDigest: taskVersion(completePlan.tasks.find(task => task.id === 'question')!), kind: 'research', status: 'advisory',
        summary: 'The exact bridge needs a Lead decision.', statement: '', premises: [], dependencies: [],
        remainingObligations: [], evidenceRefs: [], createdAt: 1, lemmaRequests: [helper] }] } : {}),
    };
    cooperative = create();
  };
  const start = async () => {
    const action = await cooperative.next(workers[0], budget);
    if (action?.kind !== 'lead' || !leadPlanDeliveryFile(action)) throw new Error('fixture_expected_publication_dispatch');
    expect(cooperative.started(workers[0], action)).toBe(true);
    cooperative.activate(workers[0], action, async () => {}, notify);
    return action;
  };
  const event = (action: Lead, kind: Publication = 'replacement'): Record<string, unknown> => {
    const base = { dispatchNonce: nonce(action), baseVersion: action.planVersion };
    if (kind === 'handoff') return { ...base, kind: 'handoff',
      handoffDecisions: [{ id: action.handoffIds![0], status: 'adopted' }] };
    if (kind === 'assessment') return { ...base, kind: 'assessment',
      assessments: ([['capacity', action.capacityRefill], ['stagnation', action.stagnationRecovery]] as const)
        .flatMap(([requestKind, request]) => request ? [{ kind: requestKind, requestId: request.requestId,
          inputDigest: request.inputDigest, outcome: 'no-independent-work',
          reason: 'The exact missing construction remains unresolved; no independent closed obligation is available.' }] : []),
    };
    return { ...base, kind: 'plan', groups: completePlan.groups,
      tasks: [...completePlan.tasks, ...(kind === 'replacement' ? [helper] : [])] };
  };
  const invalid = (action: Lead, kind: Publication = 'replacement') => kind === 'initial' ? '{broken JSON' :
    JSON.stringify({ ...event(action, kind), ...(kind === 'handoff' ? { handoffDecisions: [] } :
      kind === 'assessment' ? { assessments: [] } : { baseVersion: 'stale-version' }) });
  const publish = async (action: Lead, value: Record<string, unknown> | string) => {
    fs.appendFileSync(path.join(workers[0].worktree, log(action)), (typeof value === 'string' ? value : JSON.stringify(value)) + '\n');
    await cooperative.pulse();
  };
  const expectCorrection = (message: string, action: Lead, reason: string) => {
    for (const detail of [reason, log(action), action.planVersion!, nonce(action)]) expect(message).toContain(detail);
    expect(message).toMatch(/append/iu);
    expect(message).toMatch(/complete/iu);
  };
  const context = (action: Lead) => directSolverModules.M4.build(problem,
    { ...state, cooperation: cooperative.contextState(action, workers[0]) },
    { root: directory, worktree: workers[0].worktree, retrievalRoot: directory, environment: {},
      taskText: 'Decide the exact current mathematical obligations.', assignment: action, maxOptionalContextBytes: 0 });
  const requestCheckpoint = () => {
    const research = state.workers![0];
    research.threadId = 'lead-checkpoint-thread';
    research.contextCheckpoint = { threadId: research.threadId, requestId: 'lead-checkpoint-request', requestedAt: 1 };
    fs.writeFileSync(path.join(workers[0].worktree, 'RESEARCH.md'),
      'The exact current argument and its unresolved construction are saved before handing back writing.\n');
    return research;
  };
  const checkpoint = (requestId: string, correct = false) => ({ kind: 'checkpoint', requestId,
    notesDigest: correct ? mathDigest(fs.readFileSync(path.join(workers[0].worktree, 'RESEARCH.md'))) : '0'.repeat(64) });
  const expectCheckpointCorrection = (message: string, action: Lead, requestId: string, reason: string) => {
    for (const detail of [requestId, reason, log(action), 'notesDigest', '"kind":"checkpoint"']) expect(message).toContain(detail);
    expect(message).toMatch(/append/iu);
    expect(message).not.toContain('dispatchNonce');
    expect(message).not.toContain('"kind":"plan"');
  };

  beforeEach(() => {
    const example = localExample('solver-publication-feedback-', 'lead');
    ({ directory, problem } = example);
    workers = [leadWorker(problem, example.workspace), peerWorker(example, 'engineer', { role: 'engineer' }),
      peerWorker(example, 'researcher')];
    completePlan = parseCooperationPlan(problem, { tasks: [
      { id: 'question', kind: 'research', ownerId: workers[2].id, objective: 'Find the exact missing construction.' },
      ...problem.targets.map((target, index) => ({ id: `goal_${index}`, kind: 'goal',
        objective: `Prove ${target.theoremName}.`, ...target, dependsOn: ['question'] })),
    ] });
    state = solverState(problem, example.workspace, { runId: 'publication-feedback-fixture', phase: 'running',
      workers: workers.map(worker => ({ id: worker.id, role: worker.role, worktree: worker.worktree,
        phase: 'checking', turns: 0 })) });
    events = []; instances = []; notify = vi.fn(async (_message: string) => {});
  });
  afterEach(async () => {
    instances.forEach(instance => instance.controller.abort());
    await Promise.allSettled(instances.map(instance => instance.cooperative.stop()));
    vi.restoreAllMocks(); fs.rmSync(directory, { recursive: true, force: true });
  });

  it.each(['initial', 'replacement', 'handoff', 'assessment'] as const)(
    'saves and notifies a rejected %s before accepting its same-dispatch correction', async kind => {
      prepare(kind);
      const action = await start(), before = structuredClone(state.cooperation), originalAction = structuredClone(action);
      if (kind === 'handoff') expect(action.handoffIds).toHaveLength(1);
      if (kind === 'assessment') expect(action.capacityRefill).toBeDefined();
      let savedAtNotification: SolverRunState | undefined, rejectedOffset: number | undefined;
      notify.mockImplementation(async message => {
        savedAtNotification = readSolverRunState(savedFile());
        const feedback = savedAtNotification.cooperation!.planPublicationRejection!;
        expect(feedback.reason).toBe(rejected().at(-1)!.details!.reason);
        expect(feedback.file).toBe(log(action));
        expectCorrection(message, action, feedback.reason);
        const currentLog = path.join(workers[0].worktree, feedback.file);
        rejectedOffset = fs.statSync(currentLog).size;
        fs.appendFileSync(currentLog, JSON.stringify(event(action, kind)) + '\n');
      });
      await publish(action, invalid(action, kind));
      const reason = rejected().at(-1)!.details!.reason as string;
      const rejection = { nonce: nonce(action), file: log(action), baseVersion: action.planVersion,
        offset: rejectedOffset, reason };
      expect(state.cooperation!.planPublicationRejection).toEqual(rejection);
      expect(state.cooperation!.tasks).toEqual(before!.tasks);
      expect(state.cooperation!.planVersion).toBe(before!.planVersion);
      expect(state.cooperation!.error).toBe(before!.error);
      expect(cooperative.current(action)).toBe(true);
      expect(action).toEqual(originalAction);
      expect(notify).toHaveBeenCalledOnce();
      expectCorrection(notify.mock.calls[0][0], action, reason);
      expect(savedAtNotification!.cooperation!.planPublicationRejection).toEqual(rejection);
      expect(savedAtNotification!.cooperation!.cursors![cursor(action)]).toBe(rejection.offset);
      expect(json().planPublicationRejection).toEqual(rejection);
      expect(json(workers[1]).planPublicationRejection).toBeUndefined();
      expect(cooperative.contextState(undefined, workers[1]).planPublicationRejection).toBeUndefined();
      await cooperative.pulse();
      expect(rejected()).toHaveLength(1);
      expect(state.cooperation!.planPublicationRejection).toBeUndefined();
      expect(json().planPublicationRejection).toBeUndefined();
      if (kind === 'assessment') expect(state.cooperation!.lastCapacityRefill).toMatchObject({ status: 'assessed' });
      else expect(state.cooperation!.planPublication).toMatchObject({ nonce: nonce(action) });
      expect(state.check).toBeUndefined();
      expect(state.cooperation!.tasks.every(node => !node.proof && !node.integratedCheck)).toBe(true);
    });

  it('retries a failed notice without rereading the rejected event or changing its saved cursor', async () => {
    prepare();
    const action = await start();
    notify.mockRejectedValueOnce(new Error('transport unavailable'));
    await publish(action, invalid(action));
    const rejection = structuredClone(state.cooperation!.planPublicationRejection);
    const offset = state.cooperation!.cursors![cursor(action)];
    expect(notify).toHaveBeenCalledOnce();
    await cooperative.pulse();
    expect(notify).toHaveBeenCalledTimes(2);
    expect(state.cooperation!.planPublicationRejection).toEqual(rejection);
    expect(state.cooperation!.cursors![cursor(action)]).toBe(offset);
    expect(rejected()).toHaveLength(1);
    await cooperative.pulse();
    expect(notify).toHaveBeenCalledTimes(2);
    await publish(action, event(action));
    expect(state.cooperation!.planPublicationRejection).toBeUndefined();
  });

  it('accepts the next valid event while a rejection notice is still pending', async () => {
    prepare();
    const action = await start();
    let release!: () => void;
    const held = new Promise<void>(resolve => { release = resolve; });
    notify.mockImplementation(() => held);
    let intakeSettled = false;
    const firstPulse = publish(action, invalid(action)).then(() => { intakeSettled = true; });
    try {
      await vi.waitFor(() => expect(intakeSettled).toBe(true), { timeout: 500 });
      expect(notify).toHaveBeenCalledOnce();
      expect(readSolverRunState(savedFile()).cooperation!.planPublicationRejection).toBeDefined();
      await publish(action, event(action));
      expect(state.cooperation!.planPublication).toMatchObject({ nonce: nonce(action) });
      expect(state.cooperation!.planPublicationRejection).toBeUndefined();
      expect(notify).toHaveBeenCalledOnce();
    } finally { release(); await firstPulse; }
  });

  it.each(['initial', 'replacement'] as const)(
    'retains a rejected %s across JSON restore and supplies the new dispatch in full and short context', async kind => {
      prepare(kind);
      if (kind === 'replacement') fs.writeFileSync(path.join(workers[0].worktree, 'RESEARCH.md'),
        '```math-plan\n' + JSON.stringify({ tasks: completePlan.tasks, groups: completePlan.groups }) +
        '\n```\nThe exact missing construction is still unresolved; preserve this argument while correcting publication.\n');
      const previous = await start();
      await publish(previous, invalid(previous, kind));
      const rejection = structuredClone(state.cooperation!.planPublicationRejection);
      expect(rejection).toBeDefined();
      state = readSolverRunState(savedFile());
      cooperative = create(); await cooperative.restore();
      const action = await start();
      expect(action.planVersion).toBe(previous.planVersion);
      expect(nonce(action)).not.toBe(nonce(previous));
      expect(log(action)).not.toBe(log(previous));
      expect(state.cooperation!.planPublicationRejection).toEqual(rejection);
      expect(json().planPublicationRejection).toEqual(rejection);
      const compiled = context(action);
      expect(compiled.manifest!.included).toContainEqual(expect.objectContaining({ id: 'plan-publication-rejection', required: true }));
      expect(compiled.manifest).toMatchObject({ maxOptionalBytes: 0, optionalBytes: 0 });
      for (const message of [compiled.message, compiled.continuationMessage!]) expectCorrection(message, action, rejection!.reason);
      await publish(action, event(action, kind));
      expect(state.cooperation!.planPublicationRejection).toBeUndefined();
    });

  it.each(['replacement', 'assessment'] as const)(
    'keeps later rejected events audit-only once the %s dispatch has succeeded', async kind => {
      prepare(kind);
      const action = await start();
      await publish(action, invalid(action, kind));
      await publish(action, event(action, kind));
      notify.mockClear();
      const accepted = structuredClone(state.cooperation);
      await publish(action, '{broken JSON');
      await publish(action, { ...event(action, kind), summary: 'An additional event cannot replace this accepted dispatch.' });
      expect(rejected()).toHaveLength(3);
      expect(state.cooperation!.planPublicationRejection).toBeUndefined();
      expect(state.cooperation!.tasks).toEqual(accepted!.tasks);
      expect(state.cooperation!.planPublication).toEqual(accepted!.planPublication);
      expect(state.cooperation!.lastCapacityRefill).toEqual(accepted!.lastCapacityRefill);
      expect(notify).not.toHaveBeenCalled();
    });

  it('clears correction feedback when a human plan supersedes its dispatch and ignores its late event', async () => {
    prepare();
    const action = await start();
    await publish(action, invalid(action));
    const reason = state.cooperation!.planPublicationRejection!.reason;
    notify.mockClear();
    fs.appendFileSync(path.join(directory, 'edits.jsonl'), JSON.stringify({ id: 'human-replacement',
      baseVersion: action.planVersion, tasks: [...completePlan.tasks, { ...helper, id: 'human_bridge', theoremName: 'Tutorial.human_bridge' }],
      groups: completePlan.groups }) + '\n');
    await publish(action, event(action));
    expect(state.cooperation!.edits).toMatchObject([{ status: 'applied' }]);
    expect(cooperative.current(action)).toBe(false);
    expect(state.cooperation!.planPublicationRejection).toBeUndefined();
    expect(json().planPublicationRejection).toBeUndefined();
    expect(state.cooperation!.tasks.some(node => node.task.id === 'human_bridge')).toBe(true);
    expect(state.cooperation!.tasks.some(node => node.task.id === helper.id)).toBe(false);
    expect(notify.mock.calls.every(([message]) => !message.includes(reason))).toBe(true);
  });

  it('corrects a checkpoint through its notice after the same active Lead has already published an initial plan', async () => {
    prepare('initial');
    const action = await start();
    await publish(action, event(action, 'initial'));
    const accepted = structuredClone({ tasks: state.cooperation!.tasks, planVersion: state.cooperation!.planVersion,
      publication: state.cooperation!.planPublication });
    expect(cooperative.current(action)).toBe(true);
    const research = requestCheckpoint(), requestId = research.contextCheckpoint!.requestId!;
    let savedAtNotification: SolverRunState | undefined;
    notify.mockImplementation(async message => {
      savedAtNotification = readSolverRunState(savedFile());
      const feedback = savedAtNotification.workers![0].contextCheckpoint!.rejection!;
      expectCheckpointCorrection(message, action, requestId, feedback.reason);
      expect(savedAtNotification.cooperation!.cursors![cursor(action)]).toBe(feedback.offset);
      fs.appendFileSync(path.join(workers[0].worktree, feedback.file), JSON.stringify(checkpoint(requestId, true)) + '\n');
    });
    await publish(action, checkpoint(requestId));
    const rejection = cooperative.contextState(action, workers[0]).contextCheckpointRejection;
    expect(rejection).toMatchObject({ threadId: research.threadId, requestId, file: log(action), reason: 'math_delivery_invalid' });
    expect(state.cooperation!.planPublicationRejection).toBeUndefined();
    expect(notify).toHaveBeenCalledOnce();
    expect(savedAtNotification!.workers![0].contextCheckpoint!.rejection).toEqual({
      file: rejection!.file, offset: rejection!.offset, reason: rejection!.reason });
    expect(json().contextCheckpointRejection).toEqual(rejection);
    await cooperative.pulse();
    expect(research.contextCheckpoint).toMatchObject({ publishedNotesDigest: checkpoint(requestId, true).notesDigest });
    expect(research.contextCheckpoint!.rejection).toBeUndefined();
    expect(cooperative.contextState(action, workers[0]).contextCheckpointRejection).toBeUndefined();
    expect(json().contextCheckpointRejection).toBeUndefined();
    expect({ tasks: state.cooperation!.tasks, planVersion: state.cooperation!.planVersion,
      publication: state.cooperation!.planPublication }).toEqual(accepted);
    expect(state.check).toBeUndefined();
    expect(state.cooperation!.tasks.every(node => !node.proof && !node.integratedCheck)).toBe(true);
  });

  it('keeps plan and checkpoint corrections independent in live feedback and both context forms', async () => {
    prepare();
    const action = await start();
    await publish(action, invalid(action));
    const planRejection = structuredClone(state.cooperation!.planPublicationRejection);
    expect(planRejection).toBeDefined();
    const research = requestCheckpoint(), requestId = research.contextCheckpoint!.requestId!;
    notify.mockClear();
    await publish(action, checkpoint(requestId));
    const rejection = cooperative.contextState(action, workers[0]).contextCheckpointRejection;
    expect(rejection).toMatchObject({ threadId: research.threadId, requestId, file: log(action), reason: 'math_delivery_invalid' });
    expect(state.cooperation!.planPublicationRejection).toEqual(planRejection);
    expect(notify).toHaveBeenCalledOnce();
    expectCheckpointCorrection(notify.mock.calls[0][0], action, requestId, rejection!.reason);
    expect(json().contextCheckpointRejection).toEqual(rejection);
    expect(json(workers[1]).contextCheckpointRejection).toBeUndefined();
    expect(cooperative.contextState(undefined, workers[1]).contextCheckpointRejection).toBeUndefined();
    const compiled = context(action);
    for (const id of ['plan-publication-rejection', 'context-checkpoint-rejection'])
      expect(compiled.manifest!.included).toContainEqual(expect.objectContaining({ id, required: true }));
    for (const message of [compiled.message, compiled.continuationMessage!]) {
      for (const detail of [requestId, rejection!.reason, log(action), 'notesDigest', '"kind":"checkpoint"', planRejection!.reason])
        expect(message).toContain(detail);
    }
    await publish(action, checkpoint(requestId, true));
    expect(research.contextCheckpoint).toMatchObject({ publishedNotesDigest: checkpoint(requestId, true).notesDigest });
    expect(research.contextCheckpoint!.rejection).toBeUndefined();
    expect(cooperative.contextState(action, workers[0]).contextCheckpointRejection).toBeUndefined();
    expect(state.cooperation!.planPublicationRejection).toEqual(planRejection);
    expect(context(action).manifest!.included).not.toContainEqual(expect.objectContaining({ id: 'context-checkpoint-rejection' }));
    await publish(action, event(action));
    expect(state.cooperation!.planPublicationRejection).toBeUndefined();
  });

  it('stops exposing or retrying checkpoint diagnostics when its request or thread is replaced', async () => {
    prepare();
    const action = await start(), research = requestCheckpoint();
    for (const next of [{ threadId: research.threadId!, requestId: 'next-checkpoint-request' },
      { threadId: 'next-checkpoint-thread', requestId: 'next-checkpoint-request' }]) {
      notify.mockRejectedValueOnce(new Error('transport unavailable'));
      await publish(action, checkpoint(research.contextCheckpoint!.requestId!));
      expect(cooperative.contextState(action, workers[0]).contextCheckpointRejection).toMatchObject({ threadId: research.threadId,
        requestId: research.contextCheckpoint!.requestId, file: log(action) });
      notify.mockClear();
      research.threadId = next.threadId;
      research.contextCheckpoint = { ...next, requestedAt: 2 };
      cooperative.activate(workers[0], action, async () => {}, notify);
      await cooperative.pulse();
      expect(notify).not.toHaveBeenCalled();
      expect(cooperative.contextState(action, workers[0]).contextCheckpointRejection).toBeUndefined();
      expect(json().contextCheckpointRejection).toBeUndefined();
      const compiled = context(action);
      expect(compiled.manifest!.included).not.toContainEqual(expect.objectContaining({ id: 'context-checkpoint-rejection' }));
      expect(compiled.continuationMessage).not.toContain('math_delivery_invalid');
      expect(state.cooperation!.planPublicationRejection).toBeUndefined();
    }
  });
});
