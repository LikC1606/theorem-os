import fs from 'node:fs';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { readSolverRunState, writeSolverRunState, type SolverRunState } from '../src/solver/archive';
import type { CooperativeResearch } from '../src/solver/cooperation';
import { parseCooperationPlan } from '../src/solver/tasks';
import { assignmentDeliveryFile, type CooperativeAction } from '../src/solver/tasks';
import { commitSolverSources, git, type SolverProblem } from '../src/solver/problem';
import type { ResearchWorker } from '../src/solver/modules/organization';
import { proofReadyRecordSchema } from '../src/solver/proofReady';
import { cooperativeResearch } from './helpers/cooperation';
import { leadWorker, localExample, peerWorker, solverState } from './helpers/solver';
import { verifiedBatch } from './helpers/verifier';
import { deferred } from './helpers/async';

const host = vi.hoisted(() => ({ verify: vi.fn() }));
vi.mock('../src/math/verifier', async importOriginal => ({
  ...await importOriginal<typeof import('../src/math/verifier')>(), checkManyFormalVerifications: host.verify,
  formalVerificationToolIdentity: () => 'ready-intake-fixture', resolveMathematicsLakePackagesCache: () => undefined,
}));
type TaskAction = Extract<CooperativeAction, { kind: 'task' }>;

describe('host-owned proof readiness intake', () => {
  let directory: string, problem: SolverProblem, state: SolverRunState, workers: ResearchWorker[];
  let cooperative: CooperativeResearch, action: TaskAction, callback: ReturnType<typeof vi.fn>;
  let instances: { cooperative: CooperativeResearch; controller: AbortController }[], saves: SolverRunState[];
  let events: { event: string; details?: Record<string, unknown> }[];
  const create = () => {
    const controller = new AbortController();
    const value = cooperativeResearch({ state, workers, retrievalRoot: directory, signal: controller.signal,
      save: () => saves.push(structuredClone(state)), emit: (event, details) => events.push({ event, details }) });
    instances.push({ cooperative: value, controller }); return value;
  };
  const source = () => path.join(workers[1].worktree, problem.projectRelative, 'Submission.lean');
  const append = (value: unknown = { kind: 'ready' }) => fs.appendFileSync(
    path.join(workers[1].worktree, assignmentDeliveryFile(action.assignment)), JSON.stringify(value) + '\n');
  const activate = () => cooperative.activate(workers[1], action, async () => {}, async () => {}, callback);
  const reload = () => {
    const file = path.join(directory, 'ready-state.json'); writeSolverRunState(file, state);
    state = readSolverRunState(file); cooperative = create();
    const node = state.cooperation!.tasks.find(node => node.task.id === 'helper')!;
    action = { kind: 'task', task: node.task, assignment: node.assignment! }; activate();
  };
  const saveHelper = () => {
    fs.writeFileSync(source(), fs.readFileSync(source(), 'utf8').replace('end Tutorial',
      'lemma helper : True := by trivial\nend Tutorial'));
    return commitSolverSources(problem, workers[1].worktree);
  };

  beforeEach(async () => {
    const example = localExample('proof-ready-intake-', 'lead');
    ({ directory, problem } = example);
    workers = [leadWorker(problem, example.workspace, 'lead'), peerWorker(example, 'writer')];
    const plan = parseCooperationPlan(problem, { tasks: [
      ...problem.targets.map((target, index) => ({ id: `goal_${index}`, kind: 'goal', objective: 'Original target',
        theoremName: target.theoremName, proofPath: target.proofPath, status: 'paused' })),
      { id: 'helper', kind: 'lemma', type: 'True', theoremName: 'Tutorial.helper', proofPath: 'Submission.lean',
        objective: 'Prove the helper', ownerId: 'writer' },
    ] });
    state = solverState(problem, example.workspace, { runId: 'ready-intake', phase: 'running', failures: [],
      cooperation: { canonicalCommit: problem.baseCommit, tasks: plan.tasks.map(task => ({ task, status: 'pending', attempts: 0 })),
        groups: plan.groups.map(group => ({ group, turns: 0 })) } });
    instances = []; saves = []; events = []; callback = vi.fn(async () => {});
    host.verify.mockReset().mockImplementation(async request => verifiedBatch(request, { sessionId: 'ready-intake' }));
    cooperative = create();
    state.cooperation!.planVersion = (cooperative as any).planVersion();
    const assigned = await cooperative.next(workers[1], { maxTurns: Infinity, remainingMs: Infinity });
    if (assigned?.kind !== 'task') throw new Error('fixture_missing_assignment');
    action = assigned; expect(cooperative.started(workers[1], action)).toBe(true); activate();
  });
  afterEach(async () => {
    for (const instance of instances) { instance.controller.abort(); await instance.cooperative.stop(); }
    vi.restoreAllMocks(); fs.rmSync(directory, { recursive: true, force: true });
  });

  it('records ready before requesting turn settlement without reading or committing active sources', async () => {
    const head = git(workers[1].worktree, ['rev-parse', 'HEAD']), waiting = deferred();
    callback.mockImplementation(() => waiting.promise);
    fs.appendFileSync(source(), '\n-- still writer-owned\n');
    const read = vi.spyOn(fs, 'readFileSync');
    append(); await cooperative.pulse(workers[1].id);
    expect(callback).toHaveBeenCalledOnce();
    expect(read.mock.calls.some(([file]) => file === source())).toBe(false);
    expect(git(workers[1].worktree, ['rev-parse', 'HEAD'])).toBe(head);
    expect(host.verify).not.toHaveBeenCalled();
    expect(saves.some(save => save.cooperation?.proofReadyRecords?.[0]?.status === 'awaiting-freeze')).toBe(true);
    expect(cooperative.pendingProofReady(workers[1], action)).toMatchObject({ status: 'awaiting-freeze' });
    waiting.resolve();
  });

  it('freezes and checks one immutable snapshot and never rechecks duplicate completed ready events', async () => {
    expect(events.find(item => item.event === 'task_assigned')?.details).toMatchObject({
      taskId: action.task.id, taskDigest: action.assignment.taskDigest,
      assignmentKey: assignmentDeliveryFile(action.assignment), planVersion: state.cooperation!.planVersion,
    });
    append(); await cooperative.pulse(workers[1].id);
    const commit = saveHelper();
    expect(cooperative.proofReadyFrozen(workers[1], action, commit)).toMatchObject({ status: 'frozen', snapshotCommit: commit });
    expect(cooperative.proofReadyFrozen(workers[1], action, commit)?.snapshotCommit).toBe(commit);
    const delivered = await cooperative.deliver(workers[1], action, commit);
    cooperative.proofReadyCompleted(workers[1], action, delivered.check);
    expect(state.cooperation!.proofReadyRecords).toMatchObject([{ status: 'checked', evidence: 'unconditional',
      snapshotCommit: commit, conditions: [], receiptIds: [expect.any(String)] }]);
    const calls = host.verify.mock.calls.length;
    append(); await cooperative.pulse(workers[1].id);
    expect(host.verify).toHaveBeenCalledTimes(calls); expect(callback).toHaveBeenCalledOnce();
    expect(cooperative.pendingProofReady(workers[1], action)).toBeUndefined();
  });

  it('requires a newly consumed ready event before freezing an unfrozen request after restart', async () => {
    append(); await cooperative.pulse(workers[1].id); reload();
    expect(cooperative.pendingProofReady(workers[1], action)).toBeUndefined();
    const before = callback.mock.calls.length;
    append(); await cooperative.pulse(workers[1].id);
    expect(callback).toHaveBeenCalledTimes(before + 1);
    expect(cooperative.pendingProofReady(workers[1], action)).toMatchObject({ status: 'awaiting-freeze' });
    expect(state.cooperation!.proofReadyRecords).toHaveLength(1);
  });

  it('records conditional Lean receipts without accepting the original goal or retaining the Engineer', async () => {
    const tasks = state.cooperation!.tasks.map(({ task }) => task.id === 'helper'
      ? { ...task, conditional: true, dependsOn: ['input'] } : task);
    tasks.push({ id: 'input', kind: 'lemma', type: 'True', theoremName: 'Tutorial.input',
      proofPath: 'Submission.lean', objective: 'An unfinished input' });
    await (cooperative as any).acceptPlan(parseCooperationPlan(problem, { tasks }));
    cooperative.deactivate(workers[1]);
    const assigned = await cooperative.next(workers[1], { maxTurns: Infinity, remainingMs: Infinity });
    if (assigned?.kind !== 'task' || assigned.task.id !== 'helper') throw new Error('fixture_missing_conditional_assignment');
    action = assigned; expect(cooperative.started(workers[1], action)).toBe(true); activate();
    fs.writeFileSync(source(), fs.readFileSync(source(), 'utf8').replace('end Tutorial',
      'lemma helper : True := by exact Tutorial.input\nend Tutorial'));
    append(); await cooperative.pulse(workers[1].id);
    const commit = commitSolverSources(problem, workers[1].worktree);
    cooperative.proofReadyFrozen(workers[1], action, commit);
    const delivered = await cooperative.deliver(workers[1], action, commit);
    cooperative.proofReadyCompleted(workers[1], action, delivered.check);
    cooperative.deactivate(workers[1]);
    expect(state.cooperation!.proofReadyRecords).toMatchObject([{ status: 'checked', evidence: 'conditional',
      snapshotCommit: commit, conditions: [{ taskId: 'input', taskDigest: expect.any(String) }],
      receiptIds: [expect.any(String)] }]);
    expect(state.cooperation!.tasks.find(node => node.task.id === 'helper')).toMatchObject({ status: 'conditional' });
    expect(state.cooperation!.tasks.find(node => node.task.id === 'goal_0')!.integratedCheck).toBeUndefined();
    expect(state.cooperation!.tasks.some(node => node.status === 'running' && node.assignment?.workerId === workers[1].id)).toBe(false);
  });

  it('restores a fixed snapshot independently of later live edits and refuses to replace its commit', async () => {
    append(); await cooperative.pulse(workers[1].id); const commit = saveHelper();
    const frozen = cooperative.proofReadyFrozen(workers[1], action, commit)!;
    expect(frozen.frozenAt).toEqual(expect.any(Number));
    const frozenAt = frozen.frozenAt;
    reload();
    fs.appendFileSync(source(), '\n-- a later live edit\n');
    const now = vi.spyOn(Date, 'now').mockReturnValue(frozenAt! + 1000);
    expect(cooperative.proofReadyFrozen(workers[1], action, commit)).toMatchObject({
      status: 'frozen', snapshotCommit: commit, frozenAt });
    now.mockRestore();
    expect(events.filter(item => item.event === 'proof_ready_frozen')).toEqual([{ event: 'proof_ready_frozen', details: {
      readyId: frozen.id, taskId: action.task.id, taskDigest: action.assignment.taskDigest, workerId: workers[1].id,
      assignmentKey: assignmentDeliveryFile(action.assignment), seedCommit: action.assignment.seedCommit,
      commit, snapshotCommit: commit, sourceDigest: frozen.sourceDigest, frozenAt,
    } }]);
    expect(() => cooperative.proofReadyFrozen(workers[1], action, problem.baseCommit)).toThrow('math_proof_ready_snapshot_changed');
    expect(host.verify).not.toHaveBeenCalled();
  });

  it('supersedes readiness when the environment or task identity changes', async () => {
    append(); await cooperative.pulse(workers[1].id); state.environmentDigest = 'new-environment';
    expect(cooperative.pendingProofReady(workers[1], action)).toBeUndefined();
    expect(state.cooperation!.proofReadyRecords![0].status).toBe('superseded');
    expect(host.verify).not.toHaveBeenCalled();
  });

  it('preserves a failed freeze and requires a new submission to retry', async () => {
    append(); await cooperative.pulse(workers[1].id);
    cooperative.proofReadyFailedFreeze(workers[1], action, 'process-exit-unconfirmed');
    append(); await cooperative.pulse(workers[1].id);
    expect(callback).toHaveBeenCalledOnce(); expect(cooperative.pendingProofReady(workers[1], action)).toBeUndefined();
    append({ kind: 'ready', id: 'retry-after-stop-confirmed' }); await cooperative.pulse(workers[1].id);
    expect(callback).toHaveBeenCalledTimes(2);
    expect(state.cooperation!.proofReadyRecords).toMatchObject([{ status: 'failed' }, { status: 'awaiting-freeze' }]);
  });

  it('rejects caller-provided commits and target lists without granting freeze permission', async () => {
    append({ kind: 'ready', commit: problem.baseCommit }); append({ kind: 'ready', targets: ['other'] });
    await cooperative.pulse(workers[1].id);
    expect(state.cooperation!.deliveryReceipts).toHaveLength(2);
    expect(state.cooperation!.proofReadyRecords ?? []).toEqual([]); expect(callback).not.toHaveBeenCalled();
  });

  it('rejects malformed checked archives without a fixed snapshot and Lean receipts', () => {
    expect(proofReadyRecordSchema.safeParse({ status: 'checked', evidence: 'unconditional' }).success).toBe(false);
  });
});
