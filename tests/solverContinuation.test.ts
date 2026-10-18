import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { continuationResearchTasks, readyResearchTasks, researchCanAdvance } from '../src/solver/modules/search';
import { assignSharedResearchTask, type ResearchWorker } from '../src/solver/modules/organization';
import { taskVersion, parseCooperationPlan, markTaskAcceptance, type CooperativeAction, type TaskRecord, type RouteRecord } from '../src/solver/tasks';
import { CooperativeResearch, type CooperationState } from '../src/solver/cooperation';
import { directSolverModules } from '../src/solver/modules';
import { git, type SolverProblem } from '../src/solver/problem';
import type { SolverRunState } from '../src/solver/archive';
import { readMathResponse } from '../src/solver/deliveries';
import { recordRouteBlockers, refreshRouteBlockers } from '../src/solver/routeControl';
import { ownedSourceDigest, type TaskProof } from '../src/solver/cooperativeProof';

const node = (id: string, kind: TaskRecord['task']['kind'] = 'lemma', dependsOn: string[] = []): TaskRecord => ({
  task: { id, kind, objective: id, dependsOn, revision: 0,
    ...(['lemma', 'goal'].includes(kind) ? { proofPath: 'Submission.lean', theoremName: id, type: 'True' } : {}) },
  status: 'pending', attempts: 0,
});
const integrated = (record: TaskRecord): TaskRecord => {
  record.status = 'integrated';
  record.integratedCheck = { passed: true, taskDigest: taskVersion(record.task), conditions: [],
    verification: { status: 'kernel_verified', targetCommit: 'checked-source', results: [
      { status: 'kernel_verified', targetCommit: 'checked-source', receiptId: 'fixture-receipt' },
    ] } } as TaskRecord['integratedCheck'];
  return record;
};
const main: RouteRecord = { group: { id: 'main', objective: 'Original problem', status: 'active', revision: 0 }, turns: 0 };

describe('proof continuation scheduling', () => {
  it('advances a consumer of checked helpers before untouched core gaps and disconnected work', () => {
    const tasks = [node('explore', 'research'), node('core'), integrated(node('checked')),
      node('bridge', 'lemma', ['checked']), node('middle', 'lemma', ['core']), node('goal', 'goal', ['bridge', 'middle'])];
    expect(continuationResearchTasks(tasks).map(record => record.task.id)).toEqual(['bridge', 'core', 'explore']);
    expect(readyResearchTasks(tasks).map(record => record.task.id)).toEqual(['explore', 'core', 'bridge']);
    tasks.find(record => record.task.id === 'checked')!.integratedCheck!.taskDigest = 'obsolete';
    expect(continuationResearchTasks(tasks).map(record => record.task.id)).toEqual(['core', 'bridge', 'explore']);
  });

  it('prefers a ready original target and never counts conditional premises as proved', () => {
    const checked = integrated(node('checked')), open = node('open');
    const consumer = node('consumer', 'lemma', ['checked']), goal = node('ready-goal', 'goal', ['checked']);
    const conditional = node('conditional-goal', 'goal', ['open']); conditional.task = { ...conditional.task, conditional: true };
    const tasks = [open, checked, consumer, node('later-goal', 'goal', ['consumer']), conditional, goal];
    expect(continuationResearchTasks(tasks).map(record => record.task.id)).toEqual([
      'ready-goal', 'consumer', 'open', 'conditional-goal',
    ]);
    expect(open.status).toBe('pending');
    expect(conditional.integratedCheck).toBeUndefined();
  });

  it('offers a spare proof slot to a different route and keeps owner and group pins', () => {
    const running = [node('working-a'), node('working-b')]; running.forEach(record => record.status = 'running');
    const tried = node('tried', 'research'); tried.attempts = 5;
    const fresh = node('fresh', 'research'); fresh.task = { ...fresh.task, ownerId: 'researcher' };
    const core = node('core'), goal = node('goal', 'goal', [...running.map(record => record.task.id), 'core']);
    const tasks = [tried, core, ...running, fresh, goal];
    const ready = continuationResearchTasks(tasks, [main]);
    expect(ready.map(record => record.task.id)).toEqual(['fresh', 'core', 'tried']);
    const engineer: ResearchWorker = { id: 'engineer', role: 'engineer', worktree: '/engineer', ownedFiles: [] };
    const researcher: ResearchWorker = { ...engineer, id: 'researcher', role: 'researcher' };
    expect(assignSharedResearchTask(ready, engineer, [engineer, researcher], [main])).toBe(core);
    expect(assignSharedResearchTask(ready, researcher, [engineer, researcher], [main])).toBe(fresh);
    fresh.status = 'running';
    expect(continuationResearchTasks(tasks, [main])).toEqual([]);
    expect(continuationResearchTasks(tasks).map(record => record.task.id)).toEqual(['core', 'tried']);
    core.task = { ...core.task, ownerId: 'researcher' };
    core.assignment = { taskId: 'core', taskDigest: taskVersion(core.task), workerId: 'researcher', seedCommit: 'seed' };
    expect(assignSharedResearchTask(continuationResearchTasks(tasks), engineer, [engineer, researcher], [main])).toBe(tried);
  });

  it('preserves dependency, pause, spent route and concurrency gates', () => {
    const tasks = [node('core'), node('blocked', 'goal', ['core']), node('paused'), node('full'), node('spent')];
    tasks[2].task = { ...tasks[2].task, status: 'paused' };
    tasks[3].task = { ...tasks[3].task, groupId: 'full' }; tasks[4].task = { ...tasks[4].task, groupId: 'spent' };
    const groups: RouteRecord[] = [main,
      { group: { ...main.group, id: 'full', maxConcurrent: 1 }, turns: 0, busy: 1 },
      { group: { ...main.group, id: 'spent', maxTurns: 1 }, turns: 1 }];
    expect(continuationResearchTasks(tasks, groups).map(record => record.task.id)).toEqual(['core']);
  });
});

describe('unchanged research delivery recovery and budget wakeup', () => {
  let directory: string, seed: string, cooperative: CooperativeResearch, state: SolverRunState, record: TaskRecord;
  let lead: ResearchWorker, researcher: ResearchWorker, action: Extract<CooperativeAction, { kind: 'task' }>;
  let allowed: boolean;
  const signal = () => new AbortController().signal;
  const checkpoint = (notes: string) => {
    fs.writeFileSync(path.join(directory, 'RESEARCH.md'), notes);
    git(directory, ['add', '--', 'RESEARCH.md']);
    git(directory, ['-c', 'user.name=Fixture', '-c', 'user.email=fixture@localhost', 'commit', '--no-gpg-sign', '--quiet', '--allow-empty', '-m', 'Research checkpoint']);
    return git(directory, ['rev-parse', 'HEAD']);
  };
  beforeEach(() => {
    directory = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'continuation-test-')));
    fs.mkdirSync(path.join(directory, 'generated/p'), { recursive: true });
    fs.writeFileSync(path.join(directory, 'generated/p/Submission.lean'), 'theorem goal : True := by sorry\n');
    git(directory, ['init', '--quiet']); git(directory, ['add', '--', 'generated']);
    seed = checkpoint('Inherited research notes.');
    record = node('question', 'research'); record.status = 'running';
    record.assignment = { taskId: record.task.id, taskDigest: taskVersion(record.task), workerId: 'researcher', seedCommit: seed };
    lead = { id: 'solver', role: 'lead', worktree: directory, ownedFiles: ['Submission.lean'] };
    researcher = { ...lead, id: 'researcher', role: 'researcher' };
    const cooperation: CooperationState = { canonicalCommit: seed, tasks: [record, node('goal', 'goal', ['question'])],
      groups: [{ ...main, group: { ...main.group } }] };
    state = { runId: 'continuation-fixture', turns: 0, environmentDigest: 'fixture', cooperation,
      problem: { projectRelative: 'generated/p', ownedFiles: ['Submission.lean'], declarations: {}, targets: [],
        trustedFiles: {}, baseCommit: seed, sourceStructure: {}, sourceImports: {},
        contract: { assumptions: [], formalStatement: 'Prove the original goal.' } } as unknown as SolverProblem } as SolverRunState;
    allowed = true;
    cooperative = new CooperativeResearch({ state, workers: [lead, researcher], access: new Map(), signal: signal(),
      modelDispatchAllowed: () => allowed, save: () => {}, emit: () => {}, modules: directSolverModules, exclusiveCheck: async check => check() });
    action = { kind: 'task', task: record.task, assignment: record.assignment };
  });
  afterEach(async () => { await cooperative.stop(); vi.restoreAllMocks(); fs.rmSync(directory, { recursive: true, force: true }); });

  const parkCore = () => {
    const core = node('core'); core.status = 'blocked'; core.feedback = 'The required analytic estimate is still absent.';
    record.status = 'completed'; record.finding = 'The existing half-plane estimate does not reach the critical line.';
    const tasks = [core, record, node('goal', 'goal', ['core'])];
    const blockers = state.cooperation!.blockers = [];
    const proposal = { mechanism: 'missing cancellation estimate', scope: 'critical-line inference',
      reopenOn: [{ kind: 'contract-changed' as const }] };
    recordRouteBlockers(blockers, [proposal], core.task, tasks, 'fixture', 'problem');
    recordRouteBlockers(blockers, [proposal], core.task, tasks, 'fixture', 'problem');
    refreshRouteBlockers(blockers, tasks, 'fixture', 'problem');
    state.cooperation!.tasks = tasks;
    state.problem.receiptDigest = 'problem';
    state.cooperation!.planVersion = (cooperative as any).planVersion();
    vi.spyOn(cooperative as any, 'seed').mockReturnValue(seed);
    vi.spyOn(cooperative as any, 'acceptPlan').mockResolvedValue(undefined);
    return core;
  };
  const assessFrontier = async () => {
    const action = await cooperative.next(lead, { maxTurns: Infinity, remainingMs: Infinity });
    expect(action).toMatchObject({ kind: 'lead' });
    if (action?.kind !== 'lead') throw new Error('expected_frontier_assessment');
    await cooperative.deliver(lead, action, action.seedCommit);
    return action;
  };

  it('reconsiders a parked original-goal frontier once after later advisory findings without unblocking its proof', async () => {
    const core = parkCore(), budget = { maxTurns: Infinity, remainingMs: Infinity };
    state.cooperation!.lastLeadInputDigest = (cooperative as any).planningInputDigest();
    record.finding = 'A new paper reduces the original gap to a precise localized moment estimate.';
    const emit = vi.fn(); (cooperative as any).input.emit = emit;
    await assessFrontier();
    expect(await cooperative.next(lead, budget)).toBeUndefined();
    expect(emit).toHaveBeenCalledWith('blocked_tasks_reconsidered', expect.objectContaining({ taskIds: ['core'], goalIds: ['goal'] }));
    expect(emit).toHaveBeenCalledWith('routes_idle', expect.objectContaining({ reason: 'unchanged-mathematical-input',
      frontier: [expect.objectContaining({ taskId: 'core', parkedBy: core.routeParking })] }));
    expect(core.status).toBe('blocked'); expect(core.routeParking).toHaveLength(1);
  });

  it('dispatches an imported unresolved frontier after one Lead assessment, then preserves a real failed attempt across restore', async () => {
    const core = parkCore(), budget = { maxTurns: Infinity, remainingMs: Infinity };
    state.cooperation!.blockers = []; core.routeParking = [];
    core.feedback = 'Historical unresolved checkpoint; needs current evidence.';
    const emit = vi.fn(); (cooperative as any).input.emit = emit;
    await assessFrontier();
    const waitingLead = cooperative.next(lead, budget);
    expect(core.status).toBe('pending');
    expect(core.feedback).toContain('Historical unresolved checkpoint');
    expect(emit).toHaveBeenCalledWith('unattempted_frontier_resumed', { taskIds: ['core'], goalIds: ['goal'] });
    const work = await cooperative.next(researcher, budget);
    expect(work).toMatchObject({ kind: 'task', task: { id: 'core' } });
    if (work?.kind !== 'task') throw new Error('expected_imported_frontier_work');
    expect(cooperative.started(researcher, work)).toBe(true);
    expect(core.attempts).toBe(1);
    cooperative.rejected(work, 'The current candidate still lacks the needed estimate.', seed);
    const reassessment = await waitingLead;
    expect(reassessment).toMatchObject({ kind: 'lead' });
    if (reassessment?.kind !== 'lead') throw new Error('expected_failed_frontier_assessment');
    await cooperative.deliver(lead, reassessment, seed);
    const recovery = await cooperative.next(lead, budget);
    expect(recovery).toMatchObject({ kind: 'lead', recovery: { taskIds: ['core'] } });
    if (recovery?.kind !== 'lead') throw new Error('expected_targeted_recovery');
    state.problem.targets = [{ proofPath: 'Submission.lean', theoremName: 'goal' }];
    const waiting = checkpoint('```math-plan\n' + JSON.stringify({
      tasks: state.cooperation!.tasks.map(node => node.task), groups: state.cooperation!.groups!.map(route => route.group),
      recovery: { status: 'awaiting-input', reason: 'A new cancellation estimate is required.' },
    }) + '\n```');
    await cooperative.deliver(lead, recovery, waiting);
    expect(await cooperative.next(lead, budget)).toBeUndefined();
    expect(core.status).toBe('blocked'); expect(core.integratedCheck).toBeUndefined();
    const resumed = new CooperativeResearch({ state: JSON.parse(JSON.stringify(state)), workers: [lead, researcher],
      access: new Map(), signal: signal(), save: () => {}, emit: () => {}, modules: directSolverModules,
      exclusiveCheck: async check => check() });
    vi.spyOn(resumed as any, 'seed').mockReturnValue(seed);
    try { expect(await resumed.next(lead, budget)).toBeUndefined(); }
    finally { await resumed.stop(); }
  });

  it.each(['assigned', 'proof-retained', 'archived-parking', 'owner-unavailable', 'M5-declines'])(
    'keeps an unchanged unresolved frontier idle when %s', async control => {
      const core = parkCore(), budget = { maxTurns: Infinity, remainingMs: Infinity };
      state.cooperation!.blockers = []; core.routeParking = [];
      if (control === 'assigned') core.assignment = { ...action.assignment, taskId: 'core', taskDigest: taskVersion(core.task) };
      else if (control === 'proof-retained') core.proof = { passed: false, taskDigest: taskVersion(core.task),
        verification: { status: 'failed', results: [] } } as unknown as TaskProof;
      else if (control === 'archived-parking') {
        const blockers = state.cooperation!.blockers;
        const proposal = { mechanism: 'recurring gap', scope: 'core inference' };
        recordRouteBlockers(blockers, [proposal], core.task, state.cooperation!.tasks, 'fixture', 'problem');
        recordRouteBlockers(blockers, [proposal], core.task, state.cooperation!.tasks, 'fixture', 'problem');
        expect(blockers[0].status).toBe('parked'); expect(core.routeParking).toEqual([]);
      } else if (control === 'owner-unavailable') core.task = { ...core.task, ownerId: 'stopped-researcher' };
      else (cooperative as any).input.modules = { ...directSolverModules,
        M5: { ...directSolverModules.M5, assign: () => undefined } };
      state.cooperation!.lastLeadInputDigest = (cooperative as any).planningInputDigest();
      expect(await cooperative.next(lead, budget)).toBeUndefined();
      expect(core.status).toBe('blocked'); expect(core.attempts).toBe(0);
    });

  const prepareRecovery = () => {
    const core = parkCore();
    vi.mocked((cooperative as any).acceptPlan).mockRestore();
    state.cooperation!.blockers = []; core.routeParking = []; core.attempts = 2;
    core.feedback = 'math_task_missing_declaration\nThe required compact seed declaration was absent twice.';
    state.problem.targets = [{ proofPath: 'Submission.lean', theoremName: 'goal' }];
    const plan = parseCooperationPlan(state.problem, { tasks: state.cooperation!.tasks.map(node => node.task),
      groups: state.cooperation!.groups!.map(route => route.group) });
    for (const node of state.cooperation!.tasks) node.task = plan.tasks.find(task => task.id === node.task.id)!;
    state.cooperation!.planVersion = (cooperative as any).planVersion();
    state.cooperation!.lastLeadInputDigest = (cooperative as any).planningInputDigest();
    return core;
  };
  const recoveryPlan = (recovery: unknown, tasks = state.cooperation!.tasks.map(node => node.task), extra = {}) => checkpoint(
    '```math-plan\n' + JSON.stringify({ tasks, groups: state.cooperation!.groups!.map(route => route.group), recovery, ...extra }) + '\n```');
  const getRecovery = async () => {
    const next = await cooperative.next(lead, { maxTurns: Infinity, remainingMs: Infinity });
    expect(next).toMatchObject({ kind: 'lead', recovery: { taskIds: ['core'] } });
    if (next?.kind !== 'lead' || !next.recovery) throw new Error('expected_targeted_recovery');
    return next;
  };

  it('wakes a blocked unattempted prerequisite of explicitly pending supporting work outside the goal cone', async () => {
    parkCore();
    const prerequisite = node('supporting_compactness'); prerequisite.status = 'blocked';
    state.cooperation!.tasks.push(prerequisite, node('ambient_extension', 'lemma', ['supporting_compactness']));
    state.cooperation!.planVersion = (cooperative as any).planVersion();
    state.cooperation!.lastLeadInputDigest = (cooperative as any).planningInputDigest();
    const leadNext = cooperative.next(lead, { maxTurns: Infinity, remainingMs: Infinity });
    await vi.waitFor(() => expect(prerequisite.status).toBe('pending'));
    const work = await cooperative.next(researcher, { maxTurns: Infinity, remainingMs: Infinity });
    expect(work).toMatchObject({ kind: 'task', task: { id: 'supporting_compactness' } });
    if (work?.kind !== 'task') throw new Error('expected_supporting_prerequisite');
    expect(cooperative.started(researcher, work)).toBe(true);
    allowed = false;
    cooperative.rejected(work, 'A concrete unresolved supporting premise remains.', seed);
    expect(await leadNext).toBeUndefined();
  });

  it('accepts a typed decomposition and dispatches its fresh premise before retrying the failed core', async () => {
    prepareRecovery();
    const next = await getRecovery();
    const premise = node('compactness_premise'); premise.task = { ...premise.task, type: 'Nat.succ 0 = 1' };
    const tasks = state.cooperation!.tasks.map(node => node.task.id === 'core' ?
      { ...node.task, dependsOn: ['compactness_premise'] } : node.task);
    tasks.push(premise.task);
    await cooperative.deliver(lead, next, recoveryPlan({ status: 'planned', taskIds: ['compactness_premise'] }, tasks));
    expect(state.cooperation!.frontierRecoveries).toEqual([expect.objectContaining({ status: 'planned', readyTaskIds: ['compactness_premise'] })]);
    const work = await cooperative.next(researcher, { maxTurns: Infinity, remainingMs: Infinity });
    expect(work).toMatchObject({ kind: 'task', task: { id: 'compactness_premise' } });
    expect(readyResearchTasks(state.cooperation!.tasks).some(node => node.task.id === 'core')).toBe(false);
    expect(state.cooperation!.tasks.find(node => node.task.id === 'goal')!.integratedCheck).toBeUndefined();
  });

  it('dispatches an independent advisory investigation of the failed core without accepting or retrying that proof', async () => {
    const core = prepareRecovery(), next = await getRecovery();
    const probe = node('investigate_missing_construction', 'research', ['core']);
    const tasks = [...state.cooperation!.tasks.map(node => node.task), probe.task];
    await cooperative.deliver(lead, next, recoveryPlan({ status: 'planned', taskIds: [probe.task.id] }, tasks));
    expect(core.status).toBe('blocked'); expect(core.attempts).toBe(2);
    expect(await cooperative.next(researcher, { maxTurns: Infinity, remainingMs: Infinity })).toMatchObject({
      kind: 'task', task: { id: probe.task.id, kind: 'research' },
    });
    expect(core.integratedCheck).toBeUndefined();
  });

  const waitForRecoveryInput = async () => {
    const core = prepareRecovery(), next = await getRecovery();
    await cooperative.deliver(lead, next, recoveryPlan({ status: 'awaiting-input', reason: 'A new cancellation estimate is required.' }));
    (cooperative as any).input.continuousResearch = true;
    return core;
  };
  const waitingBudget = { maxTurns: Infinity, remainingMs: Infinity };

  it('runs one advisory investigation in continuous mode, then waits without retrying the failed proof', async () => {
    const core = await waitForRecoveryInput(), emit = vi.fn(); (cooperative as any).input.emit = emit;
    const pendingLead = cooperative.next(lead, waitingBudget);
    await vi.waitFor(() => expect(state.cooperation!.frontierRecoveries![0].investigationTaskId).toBeTruthy());
    const taskId = state.cooperation!.frontierRecoveries![0].investigationTaskId!;
    const work = await cooperative.next(researcher, waitingBudget);
    expect(work).toMatchObject({ kind: 'task', task: { id: taskId, kind: 'research', dependsOn: ['core'] } });
    if (work?.kind !== 'task') throw new Error('expected_frontier_investigation');
    expect(cooperative.started(researcher, work)).toBe(true);
    await cooperative.deliver(researcher, work, checkpoint('```math-result\n' + JSON.stringify({
      taskId, conclusion: 'inconclusive', summary: 'The inspected local inference still lacks a cancellation estimate.',
    }) + '\n```'));
    const assessment = await pendingLead;
    expect(assessment).toMatchObject({ kind: 'lead' });
    if (assessment?.kind !== 'lead') throw new Error('expected_investigation_assessment');
    await cooperative.deliver(lead, assessment, recoveryPlan(undefined));
    let finished = false;
    const waiting = cooperative.next(lead, waitingBudget).then(result => { finished = true; return result; });
    await vi.waitFor(() => expect(state.cooperation!.frontierWaiting).toMatchObject({
      taskIds: ['core'], goalIds: ['goal'], reason: 'awaiting-new-mathematical-input',
    }));
    for (let wake = 0; wake < 3; wake++) { cooperative.modelBudgetChanged(); await Promise.resolve(); }
    expect(finished).toBe(false);
    expect(state.cooperation!.tasks.filter(node => node.task.id === taskId)).toHaveLength(1);
    expect(core.status).toBe('blocked'); expect(core.attempts).toBe(2); expect(core.integratedCheck).toBeUndefined();
    expect(emit.mock.calls.filter(([event]) => event === 'frontier_investigation_requested')).toHaveLength(1);
    expect(emit.mock.calls.filter(([event, details]) => event === 'frontier_recovery_waiting' &&
      details.reason === 'awaiting-new-mathematical-input')).toHaveLength(1);
    await cooperative.stop();
    expect(await waiting).toBeUndefined();
  });

  it('restores the durable investigation marker and waits instead of regenerating completed research', async () => {
    await waitForRecoveryInput();
    const initial = cooperative.next(lead, waitingBudget);
    await vi.waitFor(() => expect(state.cooperation!.frontierRecoveries![0].investigationTaskId).toBeTruthy());
    const taskId = state.cooperation!.frontierRecoveries![0].investigationTaskId!;
    const investigation = state.cooperation!.tasks.find(node => node.task.id === taskId)!;
    investigation.status = 'completed'; investigation.attempts = 1;
    state.cooperation!.lastLeadInputDigest = (cooperative as any).planningInputDigest();
    await cooperative.stop(); expect(await initial).toBeUndefined();
    const restored = JSON.parse(JSON.stringify(state)) as SolverRunState;
    const resumed = new CooperativeResearch({ state: restored, workers: [lead, researcher], access: new Map(), signal: signal(),
      continuousResearch: true, save: () => {}, emit: () => {}, modules: directSolverModules, exclusiveCheck: async check => check() });
    vi.spyOn(resumed as any, 'seed').mockReturnValue(seed);
    try {
      await resumed.restore();
      const waiting = resumed.next(lead, waitingBudget);
      await vi.waitFor(() => expect(restored.cooperation!.frontierWaiting?.reason).toBe('awaiting-new-mathematical-input'));
      expect(restored.cooperation!.tasks.filter(node => node.task.id === taskId)).toHaveLength(1);
      expect(restored.cooperation!.tasks.find(node => node.task.id === taskId)!.status).toBe('completed');
      await resumed.stop(); expect(await waiting).toBeUndefined();
    } finally { await resumed.stop(); }
  });

  it.each(['abort', 'new-input'])('wakes continuous frontier waiting after %s', async change => {
    await waitForRecoveryInput();
    state.cooperation!.frontierRecoveries![0].investigationTaskId = 'already_investigated';
    const controller = new AbortController(); (cooperative as any).input.signal = controller.signal;
    const waiting = cooperative.next(lead, waitingBudget);
    const settled = waiting.then(value => ({ value }), error => ({ error }));
    await vi.waitFor(() => expect(state.cooperation!.frontierWaiting?.reason).toBe('awaiting-new-mathematical-input'));
    if (change === 'abort') {
      controller.abort();
      expect(await settled).toMatchObject({ error: { name: 'AbortError' } });
    } else {
      state.environmentDigest = 'new-pinned-environment';
      cooperative.modelBudgetChanged();
      expect(await settled).toMatchObject({ value: { kind: 'lead' } });
      expect(state.cooperation!.frontierWaiting).toBeUndefined();
      expect(state.cooperation!.tasks.find(node => node.task.id === 'core')!.status).toBe('blocked');
    }
  });

  it.each(['unchanged', 'revision-prose', 'renamed-helper'])(
    'rejects a %s recovery as new work and preserves the decision across restore', async change => {
      prepareRecovery();
      const next = await getRecovery();
      const tasks = state.cooperation!.tasks.map(node => node.task);
      let requested = 'core';
      if (change === 'revision-prose') tasks[0] = { ...tasks[0], revision: 1, objective: 'Reword the same construction.' };
      if (change === 'renamed-helper') {
        requested = 'same_type_new_name';
        tasks.push({ ...tasks[0], id: requested, theoremName: requested });
        const index = tasks.findIndex(task => task.id === 'goal');
        tasks[index] = { ...tasks[index], dependsOn: [requested] };
      }
      const before = JSON.stringify(state.cooperation!.tasks);
      await cooperative.deliver(lead, next, recoveryPlan({ status: 'planned', taskIds: [requested] }, tasks));
      expect(JSON.stringify(state.cooperation!.tasks)).toBe(before);
      expect(state.cooperation!.frontierRecoveries![0]).toMatchObject({ status: 'awaiting-input', reason: 'math_frontier_recovery_no_executable_step' });
      expect(await cooperative.next(lead, { maxTurns: Infinity, remainingMs: Infinity })).toBeUndefined();
      const restoredState = JSON.parse(JSON.stringify(state));
      const resumed = new CooperativeResearch({ state: restoredState, workers: [lead, researcher], access: new Map(),
        signal: signal(), save: () => {}, emit: () => {}, modules: directSolverModules, exclusiveCheck: async check => check() });
      vi.spyOn(resumed as any, 'seed').mockReturnValue(seed);
      try {
        await resumed.restore();
        expect(restoredState.cooperation.tasks.map((node: TaskRecord) => node.task)).toEqual(state.cooperation!.tasks.map(node => node.task));
        expect(await resumed.next(lead, { maxTurns: Infinity, remainingMs: Infinity })).toBeUndefined();
      } finally { await resumed.stop(); }
    });

  it.each(['dependency-contract', 'group-revision'])(
    'does not treat a consumer of transitively invalidated evidence as ready after %s changes', async change => {
      prepareRecovery();
      const base = integrated(node('base')), bridge = integrated(node('bridge', 'lemma', ['base']));
      state.cooperation!.tasks.push(base, bridge);
      state.cooperation!.planVersion = (cooperative as any).planVersion();
      state.cooperation!.lastLeadInputDigest = (cooperative as any).planningInputDigest();
      const next = await getRecovery();
      const fresh = node('consume_bridge', 'lemma', ['bridge']); fresh.task = { ...fresh.task, type: '1 + 1 = (2 : Nat)' };
      const tasks = state.cooperation!.tasks.map(node => node.task.id === 'core' ? { ...node.task, dependsOn: [fresh.task.id] } :
        change === 'dependency-contract' && node.task.id === 'base' ? { ...node.task, type: 'And True True' } : node.task);
      tasks.push(fresh.task);
      const extra = change === 'group-revision' ? { groups: [{ ...main.group, revision: 1 }] } : {};
      await cooperative.deliver(lead, next, recoveryPlan({ status: 'planned', taskIds: [fresh.task.id] }, tasks, extra));
      expect(state.cooperation!.frontierRecoveries![0].status).toBe('awaiting-input');
      expect(state.cooperation!.tasks.find(node => node.task.id === fresh.task.id)).toBeUndefined();
      expect(bridge.status).toBe('integrated');
    });

  it('keeps a checkpointed recovery requested and validates it again after process restoration', async () => {
    prepareRecovery();
    const next = await getRecovery();
    const tasks = state.cooperation!.tasks.map(node => node.task.id === 'core' ? { ...node.task, revision: 1 } : node.task);
    const saved = recoveryPlan({ status: 'planned', taskIds: ['core'] }, tasks);
    await cooperative.deliver(lead, next, saved, true);
    expect(state.cooperation!.tasks[0].task.revision).toBe(0);
    expect(state.cooperation!.frontierRecoveries![0].status).toBe('requested');
    const restoredState = JSON.parse(JSON.stringify(state));
    const resumed = new CooperativeResearch({ state: restoredState, workers: [lead, researcher], access: new Map(),
      signal: signal(), save: () => {}, emit: () => {}, modules: directSolverModules, exclusiveCheck: async check => check() });
    vi.spyOn(resumed as any, 'seed').mockReturnValue(seed);
    try {
      await resumed.restore();
      expect(restoredState.cooperation.tasks[0].task.revision).toBe(0);
      expect(await resumed.next(lead, { maxTurns: Infinity, remainingMs: Infinity })).toMatchObject({ kind: 'lead', recovery: next.recovery });
    } finally { await resumed.stop(); }
  });

  it('allows one correction of malformed recovery JSON and then parks the unchanged malformed response', async () => {
    prepareRecovery();
    const next = await getRecovery();
    const malformed = checkpoint('```math-plan\n{ invalid JSON }\n```');
    await cooperative.deliver(lead, next, malformed);
    expect(state.cooperation!.frontierRecoveries![0].status).toBe('requested');
    await cooperative.deliver(lead, await getRecovery(), malformed);
    expect(state.cooperation!.frontierRecoveries![0].status).toBe('awaiting-input');
    expect(await cooperative.next(lead, { maxTurns: Infinity, remainingMs: Infinity })).toBeUndefined();
  });

  it('preserves peer evidence that arrives during a recovery which requests missing input', async () => {
    prepareRecovery();
    const next = await getRecovery();
    (cooperative as any).record(researcher, record.task, 'research', 'advisory', 'A new concrete compactness reduction from a peer.');
    await cooperative.deliver(lead, next, recoveryPlan({ status: 'awaiting-input', reason: 'A compactness construction is still required.' }));
    expect(state.cooperation!.lastLeadInputDigest).toBe(next.planningInputDigest);
    const assessment = await cooperative.next(lead, { maxTurns: Infinity, remainingMs: Infinity });
    expect(assessment).toMatchObject({ kind: 'lead' });
    if (assessment?.kind !== 'lead') throw new Error('expected_peer_evidence_assessment');
    await cooperative.deliver(lead, assessment, recoveryPlan(undefined));
    expect(await cooperative.next(lead, { maxTurns: Infinity, remainingMs: Infinity })).toBeUndefined();
  });

  it.each(['receipt-replay', 'unrelated-helper', 'relevant-proof', 'environment'])(
    'deduplicates recovery by mathematical inputs after %s', async change => {
      const core = prepareRecovery(), input = integrated(node('checked_input'));
      core.task = { ...core.task, dependsOn: [input.task.id] };
      state.cooperation!.tasks.push(input);
      state.cooperation!.planVersion = (cooperative as any).planVersion();
      state.cooperation!.lastLeadInputDigest = (cooperative as any).planningInputDigest();
      const next = await getRecovery();
      await cooperative.deliver(lead, next, recoveryPlan({ status: 'awaiting-input', reason: 'Need a stronger checked input.' }));
      if (change === 'receipt-replay') {
        input.integratedCheck!.verification.targetCommit = 'new-projection';
        input.integratedCheck!.verification.results[0] = { ...input.integratedCheck!.verification.results[0],
          targetCommit: 'new-projection', receiptId: 'new-receipt' };
      } else if (change === 'unrelated-helper') state.cooperation!.tasks.push(integrated(node('unrelated_helper')));
      else if (change === 'environment') state.environmentDigest = 'updated-environment';
      else input.integratedCheck!.changes = [{ file: 'Submission.lean', name: input.task.theoremName!,
        after: 'a distinct proof term for the required input' }] as TaskProof['changes'];
      state.cooperation!.lastLeadInputDigest = (cooperative as any).planningInputDigest();
      const fresh = await cooperative.next(lead, { maxTurns: Infinity, remainingMs: Infinity });
      if (['relevant-proof', 'environment'].includes(change)) {
        expect(fresh).toMatchObject({ kind: 'lead', recovery: { taskIds: ['core'] } });
        expect(state.cooperation!.frontierRecoveries).toHaveLength(2);
      } else {
        expect(fresh).toBeUndefined();
        expect(state.cooperation!.frontierRecoveries).toHaveLength(1);
      }
    });

  it('rebinds an unattempted recovery premise to a live owner before checking dispatchability', async () => {
    prepareRecovery();
    const premise = node('rebound_premise'); premise.task = { ...premise.task, type: 'Nat.succ 0 = 1', ownerId: 'offline' };
    premise.assignment = { ...action.assignment, workerId: 'offline', taskId: premise.task.id, taskDigest: taskVersion(premise.task) };
    state.cooperation!.tasks.push(premise);
    state.cooperation!.planVersion = (cooperative as any).planVersion();
    state.cooperation!.lastLeadInputDigest = (cooperative as any).planningInputDigest();
    const next = await getRecovery();
    const tasks = state.cooperation!.tasks.map(node => node.task.id === 'core' ? { ...node.task, dependsOn: [premise.task.id] } :
      node.task.id === premise.task.id ? { ...node.task, ownerId: researcher.id } : node.task);
    await cooperative.deliver(lead, next, recoveryPlan({ status: 'planned', taskIds: [premise.task.id] }, tasks));
    expect(state.cooperation!.frontierRecoveries![0].status).toBe('planned');
    expect(await cooperative.next(researcher, { maxTurns: Infinity, remainingMs: Infinity })).toMatchObject({
      kind: 'task', task: { id: premise.task.id }, assignment: { workerId: researcher.id },
    });
  });

  it('records an accepted decomposition even if subsequent source integration fails', async () => {
    prepareRecovery();
    const saved: { status?: string; error?: string }[] = [];
    (cooperative as any).input.save = () => saved.push({ status: state.cooperation!.frontierRecoveries?.[0]?.status,
      error: state.cooperation!.error });
    const next = await getRecovery(), premise = node('fresh_premise');
    premise.task = { ...premise.task, type: 'Nat.succ 0 = 1' };
    const tasks = state.cooperation!.tasks.map(node => node.task.id === 'core' ? { ...node.task, dependsOn: [premise.task.id] } : node.task);
    tasks.push(premise.task);
    fs.appendFileSync(path.join(directory, 'generated/p/Submission.lean'), '\nlemma fresh_premise : Nat.succ 0 = 1 := by rfl\n');
    git(directory, ['add', '--', 'generated']);
    await cooperative.deliver(lead, next, recoveryPlan({ status: 'planned', taskIds: [premise.task.id] }, tasks));
    expect(state.cooperation!.error).toBeTruthy();
    expect(saved).toContainEqual({ status: 'planned', error: undefined });
    expect(state.cooperation!.frontierRecoveries![0].status).toBe('planned');
    expect(state.cooperation!.tasks.find(node => node.task.id === premise.task.id)).toBeDefined();
    const repair = await cooperative.next(lead, { maxTurns: Infinity, remainingMs: Infinity });
    expect(repair).toMatchObject({ kind: 'lead' });
    expect(repair && 'recovery' in repair ? repair.recovery : undefined).toBeUndefined();
  });

  it('keeps a resumed frontier behind the existing M3 readiness gate', async () => {
    const core = parkCore(), budget = { maxTurns: Infinity, remainingMs: Infinity };
    state.cooperation!.blockers = []; core.routeParking = [];
    (cooperative as any).input.modules = { ...directSolverModules, M3: { ...directSolverModules.M3, ready: () => [] } };
    state.cooperation!.lastLeadInputDigest = (cooperative as any).planningInputDigest();
    const reassessment = await cooperative.next(lead, budget);
    expect(reassessment).toMatchObject({ kind: 'lead' });
    expect(core.status).toBe('pending'); expect(core.assignment).toBeUndefined(); expect(core.attempts).toBe(0);
    if (reassessment?.kind !== 'lead') throw new Error('expected_gated_frontier_assessment');
    await cooperative.deliver(lead, reassessment, seed);
    expect(await cooperative.next(lead, budget)).toBeUndefined();
    expect(core.status).toBe('pending'); expect(core.assignment).toBeUndefined();
  });

  it('does not repeat a frontier decision for notes-only commits, duplicate delivery ids or restored state', async () => {
    parkCore();
    const budget = { maxTurns: Infinity, remainingMs: Infinity };
    const progress = { id: 'finding-one', taskId: record.task.id, taskDigest: taskVersion(record.task), kind: 'research' as const,
      status: 'advisory' as const, summary: 'The current input does not prove the required cancellation.', evidenceRefs: [],
      dependencies: [], remainingObligations: [] };
    state.cooperation!.deliveries = [progress as any];
    await assessFrontier();
    state.cooperation!.canonicalCommit = checkpoint('Only reword the explanation of the same obstacle.');
    state.cooperation!.deliveries.push({ ...progress, id: 'finding-new-id', createdAt: 42 } as any);
    expect(await cooperative.next(lead, budget)).toBeUndefined();
    const restoredState = JSON.parse(JSON.stringify(state));
    const resumed = new CooperativeResearch({ state: restoredState, workers: [lead, researcher], access: new Map(), signal: signal(),
      save: () => {}, emit: () => {}, modules: directSolverModules, exclusiveCheck: async check => check() });
    try { expect(await resumed.next(lead, budget)).toBeUndefined(); }
    finally { await resumed.stop(); }
  });

  const savePausedPlan = () => {
    vi.mocked((cooperative as any).acceptPlan).mockRestore();
    state.problem.targets = [{ proofPath: 'Submission.lean', theoremName: 'goal' }] as SolverProblem['targets'];
    return checkpoint('```math-plan\n' + JSON.stringify({
      tasks: [...state.cooperation!.tasks.map(node => node.task), {
        id: 'paused_probe', kind: 'research', objective: 'An explicitly deferred investigation', status: 'paused',
        dependsOn: [], revision: 0,
      }], groups: state.cooperation!.groups!.map(route => route.group),
    }) + '\n```');
  };

  it('consumes its own accepted plan changes without another frontier assessment', async () => {
    parkCore();
    const budget = { maxTurns: Infinity, remainingMs: Infinity };
    const action = await cooperative.next(lead, budget);
    if (action?.kind !== 'lead') throw new Error('expected_frontier_assessment');
    const commit = savePausedPlan();
    await cooperative.deliver(lead, action, commit);
    expect(state.cooperation!.lastLeadInputDigest).not.toBe(action.planningInputDigest);
    expect(state.cooperation!.lastLeadInputDigest).toBe((cooperative as any).planningInputDigest());
    expect(await cooperative.next(lead, budget)).toBeUndefined();
  });

  it('retains peer evidence arriving while Lead is accepting its own plan changes', async () => {
    parkCore();
    const budget = { maxTurns: Infinity, remainingMs: Infinity };
    const action = await cooperative.next(lead, budget);
    if (action?.kind !== 'lead') throw new Error('expected_frontier_assessment');
    const commit = savePausedPlan();
    (cooperative as any).record(researcher, record.task, 'research', 'advisory', 'A new precise estimate from a peer.');
    await cooperative.deliver(lead, action, commit);
    expect(state.cooperation!.lastLeadInputDigest).toBe(action.planningInputDigest);
    const next = await cooperative.next(lead, budget);
    expect(next).toMatchObject({ kind: 'lead' });
    if (next?.kind !== 'lead') throw new Error('expected_new_evidence_assessment');
    await cooperative.deliver(lead, next, commit);
    expect(await cooperative.next(lead, budget)).toBeUndefined();
  });

  it.each(['environment', 'proof-source'])('allows one new frontier assessment after changed %s', async change => {
    const core = parkCore(), budget = { maxTurns: Infinity, remainingMs: Infinity };
    await assessFrontier();
    if (change === 'environment') state.environmentDigest = 'new-pinned-environment';
    else {
      fs.appendFileSync(path.join(directory, 'generated/p/Submission.lean'), '\ntheorem new_input : True := by trivial\n');
      git(directory, ['add', '--', 'generated']);
      state.cooperation!.canonicalCommit = checkpoint('A newly saved proof input.');
    }
    await assessFrontier();
    expect(await cooperative.next(lead, budget)).toBeUndefined();
    expect(core.status).toBe('blocked'); expect(core.routeParking).toHaveLength(1);
  });

  it.each(['paused-task', 'paused-group', 'spent-group'])('does not reconsider an explicitly %s frontier', async control => {
    const core = parkCore();
    if (control === 'paused-task') core.task = { ...core.task, status: 'paused' };
    else if (control === 'paused-group') state.cooperation!.groups![0].group.status = 'paused';
    else { state.cooperation!.groups![0].group.maxTurns = 1; state.cooperation!.groups![0].turns = 1; }
    expect(await cooperative.next(lead, { maxTurns: Infinity, remainingMs: Infinity })).toBeUndefined();
    expect(core.status).toBe('blocked');
  });

  it('retries a dispatched but unfinished frontier decision after restoring serialized state', async () => {
    parkCore();
    const budget = { maxTurns: Infinity, remainingMs: Infinity };
    expect(await cooperative.next(lead, budget)).toMatchObject({ kind: 'lead' });
    expect(state.cooperation!.lastLeadInputDigest).toBeUndefined();
    const resumed = new CooperativeResearch({ state: JSON.parse(JSON.stringify(state)), workers: [lead, researcher],
      access: new Map(), signal: signal(), save: () => {}, emit: () => {}, modules: directSolverModules,
      exclusiveCheck: async check => check() });
    vi.spyOn(resumed as any, 'seed').mockReturnValue(seed);
    try { expect(await resumed.next(lead, budget)).toMatchObject({ kind: 'lead' }); }
    finally { await resumed.stop(); }
  });

  it('ignores a repeated advisory decision hint while a peer is still running on unchanged input', async () => {
    parkCore(); record.status = 'running';
    const progress = { id: 'progress-one', kind: 'progress', taskId: record.task.id,
      taskDigest: action.assignment.taskDigest, summary: 'The same known cancellation gap.', needsDecision: true };
    await (cooperative as any).receive(researcher, action, progress);
    await assessFrontier();
    const completed = state.cooperation!.lastLeadInputDigest;
    await (cooperative as any).receive(researcher, action, { ...progress, id: 'progress-two' });
    const pending = cooperative.next(lead, { maxTurns: Infinity, remainingMs: Infinity });
    await Promise.resolve();
    allowed = false; record.status = 'completed'; cooperative.modelBudgetChanged();
    expect(await pending).toBeUndefined();
    expect(state.cooperation!.lastLeadInputDigest).toBe(completed);
  });

  it('exits idle after assessing a blocked core hidden behind completed advisory work', async () => {
    const core = parkCore(), budget = { maxTurns: Infinity, remainingMs: Infinity };
    record.task = { ...record.task, dependsOn: [core.task.id] };
    const goal = state.cooperation!.tasks.find(item => item.task.kind === 'goal')!;
    goal.task = { ...goal.task, dependsOn: [record.task.id] };
    state.cooperation!.planVersion = (cooperative as any).planVersion();
    expect(researchCanAdvance(state.cooperation!.tasks, state.cooperation!.groups, new Set([lead.id, researcher.id]))).toBe(false);
    expect(readyResearchTasks(state.cooperation!.tasks, state.cooperation!.groups)).toEqual([]);
    const emit = vi.fn(); (cooperative as any).input.emit = emit;
    await assessFrontier();
    const inputDigest = state.cooperation!.lastLeadInputDigest;
    expect(await cooperative.next(lead, budget)).toBeUndefined();
    expect(emit).toHaveBeenCalledWith('routes_idle', expect.objectContaining({ goalIds: [goal.task.id],
      frontier: [expect.objectContaining({ taskId: core.task.id, status: 'blocked', attempts: core.attempts,
        parkedBy: core.routeParking })], inputDigest, reason: 'unchanged-mathematical-input' }));
    expect(core.status).toBe('blocked'); expect(core.routeParking).toHaveLength(1);
  });

  it('retries the first unchanged completion and asks Lead to revise after the second', async () => {
    record.attempts = 40; // Long-lived work and checkpoint counts must not consume the repair opportunity.
    await cooperative.deliver(researcher, action, seed);
    expect(record.status).toBe('pending');
    expect(state.cooperation!.unchangedResearch!.question.count).toBe(1);
    record.status = 'running';
    await cooperative.deliver(researcher, action, seed);
    expect(record.status).toBe('blocked');
    expect(state.cooperation!.deliveries).toEqual([expect.objectContaining({ kind: 'failure', status: 'failed', taskId: 'question' })]);
    vi.spyOn(cooperative as any, 'seed').mockReturnValue(seed);
    await expect(cooperative.next(lead, { maxTurns: Infinity, remainingMs: Infinity })).resolves.toMatchObject({ kind: 'lead' });
  });

  it('retains complete long-running plans when both inherited notes and task graphs exceed 64KB', () => {
    const objective = 'Preserve this exact mathematical obligation. '.repeat(2000);
    record.task = { ...record.task, objective };
    fs.writeFileSync(path.join(directory, 'RESEARCH.md'), 'Earlier advisory checkpoint. '.repeat(4000));
    for (let round = 0; round < 2; round++) {
      state.cooperation!.planEdited = true;
      (cooperative as any).syncPlanNotes();
      const response = readMathResponse(directory, 'math-plan');
      expect(response.tasks.find((task: any) => task.id === record.task.id).objective).toBe(objective);
      expect(Buffer.byteLength(fs.readFileSync(path.join(directory, 'RESEARCH.md')))).toBeGreaterThan(64_000);
    }
  });

  it('retains reproducible Lean probe artifacts with an advisory finding and never grants proof acceptance', async () => {
    const next = checkpoint('```math-result\n' + JSON.stringify({ summary: 'A reusable supporting declaration.',
      leanChecks: [{ status: 'passed', path: 'RESEARCH.md', declarations: ['probe'] }] }) +
      '\n```\n\n```lean\ntheorem probe : True := by trivial\n```\n');
    await cooperative.deliver(researcher, action, next);
    expect(record.status).toBe('completed');
    const delivery = state.cooperation!.deliveries!.find(item => item.kind === 'research')!;
    expect(delivery.status).toBe('advisory');
    expect(delivery.artifacts).toMatchObject({ scope: 'advisory-unverified', commit: next,
      taskId: record.task.id, taskDigest: action.assignment.taskDigest });
    expect(delivery.artifacts!.artifacts[0].declarations[0].name).toBe('probe');
    expect(delivery.artifacts!.reportedChecks![0].artifactIds).toHaveLength(1);
    expect(delivery.evidence).toBeUndefined();
    expect(record.integratedCheck).toBeUndefined();
  });

  it('does not count recovered checkpoints as unchanged completed findings and resets after new findings', async () => {
    await cooperative.deliver(researcher, action, seed);
    record.status = 'running';
    await cooperative.deliver(researcher, action, seed, true);
    expect(record.status).toBe('pending');
    expect(state.cooperation!.unchangedResearch!.question.count).toBe(1);
    record.status = 'running';
    await cooperative.deliver(researcher, action, checkpoint('A new concrete route and unresolved mathematical gap.'));
    expect(record.status).toBe('completed');
    expect(record.feedback).toBeUndefined();
    expect(state.cooperation!.unchangedResearch!.question).toBeUndefined();
  });

  it('pauses only the identical advisory checkpoint and keeps the original goal unfinished', async () => {
    await cooperative.deliver(researcher, action, seed, true);
    expect(record.status).toBe('pending');
    record.status = 'running';
    await cooperative.deliver(researcher, action, checkpoint('Inherited research notes.'), true);
    expect(record.status).toBe('blocked');
    expect(state.cooperation!.researchCheckpoints!.question).toMatchObject({ count: 2, paused: true });
    expect(record.feedback).toContain('math_research_checkpoint_unchanged');
    expect(state.cooperation!.tasks.find(node => node.task.kind === 'goal')!.status).toBe('pending');
    expect(state.cooperation!.tasks[0].integratedCheck).toBeUndefined();
  });

  it('continues indefinitely while advisory checkpoints save different notes or drafts', async () => {
    for (let attempt = 0; attempt < 6; attempt++) {
      record.status = 'running';
      const commit = checkpoint(`Investigation checkpoint ${attempt}: a distinct saved intermediate calculation.`);
      await cooperative.deliver(researcher, action, commit, true);
      expect(record.status).toBe('pending');
      expect(state.cooperation!.researchCheckpoints!.question).toMatchObject({ count: 1, paused: false });
    }
  });

  it('does not count transport interruptions as repeated checkpoints', async () => {
    await cooperative.deliver(researcher, action, seed, true);
    for (let attempt = 0; attempt < 5; attempt++) {
      record.status = 'running';
      cooperative.interrupted(researcher, action);
    }
    expect(record.status).toBe('pending');
    expect(state.cooperation!.researchCheckpoints!.question).toMatchObject({ count: 1, paused: false });
  });

  it.each(['peer', 'environment', 'notes', 'draft'] as const)('reopens an exact checkpoint pause after new %s input', async change => {
    await cooperative.deliver(researcher, action, seed, true);
    record.status = 'running';
    await cooperative.deliver(researcher, action, seed, true);
    expect(record.status).toBe('blocked');
    if (change === 'environment') state.environmentDigest = 'new-environment';
    else if (change === 'peer') {
      (cooperative as any).record(lead, record.task, 'progress', 'advisory', 'A peer supplies a distinct library connection.');
    } else if (change === 'notes') checkpoint('A new saved calculation is available.');
    else {
      fs.appendFileSync(path.join(directory, 'generated/p/Submission.lean'), '\nlemma candidate : True := by trivial\n');
      git(directory, ['add', '--', 'generated']);
      checkpoint('Inherited research notes.');
    }
    (cooperative as any).changed();
    expect(record.status).toBe('pending');
    expect(record.feedback).toBeUndefined();
    expect(state.cooperation!.researchCheckpoints!.question).toBeUndefined();
    expect(state.cooperation!.blockers!.find(record => record.mechanism === 'unchanged-research-checkpoint')!.status).toBe('reopened');
  });

  it('preserves an unchanged checkpoint pause through serialization and restore', async () => {
    await cooperative.deliver(researcher, action, seed, true);
    record.status = 'running';
    await cooperative.deliver(researcher, action, seed, true);
    const restoredState = JSON.parse(JSON.stringify(state));
    const resumed = new CooperativeResearch({ state: restoredState, workers: [lead, researcher], access: new Map(), signal: signal(),
      save: () => {}, emit: () => {}, modules: directSolverModules, exclusiveCheck: async check => check() });
    try {
      await resumed.restore();
      expect(restoredState.cooperation.tasks[0].status).toBe('blocked');
      expect(restoredState.cooperation.researchCheckpoints.question).toMatchObject({ count: 2, paused: true });
    } finally { await resumed.stop(); }
  });

  it.each(['running-assignment', 'different-session', 'new-task-version', 'reviewer'] as const)(
    'does not reopen an old checkpoint from another responsibility output (%s)', async responsibility => {
      await cooperative.deliver(researcher, action, seed, true);
      record.status = 'running';
      await cooperative.deliver(researcher, action, seed, true);
      if (responsibility === 'running-assignment') {
        const other = node('another-investigation', 'research'); other.status = 'running';
        other.assignment = { taskId: other.task.id, taskDigest: taskVersion(other.task), workerId: researcher.id, seedCommit: seed };
        state.cooperation!.tasks.push(other);
      } else state.workers = [{ id: researcher.id, sessionTaskId: responsibility === 'different-session' ? 'other' :
        responsibility === 'reviewer' ? undefined : record.task.id,
        sessionTaskVersion: responsibility === 'new-task-version' ? 'new-version' : taskVersion(record.task),
      }] as SolverRunState['workers'];
      checkpoint('Notes saved for a different assigned responsibility.');
      (cooperative as any).changed();
      expect(record.status).toBe('blocked');
      expect(state.cooperation!.researchCheckpoints!.question).toMatchObject({ count: 2, paused: true });
    });

  it('reopens a checkpoint for new notes owned by the same task session and version', async () => {
    await cooperative.deliver(researcher, action, seed, true);
    record.status = 'running';
    await cooperative.deliver(researcher, action, seed, true);
    state.workers = [{ id: researcher.id, sessionTaskId: record.task.id, sessionTaskVersion: taskVersion(record.task) }] as SolverRunState['workers'];
    checkpoint('A new saved calculation for this exact investigation.');
    (cooperative as any).changed();
    expect(record.status).toBe('pending');
    expect(state.cooperation!.researchCheckpoints!.question).toBeUndefined();
  });

  const failureChecker = (result: Record<string, unknown> = {}, verification: Record<string, unknown> = {}) => {
    record.task = { ...record.task, kind: 'lemma', theoremName: 'question', proofPath: 'Submission.lean', type: 'True' };
    record.assignment!.taskDigest = taskVersion(record.task);
    record.attempts = 1;
    action = { kind: 'task', task: record.task, assignment: record.assignment! };
    const checkTask = vi.fn(async (_problem, worktree, commit, task, assignment, _goals, _environment, _signal, _timeout, conditions) => ({
      commit, sourceDigest: ownedSourceDigest(state.problem, worktree, commit), seedCommit: assignment.seedCommit,
      taskDigest: taskVersion(task), passed: false, changes: [], imports: [],
      conditions: conditions.map((task: TaskRecord['task']) => ({ taskId: task.id, taskDigest: taskVersion(task) })),
      verification: { status: 'failed', targetCommit: commit, results: [{ status: 'failed', targetCommit: commit,
        error: 'Lean exited with status 1.', stdoutPreview: 'Submission.lean:1:1: error: unsolved goals\n⊢ True', ...result }], ...verification },
    }) as TaskProof);
    (cooperative as any).input.modules = { ...directSolverModules, M2: { ...directSolverModules.M2, checkTask } };
    (cooperative as any).input.access.set(lead.id, { environment: {} });
    return checkTask;
  };

  it('checks an identical failed helper once across live submissions and completed delivery', async () => {
    const checkTask = failureChecker();
    const submission = { id: 'failure_one', kind: 'proof', taskId: record.task.id, taskDigest: action.assignment.taskDigest,
      commit: seed, summary: 'The same saved candidate.' };
    await (cooperative as any).receive(researcher, action, submission);
    const repair = await cooperative.next(researcher, { maxTurns: Infinity, remainingMs: Infinity });
    if (repair?.kind !== 'task') throw new Error('expected_local_repair');
    expect(cooperative.started(researcher, repair)).toBe(true);
    await (cooperative as any).receive(researcher, action, { ...submission, id: 'failure_two' });
    await cooperative.deliver(researcher, action, seed);
    expect(checkTask).toHaveBeenCalledTimes(1);
    expect(record.status).toBe('blocked');
  });

  it.each(['source', 'environment', 'environment-variable', 'conditions'] as const)(
    'rechecks a failed helper after changed %s', async change => {
      const checkTask = failureChecker();
      const check = (commit = seed, conditions: TaskRecord['task'][] = []) =>
        (cooperative as any).check(record.task, record.assignment, directory, commit, conditions, undefined, true);
      await check();
      if (change === 'environment') state.environmentDigest = 'new-environment';
      else if (change === 'environment-variable') (cooperative as any).input.access.get(lead.id).environment.LEAN_PATH = '/updated/lean';
      else if (change === 'source') {
        fs.appendFileSync(path.join(directory, 'generated/p/Submission.lean'), '\nlemma candidate : True := by trivial\n');
        git(directory, ['add', '--', 'generated']);
      }
      const commit = change === 'source' ? checkpoint('Inherited research notes.') : seed;
      await check(commit, change === 'conditions' ? [node('condition').task] : []);
      expect(checkTask).toHaveBeenCalledTimes(2);
    });

  it('preserves unlimited checker timeouts without treating timeout changes as new mathematics', async () => {
    const checkTask = failureChecker();
    const check = () => (cooperative as any).check(record.task, record.assignment, directory, seed, [], undefined, true);
    (cooperative as any).input.timeoutMs = Infinity;
    await check();
    expect(checkTask.mock.calls[0][8]).toBe(Infinity);
    for (const timeout of [Infinity, undefined, 999]) {
      (cooperative as any).input.timeoutMs = timeout;
      await expect(check()).rejects.toThrow('math_task_repeated_failed_input');
    }
    record.task = { ...record.task, revision: 1 };
    record.assignment!.taskDigest = taskVersion(record.task);
    await expect(check()).rejects.toThrow('math_task_repeated_failed_input');
    expect(checkTask).toHaveBeenCalledTimes(1);
  });

  it('rechecks a failed helper after its dependency proof changes', async () => {
    const checkTask = failureChecker();
    const helper = integrated(node('dependency'));
    helper.integratedCheck!.changes = [{ file: 'Submission.lean', name: helper.task.theoremName!,
      after: 'lemma dependency : True := by trivial\n' }];
    markTaskAcceptance(helper.integratedCheck!);
    state.cooperation!.tasks.push(helper);
    record.task = { ...record.task, dependsOn: [helper.task.id] };
    record.assignment!.taskDigest = taskVersion(record.task);
    await (cooperative as any).check(record.task, record.assignment, directory, seed, [], undefined, true);
    helper.integratedCheck!.changes[0].after = 'lemma dependency : True := by exact True.intro\n';
    markTaskAcceptance(helper.integratedCheck!);
    await (cooperative as any).check(record.task, record.assignment, directory, seed, [], undefined, true);
    expect(checkTask).toHaveBeenCalledTimes(2);
  });

  it('honors cancellation before reusing a failed helper check', async () => {
    const checkTask = failureChecker();
    await (cooperative as any).check(record.task, record.assignment, directory, seed, [], undefined, true);
    const controller = new AbortController(); controller.abort();
    (cooperative as any).input.signal = controller.signal;
    await expect((cooperative as any).check(record.task, record.assignment, directory, seed, [], undefined, true)).rejects.toThrow();
    expect(checkTask).toHaveBeenCalledTimes(1);
  });

  it.each([
    { result: { cleanupError: 'failed to remove checkout' } },
    { result: { stdoutPreview: 'compiler process exited without Lean diagnostics' } },
    { result: { status: 'blocked' } },
    { verification: { status: 'blocked' } },
    { verification: { status: 'unavailable' } },
  ])('never reuses an unavailable, incomplete, or unclean helper check ($result, $verification)', async ({ result, verification }) => {
    const checkTask = failureChecker(result, verification);
    for (let attempt = 0; attempt < 2; attempt++)
      await (cooperative as any).check(record.task, record.assignment, directory, seed, [], undefined, true);
    expect(checkTask).toHaveBeenCalledTimes(2);
  });

  it('keeps failure suppression local to delivery checks and persistent across runtime restart', async () => {
    const checkTask = failureChecker();
    await (cooperative as any).check(record.task, record.assignment, directory, seed, [], undefined, true);
    await (cooperative as any).check(record.task, record.assignment, directory, seed, []);
    expect(checkTask).toHaveBeenCalledTimes(2);
    const resumed = new CooperativeResearch({ state: JSON.parse(JSON.stringify(state)), workers: [lead, researcher],
      access: (cooperative as any).input.access, signal: signal(), save: () => {}, emit: () => {},
      modules: (cooperative as any).input.modules, exclusiveCheck: async check => check() });
    try { await expect((resumed as any).check(record.task, record.assignment, directory, seed, [], undefined, true))
      .rejects.toThrow('math_task_repeated_failed_input'); }
    finally { await resumed.stop(); }
    expect(checkTask).toHaveBeenCalledTimes(2);
  });

  it('binds unchanged repetitions to the task version and inherited notes content', async () => {
    await cooperative.deliver(researcher, action, seed);
    seed = checkpoint('A different inherited checkpoint.');
    record.assignment!.seedCommit = seed; record.status = 'running';
    await cooperative.deliver(researcher, action, seed);
    expect(record.status).toBe('pending');
    expect(state.cooperation!.unchangedResearch!.question.count).toBe(1);
    await (cooperative as any).acceptPlan({ tasks: [
      { ...record.task, revision: 1 }, state.cooperation!.tasks[1].task,
    ], groups: [{ ...main.group }] });
    expect(state.cooperation!.unchangedResearch!.question).toBeUndefined();
    record = state.cooperation!.tasks[0];
    record.assignment = { taskId: record.task.id, taskDigest: taskVersion(record.task), workerId: researcher.id, seedCommit: seed };
    record.status = 'running'; action = { kind: 'task', task: record.task, assignment: record.assignment };
    await cooperative.deliver(researcher, action, seed);
    expect(record.status).toBe('pending');
    expect(state.cooperation!.unchangedResearch!.question.count).toBe(1);
  });

  it('wakes idle peers on model budget changes and does not schedule pending reviews', async () => {
    record.status = 'blocked';
    let settled = false;
    const pending = cooperative.next(researcher, { maxTurns: Infinity, remainingMs: Infinity }).then(value => { settled = true; return value; });
    await new Promise(resolve => setImmediate(resolve));
    expect(settled).toBe(false);
    state.cooperation!.review = { status: 'pending', commit: seed, sourceDigest: 'source' };
    allowed = false; cooperative.modelBudgetChanged();
    await expect(pending).resolves.toBeUndefined();
    await expect(cooperative.next(lead, { maxTurns: Infinity, remainingMs: Infinity })).resolves.toBeUndefined();
    expect(state.cooperation!.review.status).toBe('pending');
    state.cooperation!.review = undefined;
    state.cooperation!.statementReviews = [{ taskId: 'question', status: 'pending' }] as CooperationState['statementReviews'];
    await expect(cooperative.next(lead, { maxTurns: Infinity, remainingMs: Infinity })).resolves.toBeUndefined();
    expect(state.cooperation!.statementReviews[0].status).toBe('pending');
  });

  it('waits for active work to settle after budget exhaustion while allowing host assembly', async () => {
    cooperative.activate(researcher, action, async () => {}, async () => {});
    allowed = false;
    let settled = false;
    const pending = cooperative.next(lead, { maxTurns: Infinity, remainingMs: Infinity }).then(value => { settled = true; return value; });
    await new Promise(resolve => setImmediate(resolve));
    expect(settled).toBe(false);
    record.status = 'completed'; state.cooperation!.tasks[1].status = 'integrated';
    vi.spyOn(cooperative as any, 'seed').mockReturnValue(seed);
    cooperative.deactivate(researcher);
    await expect(pending).resolves.toMatchObject({ kind: 'assemble' });
  });
});
