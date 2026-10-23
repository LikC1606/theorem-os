import fs from 'node:fs';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import type { MathematicsVerifierBatchRequest, MathematicsVerifierBatchResult } from '../src/math/verifier';
import type { SolverRunState } from '../src/solver/archive';
import type { CooperativeResearch } from '../src/solver/cooperation';
import { directSolverModules } from '../src/solver/modules';
import { taskDependenciesReady } from '../src/solver/modules/search';
import type { ResearchWorker } from '../src/solver/modules/organization';
import { committedSource, commitSolverSources, git, type SolverProblem } from '../src/solver/problem';
import { hasTaskAcceptance, taskVersion, type CooperativeAction, type CooperativeTask } from '../src/solver/tasks';
import { deferred } from './helpers/async';
import { cooperativeResearch } from './helpers/cooperation';
import { leadWorker, localExample, peerWorker, solverState } from './helpers/solver';
import { failedBatch, verifiedBatch } from './helpers/verifier';

const host = vi.hoisted(() => ({ verify: vi.fn(), createSession: vi.fn(), captureStatements: vi.fn() }));
vi.mock('../src/math/verifier', async importOriginal => ({
  ...await importOriginal<typeof import('../src/math/verifier')>(),
  checkManyFormalVerifications: host.verify,
  formalVerificationToolIdentity: () => 'plan-concurrency-fixture-tools',
  resolveMathematicsLakePackagesCache: () => undefined,
}));
vi.mock('../src/runtime/codexSession', () => ({ createCodexMathSession: host.createSession }));
vi.mock('../src/solver/statementReview', async importOriginal => ({
  ...await importOriginal<typeof import('../src/solver/statementReview')>(),
  captureStatementContexts: host.captureStatements,
}));

function verified(request: MathematicsVerifierBatchRequest, passed = true): MathematicsVerifierBatchResult {
  const batch = verifiedBatch(request, { sessionId: 'plan-concurrency-fixture', checks: true });
  return passed ? batch : failedBatch(batch, { stdoutPreview: () => 'Submission.lean:1:0: error: fixture obsolete recheck failure' });
}
const budget = { maxTurns: 20, remainingMs: Infinity };
type TaskAction = Extract<CooperativeAction, { kind: 'task' }>;

describe('plan synchronization with concurrent host control', () => {
  let directory: string, workspace: string, problem: SolverProblem, state: SolverRunState;
  let workers: ResearchWorker[], cooperative: CooperativeResearch, controller: AbortController;
  let lockHeld: boolean, exclusive: <T>(check: () => Promise<T>) => Promise<T>;
  let pending: Promise<unknown>[], releases: (() => void)[];
  let events: { event: string; details?: Record<string, unknown> }[];
  const node = (id: string) => state.cooperation!.tasks.find(item => item.task.id === id)!;
  const track = <T,>(promise: Promise<T>) => { pending.push(promise); void promise.catch(() => {}); return promise; };
  const create = () => cooperativeResearch({ state, workers, retrievalRoot: directory, signal: controller.signal,
    emit: (event, details) => events.push({ event, details }), exclusiveCheck: check => exclusive(check) });
  const source = () => committedSource(workspace, state.cooperation!.canonicalCommit!, `${problem.projectRelative}/Submission.lean`);
  const writeLemma = (worker: ResearchWorker, name: string, type = 'True', proof = 'by trivial') => {
    const file = path.join(worker.worktree, problem.projectRelative, 'Submission.lean');
    fs.writeFileSync(file, fs.readFileSync(file, 'utf8').replace('theorem add_zero', `lemma ${name} : ${type} := ${proof}\ntheorem add_zero`));
    return commitSolverSources(problem, worker.worktree);
  };
  const gateCheck = () => {
    const entered = deferred<MathematicsVerifierBatchRequest>(), result = deferred<MathematicsVerifierBatchResult>();
    let request: MathematicsVerifierBatchRequest | undefined, heldAtEntry: boolean | undefined;
    host.verify.mockImplementationOnce(async (input: MathematicsVerifierBatchRequest) => {
      request = input; heldAtEntry = lockHeld; entered.resolve(input); return result.promise;
    });
    const release = (passed = true) => { if (request) result.resolve(verified(request, passed)); };
    releases.push(release);
    const waitFor = (delivery: Promise<unknown>) => Promise.race([entered.promise, delivery.then(() => {
      throw new Error(`Delivery completed before the expected verifier check: ${JSON.stringify(events.slice(-5))}`);
    })]);
    return { entered: entered.promise, waitFor, release, heldAtEntry: () => heldAtEntry };
  };
  const edit = (id: string, change: (task: CooperativeTask) => CooperativeTask) => {
    fs.appendFileSync(path.join(directory, 'edits.jsonl'), JSON.stringify({ id, baseVersion: state.cooperation!.planVersion,
      tasks: state.cooperation!.tasks.map(item => change(item.task)), groups: state.cooperation!.groups!.map(item => item.group) }) + '\n');
    return track(cooperative.pulse(workers[0].id));
  };
  const writeLeadPlan = () => fs.writeFileSync(path.join(workspace, 'RESEARCH.md'), '```math-plan\n' + JSON.stringify({
    tasks: state.cooperation!.tasks.map(item => item.task), groups: state.cooperation!.groups!.map(item => item.group),
  }) + '\n```\n');
  const sync = () => track((cooperative as any).schedulePlanSynchronization() as Promise<void>);
  const integrateA = async (proof = 'by trivial') => {
    const current = node('a');
    const action: TaskAction = { kind: 'task', task: current.task, assignment: current.assignment! };
    await cooperative.deliver(workers[1], action, writeLemma(workers[1], 'a', current.task.type, proof));
    expect(node('a').status).toBe('integrated');
  };

  beforeEach(() => {
    host.verify.mockReset().mockImplementation(async request => verified(request));
    host.createSession.mockReset().mockImplementation(() => { throw new Error('fixture_real_models_forbidden'); });
    host.captureStatements.mockReset().mockImplementation(() => { throw new Error('fixture_statement_capture_forbidden'); });
    const example = localExample('solver-plan-concurrency-');
    ({ directory, workspace, problem } = example);
    workers = [leadWorker(problem, workspace, 'lead'), ...['author', 'consumer', 'independent'].map(id => peerWorker(example, id))];
    const lemma = (id: string, ownerId: string, dependsOn: string[] = []): CooperativeTask => ({ id, ownerId, kind: 'lemma',
      objective: `Prove ${id}.`, proofPath: 'Submission.lean', theoremName: `Tutorial.${id}`, type: 'True', dependsOn, revision: 0 });
    const a = lemma('a', 'author');
    state = solverState(problem, workspace, { runId: 'plan-concurrency-fixture', phase: 'running', failures: [],
      cooperation: { canonicalCommit: problem.baseCommit,
        groups: [{ group: { id: 'main', objective: 'Prove the original problem.', status: 'active', revision: 0 }, turns: 0 }],
        tasks: [{ task: a, status: 'running', attempts: 1,
          assignment: { taskId: 'a', taskDigest: taskVersion(a), workerId: 'author', seedCommit: problem.baseCommit,
            assignmentId: 'a-dispatch', dependencies: [] } },
        ...[lemma('b', 'consumer', ['a']), lemma('c', 'independent')].map(task => ({ task, status: 'pending' as const, attempts: 0 })),
        ...problem.targets.map((target, index) => ({ task: { id: `goal_${index}`, kind: 'goal' as const,
          objective: `Prove ${target.theoremName}.`, theoremName: target.theoremName, proofPath: target.proofPath,
          dependsOn: ['b'], revision: 0, status: 'paused' as const }, status: 'pending' as const, attempts: 0 }))] } });
    events = []; pending = []; releases = []; lockHeld = false; controller = new AbortController();
    let queue = Promise.resolve();
    exclusive = async check => {
      const previous = queue, { promise, resolve } = deferred();
      queue = promise;
      await previous; lockHeld = true;
      try { return await check(); } finally { lockHeld = false; resolve(); }
    };
    cooperative = create(); state.cooperation!.planVersion = (cooperative as any).planVersion();
  });
  afterEach(async () => {
    for (const release of releases) release();
    controller.abort(); await Promise.allSettled(pending); await cooperative.stop();
    expect(host.createSession).not.toHaveBeenCalled();
    vi.restoreAllMocks(); fs.rmSync(directory, { recursive: true, force: true });
  });

  it('advances the edit cursor and allows independent work while keeping a revalidated dependency unavailable', async () => {
    await integrateA();
    const gate = gateCheck();
    await edit('describe-a', task => task.id === 'a' ? { ...task, revision: 1, objective: 'Clarify the same theorem.' } : task);
    await gate.entered;
    expect(gate.heldAtEntry()).toBe(false);
    expect(node('a').pendingValidation).toMatchObject({ taskDigest: taskVersion(node('a').task), proof: true });
    expect(state.cooperation!.cursors!.edits).toBe(fs.statSync(path.join(directory, 'edits.jsonl')).size);
    expect(taskDependenciesReady(node('b').task, state.cooperation!.tasks)).toBe(false);
    expect(directSolverModules.M3.ready(state.cooperation!.tasks, state.cooperation!.groups).map(item => item.task.id)).not.toContain('b');
    const independent = await cooperative.next(workers[3], budget);
    expect(independent).toMatchObject({ kind: 'task', task: { id: 'c' } });
    expect(cooperative.started(workers[3], independent!)).toBe(true);
    const waiting = node('b');
    waiting.assignment = { taskId: 'b', taskDigest: taskVersion(waiting.task), workerId: 'consumer', seedCommit: state.cooperation!.canonicalCommit! };
    expect(cooperative.started(workers[2], { kind: 'task', task: waiting.task, assignment: waiting.assignment })).toBe(false);
    await edit('pause-consumer', task => task.id === 'b' ? { ...task, status: 'paused' } : task);
    expect(state.cooperation!.edits).toContainEqual(expect.objectContaining({ id: 'pause-consumer', status: 'applied' }));
    gate.release(); await sync();
    expect(node('a').pendingValidation).toBeUndefined();
    expect(node('a').integratedCheck?.taskDigest).toBe(taskVersion(node('a').task));
    expect(state.cooperation!.edits!.every(item => !item.pendingSync)).toBe(true);
  });

  it.each(['type-spelling', 'conditional-flag', 'default-group', 'different-type', 'new-dependency'] as const)
  ('rechecks the saved canonical proof under a revised %s contract before accepting or blocking it', async change => {
    const previous = node('a');
    if (change === 'type-spelling') previous.task = { ...previous.task, type: 'forall n : Nat, True -> True' };
    if (change === 'conditional-flag') previous.task = { ...previous.task, conditional: true };
    if (change === 'default-group') previous.task = { ...previous.task, groupId: 'main' };
    previous.assignment = { ...previous.assignment!, taskDigest: taskVersion(previous.task) };
    await integrateA(change === 'type-spelling' ? 'by intro n h; exact h' : 'by trivial');
    const receipt = previous.integratedCheck!, canonical = state.cooperation!.canonicalCommit, independent = node('c');
    const gate = gateCheck();
    await edit('revise-proof-contract', task => task.id !== 'a' ? task
      : change === 'type-spelling' ? { ...task, type: '∀ n : Nat, True → True' }
      : change === 'conditional-flag' ? { ...task, conditional: undefined }
      : change === 'default-group' ? { ...task, groupId: undefined }
      : change === 'different-type' ? { ...task, type: 'False' } : { ...task, dependsOn: ['c'] });
    await gate.entered;
    expect(node('a')).toBe(previous);
    expect(previous.pendingValidation).toMatchObject({ proof: true, taskDigest: taskVersion(previous.task) });
    expect(previous.integratedCheck).toBe(receipt);
    expect(previous.integratedCheck!.taskDigest).not.toBe(taskVersion(previous.task));
    expect(taskDependenciesReady(node('b').task, state.cooperation!.tasks)).toBe(false);
    expect(host.verify.mock.calls.at(-1)![1]).toMatchObject({ expectedDeclarationType: previous.task.type });
    expect(node('c')).toBe(independent); expect(independent.status).toBe('pending');
    expect(independent.pendingValidation).toBeUndefined(); expect(independent.attempts).toBe(0);
    gate.release(change !== 'different-type'); await sync();
    expect(previous.pendingValidation).toBeUndefined();
    expect(previous.attempts).toBe(1);
    expect(state.cooperation!.canonicalCommit).toBe(canonical);
    expect(previous.integratedCheck).not.toBe(receipt);
    expect(previous.integratedCheck!.taskDigest).toBe(taskVersion(previous.task));
    if (change === 'different-type') {
      expect(previous.status).toBe('blocked'); expect(previous.integratedCheck!.passed).toBe(false);
    } else if (change === 'new-dependency') {
      expect(previous).toMatchObject({ status: 'blocked', feedback: 'math_task_dependency_invalidated' });
    } else {
      expect(previous.status).toBe('integrated'); expect(previous.feedback).toBeUndefined();
      expect(hasTaskAcceptance(previous.integratedCheck!)).toBe(true);
    }
    expect(node('c')).toBe(independent); expect(independent.status).toBe('pending');
    expect(independent.pendingValidation).toBeUndefined(); expect(independent.attempts).toBe(0);
  });

  it('resets a renamed declaration without trying to revalidate it as the old theorem', async () => {
    await integrateA();
    const previous = node('a'), receipt = previous.integratedCheck;
    host.verify.mockClear();
    await edit('rename-helper', task => task.id === 'a' ? { ...task, theoremName: 'Tutorial.renamed' } : task);
    await sync();
    expect(node('a')).not.toBe(previous);
    expect(node('a')).toMatchObject({ status: 'pending', attempts: 1 });
    expect(node('a').pendingValidation).toBeUndefined(); expect(node('a').integratedCheck).toBeUndefined();
    expect(state.cooperation!.history).toContainEqual(expect.objectContaining({ integratedCheck: receipt }));
    expect(host.verify).not.toHaveBeenCalled();
  });

  it('reclaims a stale Lead while preserving integrated proof and active peer work and waking a waiting peer', async () => {
    await integrateA();
    const acceptedProof = structuredClone(node('a').proof), acceptedCheck = structuredClone(node('a').integratedCheck);
    const running = await cooperative.next(workers[3], budget);
    expect(running).toMatchObject({ kind: 'task', task: { id: 'c' } });
    expect(cooperative.started(workers[3], running!)).toBe(true);
    const peerInterrupt = vi.fn(async () => {});
    cooperative.activate(workers[3], running!, peerInterrupt, async () => {});
    const peerAssignment = node('c').assignment;
    const oldLead: CooperativeAction = { kind: 'lead', seedCommit: state.cooperation!.canonicalCommit!,
      planVersion: state.cooperation!.planVersion! };
    const leadInterrupt = vi.fn(async () => {});
    cooperative.activate(workers[0], oldLead, leadInterrupt, async () => {});
    const oldPlan = state.cooperation!.tasks.map(item => item.task);

    const waiting = track(cooperative.next(workers[1], budget));
    const task: CooperativeTask = { id: 'new_frontier', ownerId: 'author', kind: 'lemma',
      objective: 'Prove the newly identified independent frontier lemma.', proofPath: 'Submission.lean',
      theoremName: 'Tutorial.new_frontier', type: 'True', dependsOn: [], revision: 0 };
    fs.appendFileSync(path.join(directory, 'edits.jsonl'), JSON.stringify({ id: 'add-frontier',
      baseVersion: state.cooperation!.planVersion,
      tasks: [...state.cooperation!.tasks.map(item => item.task), task],
      groups: state.cooperation!.groups!.map(item => item.group) }) + '\n');
    await cooperative.pulse(workers[0].id);
    const assigned = await waiting;

    expect(assigned).toMatchObject({ kind: 'task', task: { id: 'new_frontier' }, assignment: { workerId: 'author' } });
    expect(node('a').status).toBe('integrated');
    expect(node('a').proof).toEqual(acceptedProof);
    expect(node('a').integratedCheck).toEqual(acceptedCheck);
    expect(node('c').status).toBe('running');
    expect(node('c').assignment).toBe(peerAssignment);
    expect(cooperative.current(running!)).toBe(true);
    expect(peerInterrupt).not.toHaveBeenCalled();
    expect(leadInterrupt).toHaveBeenCalledOnce();
    expect(cooperative.current(oldLead)).toBe(false);
    expect(cooperative.started(workers[0], oldLead)).toBe(false);

    // An interrupted session can still flush its old response; it must not replace the accepted graph.
    const version = state.cooperation!.planVersion;
    fs.writeFileSync(path.join(workspace, 'RESEARCH.md'), '```math-plan\n' + JSON.stringify({
      tasks: oldPlan, groups: state.cooperation!.groups!.map(item => item.group),
    }) + '\n```\n');
    cooperative.deactivate(workers[0]);
    await cooperative.deliver(workers[0], oldLead, commitSolverSources(problem, workspace));
    expect(state.cooperation!.planVersion).toBe(version);
    expect(node('new_frontier').assignment).toBe(assigned!.kind === 'task' ? assigned!.assignment : undefined);
    expect(events.some(item => item.event === 'lead_decision_superseded')).toBe(true);
    const freshLead = await cooperative.next(workers[0], budget);
    expect(freshLead).toMatchObject({ kind: 'lead', planVersion: version });
    expect(cooperative.current(freshLead!)).toBe(true);
    expect(leadInterrupt).toHaveBeenCalledOnce();
  });

  it.each([true, false])('discards an obsolete %s recheck after a mathematical revision without publishing a failure', async passed => {
    await integrateA(); const gate = gateCheck();
    const prepare = vi.spyOn(cooperative as any, 'prepareStatementContexts').mockReturnValue(undefined);
    await edit('old-description', task => task.id === 'a' ? { ...task, revision: 1, objective: 'Describe a.' } : task);
    await gate.entered;
    await edit('new-mathematics', task => task.id === 'a' ? { ...task, revision: 2, type: 'True ∧ True' } : task);
    const current = node('a'), saved = JSON.parse(JSON.stringify(current));
    const latest = gateCheck();
    gate.release(passed); await latest.entered;
    expect(node('a')).toBe(current); expect(node('a')).toEqual(saved);
    expect(node('a').pendingValidation).toMatchObject({ taskDigest: taskVersion(node('a').task), proof: true });
    expect(taskDependenciesReady(node('b').task, state.cooperation!.tasks)).toBe(false);
    expect(host.verify.mock.calls.at(-1)![1]).toMatchObject({ expectedDeclarationType: 'True ∧ True' });
    latest.release(false); await sync();
    expect(node('a').pendingValidation).toBeUndefined();
    expect(node('a')).toMatchObject({ status: 'blocked', integratedCheck: { passed: false, taskDigest: taskVersion(node('a').task) } });
    expect(prepare.mock.calls.some(([tasks]) => tasks.some((item: { task: CooperativeTask }) =>
      item.task.id === 'a' && item.task.revision === 1))).toBe(false);
    expect(prepare.mock.calls.some(([tasks]) => tasks.some((item: { task: CooperativeTask }) =>
      item.task.id === 'a' && item.task.revision === 2))).toBe(true);
    expect(state.cooperation!.deliveries?.some(item => item.kind === 'failure' || item.status === 'failed')).not.toBe(true);
    expect(events.some(item => item.event === 'delivery_rejected')).toBe(false);
  });

  it.each(['passed', 'failed', 'rejected', 'unavailable'] as const)('stops obsolete rechecks after an in-flight %s result settles', async result => {
    await integrateA();
    const tasks = ['a', 'b', 'c'].map(id => ({ ...node(id), status: 'integrated' as const, integratedCheck: undefined }));
    const baseline = structuredClone(tasks);
    const entered = deferred<void>(), release = deferred<void>();
    releases.push(() => release.resolve());
    const receipt = { ...node('a').proof!, passed: result === 'passed' };
    const check = vi.spyOn(cooperative as any, 'check').mockImplementationOnce(async () => {
      entered.resolve(); await release.promise;
      if (result === 'unavailable') throw new Error('math_verifier_unavailable');
      if (result === 'rejected') throw new Error('math_task_missing_declaration');
      return receipt;
    }).mockResolvedValue(receipt);
    let current = true;
    const rechecking = track((cooperative as any).recheckIntegrated(state.cooperation!.canonicalCommit!, true, {
      tasks, ids: new Set(tasks.map(item => item.task.id)), environment: {}, environmentDigest: state.environmentDigest,
      current: () => current,
    }) as Promise<boolean>);
    await entered.promise; current = false; release.resolve();
    if (result === 'unavailable') await expect(rechecking).rejects.toThrow('math_verifier_unavailable');
    else await rechecking;
    expect(check.mock.calls.map(([task]) => task.id)).toEqual(['a']);
    if (result !== 'unavailable') await expect(rechecking).resolves.toBe(false);
    expect(tasks).toEqual(baseline);
    expect(events.filter(item => item.event === 'task_recheck_finished')).toHaveLength(0);
    expect(state.cooperation!.recheck).toMatchObject({ completed: 0, taskId: 'a' });
    expect((cooperative as any).failure).toBeUndefined();
  });

  it('keeps newer progress when an identical task receives a new validation identity', async () => {
    await integrateA();
    const saved: { progress: NonNullable<NonNullable<SolverRunState['cooperation']>['recheck']>; locked: boolean }[] = [];
    vi.spyOn((cooperative as any).input, 'save').mockImplementation(() => {
      const progress = state.cooperation!.recheck;
      if (progress) saved.push({ progress: { ...progress }, locked: lockHeld });
    });
    const gate = gateCheck();
    await edit('describe-for-progress', task => task.id === 'a' ? { ...task, revision: 1, objective: 'Describe a.' } : task);
    await gate.entered;
    expect(state.cooperation!.recheck).toMatchObject({ total: 1, completed: 0, taskId: 'a' });
    const previous = node('a').pendingValidation!;
    const newer = { ...previous, id: 'new-validation-for-identical-mathematics' };
    const newerProgress = { ...state.cooperation!.recheck! };
    await exclusive(async () => {
      node('a').pendingValidation = newer;
      state.cooperation!.recheck = newerProgress;
    });
    expect(newer.taskDigest).toBe(previous.taskDigest);
    const prepared = deferred<void>(), release = deferred<void>();
    releases.push(() => release.resolve());
    const recheck = (cooperative as any).recheckIntegrated.bind(cooperative);
    vi.spyOn(cooperative as any, 'recheckIntegrated').mockImplementationOnce(async (...args) => {
      prepared.resolve(); await release.promise; return recheck(...args);
    });
    const savesBeforeCompletion = saved.length;
    gate.release(); await prepared.promise;
    expect(state.cooperation!.recheck).toBe(newerProgress);
    expect(saved).toHaveLength(savesBeforeCompletion);
    expect(node('a').pendingValidation).toBe(newer);
    release.resolve(); await sync();
    expect(state.cooperation!.recheck).toMatchObject({ total: 1, completed: 1 });
    expect(node('a').pendingValidation).toBeUndefined();
    expect(saved.every(item => item.locked)).toBe(true);
    expect(saved.some(item => item.progress.completed === 1)).toBe(true);
  });

  it('keeps every target pending when only one validation identity changes during a shared snapshot', async () => {
    await integrateA();
    const action = await cooperative.next(workers[3], budget);
    expect(action).toMatchObject({ kind: 'task', task: { id: 'c' } });
    await cooperative.deliver(workers[3], action!, writeLemma(workers[3], 'c'));
    const gate = gateCheck();
    const prepare = vi.spyOn(cooperative as any, 'prepareStatementContexts').mockReturnValue(undefined);
    await edit('describe-independent-pair', task => ['a', 'c'].includes(task.id)
      ? { ...task, revision: 1, objective: `Clarify ${task.id}.` } : task);
    await gate.entered;
    const first = node('a').pendingValidation!, second = { ...node('c').pendingValidation!, id: 'newer-c-validation' };
    const checks = [node('a').integratedCheck, node('c').integratedCheck];
    await exclusive(async () => { node('c').pendingValidation = second; });
    const entered = deferred<void>(), release = deferred<void>(); releases.push(() => release.resolve());
    const recheck = (cooperative as any).recheckIntegrated.bind(cooperative);
    vi.spyOn(cooperative as any, 'recheckIntegrated').mockImplementationOnce(async (...args) => {
      entered.resolve(); await release.promise; return recheck(...args);
    });
    const calls = host.verify.mock.calls.length;
    gate.release(); await entered.promise;
    expect(host.verify.mock.calls).toHaveLength(calls);
    expect(node('a').pendingValidation).toBe(first); expect(node('c').pendingValidation).toBe(second);
    expect(node('a').integratedCheck).toBe(checks[0]); expect(node('c').integratedCheck).toBe(checks[1]);
    expect(prepare).not.toHaveBeenCalled();
    release.resolve(); await sync();
    for (const id of ['a', 'c']) {
      expect(node(id).pendingValidation).toBeUndefined();
      expect(node(id).integratedCheck?.taskDigest).toBe(taskVersion(node(id).task));
      expect(node(id).status).toBe('integrated');
    }
  });

  it('rebases validation after an independent proof integrates and retains both declarations', async () => {
    await integrateA(); const gate = gateCheck();
    const canonical = state.cooperation!.canonicalCommit!;
    const prepare = vi.spyOn(cooperative as any, 'prepareStatementContexts').mockReturnValue(undefined);
    await edit('describe-before-integration', task => task.id === 'a' ? { ...task, revision: 1, objective: 'Describe a.' } : task);
    const old = await gate.entered;
    const action = await cooperative.next(workers[3], budget);
    expect(action).toMatchObject({ kind: 'task', task: { id: 'c' } });
    await cooperative.deliver(workers[3], action!, writeLemma(workers[3], 'c'));
    expect(node('c').status).toBe('integrated');
    expect(source()).toContain('lemma c : True := by trivial');
    gate.release(); await sync();
    expect(node('a').pendingValidation).toBeUndefined();
    expect(node('a').status).toBe('integrated'); expect(node('c').status).toBe('integrated');
    expect(source()).toContain('lemma a : True := by trivial'); expect(source()).toContain('lemma c : True := by trivial');
    expect(prepare.mock.calls.some(([, commit]) => commit === canonical)).toBe(false);
    expect(events).toContainEqual(expect.objectContaining({ event: 'plan_recheck_rebased' }));
    expect(node('a').integratedCheck!.commit).not.toBe(old.targetCommit);
  });

  it('restores pending validation independently of an already advanced input cursor', async () => {
    await integrateA(); const oldGate = gateCheck();
    await edit('resume-description', task => task.id === 'a' ? { ...task, revision: 1, objective: 'Describe a.' } : task);
    await oldGate.entered;
    const saved = JSON.parse(JSON.stringify(state));
    controller.abort(); oldGate.release(); await Promise.allSettled([(cooperative as any).planSynchronization]); await cooperative.stop();
    state = saved; controller = new AbortController(); cooperative = create();
    const gate = gateCheck(), restoring = track(cooperative.restore());
    await gate.entered;
    expect(gate.heldAtEntry()).toBe(false);
    expect(taskDependenciesReady(node('b').task, state.cooperation!.tasks)).toBe(false);
    expect(state.cooperation!.edits).toHaveLength(1);
    gate.release(); await restoring;
    expect(node('a').pendingValidation).toBeUndefined(); expect(node('a').status).toBe('integrated');
    expect(state.cooperation!.edits![0]).toMatchObject({ status: 'applied' });
    expect(state.cooperation!.edits![0].recheck!.tasks.find(item => item.taskId === 'a')!.status).toBe('passed');
    expect(state.cooperation!.edits![0].pendingSync).toBeUndefined();
    expect(state.cooperation!.history ?? []).toHaveLength(saved.cooperation.history?.length ?? 0);
    expect(state.cooperation!.cursors!.edits).toBe(fs.statSync(path.join(directory, 'edits.jsonl')).size);
  });

  it.each([true, false])('preserves a newer Lead draft after source validation (concurrent control: %s)', async control => {
    await integrateA();
    // Legacy receipts without a reference footprint must be checked after source changes.
    delete node('a').integratedCheck!.references;
    const canonical = state.cooperation!.canonicalCommit!;
    // A Lead journal makes its source seed a distinct commit even within one clock tick.
    fs.writeFileSync(path.join(workspace, 'RESEARCH.md'), 'Lead journal before canonical source synchronization.\n');
    commitSolverSources(problem, workspace);
    const seed = (cooperative as any).seed(workers[0], canonical) as string;
    expect(seed).not.toBe(canonical);
    writeLeadPlan();
    const commit = writeLemma(workers[0], 'lead_helper');
    const action: CooperativeAction = { kind: 'lead', seedCommit: seed, planVersion: state.cooperation!.planVersion };
    const gate = gateCheck(), delivery = track(cooperative.deliver(workers[0], action, commit));
    await gate.waitFor(delivery);
    expect(gate.heldAtEntry()).toBe(false);
    if (control) await edit('pause-during-lead-check', task => task.id === 'b' ? { ...task, status: 'paused' } : task);
    const newerDraft = writeLemma(workers[0], 'newer_draft');
    gate.release(); await delivery; await sync();
    expect(git(workspace, ['rev-parse', 'HEAD'])).toBe(newerDraft);
    expect(fs.readFileSync(path.join(workspace, problem.projectRelative, 'Submission.lean'), 'utf8')).toContain('lemma newer_draft');
    expect(source()).toContain('lemma lead_helper');
    expect(source()).not.toContain('lemma newer_draft');
    if (control) {
      expect(node('b').task.status).toBe('paused');
      expect(state.cooperation!.edits!.find(item => item.id === 'pause-during-lead-check')!.status).toBe('applied');
    }
  });

  it('persists a preparation failure after accepting an edit and retries it on restore without replaying the plan', async () => {
    await integrateA();
    const error = Object.assign(new Error('Statement context storage EIO'), { code: 'EIO' });
    vi.spyOn(cooperative as any, 'prepareStatementContexts').mockRejectedValueOnce(error);
    await edit('statement-preparation-retry', task => task.id === 'a' ? { ...task, statementReview: true, informalStatement: 'True.' } : task);
    await expect(sync()).rejects.toBe(error);
    expect(node('a').pendingValidation).toBeDefined();
    expect(state.cooperation!.edits![0]).toMatchObject({ status: 'applied', pendingSync: true });
    const saved = JSON.parse(JSON.stringify(state));
    expect(saved.cooperation.cursors.edits).toBe(fs.statSync(path.join(directory, 'edits.jsonl')).size);
    expect(events.some(item => item.event === 'edit_rejected')).toBe(false);
    controller.abort(); await cooperative.stop();
    state = saved; controller = new AbortController(); cooperative = create();
    vi.spyOn(cooperative as any, 'prepareStatementContexts').mockReturnValue(undefined);
    const accept = vi.spyOn(cooperative as any, 'acceptPlan');
    await cooperative.restore(); await cooperative.pulse();
    expect(accept.mock.calls.every(([, appliedEdit]) => appliedEdit === undefined)).toBe(true);
    expect(node('a').pendingValidation).toBeUndefined();
    expect(state.cooperation!.edits).toHaveLength(1);
    expect(state.cooperation!.history ?? []).toHaveLength(saved.cooperation.history?.length ?? 0);
    expect(state.cooperation!.edits![0]).toMatchObject({ status: 'applied' });
    expect(state.cooperation!.edits![0].pendingSync).toBeUndefined();
    expect(state.cooperation!.statementReviews).toContainEqual(expect.objectContaining({ taskId: 'a', status: 'pending' }));
  });

  it('allows independent work and another edit while preparing a fixed statement context', async () => {
    await integrateA();
    const entered = deferred<void>(), release = deferred<void>();
    releases.push(() => release.resolve());
    vi.spyOn(cooperative as any, 'prepareStatementContexts').mockImplementationOnce(() => {
      expect(lockHeld).toBe(false); entered.resolve(); return release.promise;
    }).mockReturnValue(undefined);
    await edit('prepare-statement', task => task.id === 'a' ? { ...task, statementReview: true, informalStatement: 'True.' } : task);
    await entered.promise;
    expect(node('a').pendingValidation).toBeDefined();
    expect(taskDependenciesReady(node('b').task, state.cooperation!.tasks)).toBe(false);
    const independent = await cooperative.next(workers[3], budget);
    expect(independent).toMatchObject({ kind: 'task', task: { id: 'c' } });
    await edit('control-during-statement', task => task.id === 'b' ? { ...task, status: 'paused' } : task);
    expect(state.cooperation!.edits!.find(item => item.id === 'control-during-statement')!.status).toBe('applied');
    release.resolve(); await sync();
    expect(node('a').pendingValidation).toBeUndefined();
    expect(state.cooperation!.statementReviews).toContainEqual(expect.objectContaining({ taskId: 'a', status: 'pending' }));
  });

  it('skips obsolete statement preparation after waiting for an earlier preparation to settle', async () => {
    await integrateA();
    const tasks = state.cooperation!.tasks.map(item => ({ ...item, task: item.task.id === 'a'
      ? { ...item.task, statementReview: true, informalStatement: 'True.' } : item.task }));
    const release = deferred<void>(); releases.push(() => release.resolve());
    const earlier = release.promise.finally(() => { (cooperative as any).preparingStatements = undefined; });
    (cooperative as any).preparingStatements = earlier;
    let current = true;
    const preparing = track((cooperative as any).prepareStatementContexts(tasks, state.cooperation!.canonicalCommit!, {
      environment: {}, digest: state.environmentDigest, current: () => current,
    }) as Promise<void>);
    expect(host.captureStatements).not.toHaveBeenCalled();
    current = false; release.resolve();
    await preparing;
    expect(host.captureStatements).not.toHaveBeenCalled();
    expect((cooperative as any).preparingStatementTasks.size).toBe(0);
    expect((cooperative as any).preparingStatements).toBeUndefined();
  });

  it('integrates a previously delivered consumer once its source dependency finishes validation', async () => {
    await integrateA();
    const consumer = await cooperative.next(workers[2], budget);
    expect(consumer).toMatchObject({ kind: 'task', task: { id: 'b' } });
    const consumerCommit = writeLemma(workers[2], 'b');
    const canonical = state.cooperation!.canonicalCommit!;
    const seed = (cooperative as any).seed(workers[0], canonical) as string;
    writeLeadPlan();
    delete node('a').integratedCheck!.references;
    const commit = writeLemma(workers[0], 'lead_helper');
    const gate = gateCheck(), delivery = track(cooperative.deliver(workers[0], {
      kind: 'lead', seedCommit: seed, planVersion: state.cooperation!.planVersion,
    }, commit));
    await gate.waitFor(delivery);
    await cooperative.deliver(workers[2], consumer!, consumerCommit);
    expect(node('b').status).toBe('delivered');
    expect(source()).not.toContain('lemma b : True := by trivial');
    gate.release(); await delivery; await sync();
    expect(node('b').status).toBe('integrated'); expect(source()).toContain('lemma b : True := by trivial');
    expect(state.cooperation!.deliveries!.filter(item => item.taskId === 'b' && item.kind === 'proof' && item.status === 'verified')).toHaveLength(1);
  });
});
