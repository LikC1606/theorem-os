import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { CooperativeResearch } from '../src/solver/cooperation';
import { ownedSourceDigest, type TaskProof } from '../src/solver/cooperativeProof';
import { directSolverModules } from '../src/solver/modules';
import type { ResearchWorker } from '../src/solver/modules/organization';
import { markTaskAcceptance, taskVersion, type CooperativeAction, type CooperativeTask, type TaskAssignment, type TaskRecord } from '../src/solver/tasks';
import type { SolverRunState } from '../src/solver/archive';
import { git, type SolverProblem } from '../src/solver/problem';
import { hashMathFormalSourceDeclaration } from '../src/math/leanSource';

const task = (id: string, kind: CooperativeTask['kind'] = 'lemma', dependsOn: string[] = []): CooperativeTask => ({
  id, kind, objective: id, revision: 0, dependsOn,
  ...(['lemma', 'goal'].includes(kind) ? { proofPath: 'Submission.lean', theoremName: id, type: 'True' } : {}),
});
const budget = { maxTurns: Infinity, remainingMs: Infinity };
const missing = 'math_task_missing_declaration\nThe assigned theorem is absent; no Lean check started.';

describe('persistent typed delivery failure guards', () => {
  let directory: string, seed: string, candidate: TaskRecord, state: SolverRunState;
  let lead: ResearchWorker, researcher: ResearchWorker, cooperative: CooperativeResearch;
  let action: Extract<CooperativeAction, { kind: 'task' }>;
  let checker: ReturnType<typeof vi.fn<typeof directSolverModules.M2.checkTask & {}>>;
  let emit: ReturnType<typeof vi.fn>;
  const instances: CooperativeResearch[] = [];
  const sourceFile = () => path.join(directory, 'generated/p/Submission.lean');
  const commit = (notes = 'Saved notes.') => {
    fs.writeFileSync(path.join(directory, 'RESEARCH.md'), notes);
    git(directory, ['add', '--', 'generated', 'RESEARCH.md']);
    git(directory, ['-c', 'user.name=Fixture', '-c', 'user.email=fixture@localhost', 'commit', '--no-gpg-sign', '--quiet', '--allow-empty', '-m', 'Saved candidate']);
    return git(directory, ['rev-parse', 'HEAD']);
  };
  const failure = (worktree: string, version: string, obligation: CooperativeTask, assignment: TaskAssignment,
    conditions: readonly CooperativeTask[] = []): TaskProof => ({
    commit: version, sourceDigest: ownedSourceDigest(state.problem, worktree, version), taskDigest: taskVersion(obligation),
    seedCommit: assignment.seedCommit, passed: false, changes: [], imports: [],
    conditions: conditions.map(task => ({ taskId: task.id, taskDigest: taskVersion(task) })),
    verification: { status: 'failed', targetCommit: version, results: [{ status: 'failed', targetCommit: version,
      error: 'Lean exited with status 1.', stdoutPreview: 'Submission.lean:1:1: error: Unknown identifier FAILURE' }] },
  } as TaskProof);
  const create = (restored = state) => {
    const instance = new CooperativeResearch({ state: restored, workers: [lead, researcher],
      access: new Map([[lead.id, { environment: {} } as any]]), signal: new AbortController().signal,
      save: () => {}, emit, exclusiveCheck: async check => check(),
      modules: { ...directSolverModules, M2: { ...directSolverModules.M2, checkTask: checker } } });
    vi.spyOn(instance as any, 'seed').mockReturnValue(seed);
    instances.push(instance); return instance;
  };
  const check = (version = seed, conditions?: readonly CooperativeTask[], instance = cooperative) =>
    (instance as any).check(candidate.task, candidate.assignment, directory, version, conditions, undefined, true) as Promise<TaskProof>;
  const exhaustRepair = async () => {
    await cooperative.deliver(researcher, action, seed);
    const repair = await cooperative.next(researcher, budget);
    expect(repair).toMatchObject({ kind: 'task', task: { id: candidate.task.id } });
    if (repair?.kind !== 'task') throw new Error('expected_local_repair');
    expect(cooperative.started(researcher, repair)).toBe(true);
    await cooperative.deliver(researcher, repair, seed);
    expect(candidate.status).toBe('blocked');
    return repair;
  };
  beforeEach(() => {
    directory = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'repeated-delivery-')));
    fs.mkdirSync(path.join(directory, 'generated/p'), { recursive: true });
    fs.writeFileSync(sourceFile(), 'lemma candidate : True := by exact FAILURE\n');
    fs.writeFileSync(path.join(directory, 'generated/p/notes.txt'), 'Advisory material.');
    git(directory, ['init', '--quiet']); seed = commit();
    lead = { id: 'lead', role: 'lead', worktree: directory, ownedFiles: ['Submission.lean', 'notes.txt'] };
    researcher = { ...lead, id: 'researcher', role: 'researcher' };
    candidate = { task: task('candidate'), status: 'running', attempts: 1,
      assignment: { taskId: 'candidate', taskDigest: taskVersion(task('candidate')), workerId: 'researcher', seedCommit: seed } };
    state = { runId: 'fixture', turns: 0, environmentDigest: 'environment', buildDigest: 'build', evaluatorDigest: 'evaluator',
      // Keep this goal prerequisite-first so dispatches exercise the candidate's local repair.
      cooperation: { canonicalCommit: seed, tasks: [candidate,
        { task: { ...task('goal', 'goal', ['candidate']), conditional: false }, status: 'pending', attempts: 0 }],
        groups: [{ group: { id: 'main', objective: 'Original goal', status: 'active', revision: 0 }, turns: 0 }] },
      problem: { receiptDigest: 'problem', projectRelative: 'generated/p', ownedFiles: lead.ownedFiles,
        declarations: { 'Submission.lean': [] }, targets: [{ proofPath: 'Submission.lean', theoremName: 'goal' }],
        trustedFiles: {}, baseCommit: seed, sourceStructure: {}, sourceImports: {},
        contract: { assumptions: [], formalStatement: 'Original goal.' } } as unknown as SolverProblem } as SolverRunState;
    checker = vi.fn(async (_problem, worktree, version, obligation, assignment, _goals, _environment, _signal, _timeout, conditions = []) =>
      failure(worktree, version, obligation, assignment, conditions));
    emit = vi.fn(); cooperative = create();
    action = { kind: 'task', task: candidate.task, assignment: candidate.assignment! };
  });
  afterEach(async () => {
    for (const instance of instances.splice(0)) await instance.stop();
    vi.restoreAllMocks(); fs.rmSync(directory, { recursive: true, force: true });
  });

  it.each(['notes', 'owned-non-Lean'] as const)('skips a repeated deterministic failure after a %s commit', async change => {
    await check();
    if (change === 'owned-non-Lean') fs.writeFileSync(path.join(directory, 'generated/p/notes.txt'), 'Different prose.');
    const version = commit('A new explanation of the unchanged proof.');
    await expect(check(version)).rejects.toThrow('math_task_repeated_failed_input');
    expect(checker).toHaveBeenCalledTimes(1);
    expect(state.cooperation!.failedTaskInputs).toHaveLength(1);
  });

  it('retains the repair grant through next and release, and consumes it only at started', async () => {
    checker.mockRejectedValue(new Error(missing));
    await cooperative.deliver(researcher, action, seed);
    const failed = state.cooperation!.failedTaskInputs![0];
    expect(candidate.status).toBe('pending'); expect(failed.repair?.pending).toBe(true);
    let repair = await cooperative.next(researcher, budget);
    expect(repair).toMatchObject({ kind: 'task', task: { id: candidate.task.id } }); expect(failed.repair?.pending).toBe(true);
    if (repair?.kind !== 'task') throw new Error('expected_local_repair');
    cooperative.release(researcher, repair);
    expect(candidate.attempts).toBe(1); expect(failed.repair?.pending).toBe(true);
    repair = await cooperative.next(researcher, budget);
    expect(repair).toMatchObject({ kind: 'task', task: { id: candidate.task.id } });
    if (repair?.kind !== 'task') throw new Error('expected_reserved_repair');
    expect(cooperative.started(researcher, repair)).toBe(true);
    expect(failed.repair?.pending).toBe(false); expect(candidate.attempts).toBe(2);
    await cooperative.deliver(researcher, repair, seed);
    expect(candidate.status).toBe('blocked'); expect(checker).toHaveBeenCalledTimes(1);
  });

  it.each(['transport', 'restart'] as const)('preserves an uncompleted repair after %s before a source edit', async interruption => {
    await cooperative.deliver(researcher, action, seed);
    let work = await cooperative.next(researcher, budget);
    expect(work).toMatchObject({ kind: 'task', task: { id: candidate.task.id } });
    if (work?.kind !== 'task') throw new Error('expected_local_repair');
    expect(cooperative.started(researcher, work)).toBe(true);
    let current = cooperative, currentState = state;
    if (interruption === 'restart') {
      currentState = JSON.parse(JSON.stringify(state)) as SolverRunState;
      current = create(currentState); await current.restore();
    } else await current.deliver(researcher, work, seed, true, 'request-failure');
    expect(currentState.cooperation!.failedTaskInputs![0].repair?.pending).toBe(true);
    work = await current.next(researcher, budget);
    expect(work).toMatchObject({ kind: 'task', task: { id: candidate.task.id } });
    if (work?.kind !== 'task') throw new Error('expected_resumed_repair');
    expect(current.started(researcher, work)).toBe(true);
    await current.deliver(researcher, work, seed);
    expect(currentState.cooperation!.tasks[0].status).toBe('blocked');
    expect(currentState.cooperation!.failedTaskInputs![0].repair).toMatchObject({ pending: false });
    expect(currentState.cooperation!.failedTaskInputs![0].repair?.startedAttempt).toBeUndefined();
    expect(checker).toHaveBeenCalledTimes(1);
  });

  it.each(['checkpoint', 'request-failure'] as const)('continues successive changed drafts after %s without a turn limit', async kind => {
    let work = action, version = seed;
    for (let index = 0; index < 4; index++) {
      fs.writeFileSync(sourceFile(), `lemma candidate : True := by exact FAILURE_${index}\n`); version = commit();
      await cooperative.deliver(researcher, work, version, true, kind);
      expect(candidate.status).toBe('pending');
      const next = await cooperative.next(researcher, budget);
      expect(next).toMatchObject({ kind: 'task', task: { id: candidate.task.id } });
      if (next?.kind !== 'task') throw new Error('expected_changed_draft_continuation');
      expect(cooperative.started(researcher, next)).toBe(true); work = next;
    }
    expect(candidate.attempts).toBe(5); expect(checker).toHaveBeenCalledTimes(4);
    await cooperative.deliver(researcher, work, version, true, 'checkpoint');
    expect(candidate.status).toBe('blocked'); expect(checker).toHaveBeenCalledTimes(4);
  });

  it('restores the first repair after failure persistence before delivery publication', async () => {
    await check();
    const restored = JSON.parse(JSON.stringify(state)) as SolverRunState;
    delete restored.cooperation!.failedTaskInputs![0].repair;
    const resumed = create(restored); await resumed.restore();
    expect(restored.cooperation!.failedTaskInputs![0].repair?.pending).toBe(true);
    const work = await resumed.next(researcher, budget);
    expect(work).toMatchObject({ kind: 'task', task: { id: 'candidate' } });
    expect(checker).toHaveBeenCalledTimes(1);
  });

  it('keeps one repair after duplicate live proof receipts and completed delivery', async () => {
    const submission = { id: 'first', kind: 'proof', taskId: candidate.task.id, taskDigest: action.assignment.taskDigest,
      commit: seed, summary: 'The saved candidate.' };
    await (cooperative as any).receive(researcher, action, submission);
    await (cooperative as any).receive(researcher, action, { ...submission, id: 'second' });
    await cooperative.deliver(researcher, action, seed);
    expect(candidate.status).toBe('pending'); expect(candidate.attempts).toBe(1);
    expect(state.cooperation!.failedTaskInputs![0].repair?.pending).toBe(true);
    expect(checker).toHaveBeenCalledTimes(1);
  });

  it('blocks a revision, prose and missing-helper rename before dispatch while independent research remains ready', async () => {
    fs.writeFileSync(sourceFile(), 'theorem goal : True := by sorry\n'); seed = commit();
    state.cooperation!.canonicalCommit = seed; candidate.assignment!.seedCommit = seed;
    checker.mockRejectedValue(new Error(missing)); await exhaustRepair();
    candidate.task = { ...candidate.task, id: 'renamed', theoremName: 'new_helper', revision: 7, objective: 'A different description.' };
    candidate.status = 'pending'; candidate.attempts = 0; candidate.assignment = undefined; candidate.proof = undefined;
    state.cooperation!.tasks[1].task = task('goal', 'goal', ['renamed']);
    state.cooperation!.tasks.push({ task: task('investigate', 'research'), status: 'pending', attempts: 0 });
    const work = await cooperative.next(researcher, budget);
    expect(work).toMatchObject({ kind: 'task', task: { id: 'investigate' } });
    expect(candidate.status).toBe('blocked'); expect(candidate.attempts).toBe(0);
    expect(checker).toHaveBeenCalledTimes(1);
  });

  it('preserves failure and unused repair records across serialization and restore', async () => {
    await cooperative.deliver(researcher, action, seed);
    const restored = JSON.parse(JSON.stringify(state)) as SolverRunState, resumed = create(restored);
    await resumed.restore();
    const work = await resumed.next(researcher, budget);
    expect(work).toMatchObject({ kind: 'task', task: { id: 'candidate' } });
    if (work?.kind !== 'task') throw new Error('expected_restored_repair');
    expect(resumed.started(researcher, work)).toBe(true);
    await resumed.deliver(researcher, work, seed);
    expect(restored.cooperation!.tasks[0].status).toBe('blocked');
    expect(restored.cooperation!.failedTaskInputs![0].repair?.pending).toBe(false);
    expect(checker).toHaveBeenCalledTimes(1);
  });

  it('reopens a failed assignment after changed Lean bytes owned by its current session', async () => {
    await exhaustRepair();
    fs.writeFileSync(sourceFile(), 'lemma candidate : True := by exact NEW_ATTEMPT\n');
    const version = commit();
    const work = await cooperative.next(researcher, budget);
    expect(work).toMatchObject({ kind: 'task', task: { id: 'candidate' } });
    await check(version); expect(checker).toHaveBeenCalledTimes(2);
    expect(state.cooperation!.failedTaskInputs).toHaveLength(2);
  });

  it('does not reopen an old failure from a worktree reused for another task', async () => {
    await exhaustRepair();
    state.workers = [{ id: researcher.id, sessionTaskId: 'different', sessionTaskVersion: 'different' }] as SolverRunState['workers'];
    fs.writeFileSync(sourceFile(), 'lemma unrelated : True := by trivial\n'); commit();
    (cooperative as any).changed();
    expect(candidate.status).toBe('blocked'); expect(candidate.feedback).toContain('math_task_repeated_failed_input');
  });

  it.each(['premises', 'type', 'environment', 'environment-variable', 'build', 'evaluator', 'conditions'] as const)(
    'permits a new check after changed %s inputs', async change => {
      await check();
      if (change === 'premises') candidate.task = { ...candidate.task, premises: ['A new explicit premise.'] };
      else if (change === 'type') candidate.task = { ...candidate.task, type: '1 = 1' };
      else if (change === 'environment') state.environmentDigest = 'new-environment';
      else if (change === 'environment-variable') (cooperative as any).input.access.get(lead.id).environment.LEAN_PATH = '/new/path';
      else if (change === 'build') state.buildDigest = 'new-build';
      else if (change === 'evaluator') state.evaluatorDigest = 'new-evaluator';
      candidate.assignment!.taskDigest = taskVersion(candidate.task);
      await check(seed, change === 'conditions' ? [task('assumption')] : undefined);
      expect(checker).toHaveBeenCalledTimes(2);
    });

  it('does not reset a deterministic failure when only the checker timeout changes', async () => {
    await check(); (cooperative as any).input.timeoutMs = Infinity;
    await expect(check()).rejects.toThrow('math_task_repeated_failed_input');
    (cooperative as any).input.timeoutMs = 999;
    await expect(check()).rejects.toThrow('math_task_repeated_failed_input');
    expect(checker).toHaveBeenCalledTimes(1);
  });

  it('keeps recurrence stable after unrelated shell environment changes on restart', async () => {
    await check();
    Object.assign((cooperative as any).input.access.get(lead.id).environment, { PWD: '/other', SHLVL: '3', TERM: 'xterm' });
    await expect(check()).rejects.toThrow('math_task_repeated_failed_input');
    expect(checker).toHaveBeenCalledTimes(1);
  });

  const checkedDependency = () => {
    const dependency: TaskRecord = { task: task('dependency'), status: 'integrated', attempts: 1 };
    dependency.integratedCheck = { ...failure(directory, seed, dependency.task, candidate.assignment!), passed: true,
      changes: [{ file: 'Submission.lean', name: 'dependency', after: 'lemma dependency : True := by trivial\n' }],
      verification: { status: 'kernel_verified', targetCommit: seed,
        results: [{ status: 'kernel_verified', targetCommit: seed, receiptId: 'first' }] } } as TaskProof;
    markTaskAcceptance(dependency.integratedCheck);
    state.cooperation!.tasks.push(dependency); candidate.task = { ...candidate.task, dependsOn: ['dependency'] };
    candidate.assignment!.taskDigest = taskVersion(candidate.task);
    return dependency;
  };
  it('ignores dependency receipt replay and whole-file metadata but allows new checked declaration evidence', async () => {
    const dependency = checkedDependency(); await check();
    dependency.integratedCheck!.sourceDigest = 'unrelated-whole-file-change';
    dependency.integratedCheck!.verification.results[0].receiptId = 'replayed';
    markTaskAcceptance(dependency.integratedCheck!);
    await expect(check()).rejects.toThrow('math_task_repeated_failed_input');
    dependency.integratedCheck!.changes[0].after = 'lemma dependency : True := by exact True.intro\n';
    markTaskAcceptance(dependency.integratedCheck!);
    await check(); expect(checker).toHaveBeenCalledTimes(2);
  });

  it('does not treat loss of a fresh dependency acceptance after restart as new mathematical input', async () => {
    checkedDependency(); await check();
    const restored = JSON.parse(JSON.stringify(state)) as SolverRunState, resumed = create(restored);
    await expect(check(seed, undefined, resumed)).rejects.toThrow('math_task_repeated_failed_input');
    expect(checker).toHaveBeenCalledTimes(1);
  });

  it('keeps a failed OR branch blocked after assignment reset and permits a different checked branch', async () => {
    candidate.task = task('candidate', 'goal'); candidate.assignment!.taskDigest = taskVersion(candidate.task);
    action = { kind: 'task', task: candidate.task, assignment: candidate.assignment! };
    const branches = ['left', 'right'].map(id => {
      const record: TaskRecord = { task: task(id), status: 'integrated', attempts: 1 };
      record.integratedCheck = { ...failure(directory, seed, record.task, candidate.assignment!), passed: true,
        changes: [{ file: 'Submission.lean', name: id, after: `lemma ${id} : True := by trivial\n` }],
        verification: { status: 'kernel_verified', targetCommit: seed,
          results: [{ status: 'kernel_verified', targetCommit: seed, receiptId: id }] } } as TaskProof;
      markTaskAcceptance(record.integratedCheck); return record;
    });
    state.cooperation!.tasks.push(...branches);
    state.cooperation!.proofRoutes = branches.map(record => ({ id: `via_${record.task.id}`, targetTaskId: candidate.task.id,
      prerequisiteTaskIds: [], closingTaskId: record.task.id }));
    (cooperative as any).syncProofRoutes(); candidate.assignment!.routeId = 'via_left';
    await exhaustRepair();
    candidate.assignment = undefined; candidate.proof = undefined; candidate.status = 'pending';
    const research: TaskRecord = { task: task('investigate', 'research'), status: 'pending', attempts: 0 };
    state.cooperation!.tasks.push(research);
    const independent = await cooperative.next(researcher, budget);
    expect(independent).toMatchObject({ kind: 'task', task: { id: 'investigate' } });
    expect(candidate.status).toBe('blocked'); expect(checker).toHaveBeenCalledTimes(1);
    research.status = 'completed'; branches[0].status = 'blocked';
    const alternate = await cooperative.next(researcher, budget);
    expect(alternate).toMatchObject({ kind: 'task', task: { id: 'candidate' }, assignment: { routeId: 'via_right' } });
    expect(checker).toHaveBeenCalledTimes(1);
  });

  it('serializes identical in-flight candidates before persisting a deterministic failure', async () => {
    let release!: () => void;
    const pending = new Promise<void>(resolve => { release = resolve; });
    checker.mockImplementationOnce(async (_problem, worktree, version, obligation, assignment, _goals, _env, _signal, _timeout, conditions) => {
      await pending; return failure(worktree, version, obligation, assignment, conditions);
    });
    const first = check(), repeated = check(); release();
    const results = await Promise.allSettled([first, repeated]);
    expect(results.map(result => result.status)).toEqual(['fulfilled', 'rejected']);
    expect(checker).toHaveBeenCalledTimes(1);
  });

  it.each(['unavailable', 'blocked', 'cleanup', 'no-diagnostics'] as const)('does not persist %s verification as a mathematical failure', async kind => {
    checker.mockImplementation(async (_problem, worktree, version, obligation, assignment, _goals, _env, _signal, _timeout, conditions) => {
      const proof = failure(worktree, version, obligation, assignment, conditions);
      if (kind === 'unavailable' || kind === 'blocked') proof.verification.status = kind;
      else if (kind === 'cleanup') proof.verification.results[0].cleanupError = 'Temporary checkout unavailable.';
      else proof.verification.results[0].stdoutPreview = 'Request timed out before diagnostics.';
      return proof;
    });
    await check(); await check();
    expect(checker).toHaveBeenCalledTimes(2); expect(state.cooperation!.failedTaskInputs).toBeUndefined();
  });

  it.each(['sorry', 'admit'] as const)('persists an explicit %s rejection even without compiler diagnostics', async kind => {
    checker.mockImplementation(async (_problem, worktree, version, obligation, assignment, _goals, _env, _signal, _timeout, conditions) => {
      const proof = failure(worktree, version, obligation, assignment, conditions);
      proof.verification.results[0].stdoutPreview = undefined;
      proof.verification.results[0][kind === 'sorry' ? 'sorryCount' : 'admitCount'] = 1;
      return proof;
    });
    await check(); await expect(check()).rejects.toThrow('math_task_repeated_failed_input');
    expect(checker).toHaveBeenCalledTimes(1); expect(state.cooperation!.failedTaskInputs).toHaveLength(1);
  });

  it.each(['Invalid authentication', 'Request failed: rate limit', 'Request timed out'])(
    'ignores a transient verifier error even if a result retains diagnostics: %s', async error => {
      checker.mockImplementation(async (_problem, worktree, version, obligation, assignment, _goals, _env, _signal, _timeout, conditions) => {
        const proof = failure(worktree, version, obligation, assignment, conditions);
        proof.verification.results[0].error = error; return proof;
      });
      await check(); await check();
      expect(checker).toHaveBeenCalledTimes(2); expect(state.cooperation!.failedTaskInputs).toBeUndefined();
    });

  it.each(['Invalid authentication', '429 rate limit', 'stream disconnected before completion'])(
    'does not persist a transient request failure: %s', async message => {
      checker.mockRejectedValue(new Error(message));
      await expect(check()).rejects.toThrow(message); await expect(check()).rejects.toThrow(message);
      expect(checker).toHaveBeenCalledTimes(2); expect(state.cooperation!.failedTaskInputs).toBeUndefined();
    });

  it.each(['integrated', 'conditional', 'delivered', 'pending'] as const)('preserves a current passed proof in %s state', async status => {
    await check(); candidate.status = status;
    candidate.proof = { ...failure(directory, seed, candidate.task, candidate.assignment!), passed: true };
    (cooperative as any).changed();
    expect(candidate.status).toBe(status); expect(candidate.proof.passed).toBe(true);
  });

  it('allows a different already saved proof of the same type after a missing target', async () => {
    fs.writeFileSync(sourceFile(), 'lemma available : True := by trivial\n'); seed = commit();
    state.cooperation!.canonicalCommit = seed; candidate.assignment!.seedCommit = seed;
    checker.mockRejectedValueOnce(new Error(missing)); await cooperative.deliver(researcher, action, seed);
    candidate.task = { ...candidate.task, theoremName: 'available' };
    candidate.assignment!.taskDigest = taskVersion(candidate.task);
    expect(await cooperative.next(researcher, budget)).toMatchObject({ kind: 'task', task: { theoremName: 'available' } });
    checker.mockImplementation(async (_problem, worktree, version, obligation, assignment) => {
      const proof = failure(worktree, version, obligation, assignment), taskDigest = taskVersion(obligation);
      return { ...proof, passed: true, verification: { status: 'kernel_verified', targetCommit: version,
        results: [{ status: 'kernel_verified', targetCommit: version, proofPath: obligation.proofPath,
          theoremName: obligation.theoremName, statementHash: taskDigest, leanStatementHash: taskDigest, claim: 'statement',
          receiptId: 'checked-available-proof',
          sourceDeclarationHash: hashMathFormalSourceDeclaration(fs.readFileSync(sourceFile(), 'utf8'), obligation.theoremName!) }] } } as TaskProof;
    });
    const passed = await check();
    expect(passed.passed).toBe(true); expect(checker).toHaveBeenCalledTimes(2);
  });

  it('separates saved same-body targets with different namespace and notation contexts', async () => {
    fs.writeFileSync(sourceFile(), 'namespace Bad\nlocal notation "witness" => (0 : Nat)\n' +
      'lemma bad : True := by exact witness\nend Bad\nnamespace Good\n' +
      'local notation "witness" => True.intro\nlemma good : True := by exact witness\nend Good\n');
    seed = commit(); state.cooperation!.canonicalCommit = seed; candidate.assignment!.seedCommit = seed;
    candidate.task = { ...candidate.task, theoremName: 'Bad.bad' };
    candidate.assignment!.taskDigest = taskVersion(candidate.task);
    await check();
    candidate.task = { ...candidate.task, theoremName: 'Good.good' };
    candidate.assignment!.taskDigest = taskVersion(candidate.task);
    await check();
    expect(checker).toHaveBeenCalledTimes(2);
  });
});
