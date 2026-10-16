import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { canonicalMathProblemStatementPayloads, type MathProblemContract } from '../src/math/contracts';
import { LEAN_EVAL_BENCHMARK_COMMIT } from '../src/math/leanEvalCatalogAdapter';
import { mathDigest } from '../src/math/mathRuntimeIo';
import { hashMathFormalSourceDeclaration, type MathematicsVerifierBatchRequest,
  type MathematicsVerifierBatchResult, type MathematicsVerifierExecutionOptions } from '../src/math/verifier';
import { CooperativeResearch, parseCooperationPlan, taskVersion, type CooperativeAction,
  type CooperationState, type TaskAssignment, type TaskRecord } from '../src/solver/cooperation';
import { checkTaskProof } from '../src/solver/cooperativeProof';
import { directSolverModules } from '../src/solver/modules';
import { committedSource, commitSolverSources, git, readSolverProblem, type SolverProblem } from '../src/solver/problem';

const host = vi.hoisted(() => ({ verify: vi.fn(), open: vi.fn() }));
vi.mock('../src/math/verifier', async importOriginal => ({
  ...await importOriginal<typeof import('../src/math/verifier')>(),
  checkManyFormalVerifications: host.verify, resolveMathematicsLakePackagesCache: () => undefined,
}));
vi.mock('../src/runtime/codexSession', () => ({ createCodexMathSession: host.open }));

function verified(request: MathematicsVerifierBatchRequest): MathematicsVerifierBatchResult {
  const source = fs.readFileSync(path.join(request.projectRoot, 'Submission.lean'), 'utf8');
  const status = source.includes('sorry') ? 'failed' : 'kernel_verified';
  return { schema: 'deepscientist.mathematics.verification-batch/v1', status, targetCommit: request.targetCommit!,
    sessionId: 'fixture', events: [], startedAt: 1, checkedAt: 2, durationMs: 1,
    results: request.items.map(item => ({ ...item, sourceDeclarationHash: item.expectedSourceDeclarationHash,
      receiptId: `fixture-${request.targetCommit}-${item.theoremName}`, targetCommit: request.targetCommit,
      status, claim: 'statement' })) as MathematicsVerifierBatchResult['results'] };
}

function deferred() {
  let resolve!: () => void;
  const promise = new Promise<void>(done => { resolve = done; });
  return { promise, resolve };
}

describe('candidate prerequisite recovery', () => {
  let directory: string;
  let workspace: string;
  let peerRoot: string;
  let problem: SolverProblem;
  const original = 'namespace Submission\ndef fixed : Nat := 2\n' +
    'theorem first : True := by sorry\ntheorem second : True := by sorry\nend Submission\n';
  const withHelpers = (helpers: string) => original.replace('theorem first', `${helpers}theorem first`);

  beforeEach(() => {
    vi.clearAllMocks();
    host.verify.mockReset().mockImplementation(async request => verified(request));
    host.open.mockReset().mockImplementation(() => { throw new Error('unexpected_model_call'); });
    directory = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'math-candidate-recovery-')));
    workspace = path.join(directory, 'public'); peerRoot = path.join(directory, 'peer');
    const project = path.join(workspace, 'generated/p');
    fs.mkdirSync(project, { recursive: true }); fs.mkdirSync(`${workspace}.source`);
    fs.writeFileSync(path.join(project, 'Submission.lean'), original);
    fs.writeFileSync(path.join(project, 'Challenge.lean'), original);
    fs.writeFileSync(path.join(project, 'lean-toolchain'), 'leanprover/lean4:v4.31.0');
    fs.writeFileSync(path.join(project, 'lakefile.toml'), 'name = "proof"\n');
    const payload = canonicalMathProblemStatementPayloads({ informalStatement: 'Prove both claims', formalStatement: original, assumptions: [] });
    const contract: MathProblemContract = { problemId: 'p', informalStatement: 'Prove both claims', formalStatement: original,
      assumptions: [], knownTraps: [], acceptanceCriteria: ['Both original targets'], officialVerificationCommand: 'lake test',
      statementHash: mathDigest(payload.informal), leanStatementHash: mathDigest(payload.lean) };
    const receipt = { schema: 'deepscientist.mathematics.lean-eval-bootstrap-receipt.v1', receiptId: 'fixture', problemId: 'p',
      benchmarkCommit: LEAN_EVAL_BENCHMARK_COMMIT, catalogHash: 'a'.repeat(64), leaderboardSource: 'disabled', contract,
      workspaceRoot: workspace, projectRoot: project, sourceProjectRoot: `${workspace}.source`,
      activeProblemPath: path.join(workspace, 'active-problem.json'), createdAt: 1,
      trustedFiles: ['Challenge.lean', 'lean-toolchain', 'lakefile.toml'], solverOwnedFiles: ['Submission.lean'],
      publicObligations: ['Submission.first', 'Submission.second'].map(name => ({ name,
        declarationHash: hashMathFormalSourceDeclaration(original, name) })) };
    fs.writeFileSync(receipt.activeProblemPath, JSON.stringify(receipt));
    git(workspace, ['init', '--quiet']); git(workspace, ['add', 'generated']);
    git(workspace, ['-c', 'user.name=Fixture', '-c', 'user.email=fixture@localhost', 'commit', '--no-gpg-sign', '--quiet', '-m', 'Public baseline']);
    fs.appendFileSync(path.join(workspace, '.git/info/exclude'), '\n/active-problem.json\n**/.lake/\n');
    problem = readSolverProblem(workspace, receipt.activeProblemPath);
    git(workspace, ['worktree', 'add', '--detach', '--quiet', peerRoot, problem.baseCommit]);
  });
  afterEach(() => { fs.rmSync(directory, { recursive: true, force: true }); });

  function run(candidateSource: string, seedSource?: string, sourceKind: 'lemma' | 'goal' = 'lemma') {
    const file = path.join(peerRoot, 'generated/p/Submission.lean');
    if (seedSource) { fs.writeFileSync(file, seedSource); commitSolverSources(problem, peerRoot); }
    const seedCommit = git(peerRoot, ['rev-parse', 'HEAD']);
    fs.writeFileSync(file, candidateSource);
    const commit = commitSolverSources(problem, peerRoot);
    const plan = parseCooperationPlan(problem, { tasks: [
      { id: 'prerequisite', kind: 'lemma', objective: 'Establish the prerequisite', theoremName: 'Submission.prerequisite', type: 'True' },
      { id: 'successor', kind: sourceKind, objective: 'Use the prerequisite',
        theoremName: sourceKind === 'goal' ? 'Submission.first' : 'Submission.successor',
        ...(sourceKind === 'lemma' ? { type: 'True' } : {}), conditional: true, dependsOn: ['prerequisite'] },
      ...problem.targets.filter(target => sourceKind !== 'goal' || target.theoremName !== 'Submission.first')
        .map(target => ({ id: target.theoremName.split('.').at(-1), kind: 'goal',
        objective: 'Preserve the original target', theoremName: target.theoremName, status: 'paused' })),
    ] });
    const [prerequisite, successor] = plan.tasks;
    const oldAssignment: TaskAssignment = { taskId: prerequisite.id, taskDigest: taskVersion(prerequisite),
      workerId: 'previous-researcher', seedCommit };
    const assignment: TaskAssignment = { taskId: successor.id, taskDigest: taskVersion(successor),
      workerId: 'researcher', seedCommit, canonicalCommit: seedCommit,
      dependencies: [{ taskId: prerequisite.id, taskDigest: taskVersion(prerequisite) }] };
    const target: TaskRecord = { task: prerequisite, status: 'blocked', attempts: 2,
      assignment: oldAssignment, feedback: 'Original failed attempt' };
    const source: TaskRecord = { task: successor, status: 'running', attempts: 1, assignment };
    const archive: CooperationState = { canonicalCommit: seedCommit, tasks: [target, source,
      ...plan.tasks.slice(2).map(task => ({ task, status: 'pending' as const, attempts: 0 }))],
      groups: plan.groups.map(group => ({ group, turns: 1 })) };
    const state: any = { problem, runId: 'candidate-recovery', environmentDigest: 'fixture', turns: 7,
      phase: 'running', failures: [], cooperation: archive };
    const lead = { id: 'lead', role: 'lead', worktree: workspace, ownedFiles: problem.ownedFiles } as const;
    const peer = { id: 'researcher', role: 'researcher', worktree: peerRoot, ownedFiles: problem.ownedFiles } as const;
    const events: { event: string; details?: Record<string, unknown> }[] = [];
    const checkTask = vi.fn(checkTaskProof);
    const cooperative = new CooperativeResearch({ state, workers: [lead, peer],
      access: new Map([[lead.id, { environment: {}, retrievalRoot: workspace }]]),
      signal: new AbortController().signal, save: () => {}, emit: (event, details) => events.push({ event, details }),
      modules: { ...directSolverModules, M2: { ...directSolverModules.M2, checkTask } }, exclusiveCheck: async check => check() });
    const action: Extract<CooperativeAction, { kind: 'task' }> = { kind: 'task', task: successor, assignment };
    return { cooperative, peer, target, source, action, oldAssignment, seedCommit, commit, archive, state, events, checkTask };
  }

  it('recovers a blocked predecessor from a conditional successor using fresh isolated and merged checks', async () => {
    const fixture = run(withHelpers('lemma prerequisite : True := by trivial\nlemma successor : True := by exact prerequisite\n'));
    const { cooperative, peer, action, commit, target, source, archive, seedCommit, checkTask, events } = fixture;
    await cooperative.deliver(peer, action, commit);

    expect(target.status).toBe('integrated'); expect(source.status).toBe('integrated');
    expect(target.proof).toMatchObject({ commit, seedCommit, passed: true });
    expect(target.proof!.conditions ?? []).toEqual([]);
    expect(target.integratedCheck).toMatchObject({ commit: archive.canonicalCommit, passed: true });
    const targetChecks = checkTask.mock.calls.filter(inputs => inputs[3].id === target.task.id);
    expect(targetChecks).toHaveLength(2);
    expect(targetChecks[0]![2]).toBe(commit); expect(targetChecks[0]![4].seedCommit).toBe(seedCommit);
    expect(targetChecks[0]![9]).toEqual([]);
    expect(targetChecks[1]![2]).toBe(target.integratedCheck!.commit);
    expect(targetChecks[1]![4].seedCommit).toBe(target.integratedCheck!.commit);
    expect(target.proof!.verification.targetCommit).not.toBe(commit);
    expect(committedSource(workspace, archive.canonicalCommit!, 'generated/p/Submission.lean')).toContain('lemma prerequisite : True := by trivial');
    expect(events.some(item => item.event === 'task_candidate_found')).toBe(true);
    expect(fixture.state.turns).toBe(7); expect(target.attempts).toBe(2); expect(host.open).not.toHaveBeenCalled();
  });

  it('recovers while the active source occupies the last model slot and the route turn budget is exhausted', async () => {
    const fixture = run(withHelpers('lemma prerequisite : True := by trivial\nlemma successor : True := by exact prerequisite\n'));
    const route = fixture.archive.groups![0]!;
    route.group = { ...route.group, maxConcurrent: 1, maxTurns: route.turns };
    fixture.cooperative.activate(fixture.peer, fixture.action, async () => {}, async () => {});
    expect(route.busy).toBe(1);
    await fixture.cooperative.deliver(fixture.peer, fixture.action, fixture.commit);

    expect(fixture.target.status).toBe('integrated'); expect(fixture.source.status).toBe('integrated');
    expect(fixture.checkTask.mock.calls.filter(inputs => inputs[3].id === fixture.target.task.id)).toHaveLength(2);
    expect(route.turns).toBe(1); expect(fixture.state.turns).toBe(7); expect(host.open).not.toHaveBeenCalled();
  });

  it.each(['group', 'problem'] as const)('does not recover another group predecessor, sharing=%s', async sharing => {
    const fixture = run(withHelpers('lemma prerequisite : True := by trivial\nlemma successor : True := by exact prerequisite\n'));
    // Private cross-group edges can only enter through a restored graph, never a newly validated plan.
    fixture.target.task = { ...fixture.target.task, groupId: 'private', sharing };
    const digest = taskVersion(fixture.target.task);
    fixture.oldAssignment.taskDigest = digest;
    fixture.action.assignment.dependencies = [{ taskId: fixture.target.task.id, taskDigest: digest }];
    fixture.archive.groups!.push({ group: { id: 'private', objective: 'Other route', revision: 0, status: 'active' }, turns: 0 });
    await fixture.cooperative.deliver(fixture.peer, fixture.action, fixture.commit);

    expect(fixture.source.status).toBe('conditional'); expect(fixture.target.status).toBe('blocked');
    expect(fixture.target.assignment).toBe(fixture.oldAssignment); expect(fixture.target.proof).toBeUndefined();
    expect(fixture.archive.canonicalCommit).toBe(fixture.seedCommit);
    expect(fixture.checkTask.mock.calls.map(inputs => inputs[3].id)).toEqual(['successor']);
    expect(fixture.events.some(item => item.event === 'task_candidate_found')).toBe(false);
    expect(host.open).not.toHaveBeenCalled();
  });

  it('keeps the original blocked state when the discovered proof fails', async () => {
    const fixture = run(withHelpers('lemma prerequisite : True := by sorry\nlemma successor : True := by exact prerequisite\n'));
    const { cooperative, peer, action, commit, target, source, oldAssignment, archive, seedCommit, events } = fixture;
    await cooperative.deliver(peer, action, commit);

    expect(source.status).toBe('conditional');
    expect(target).toMatchObject({ status: 'blocked', feedback: 'Original failed attempt', attempts: 2 });
    expect(target.assignment).toBe(oldAssignment); expect(target.proof).toBeUndefined();
    expect(archive.canonicalCommit).toBe(seedCommit);
    expect(events.some(item => item.event === 'task_candidate_check_failed')).toBe(true);
    expect(host.verify).toHaveBeenCalledTimes(2); expect(host.open).not.toHaveBeenCalled();
  });

  it('checks the predecessor against its assigned type without conditional binders', async () => {
    const fixture = run(withHelpers('lemma prerequisite : False := by trivial\nlemma successor : True := by exact prerequisite\n'));
    host.verify.mockImplementation(async (request: MathematicsVerifierBatchRequest, options: MathematicsVerifierExecutionOptions) => {
      const result = verified(request);
      if (!request.items.some(item => item.theoremName === 'Submission.prerequisite')) return result;
      expect(options.expectedDeclarationType).toBe('True');
      const projected = fs.readFileSync(path.join(request.projectRoot, 'Submission.lean'), 'utf8');
      expect(projected).toContain('lemma prerequisite : False');
      return { ...result, status: 'failed', results: result.results.map(item => ({ ...item, status: 'failed' })) };
    });
    await fixture.cooperative.deliver(fixture.peer, fixture.action, fixture.commit);

    expect(fixture.source.status).toBe('conditional'); expect(fixture.target.status).toBe('blocked');
    expect(fixture.target.assignment).toBe(fixture.oldAssignment); expect(fixture.target.proof).toBeUndefined();
    expect(fixture.archive.canonicalCommit).toBe(fixture.seedCommit);
    expect(host.verify).toHaveBeenCalledTimes(2); expect(host.open).not.toHaveBeenCalled();
  });

  it('uses the author seed and rejects another inherited helper statement change', async () => {
    const seed = withHelpers('lemma successor (n : Nat) : True := by trivial\n');
    const fixture = run(withHelpers('lemma prerequisite : True := by trivial\nlemma successor : True := by exact prerequisite\n'), seed);
    const { cooperative, peer, action, commit, target, source, oldAssignment, archive, seedCommit, checkTask, events } = fixture;
    await cooperative.deliver(peer, action, commit);

    expect(source.status).toBe('conditional'); expect(target.status).toBe('blocked');
    expect(target.assignment).toBe(oldAssignment); expect(archive.canonicalCommit).toBe(seedCommit);
    const targetCheck = checkTask.mock.calls.find(inputs => inputs[3].id === target.task.id)!;
    expect(targetCheck[4].seedCommit).toBe(seedCommit); expect(targetCheck[4].seedCommit).not.toBe(commit);
    expect(events).toContainEqual({ event: 'task_candidate_check_failed', details: expect.objectContaining({
      taskId: target.task.id, reason: expect.stringContaining('math_task_existing_declaration_changed'),
    }) });
    expect(host.verify).toHaveBeenCalledOnce(); expect(host.open).not.toHaveBeenCalled();
  });

  it('does not publish a proof when its task version changes during the preflight check', async () => {
    const fixture = run(withHelpers('lemma prerequisite : True := by trivial\nlemma successor : True := by exact prerequisite\n'));
    const entered = deferred(), release = deferred();
    host.verify.mockImplementation(async (request: MathematicsVerifierBatchRequest, _options: MathematicsVerifierExecutionOptions) => {
      if (request.items.some(item => item.theoremName === 'Submission.prerequisite')) {
        entered.resolve(); await release.promise;
      }
      return verified(request);
    });
    const pending = fixture.cooperative.deliver(fixture.peer, fixture.action, fixture.commit);
    await entered.promise;
    fixture.target.task = { ...fixture.target.task, revision: fixture.target.task.revision + 1, type: 'False' };
    release.resolve(); await pending;

    expect(fixture.target.status).toBe('blocked'); expect(fixture.target.assignment).toBe(fixture.oldAssignment);
    expect(fixture.target.proof).toBeUndefined(); expect(fixture.archive.canonicalCommit).toBe(fixture.seedCommit);
    expect(fixture.events).toContainEqual({ event: 'task_candidate_superseded',
      details: { taskId: fixture.target.task.id, commit: fixture.commit } });
    expect(host.verify).toHaveBeenCalledTimes(2); expect(host.open).not.toHaveBeenCalled();
  });

  it('does not publish when a predecessor worker becomes active during its preflight check', async () => {
    const fixture = run(withHelpers('lemma prerequisite : True := by trivial\nlemma successor : True := by exact prerequisite\n'));
    const entered = deferred(), release = deferred();
    host.verify.mockImplementation(async (request: MathematicsVerifierBatchRequest) => {
      if (request.items.some(item => item.theoremName === 'Submission.prerequisite')) {
        entered.resolve(); await release.promise;
      }
      return verified(request);
    });
    const pending = fixture.cooperative.deliver(fixture.peer, fixture.action, fixture.commit);
    await entered.promise;
    fixture.cooperative.activate({ ...fixture.peer, id: 'lead', role: 'lead', worktree: workspace },
      { kind: 'task', task: fixture.target.task, assignment: fixture.oldAssignment }, async () => {}, async () => {});
    release.resolve(); await pending;

    expect(fixture.target.status).toBe('blocked'); expect(fixture.target.assignment).toBe(fixture.oldAssignment);
    expect(fixture.target.proof).toBeUndefined(); expect(fixture.archive.canonicalCommit).toBe(fixture.seedCommit);
    expect(fixture.events).toContainEqual({ event: 'task_candidate_superseded',
      details: { taskId: fixture.target.task.id, commit: fixture.commit } });
    expect(host.verify).toHaveBeenCalledTimes(2); expect(host.open).not.toHaveBeenCalled();
  });

  it('recovers a predecessor from an original goal after restoring only its goal proof in an isolated candidate', async () => {
    const candidate = withHelpers('lemma prerequisite : True := by trivial\n')
      .replace('theorem first : True := by sorry', 'theorem first : True := by exact prerequisite');
    const fixture = run(candidate, undefined, 'goal');
    await fixture.cooperative.deliver(fixture.peer, fixture.action, fixture.commit);

    expect(fixture.target.status, JSON.stringify(fixture.events)).toBe('integrated'); expect(fixture.source.status).toBe('integrated');
    expect(fixture.target.proof).toMatchObject({ passed: true, seedCommit: fixture.seedCommit });
    expect(fixture.target.proof!.commit).not.toBe(fixture.commit);
    const isolated = committedSource(workspace, fixture.target.proof!.commit, 'generated/p/Submission.lean');
    expect(isolated).toContain('theorem first : True := by sorry');
    expect(isolated).toContain('lemma prerequisite : True := by trivial');
    expect(committedSource(workspace, fixture.commit, 'generated/p/Submission.lean')).toBe(candidate);
    expect(fixture.source.integratedCheck).toMatchObject({ passed: true, commit: fixture.archive.canonicalCommit });
    expect(fixture.source.integratedCheck!.conditions ?? []).toEqual([]);
    expect(committedSource(workspace, fixture.archive.canonicalCommit!, 'generated/p/Submission.lean'))
      .toContain('theorem first : True := by exact prerequisite');
    expect(fixture.checkTask.mock.calls.filter(inputs => inputs[3].id === fixture.target.task.id)).toHaveLength(2);
    expect(host.verify).toHaveBeenCalledTimes(4); expect(host.open).not.toHaveBeenCalled();
  });

  it.each([true, false])('requires a fresh archived source check before predecessor recovery, fresh passed=%s', async passed => {
    const fixture = run(withHelpers('lemma prerequisite : True := by trivial\nlemma successor : True := by exact prerequisite\n'));
    const proof = await checkTaskProof(problem, peerRoot, fixture.commit, fixture.source.task, fixture.action.assignment,
      [], {}, new AbortController().signal, 180_000, [fixture.target.task], 'fixture');
    const archived = JSON.parse(JSON.stringify(proof));
    archived.verification.results[0].receiptId = 'archived-receipt-cannot-authorize-recovery';
    fixture.source.proof = archived; fixture.source.status = 'conditional';
    host.verify.mockClear(); fixture.checkTask.mockClear();
    if (!passed) host.verify.mockImplementation(async (request: MathematicsVerifierBatchRequest) => {
      const result = verified(request);
      return request.items.some(item => item.theoremName === 'Submission.successor') ? {
        ...result, status: 'failed', results: result.results.map(item => ({ ...item, status: 'failed' })),
      } : result;
    });

    await fixture.cooperative.restore();

    const checkedTasks = fixture.checkTask.mock.calls.map(inputs => inputs[3].id);
    expect(checkedTasks[0]).toBe('successor');
    expect(fixture.checkTask.mock.calls[0]![4]).toBe(fixture.action.assignment);
    expect(fixture.checkTask.mock.calls[0]![9]).toEqual([fixture.target.task]);
    if (passed) {
      expect(checkedTasks).toEqual(['successor', 'prerequisite', 'prerequisite', 'successor']);
      expect(fixture.target.status).toBe('integrated'); expect(fixture.source.status).toBe('integrated');
      expect(fixture.source.proof).not.toBe(archived);
      expect(fixture.source.proof!.verification.results[0]!.receiptId).not.toBe('archived-receipt-cannot-authorize-recovery');
    } else {
      expect(checkedTasks).toEqual(['successor']); expect(fixture.target.status).toBe('blocked');
      expect(fixture.target.assignment).toBe(fixture.oldAssignment); expect(fixture.target.proof).toBeUndefined();
      expect(fixture.archive.canonicalCommit).toBe(fixture.seedCommit);
      expect(fixture.events.some(item => item.event === 'task_candidate_source_deferred')).toBe(true);
    }
    expect(host.open).not.toHaveBeenCalled();
  });
});
