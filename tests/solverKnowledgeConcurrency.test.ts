import fs from 'node:fs';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { LAKE_CONFIGURATION_FILES, mathLocalModuleBuildOrder } from '../src/math/mathConstructionSources';
import { canonicalMathJson, mathDigest } from '../src/math/mathRuntimeIo';
import type { MathematicsVerifierBatchRequest } from '../src/math/verifier';
import type { SolverRunState } from '../src/solver/archive';
import type { CooperativeResearch } from '../src/solver/cooperation';
import type { KnowledgeContextSnapshot } from '../src/solver/knowledgeContext';
import type { ResearchWorker } from '../src/solver/modules/organization';
import { committedSource, commitSolverSources, type SolverProblem } from '../src/solver/problem';
import { assignmentDeliveryFile, taskVersion, type CooperativeAction, type CooperativeTask } from '../src/solver/tasks';
import { deferred } from './helpers/async';
import { cooperativeResearch, workerAccess } from './helpers/cooperation';
import { leadWorker, localExample, peerWorker, solverState } from './helpers/solver';
import { verifiedBatch } from './helpers/verifier';

const host = vi.hoisted(() => ({ verify: vi.fn(), check: vi.fn(), identity: vi.fn(), createSession: vi.fn() }));
vi.mock('../src/math/verifier', async importOriginal => ({
  ...await importOriginal<typeof import('../src/math/verifier')>(),
  checkManyFormalVerifications: host.verify,
  formalVerificationToolIdentity: () => undefined,
  resolveMathematicsLakePackagesCache: () => undefined,
}));
vi.mock('../src/math/leanTypeDiagnostics', async importOriginal => ({
  ...await importOriginal<typeof import('../src/math/leanTypeDiagnostics')>(), checkLeanType: host.check,
}));
vi.mock('../src/math/leanResidualGoals', async importOriginal => ({
  ...await importOriginal<typeof import('../src/math/leanResidualGoals')>(), leanDiagnosticEnvironmentIdentity: host.identity,
}));
vi.mock('../src/runtime/codexSession', () => ({ createCodexMathSession: host.createSession }));

type TaskAction = Extract<CooperativeAction, { kind: 'task' }>;
type DiagnosticInput = Parameters<typeof import('../src/math/leanTypeDiagnostics').checkLeanType>[0];
const knowledge = { digest: 'pinned-catalog', base: { entries: [{ id: 'saved-theorem' }] } } as KnowledgeContextSnapshot;

describe('proof delivery with concurrent knowledge application checks', () => {
  let directory: string, problem: SolverProblem, state: SolverRunState;
  let workers: ResearchWorker[], cooperative: CooperativeResearch, controller: AbortController, action: TaskAction;
  let pending: Promise<unknown>[], releases: (() => void)[], lockHeld: boolean;
  let events: { event: string; details?: Record<string, unknown> }[];
  let onSave: () => void;

  const node = () => state.cooperation!.tasks.find(item => item.task.id === action.task.id)!;
  const records = () => state.cooperation!.deliveries ?? [];
  const track = <T,>(promise: Promise<T>) => {
    pending.push(promise); void promise.catch(() => {}); return promise;
  };
  const commitProof = ({ application = true, rejectedUse = false } = {}) => {
    const worker = workers[1], file = path.join(worker.worktree, problem.projectRelative, 'Submission.lean');
    fs.writeFileSync(file, fs.readFileSync(file, 'utf8').replace('theorem add_zero',
      'lemma knowledge_lemma : True := by trivial\ntheorem add_zero'));
    fs.writeFileSync(path.join(worker.worktree, 'RESEARCH.md'), JSON.stringify({ summary: 'A checked reusable lemma.',
      knowledgeUses: [{ id: 'saved-theorem', catalogDigest: knowledge.digest,
        declaration: { name: 'Tutorial.knowledge_lemma', file: 'Submission.lean' },
        ...(application ? { application: { expression: 'True.intro', expectedType: 'True',
          context: { file: 'Submission.lean', declaration: action.task.theoremName } } } : {}) },
        ...(rejectedUse ? [{ id: 'not-in-the-pinned-catalog' }] : [])] }));
    return commitSolverSources(problem, worker.worktree);
  };
  const secondProof = (dependsOnKnowledge = false) => {
    const worker = workers[2];
    const task: CooperativeTask = { id: 'independent', kind: 'lemma', objective: 'Prove another reusable lemma.',
      theoremName: 'Tutorial.second_lemma', proofPath: 'Submission.lean', type: 'True', revision: 0,
      dependsOn: dependsOnKnowledge ? [action.task.id] : [], ...(dependsOnKnowledge ? { conditional: true } : {}) };
    const second: TaskAction = { kind: 'task', task, assignment: { taskId: task.id, taskDigest: taskVersion(task),
      workerId: worker.id, seedCommit: problem.baseCommit, assignmentId: 'second-dispatch',
      dependencies: dependsOnKnowledge ? [{ taskId: action.task.id, taskDigest: taskVersion(action.task) }] : [] } };
    const record = state.cooperation!.tasks.find(item => item.task.id === task.id)!;
    Object.assign(record, { task, assignment: second.assignment, status: 'running', attempts: 1 });
    const file = path.join(worker.worktree, problem.projectRelative, 'Submission.lean');
    fs.writeFileSync(file, fs.readFileSync(file, 'utf8').replace('theorem add_zero',
      `lemma second_lemma : True := by ${dependsOnKnowledge ? 'exact knowledge_lemma' : 'trivial'}\ntheorem add_zero`));
    return { action: second, node: record, commit: commitSolverSources(problem, worker.worktree) };
  };
  const canonicalSource = () => committedSource(workers[0].worktree, state.cooperation!.canonicalCommit!,
    `${problem.projectRelative}/Submission.lean`);
  const diagnosticResult = (input: DiagnosticInput) => {
    const files = [...mathLocalModuleBuildOrder(input.projectRoot, input.file).map(module => module.file),
      ...LAKE_CONFIGURATION_FILES.filter(file => fs.existsSync(path.join(input.projectRoot, file)))]
      .map(file => ({ file, digest: mathDigest(fs.readFileSync(path.join(input.projectRoot, file))) }));
    const contents = canonicalMathJson({ files, expression: input.expression, type: input.type });
    const artifact = { path: '.lake/knowledge-application-fixture.json', digest: mathDigest(contents) };
    fs.mkdirSync(path.join(input.projectRoot, '.lake'), { recursive: true });
    fs.writeFileSync(path.join(input.projectRoot, artifact.path), contents);
    return { status: 'elaborated', exitCode: 0, timedOut: false, sourceFiles: files, artifact,
      sourceSnapshotDigest: mathDigest(canonicalMathJson(files)), projectionDigest: mathDigest('application-projection'),
      environment: host.identity(), type: input.type, constants: ['True.intro'], stdout: '', stderr: '' };
  };
  const gateKnowledge = () => {
    const entered = deferred<DiagnosticInput>(), released = deferred(), aborted = deferred();
    let heldAtEntry: boolean | undefined;
    let cleaned = false;
    host.check.mockImplementation(async (input: DiagnosticInput) => {
      const result = diagnosticResult(input);
      input.signal?.addEventListener('abort', () => aborted.resolve(), { once: true });
      heldAtEntry = lockHeld; entered.resolve(input);
      try { await released.promise; return result; }
      finally { cleaned = true; }
    });
    const release = () => released.resolve(); releases.push(release);
    return { entered: entered.promise, aborted: aborted.promise, release, heldAtEntry: () => heldAtEntry, cleaned: () => cleaned };
  };
  const edit = (id: string, change: (task: CooperativeTask) => CooperativeTask) => {
    fs.appendFileSync(path.join(directory, 'edits.jsonl'), JSON.stringify({ id, baseVersion: state.cooperation!.planVersion,
      tasks: state.cooperation!.tasks.map(item => change(item.task)),
      groups: state.cooperation!.groups!.map(item => item.group),
    }) + '\n');
    return track(cooperative.pulse(workers[0].id));
  };

  beforeEach(() => {
    host.verify.mockReset().mockImplementation(async (request: MathematicsVerifierBatchRequest) =>
      verifiedBatch(request, { sessionId: 'knowledge-concurrency-fixture', checks: true }));
    host.check.mockReset().mockImplementation(async (input: DiagnosticInput) => diagnosticResult(input));
    host.identity.mockReset().mockReturnValue({ environmentDigest: mathDigest('diagnostic-environment'), toolIdentity: mathDigest('fixture-tools') });
    host.createSession.mockReset().mockImplementation(() => { throw new Error('fixture_real_models_forbidden'); });
    const example = localExample('solver-knowledge-concurrency-');
    ({ directory, problem } = example);
    workers = [leadWorker(problem, example.workspace), ...['author', 'independent'].map(id => peerWorker(example, id))];
    const task: CooperativeTask = { id: 'knowledge', kind: 'lemma', objective: 'Prove a reusable lemma.',
      theoremName: 'Tutorial.knowledge_lemma', proofPath: 'Submission.lean', type: 'True', dependsOn: [], revision: 0 };
    action = { kind: 'task', task, assignment: { taskId: task.id, taskDigest: taskVersion(task), workerId: workers[1].id,
      seedCommit: problem.baseCommit, assignmentId: 'knowledge-dispatch', dependencies: [] } };
    state = solverState(problem, example.workspace, { runId: 'knowledge-concurrency-fixture', phase: 'running', failures: [],
      cooperation: { canonicalCommit: problem.baseCommit,
        groups: [{ group: { id: 'main', objective: 'Prove the original problem.', status: 'active', revision: 0 }, turns: 0 }],
        tasks: [{ task, assignment: action.assignment, status: 'running', attempts: 1 },
          { task: { id: 'independent', kind: 'research', objective: 'Find another useful approach.', dependsOn: [], revision: 0 },
            status: 'pending', attempts: 0 }, ...problem.targets.map((target, index) => ({
            task: { id: `goal_${index}`, kind: 'goal' as const, objective: `Prove ${target.theoremName}.`,
              theoremName: target.theoremName, proofPath: target.proofPath, dependsOn: [], revision: 0, status: 'paused' as const },
            status: 'pending' as const, attempts: 0,
          }))] } });
    events = []; pending = []; releases = []; lockHeld = false; onSave = () => {}; controller = new AbortController();
    let queue = Promise.resolve();
    const exclusive = async <T,>(check: () => Promise<T>): Promise<T> => {
      const previous = queue; let release!: () => void;
      queue = new Promise<void>(resolve => { release = resolve; });
      await previous; lockHeld = true;
      try { return await check(); } finally { lockHeld = false; release(); }
    };
    const access = workerAccess(workers, directory);
    for (const value of access.values()) value.environment = { PATH: '/usr/bin:/bin', ELAN_HOME: '', LEAN_PATH: '', LEAN_SYSROOT: '',
      DEEPSCIENTIST_MATH_ENV_FILE: path.join(directory, 'missing.env') };
    access.get(workers[1].id)!.knowledgeSnapshot = knowledge;
    cooperative = cooperativeResearch({ state, workers, retrievalRoot: directory, access, signal: controller.signal,
      save: () => onSave(), emit: (event, details) => events.push({ event, details }), exclusiveCheck: exclusive });
    state.cooperation!.planVersion = (cooperative as any).planVersion();
  });
  afterEach(async () => {
    for (const release of releases) release();
    controller.abort(); await Promise.allSettled(pending); await cooperative.stop();
    expect(host.createSession).not.toHaveBeenCalled();
    vi.restoreAllMocks(); fs.rmSync(directory, { recursive: true, force: true });
  });

  it('applies an independent plan edit before a selected application check finishes', async () => {
    const commit = commitProof(), gate = gateKnowledge();
    const delivery = track(cooperative.deliver(workers[1], action, commit));
    await gate.entered;

    let applied = false;
    const pulse = edit('independent-during-knowledge', task => task.id === 'independent'
      ? { ...task, objective: 'Find a sharper independent approach.', revision: task.revision + 1 } : task);
    void pulse.then(() => { applied = true; }, () => {});
    await vi.waitFor(() => {
      expect(state.cooperation!.edits).toContainEqual(expect.objectContaining({ id: 'independent-during-knowledge', status: 'applied' }));
      expect(applied).toBe(true);
    });
    expect(gate.heldAtEntry()).toBe(false);

    gate.release(); await delivery;

    expect(records().filter(record => record.kind === 'proof')).toMatchObject([{ taskId: action.task.id, status: 'verified', commit,
      knowledgeUses: [{ consumer: { taskId: action.task.id, taskDigest: taskVersion(action.task) },
        application: { check: { status: 'elaborated', proofAcceptance: 'not-assessed' } } }] }]);
    expect(host.check).toHaveBeenCalledTimes(1);
  });

  it('publishes normalized reference uses without starting an optional Lean application check', async () => {
    const commit = commitProof({ application: false });

    await track(cooperative.deliver(workers[1], action, commit));

    expect(node()).toMatchObject({ status: 'integrated', integratedCheck: { passed: true } });
    expect(records().filter(record => record.kind === 'proof')).toMatchObject([{ taskId: action.task.id, status: 'verified',
      knowledgeUses: [{ id: 'saved-theorem', catalogDigest: knowledge.digest,
        consumer: { taskId: action.task.id, taskDigest: taskVersion(action.task) } }] }]);
    expect(records()[0].knowledgeUses![0].application).toBeUndefined();
    expect(host.check).not.toHaveBeenCalled();
    expect(events.filter(item => item.event === 'knowledge_use_observed')).toHaveLength(1);
  });

  it('integrates an independent proof while the first delivery still awaits its application check', async () => {
    const second = secondProof(), commit = commitProof(), gate = gateKnowledge();
    const first = track(cooperative.deliver(workers[1], action, commit));
    let firstSettled = false;
    void first.then(() => { firstSettled = true; }, () => { firstSettled = true; });
    await gate.entered;
    const core = records().find(record => record.kind === 'proof' && record.taskId === action.task.id)!;
    expect(core).toMatchObject({ status: 'verified', commit });

    const independent = track(cooperative.deliver(workers[2], second.action, second.commit));
    await vi.waitFor(() => expect(second.node.status).toBe('integrated'), { timeout: 5000 });
    await independent;

    expect(canonicalSource()).toContain('lemma knowledge_lemma : True := by trivial');
    expect(canonicalSource()).toContain('lemma second_lemma : True := by trivial');
    expect(records().filter(record => record.kind === 'proof')).toHaveLength(2);
    expect(firstSettled).toBe(false);
    expect(gate.cleaned()).toBe(false);
    expect(host.check).toHaveBeenCalledTimes(1);

    gate.release(); await first;

    expect(records().find(record => record.id === core.id)).toBe(core);
    expect(core.knowledgeUses).toMatchObject([{ application: { check: { status: 'elaborated' } } }]);
    expect(events.filter(item => item.event === 'delivery_published' && item.details?.deliveryId === core.id)).toHaveLength(1);
  });

  it('integrates a ready conditional parent before its child application check finishes', async () => {
    const parent = secondProof(true);
    await track(cooperative.deliver(workers[2], parent.action, parent.commit));
    expect(parent.node).toMatchObject({ status: 'conditional', proof: { passed: true,
      conditions: [{ taskId: action.task.id, taskDigest: taskVersion(action.task) }] } });
    const conditionalProof = parent.node.proof;
    const commit = commitProof(), gate = gateKnowledge();
    const child = track(cooperative.deliver(workers[1], action, commit));
    let childSettled = false;
    void child.then(() => { childSettled = true; }, () => { childSettled = true; });
    await gate.entered;

    await vi.waitFor(() => expect(parent.node.status).toBe('integrated'), { timeout: 5000 });

    expect(parent.node.proof).toBe(conditionalProof);
    expect(parent.node.integratedCheck).toMatchObject({ passed: true });
    expect(parent.node.integratedCheck?.conditions ?? []).toEqual([]);
    expect(canonicalSource()).toContain('lemma second_lemma : True := by exact knowledge_lemma');
    expect(records().filter(record => record.kind === 'proof' && record.taskId === parent.action.task.id).map(record => record.status))
      .toEqual(['conditional', 'verified']);
    expect(childSettled).toBe(false);
    expect(gate.cleaned()).toBe(false);

    gate.release(); await child;

    expect(records().find(record => record.kind === 'proof' && record.taskId === action.task.id)?.knowledgeUses)
      .toMatchObject([{ application: { check: { status: 'elaborated' } } }]);
  });

  it('does not publish an old application result after its task contract changes', async () => {
    const commit = commitProof({ rejectedUse: true }), gate = gateKnowledge();
    const delivery = track(cooperative.deliver(workers[1], action, commit));
    await gate.entered;

    let applied = false;
    const pulse = edit('revise-during-knowledge', task => task.id === action.task.id
      ? { ...task, type: 'True ∧ True', revision: task.revision + 1 } : task);
    void pulse.then(() => { applied = true; }, () => {});
    await vi.waitFor(() => {
      expect(state.cooperation!.edits).toContainEqual(expect.objectContaining({ id: 'revise-during-knowledge', status: 'applied' }));
      expect(applied).toBe(true);
    });
    expect(cooperative.current(action)).toBe(false);
    const current = node(), snapshot = JSON.parse(JSON.stringify(current));
    const historical = records().filter(record => record.kind === 'proof' && record.taskDigest === action.assignment.taskDigest);
    expect(historical).toHaveLength(1);
    expect(historical[0]).toMatchObject({ status: 'superseded', commit });
    const recordedKnowledge = structuredClone(historical[0].knowledgeUses);
    const beforeCompletion = events.length;

    gate.release(); await delivery;

    expect(node()).toBe(current); expect(node()).toEqual(snapshot);
    expect(records().filter(record => record.kind === 'proof' && record.taskDigest === action.assignment.taskDigest)).toEqual(historical);
    expect(historical[0].knowledgeUses).toEqual(recordedKnowledge);
    expect(events.slice(beforeCompletion).filter(item => ['knowledge_use_observed', 'knowledge_use_rejected'].includes(item.event) &&
      item.details?.commit === commit)).toEqual([]);
    expect(host.check).toHaveBeenCalledTimes(1);
  });

  it.each(['status', 'assignment', 'proof', 'integratedCheck', 'environment', 'problem receipt', 'removed'] as const)
  ('preserves the core record and drops late knowledge results after its %s changes', async change => {
    const commit = commitProof({ rejectedUse: true }), gate = gateKnowledge();
    const delivery = track(cooperative.deliver(workers[1], action, commit));
    await gate.entered;
    const delivered = node();
    const core = records().find(record => record.kind === 'proof' && record.taskId === action.task.id)!;
    expect(core).toMatchObject({ status: 'verified', commit });
    const coreBeforeCompletion = structuredClone(core);

    switch (change) {
      case 'status': delivered.status = 'pending'; break;
      case 'assignment': delivered.assignment = { ...delivered.assignment! }; break;
      case 'proof': delivered.proof = structuredClone(delivered.proof); break;
      case 'integratedCheck': delivered.integratedCheck = structuredClone(delivered.integratedCheck); break;
      case 'environment': state.environmentDigest = 'changed-environment'; break;
      case 'problem receipt': state.problem.receiptDigest = 'changed-problem-receipt'; break;
      case 'removed': state.cooperation!.tasks = state.cooperation!.tasks.filter(record => record !== delivered); break;
    }
    const tasksBeforeCompletion = structuredClone(state.cooperation!.tasks);
    const environmentBeforeCompletion = state.environmentDigest, receiptBeforeCompletion = state.problem.receiptDigest;
    const beforeCompletion = events.length;

    gate.release(); await delivery;

    expect(records().filter(record => record.kind === 'proof')).toEqual([core]);
    expect(core).toEqual(coreBeforeCompletion);
    expect(state.cooperation!.tasks).toEqual(tasksBeforeCompletion);
    expect(state.environmentDigest).toBe(environmentBeforeCompletion);
    expect(state.problem.receiptDigest).toBe(receiptBeforeCompletion);
    expect(events.slice(beforeCompletion).filter(item => ['knowledge_use_observed', 'knowledge_use_rejected'].includes(item.event) &&
      item.details?.commit === commit)).toEqual([]);
    expect(host.check).toHaveBeenCalledTimes(1);
  });

  it('checks and publishes a selected application once for duplicate proof deliveries', async () => {
    const commit = commitProof(), gate = gateKnowledge();
    const first = track(cooperative.deliver(workers[1], action, commit));
    await gate.entered;
    const duplicate = track(cooperative.deliver(workers[1], action, commit));
    let settled = 0;
    for (const delivery of [first, duplicate]) void delivery.then(() => { settled++; }, () => { settled++; });
    await Promise.resolve(); await Promise.resolve();
    expect(host.check).toHaveBeenCalledTimes(1);
    expect(records().filter(record => record.kind === 'proof')).toHaveLength(1);
    expect(settled).toBe(0);

    gate.release(); await Promise.all([first, duplicate]);
    await track(cooperative.deliver(workers[1], action, commit));

    expect(host.check).toHaveBeenCalledTimes(1);
    expect(records().filter(record => record.kind === 'proof')).toHaveLength(1);
    expect(records()[0]).toMatchObject({ taskId: action.task.id, status: 'verified', commit,
      knowledgeUses: [{ application: { check: { status: 'elaborated' } } }] });
    expect(events.filter(item => item.event === 'knowledge_use_observed')).toHaveLength(1);
  });

  it('retries an annotation save failure on the accepted proof when a duplicate log line changes its commit', async () => {
    const commit = commitProof(), file = path.join(workers[1].worktree, assignmentDeliveryFile(action.assignment));
    const key = `${workers[1].id}/${assignmentDeliveryFile(action.assignment)}`, cursors: Record<string, number> = {};
    const prefix = JSON.stringify({ summary: 'Accepted prefix.' }) + '\n';
    const suffix = JSON.stringify({ summary: 'Accepted suffix.' }) + '\n';
    const submission = { id: 'knowledge-proof', kind: 'proof', commit, summary: 'A checked reusable lemma.' };
    fs.writeFileSync(file, prefix + JSON.stringify(submission) + '\n' + suffix);
    const prefixEnd = Buffer.byteLength(prefix), snapshots: Record<string, number>[] = [];
    const failure = Object.assign(new Error('Transient annotation save failure.'), { code: 'EIO' });
    let failedOnce = false;
    onSave = () => {
      snapshots.push({ ...cursors });
      if (!failedOnce && records().some(record => record.kind === 'proof' && record.taskId === action.task.id &&
          record.knowledgeUses?.some(use => use.application?.check))) {
        failedOnce = true; throw failure;
      }
    };
    const poll = () => track((cooperative as any).readWorkerDeliveries(workers[1], action, cursors) as Promise<void>);

    await expect(poll()).rejects.toBe(failure);

    const core = records().find(record => record.kind === 'proof' && record.taskId === action.task.id)!;
    expect(core).toMatchObject({ status: 'verified', commit, submissionId: submission.id });
    expect(core.knowledgeUses).toHaveLength(1);
    expect(core.knowledgeUses![0].application?.check).toBeUndefined();
    expect(cursors[key]).toBe(prefixEnd);
    expect(snapshots.at(-1)?.[key]).toBe(prefixEnd);
    expect(records().map(record => record.summary)).toEqual(['Accepted prefix.', submission.summary]);
    expect(events.filter(item => item.event === 'delivery_published' && item.details?.deliveryId === core.id)).toHaveLength(1);
    expect(events.filter(item => item.event === 'knowledge_use_observed')).toEqual([]);
    expect(host.check).toHaveBeenCalledTimes(1);
    const proof = node().proof, integratedCheck = node().integratedCheck, canonical = state.cooperation!.canonicalCommit;
    const verifications = host.verify.mock.calls.length;

    expect(problem.baseCommit).not.toBe(commit);
    fs.writeFileSync(file, prefix + JSON.stringify({ ...submission, commit: problem.baseCommit }) + '\n' + suffix);
    await poll(); await poll();

    expect(records().filter(record => record.kind === 'proof')).toEqual([core]);
    expect(records().find(record => record.id === core.id)).toBe(core);
    expect(core).toMatchObject({ status: 'verified', commit, submissionId: submission.id,
      knowledgeUses: [{ application: { check: { status: 'elaborated', commit } } }] });
    expect(node().proof).toBe(proof);
    expect(node().integratedCheck).toBe(integratedCheck);
    expect(state.cooperation!.canonicalCommit).toBe(canonical);
    expect(host.verify).toHaveBeenCalledTimes(verifications);
    expect(host.check).toHaveBeenCalledTimes(2);
    expect(cursors[key]).toBe(fs.statSync(file).size);
    expect(snapshots.at(-1)?.[key]).toBe(fs.statSync(file).size);
    expect(records().map(record => record.summary)).toEqual(['Accepted prefix.', submission.summary, 'Accepted suffix.']);
    expect(events.filter(item => item.event === 'delivery_published' && item.details?.deliveryId === core.id)).toHaveLength(1);
    expect(events.filter(item => item.event === 'knowledge_use_observed' && item.details?.commit === commit)).toHaveLength(1);
  });

  it('waits for cancelled application cleanup before stopping and publishes no late knowledge observations', async () => {
    const commit = commitProof({ rejectedUse: true }), gate = gateKnowledge();
    const delivery = track(cooperative.deliver(workers[1], action, commit));
    await gate.entered;
    const core = records().find(record => record.kind === 'proof' && record.taskId === action.task.id)!;
    expect(core).toMatchObject({ status: 'verified', commit });
    const recordedKnowledge = structuredClone(core.knowledgeUses);
    const beforeCancellation = events.length;

    controller.abort(); await gate.aborted;
    const stopped = track(cooperative.stop());
    let stopSettled = false, deliverySettled = false;
    void stopped.then(() => { stopSettled = true; }, () => { stopSettled = true; });
    void delivery.then(() => { deliverySettled = true; }, () => { deliverySettled = true; });
    await Promise.resolve(); await Promise.resolve();

    expect(gate.cleaned()).toBe(false);
    expect(stopSettled).toBe(false);
    expect(deliverySettled).toBe(false);

    gate.release(); await Promise.allSettled([delivery, stopped]);

    expect(gate.cleaned()).toBe(true);
    expect(stopSettled).toBe(true);
    expect(records().filter(record => record.kind === 'proof')).toEqual([core]);
    expect(core).toMatchObject({ status: 'verified', commit });
    expect(core.knowledgeUses).toEqual(recordedKnowledge);
    expect(events.slice(beforeCancellation).filter(item => ['knowledge_use_observed', 'knowledge_use_rejected'].includes(item.event) &&
      item.details?.commit === commit)).toEqual([]);
  });
});
