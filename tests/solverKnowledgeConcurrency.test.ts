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
import { commitSolverSources, type SolverProblem } from '../src/solver/problem';
import { taskVersion, type CooperativeAction, type CooperativeTask } from '../src/solver/tasks';
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

  const node = () => state.cooperation!.tasks.find(item => item.task.id === action.task.id)!;
  const records = () => state.cooperation!.deliveries ?? [];
  const track = <T,>(promise: Promise<T>) => {
    pending.push(promise); void promise.catch(() => {}); return promise;
  };
  const commitProof = () => {
    const worker = workers[1], file = path.join(worker.worktree, problem.projectRelative, 'Submission.lean');
    fs.writeFileSync(file, fs.readFileSync(file, 'utf8').replace('theorem add_zero',
      'lemma knowledge_lemma : True := by trivial\ntheorem add_zero'));
    fs.writeFileSync(path.join(worker.worktree, 'RESEARCH.md'), JSON.stringify({ summary: 'A checked reusable lemma.',
      knowledgeUses: [{ id: 'saved-theorem', catalogDigest: knowledge.digest,
        declaration: { name: 'Tutorial.knowledge_lemma', file: 'Submission.lean' },
        application: { expression: 'True.intro', expectedType: 'True',
          context: { file: 'Submission.lean', declaration: action.task.theoremName } } }] }));
    return commitSolverSources(problem, worker.worktree);
  };
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
    const entered = deferred<DiagnosticInput>(), released = deferred();
    let heldAtEntry: boolean | undefined;
    host.check.mockImplementation(async (input: DiagnosticInput) => {
      const result = diagnosticResult(input);
      heldAtEntry = lockHeld; entered.resolve(input);
      await released.promise;
      return result;
    });
    const release = () => released.resolve(); releases.push(release);
    return { entered: entered.promise, release, heldAtEntry: () => heldAtEntry };
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
    events = []; pending = []; releases = []; lockHeld = false; controller = new AbortController();
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
      emit: (event, details) => events.push({ event, details }), exclusiveCheck: exclusive });
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

  it('does not publish an old application result after its task contract changes', async () => {
    const commit = commitProof(), gate = gateKnowledge();
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

    gate.release(); await delivery;

    expect(node()).toBe(current); expect(node()).toEqual(snapshot);
    expect(records().filter(record => record.kind === 'proof' && record.taskDigest === action.assignment.taskDigest)).toEqual([]);
    expect(events.filter(item => item.event === 'knowledge_use_observed' && item.details?.commit === commit)).toEqual([]);
    expect(host.check).toHaveBeenCalledTimes(1);
  });

  it('checks and publishes a selected application once for duplicate proof deliveries', async () => {
    const commit = commitProof(), gate = gateKnowledge();
    const first = track(cooperative.deliver(workers[1], action, commit));
    await gate.entered;
    const duplicate = track(cooperative.deliver(workers[1], action, commit));
    await Promise.resolve(); await Promise.resolve();
    expect(host.check).toHaveBeenCalledTimes(1);

    gate.release(); await Promise.all([first, duplicate]);
    await track(cooperative.deliver(workers[1], action, commit));

    expect(host.check).toHaveBeenCalledTimes(1);
    expect(records().filter(record => record.kind === 'proof')).toHaveLength(1);
    expect(records()[0]).toMatchObject({ taskId: action.task.id, status: 'verified', commit,
      knowledgeUses: [{ application: { check: { status: 'elaborated' } } }] });
    expect(events.filter(item => item.event === 'knowledge_use_observed')).toHaveLength(1);
  });
});
