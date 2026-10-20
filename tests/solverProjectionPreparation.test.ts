import fs from 'node:fs';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { bootstrapLocalExample, LOCAL_EXAMPLE_PROOF } from '../src/math/localExample';
import type { MathematicsVerifierBatchRequest } from '../src/math/verifier';
import type { SolverRunState } from '../src/solver/archive';
import type { CooperativeResearch } from '../src/solver/cooperation';
import * as proofApi from '../src/solver/cooperativeProof';
import { committedSource, commitSolverSources, readSolverProblem, type SolverProblem } from '../src/solver/problem';
import { taskVersion, type CooperativeTask } from '../src/solver/tasks';
import { cooperativeResearch } from './helpers/cooperation';
import { temporaryDirectory } from './helpers/files';
import { leadWorker, solverState } from './helpers/solver';
import { receiptBatch } from './helpers/verifier';

const host = vi.hoisted(() => ({ verify: vi.fn(), createSession: vi.fn() }));
vi.mock('../src/math/verifier', async importOriginal => ({
  ...await importOriginal<typeof import('../src/math/verifier')>(),
  checkManyFormalVerifications: host.verify,
  formalVerificationToolIdentity: () => 'projection-preparation-fixture-tools',
  resolveMathematicsLakePackagesCache: () => undefined,
}));
vi.mock('../src/math/mathProofEnvironment', async importOriginal => ({
  ...await importOriginal<typeof import('../src/math/mathProofEnvironment')>(), resolveMathProofEnvironment: () => undefined,
}));
vi.mock('../src/runtime/codexSession', () => ({ createCodexMathSession: host.createSession }));

const verified = (request: MathematicsVerifierBatchRequest) => receiptBatch(request,
  { sessionId: 'projection-preparation-fixture', receiptId: (_, theoremName) => `receipt-${request.targetCommit}-${theoremName}` });

type Projector = ReturnType<typeof proofApi.createTaskSourceProjector>;
type Preparation = { commit: string; worktree: string; targets: string[]; project: Projector };

describe('integrated task projection preparation', () => {
  let directory: string, workspace: string, file: string, problem: SolverProblem, state: SolverRunState;
  let cooperative: CooperativeResearch | undefined, controller: AbortController, preparations: Preparation[];
  let events: { event: string; details?: Record<string, unknown> }[];

  const helpers = () => state.cooperation!.tasks.filter(node => node.task.kind === 'lemma');
  const recheck = (commit = state.cooperation!.canonicalCommit!) => (cooperative as any).recheckIntegrated(commit) as Promise<void>;
  const prepare = (count: number) => {
    const receipt = bootstrapLocalExample(workspace);
    problem = readSolverProblem(workspace, receipt.activeProblemPath);
    file = path.join(receipt.projectRoot, 'Submission.lean');
    fs.writeFileSync(file, LOCAL_EXAMPLE_PROOF);
    commitSolverSources(problem, workspace);
    const tasks: CooperativeTask[] = Array.from({ length: count }, (_, index) => ({ id: `helper_${index}`,
      kind: 'lemma', objective: `Prove helper ${index}.`, proofPath: 'Submission.lean',
      theoremName: `Tutorial.helper_${index}`, type: 'True', dependsOn: [], revision: 0 }));
    const declarations = tasks.map(task => `lemma ${task.id} : True := by trivial`).join('\n');
    fs.writeFileSync(file, LOCAL_EXAMPLE_PROOF.replace('theorem add_zero', `${declarations}\n\ntheorem add_zero`));
    const canonical = commitSolverSources(problem, workspace);
    state = solverState(problem, workspace, { runId: 'projection-preparation-fixture', phase: 'running', failures: [],
      cooperation: { canonicalCommit: canonical,
        groups: [{ group: { id: 'main', objective: 'Prove the original problem.', status: 'active', revision: 0 }, turns: 0 }],
        tasks: [...tasks.map(task => ({ task, status: 'integrated' as const, attempts: 1 })),
          ...problem.targets.map((target, index) => ({
            task: { id: `goal_${index}`, kind: 'goal' as const, objective: `Prove ${target.theoremName}.`,
              theoremName: target.theoremName, proofPath: target.proofPath, dependsOn: [], revision: 0, status: 'paused' as const },
            status: 'pending' as const, attempts: 0,
          }))] } });
    const lead = leadWorker(problem, workspace);
    cooperative = cooperativeResearch({ state, workers: [lead], retrievalRoot: directory,
      access: new Map([[lead.id, { environment: { PATH: '/usr/bin:/bin',
        DEEPSCIENTIST_MATH_ENV_FILE: path.join(directory, 'math.env') }, retrievalRoot: directory }]]),
      signal: controller.signal, emit: (event, details) => events.push({ event, details }), exclusiveCheck: check => check() });
    return canonical;
  };
  const expectVerified = (canonical: string) => {
    for (const node of helpers()) {
      expect(node, node.feedback).toMatchObject({ status: 'integrated', integratedCheck: {
        passed: true, commit: canonical, seedCommit: canonical, taskDigest: taskVersion(node.task),
        verification: { status: 'kernel_verified', results: [{ theoremName: node.task.theoremName,
          proofPath: node.task.proofPath, statementHash: taskVersion(node.task), leanStatementHash: taskVersion(node.task) }] },
      } });
      expect(node.integratedCheck!.verification.results).toHaveLength(1);
    }
    expect(state.cooperation!.recheck).toMatchObject({ canonicalCommit: canonical, total: helpers().length, completed: helpers().length });
    expect(events.filter(item => item.event === 'task_recheck_batch_fallback')).toEqual([]);
  };

  beforeEach(() => {
    host.verify.mockReset().mockImplementation(async request => verified(request));
    host.createSession.mockReset().mockImplementation(() => { throw new Error('fixture_real_models_forbidden'); });
    directory = temporaryDirectory('solver-projection-preparation-');
    workspace = path.join(directory, 'workspace');
    preparations = []; events = []; controller = new AbortController(); cooperative = undefined;
    const original = proofApi.createTaskSourceProjector;
    vi.spyOn(proofApi, 'createTaskSourceProjector').mockImplementation((problem, worktree, commit) => {
      const project = original(problem, worktree, commit), targets: string[] = [];
      const wrapped: Projector = (task, retainedGoals, conditions) => {
        targets.push(task.id);
        return project(task, retainedGoals, conditions);
      };
      preparations.push({ commit, worktree, targets, project: wrapped });
      return wrapped;
    });
  });
  afterEach(async () => {
    controller.abort(); await cooperative?.stop();
    expect(host.createSession).not.toHaveBeenCalled();
    vi.restoreAllMocks(); fs.rmSync(directory, { recursive: true, force: true });
  });

  it.each([{ count: 64, oldGroupingCalls: 96 }, { count: 128, oldGroupingCalls: 320 }])
  ('prepares $count helper grouping and host checks once per snapshot', async ({ count, oldGroupingCalls }) => {
    const canonical = prepare(count);

    await recheck();

    expectVerified(canonical);
    expect(proofApi.createTaskSourceProjector).toHaveBeenCalledTimes(2);
    expect(preparations.map(item => [item.worktree, item.commit])).toEqual([[workspace, canonical], [workspace, canonical]]);
    const targetIds = helpers().map(node => node.task.id);
    expect(preparations[0]!.targets).toEqual(targetIds);
    expect(preparations[0]!.targets.length).toBeLessThan(oldGroupingCalls);
    // Every target still crosses the host's exact-source receipt boundary.
    expect(preparations[1]!.targets).toEqual(targetIds);
    expect(host.verify).toHaveBeenCalledTimes(count / 32);
    const requests = host.verify.mock.calls.map(([request]) => request as MathematicsVerifierBatchRequest);
    expect(requests.map(request => request.items.length)).toEqual(Array(count / 32).fill(32));
    expect(requests.flatMap(request => request.items.map(item => item.theoremName))).toEqual(helpers().map(node => node.task.theoremName));
  });

  it('reuses host preparation for the same canonical commit and rebuilds it after proof bytes change', async () => {
    const canonical = prepare(4), targetIds = helpers().map(node => node.task.id);
    await recheck();
    expectVerified(canonical);
    const firstHost = preparations[1]!;
    await recheck();

    expectVerified(canonical);
    expect(preparations).toHaveLength(3);
    expect(firstHost.targets).toEqual([...targetIds, ...targetIds]);
    expect(host.verify).toHaveBeenCalledOnce();

    fs.writeFileSync(file, fs.readFileSync(file, 'utf8').replace('helper_0 : True := by trivial', 'helper_0 : True := by exact True.intro'));
    const changed = commitSolverSources(problem, workspace);
    state.cooperation!.canonicalCommit = changed;
    await recheck();

    expect(changed).not.toBe(canonical);
    expectVerified(changed);
    expect(preparations).toHaveLength(5);
    expect(preparations.slice(3).map(item => [item.commit, item.targets])).toEqual([[changed, targetIds], [changed, targetIds]]);
    expect(firstHost.targets).toEqual([...targetIds, ...targetIds]);
    expect(host.verify).toHaveBeenCalledTimes(2);
    const request = host.verify.mock.calls[1]![0] as MathematicsVerifierBatchRequest;
    expect(committedSource(workspace, request.targetCommit!, `${problem.projectRelative}/Submission.lean`))
      .toContain('helper_0 : True := by exact True.intro');
  });
});
