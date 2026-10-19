import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { bootstrapLocalExample, LOCAL_EXAMPLE_STATEMENT } from '../src/math/localExample';
import type { MathematicsVerifierBatchRequest, MathematicsVerifierBatchResult } from '../src/math/verifier';
import { readSolverRunState, writeSolverRunState, type SolverRunState } from '../src/solver/archive';
import { CooperativeResearch, parseCooperationPlan, readCooperationPlan } from '../src/solver/cooperation';
import { directSolverModules } from '../src/solver/modules';
import type { ResearchWorker } from '../src/solver/modules/organization';
import { commitSolverSources, committedSource, git, readSolverProblem, type SolverProblem } from '../src/solver/problem';
import { taskVersion, type CooperativeTask } from '../src/solver/tasks';

const host = vi.hoisted(() => ({ verify: vi.fn(), createSession: vi.fn() }));
vi.mock('../src/math/verifier', async importOriginal => ({
  ...await importOriginal<typeof import('../src/math/verifier')>(),
  checkManyFormalVerifications: host.verify,
  resolveMathematicsLakePackagesCache: () => undefined,
}));
vi.mock('../src/runtime/codexSession', () => ({ createCodexMathSession: host.createSession }));

function verified(request: MathematicsVerifierBatchRequest): MathematicsVerifierBatchResult {
  return { schema: 'deepscientist.mathematics.verification-batch/v1', status: 'kernel_verified',
    targetCommit: request.targetCommit!, sessionId: 'restore-fixture', events: [], startedAt: 1, checkedAt: 2, durationMs: 1,
    results: request.items.map(item => ({ ...item, sourceDeclarationHash: item.expectedSourceDeclarationHash,
      receiptId: `fixture-${request.targetCommit}-${item.theoremName}`, targetCommit: request.targetCommit,
      status: 'kernel_verified', claim: 'statement' })) as MathematicsVerifierBatchResult['results'] };
}

describe('cooperative Lead checkpoint restoration', () => {
  let directory: string, workspace: string, problem: SolverProblem, state: SolverRunState;
  let lead: ResearchWorker, peer: ResearchWorker;
  let instances: { cooperative: CooperativeResearch; controller: AbortController }[];
  let events: { event: string; details?: Record<string, unknown> }[];
  const budget = { maxTurns: Infinity, remainingMs: Infinity };

  const goalTasks = (dependsOn: string[] = []): CooperativeTask[] => problem.targets.map((target, index) => ({
    id: `goal_${index}`, kind: 'goal', objective: `Prove ${target.theoremName}.`,
    theoremName: target.theoremName, proofPath: target.proofPath, dependsOn, revision: 0,
  }));
  const savePlan = (tasks: CooperativeTask[]) => {
    const plan = parseCooperationPlan(problem, { tasks });
    fs.writeFileSync(path.join(workspace, 'RESEARCH.md'), '```math-plan\n' + JSON.stringify(plan) + '\n```');
    state.cooperation!.tasks = plan.tasks.map(task => ({ task, status: 'pending', attempts: 0 }));
    state.cooperation!.groups = plan.groups.map(group => ({ group, turns: 0 }));
    return plan;
  };
  const create = (requestLead = false) => {
    if (requestLead) state.cooperation!.error = 'A Lead assessment is requested.';
    const controller = new AbortController();
    const cooperative = new CooperativeResearch({ state, workers: [lead, peer],
      access: new Map([lead, peer].map(worker => [worker.id, { environment: {}, retrievalRoot: directory }])),
      signal: controller.signal, save: () => {}, emit: (event, details) => events.push({ event, details }),
      modules: directSolverModules, exclusiveCheck: async check => check() });
    instances.push({ cooperative, controller });
    return cooperative;
  };
  const restart = async (cooperative: CooperativeResearch) => {
    const instance = instances.find(item => item.cooperative === cooperative)!;
    instance.controller.abort();
    await cooperative.stop();
    const stateFile = path.join(directory, 'state.json');
    writeSolverRunState(stateFile, state);
    state = readSolverRunState(stateFile);
    return create();
  };
  const source = (worker = lead) => fs.readFileSync(path.join(worker.worktree, problem.projectRelative, 'Submission.lean'), 'utf8');
  const canonicalSource = () => committedSource(workspace, state.cooperation!.canonicalCommit!,
    `${problem.projectRelative}/Submission.lean`);
  const writeProof = (worker: ResearchWorker, name: 'add_zero' | 'zero_add', body: string, prefix = '') => {
    const target = name === 'add_zero' ? 'n + 0 = n := by sorry' : '0 + n = n := by sorry';
    expect(source(worker)).toContain(target);
    fs.writeFileSync(path.join(worker.worktree, problem.projectRelative, 'Submission.lean'),
      prefix + source(worker).replace(target, target.replace('by sorry', body)));
  };
  const leadAssignment = async (cooperative: CooperativeResearch) => {
    const assignment = await cooperative.next(lead, budget);
    expect(assignment?.kind).toBe('lead');
    return assignment;
  };
  const deliverPeerProof = async (cooperative: CooperativeResearch, name: 'add_zero' | 'zero_add', body: string) => {
    const assignment = await cooperative.next(peer, budget);
    expect(assignment?.kind).toBe('task');
    if (assignment?.kind !== 'task') throw new Error('missing_peer_assignment');
    expect(assignment.task.theoremName).toBe(`Tutorial.${name}`);
    expect(cooperative.started(peer, assignment)).toBe(true);
    writeProof(peer, name, body);
    await cooperative.deliver(peer, assignment, commitSolverSources(problem, peer.worktree));
    expect(state.cooperation!.tasks.find(node => node.task.id === assignment.task.id)?.status).toBe('integrated');
  };

  beforeEach(() => {
    host.verify.mockReset().mockImplementation(async request => verified(request));
    host.createSession.mockReset().mockImplementation(() => { throw new Error('real_models_are_not_used_in_restore_tests'); });
    directory = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'solver-restore-test-')));
    workspace = path.join(directory, 'workspace');
    const receipt = bootstrapLocalExample(workspace);
    problem = readSolverProblem(workspace, receipt.activeProblemPath);
    const peerWorkspace = path.join(directory, 'peer');
    git(workspace, ['worktree', 'add', '--quiet', '--detach', peerWorkspace, problem.baseCommit]);
    lead = { id: 'solver', role: 'lead', worktree: workspace, ownedFiles: problem.ownedFiles };
    peer = { id: 'researcher', role: 'researcher', worktree: peerWorkspace, ownedFiles: problem.ownedFiles };
    state = { schema: 'deepscientist.math.solver.v1', runId: 'restore-fixture', problem,
      taskDigest: 'task', buildDigest: 'build', environmentDigest: 'environment', evaluatorDigest: 'evaluator',
      model: 'unused', effort: 'unused', worktree: workspace, phase: 'running', turns: 0, failures: [],
      cooperation: { canonicalCommit: problem.baseCommit, tasks: [] } };
    instances = []; events = [];
    savePlan(goalTasks());
  });
  afterEach(async () => {
    for (const instance of instances) {
      instance.controller.abort();
      await instance.cooperative.stop();
    }
    expect(host.createSession).not.toHaveBeenCalled();
    vi.restoreAllMocks();
    fs.rmSync(directory, { recursive: true, force: true });
  });

  it.each(['$$n + 0 = n$$', '$&', "$'", '$`'])
  ('preserves exact mathematical text %s without invalidating completed findings or their consumers', async text => {
    const objective = `Investigate ${text}; preserve this mathematical contract exactly.`;
    const plan = savePlan([{ id: 'research', kind: 'research', objective, dependsOn: [], revision: 0 }, ...goalTasks(['research'])]);
    const research = state.cooperation!.tasks[0];
    research.status = 'completed'; research.attempts = 1;
    research.finding = 'A concrete library connection was already established.';
    state.cooperation!.planEdited = true;
    const versions = state.cooperation!.tasks.map(node => taskVersion(node.task));
    const cooperative = create();

    await cooperative.restore();

    expect(readCooperationPlan(problem, workspace)).toEqual(plan);
    expect(state.cooperation!.tasks.map(node => taskVersion(node.task))).toEqual(versions);
    expect(state.cooperation!.tasks[0]).toMatchObject({ status: 'completed', finding: research.finding, attempts: 1 });
    expect(events.filter(item => item.event === 'plan_updated').flatMap(item => item.details?.invalidated ?? [])).toEqual([]);
  });

  it('recovers a valid initial saved plan and proceeds without another initial Lead planning turn', async () => {
    const plan = readCooperationPlan(problem, workspace);
    commitSolverSources(problem, workspace);
    state.cooperation!.tasks = []; state.cooperation!.groups = undefined;
    const cooperative = create();

    await cooperative.restore();

    expect(state.cooperation!.tasks.map(node => node.task)).toEqual(plan.tasks);
    const nextLead = cooperative.next(lead, budget);
    await deliverPeerProof(cooperative, 'add_zero', 'by rfl');
    await deliverPeerProof(cooperative, 'zero_add', 'by exact Nat.zero_add n');
    expect((await nextLead)?.kind).toBe('assemble');
    expect(state.cooperation!.initialPlanFallback).toBeUndefined();
  });

  it('preserves a committed Lead proof and its new library import after process restoration', async () => {
    const cooperative = create(true);
    await leadAssignment(cooperative);
    writeProof(lead, 'add_zero', 'by rfl', 'import Mathlib.Data.Nat.Basic\n\n');
    commitSolverSources(problem, workspace);
    expect(git(workspace, ['diff', 'HEAD', '--name-only', '--', `${problem.projectRelative}/Submission.lean`])).toBe('');
    const resumed = await restart(cooperative);

    await resumed.restore();

    expect(canonicalSource()).toBe(source());
    expect(canonicalSource()).toContain('import Mathlib.Data.Nat.Basic');
    expect(canonicalSource()).toContain('n + 0 = n := by rfl');
    expect(canonicalSource()).toContain('0 + n = n := by sorry');
  });

  it('merges an uncommitted Lead proof with a newer independently integrated peer proof', async () => {
    savePlan([...goalTasks()].reverse());
    const cooperative = create(true);
    await leadAssignment(cooperative);
    await deliverPeerProof(cooperative, 'zero_add', 'by exact Nat.zero_add n');
    expect(canonicalSource()).toContain('0 + n = n := by exact Nat.zero_add n');
    expect(source()).toBe(LOCAL_EXAMPLE_STATEMENT);
    writeProof(lead, 'add_zero', 'by rfl');
    const resumed = await restart(cooperative);

    await resumed.restore();

    expect(source()).toContain('n + 0 = n := by rfl');
    expect(source()).toContain('0 + n = n := by exact Nat.zero_add n');
    expect(canonicalSource()).toBe(source());
    expect(state.cooperation!.tasks.find(node => node.task.theoremName === 'Tutorial.zero_add')?.status).toBe('integrated');
    expect(events.filter(item => item.event === 'lead_draft_preserved')).toEqual([]);
  });

  it.each(['unknown-seed', 'conflicting-declaration'] as const)
  ('preserves a %s draft as advisory evidence without reverting accepted sources or duplicating recovery records', async scenario => {
    const unknownSeed = scenario === 'unknown-seed';
    if (unknownSeed) savePlan([...goalTasks()].reverse());
    const cooperative = create(true);
    await leadAssignment(cooperative);
    await deliverPeerProof(cooperative, unknownSeed ? 'zero_add' : 'add_zero',
      unknownSeed ? 'by exact Nat.zero_add n' : 'by rfl');
    const acceptedSource = canonicalSource();
    const acceptedTask = unknownSeed ? 'Tutorial.zero_add' : 'Tutorial.add_zero';
    const draftBody = unknownSeed ? 'by rfl' : 'by exact Nat.add_zero n';
    writeProof(lead, 'add_zero', draftBody);
    if (unknownSeed) delete state.cooperation!.leadSeedCommit;
    const resumed = await restart(cooperative);

    await resumed.restore();

    expect(canonicalSource()).toBe(acceptedSource);
    expect(source()).toBe(acceptedSource);
    expect(state.cooperation!.tasks.find(node => node.task.theoremName === acceptedTask)?.status).toBe('integrated');
    const preserved = state.cooperation!.deliveries!.filter(record => record.producer === lead.id && record.kind === 'progress');
    expect(preserved).toHaveLength(1);
    const delivery = preserved[0]!;
    expect(delivery).toMatchObject({ status: 'advisory', summary: expect.stringContaining('Saved Lead draft pending integration:') });
    expect(delivery.evidence).toBeUndefined();
    expect(delivery.commit).toBeTypeOf('string');
    const draftCommit = delivery.commit!;
    expect(committedSource(workspace, draftCommit, `${problem.projectRelative}/Submission.lean`))
      .toContain(`n + 0 = n := ${draftBody}`);
    expect(git(workspace, ['rev-parse', `refs/math/${state.runId}/evidence/${draftCommit}`])).toBe(draftCommit);
    expect(events.filter(item => item.event === 'lead_draft_preserved')).toHaveLength(1);
    expect(state.check).toBeUndefined();

    const secondRestore = await restart(resumed);
    await secondRestore.restore();

    expect(canonicalSource()).toBe(acceptedSource);
    expect(state.cooperation!.deliveries!.filter(record => record.producer === lead.id && record.kind === 'progress'))
      .toEqual(preserved);
    expect(events.filter(item => item.event === 'lead_draft_preserved')).toHaveLength(1);
    expect(state.cooperation!.tasks.find(node => node.task.theoremName === acceptedTask)?.status).toBe('integrated');
    expect(state.check).toBeUndefined();
  });
});
