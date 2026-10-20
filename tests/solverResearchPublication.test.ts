import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, beforeEach, expect, it, vi } from 'vitest';
import { bootstrapLocalExample } from '../src/math/localExample';
import type { SolverRunState } from '../src/solver/archive';
import type { TaskProof } from '../src/solver/cooperativeProof';
import { CooperativeResearch, parseCooperationPlan } from '../src/solver/cooperation';
import { directSolverModules } from '../src/solver/modules';
import { buildResearchContext } from '../src/solver/modules/context';
import type { ResearchWorker } from '../src/solver/modules/organization';
import { committedSource, commitSolverSources, git, readSolverProblem } from '../src/solver/problem';
import { pendingResearchChallenges } from '../src/solver/researchChallenges';
import { pendingResearchHandoffs } from '../src/solver/researchHandoffs';
import { assignmentDeliveryFile, taskVersion, type CooperativeAction } from '../src/solver/tasks';

let directory: string, state: SolverRunState, workers: ResearchWorker[], cooperative: CooperativeResearch;
let controller: AbortController, action: Extract<CooperativeAction, { kind: 'task' }>;
const finding = (summary = 'EXACT_LOCAL_COUNTEREXAMPLE') => ({ summary, conclusion: 'refuted', needsDecision: true,
  evidenceRefs: ['nine-listed-constraints-only'], remainingObligations: ['original_goal_1'] });
const publish = (value: unknown) => (cooperative as any).receive(workers[1], action, value, true);
const create = () => new CooperativeResearch({ state, workers, modules: directSolverModules,
  access: new Map(workers.map(worker => [worker.id, { environment: {}, retrievalRoot: directory }])),
  signal: controller.signal, save: () => {}, emit: () => {}, exclusiveCheck: async check => check() });

beforeEach(() => {
  directory = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'research-publication-')));
  const workspace = path.join(directory, 'lead'), receipt = bootstrapLocalExample(workspace);
  const problem = readSolverProblem(workspace, receipt.activeProblemPath);
  workers = [{ id: 'lead', role: 'lead', worktree: workspace, ownedFiles: problem.ownedFiles }, ...['proof', 'other'].map(id => {
    const worktree = path.join(directory, id);
    git(workspace, ['worktree', 'add', '--quiet', '--detach', worktree, problem.baseCommit]);
    return { id, role: 'researcher' as const, worktree, ownedFiles: problem.ownedFiles };
  })];
  const parsed = parseCooperationPlan(problem, { tasks: [{ id: 'helper', kind: 'lemma', objective: 'Prove the exact helper.',
    theoremName: 'Tutorial.helper', type: 'True', proofPath: 'Submission.lean', sharing: 'group' },
    { id: 'other', kind: 'research', objective: 'Independent route', groupId: 'other' },
    ...problem.targets.map((target, index) => ({ id: `original_goal_${index + 1}`, kind: 'goal', objective: 'Original goal',
      theoremName: target.theoremName, proofPath: target.proofPath, status: 'paused' }))],
    groups: [{ id: 'main', objective: 'Main route' }, { id: 'other', objective: 'Other route' }] });
  const task = parsed.tasks[0];
  action = { kind: 'task', task, assignment: { taskId: task.id, taskDigest: taskVersion(task), workerId: 'proof',
    seedCommit: problem.baseCommit, assignmentId: 'active-proof', dependencies: [] } };
  state = { schema: 'deepscientist.math.solver.v1', runId: 'publication-fixture', problem, taskDigest: 'task',
    buildDigest: 'build', environmentDigest: 'environment', evaluatorDigest: 'evaluator', model: 'unused', effort: 'unused',
    worktree: workspace, phase: 'running', turns: 0, cooperation: { canonicalCommit: problem.baseCommit,
      groups: parsed.groups.map(group => ({ group, turns: 0 })), tasks: parsed.tasks.map(task => ({ task, attempts: 1,
        status: task.id === 'helper' ? 'running' : 'pending', ...(task.id === 'helper' ? { assignment: action.assignment } : {}) })) } };
  controller = new AbortController(); cooperative = create();
});
afterEach(async () => {
  vi.restoreAllMocks();
  controller.abort(); await cooperative.stop(); fs.rmSync(directory, { recursive: true, force: true });
});

it.each(['task', 'status', 'assignment', 'proof', 'integrated-check', 'environment', 'removed'] as const)
('does not publish an old proof when %s changes during application checking', async change => {
  const node = state.cooperation!.tasks[0];
  const proof = { taskDigest: taskVersion(node.task), passed: false, commit: state.problem.baseCommit,
    sourceDigest: 'source', verification: { status: 'failed', targetCommit: state.problem.baseCommit, results: [] } } as unknown as TaskProof;
  node.status = 'blocked'; node.proof = proof;
  let release!: (value: []) => void;
  const checking = new Promise<[]>(resolve => { release = resolve; });
  vi.spyOn(cooperative as any, 'knowledgeUses').mockReturnValue(checking);
  const pending = (cooperative as any).finishProofDelivery(workers[1], node, proof, 'Old proof result', {});
  if (change === 'task') node.task = { ...node.task, revision: node.task.revision + 1 };
  if (change === 'status') node.status = 'running';
  if (change === 'assignment') node.assignment = { ...node.assignment!, assignmentId: 'new-assignment' };
  if (change === 'proof') node.proof = { ...proof, commit: 'another-check' };
  if (change === 'integrated-check') node.integratedCheck = { ...proof };
  if (change === 'environment') state.environmentDigest = 'changed-environment';
  if (change === 'removed') state.cooperation!.tasks.shift();
  release([]); await pending;
  expect(state.cooperation!.deliveries ?? []).toEqual([]);
});

it('publishes an unchanged proof once when duplicate application checks finish together', async () => {
  const node = state.cooperation!.tasks[0];
  const proof = { taskDigest: taskVersion(node.task), passed: false, commit: state.problem.baseCommit,
    sourceDigest: 'source', verification: { status: 'failed', targetCommit: state.problem.baseCommit, results: [] } } as unknown as TaskProof;
  node.status = 'blocked'; node.proof = proof;
  let release!: (value: []) => void;
  const checking = new Promise<[]>(resolve => { release = resolve; });
  vi.spyOn(cooperative as any, 'knowledgeUses').mockReturnValue(checking);
  const publications = [1, 2].map(() => (cooperative as any).finishProofDelivery(workers[1], node, proof, 'Same proof', {}));
  release([]); await Promise.all(publications);
  expect(state.cooperation!.deliveries).toHaveLength(1);
  expect(state.cooperation!.deliveries![0]).toMatchObject({ taskDigest: taskVersion(node.task), status: 'failed',
    commit: state.problem.baseCommit });
});

it('publishes to mandatory Lead input while proof remains active, without touching live files or granting acceptance', async () => {
  const interrupt = vi.fn(async () => {});
  cooperative.activate(workers[1], action, interrupt, async () => {});
  const file = path.join(workers[1].worktree, 'RESEARCH.md');
  fs.writeFileSync(file, 'UNFINISHED_LIVE_PROOF_NOTES');
  const head = git(workers[1].worktree, ['rev-parse', 'HEAD']);
  await publish({ kind: 'research', finding: finding() });
  const node = state.cooperation!.tasks[0], [delivery] = state.cooperation!.deliveries!;
  expect(cooperative.current(action)).toBe(true);
  expect(node.status).toBe('running'); expect(node.proof).toBeUndefined(); expect(node.finding).toBeUndefined();
  expect(state.cooperation!.blockers ?? []).toEqual([]); expect(interrupt).not.toHaveBeenCalled();
  expect(git(workers[1].worktree, ['rev-parse', 'HEAD'])).toBe(head);
  expect(fs.readFileSync(file, 'utf8')).toBe('UNFINISHED_LIVE_PROOF_NOTES');
  expect(committedSource(workers[0].worktree, delivery.commit!, 'RESEARCH.md')).toBe(delivery.finding);
  const context = buildResearchContext(state.problem, state, { taskText: 'Exact problem controls', root: directory,
    worktree: workers[0].worktree, environment: {}, retrievalRoot: directory, assignment: { kind: 'lead', seedCommit: head },
    frozenContexts: Object.fromEntries(state.problem.ownedFiles.filter(file => file.endsWith('.lean')).map(file => [file,
      committedSource(workers[0].worktree, state.problem.baseCommit, `${state.problem.projectRelative}/${file}`)])),
    maxOptionalContextBytes: 0 });
  expect(context.message).toContain('EXACT_LOCAL_COUNTEREXAMPLE');
  expect(context.manifest!.included).toContainEqual(expect.objectContaining({ id: 'research-challenges', required: true }));
});

it('retains multiple findings and proposals independently across restart and duplicate submissions', async () => {
  const first = { kind: 'research', finding: { ...finding(), lemmaRequests: [{ id: 'bridge', kind: 'lemma', objective: 'Repair the local gap',
    theoremName: 'Tutorial.bridge', type: 'True', proofPath: 'Submission.lean' }] } };
  await publish(first); await publish(first);
  const adopted = state.cooperation!.deliveries![0].lemmaRequests![0];
  state.cooperation!.tasks.push({ task: adopted, status: 'pending', attempts: 0 });
  await publish({ ...first, finding: { ...first.finding, summary: 'UPDATED_FINDING_AFTER_ADOPTION' } });
  await publish({ kind: 'research', finding: finding('SECOND_DISTINCT_FINDING') });
  expect(state.cooperation!.deliveries).toHaveLength(3);
  expect(pendingResearchHandoffs(state.cooperation!)).toHaveLength(1);
  expect(pendingResearchChallenges(state.cooperation!)).toHaveLength(3);
  cooperative.deactivate(workers[1]); await cooperative.stop();
  state = JSON.parse(JSON.stringify(state)); cooperative = create();
  await publish(first);
  expect(state.cooperation!.deliveries).toHaveLength(3);
  expect(pendingResearchChallenges(state.cooperation!).map(item => item.summary)).toEqual([
    'EXACT_LOCAL_COUNTEREXAMPLE', 'UPDATED_FINDING_AFTER_ADOPTION', 'SECOND_DISTINCT_FINDING']);
});

it('keeps private findings within their route and excludes stale or late events from decisions', async () => {
  await publish({ kind: 'research', finding: finding() });
  const other = state.cooperation!.tasks.find(node => node.task.id === 'other')!;
  const scoped = cooperative.contextState({ kind: 'task', task: other.task, assignment: { taskId: other.task.id,
    taskDigest: taskVersion(other.task), workerId: workers[2].id, seedCommit: state.problem.baseCommit } }, workers[2]);
  expect(JSON.stringify(scoped)).not.toContain('EXACT_LOCAL_COUNTEREXAMPLE');
  state.cooperation!.tasks[0].task = { ...action.task, revision: 1 };
  await publish({ kind: 'research', finding: finding('LATE_FINDING') });
  expect(state.cooperation!.deliveries!.at(-1)?.status).toBe('superseded');
  expect(pendingResearchChallenges(state.cooperation!)).toEqual([]);
});

it('rejects an invalid research event and continues consuming the following line', async () => {
  const log = path.join(workers[1].worktree, assignmentDeliveryFile(action.assignment));
  fs.writeFileSync(log, JSON.stringify({ kind: 'research', finding: { summary: 'Invalid', conclusion: 'accepted' } }) + '\n' +
    JSON.stringify({ kind: 'research', finding: finding() }) + '\n');
  const cursors = {};
  await (cooperative as any).readWorkerDeliveries(workers[1], action, cursors);
  expect(state.cooperation!.deliveries).toHaveLength(1);
  expect(pendingResearchChallenges(state.cooperation!)).toHaveLength(1);
});

it('tracks changed complete arguments even when short summaries and advisory conclusions match', async () => {
  const event = { kind: 'research', finding: { summary: 'Same short summary', conclusion: 'supporting', argument: 'First exact argument' } };
  await publish(event);
  const input = (cooperative as any).planningInputDigest();
  const checkpoint = (cooperative as any).checkpointInputDigest(action.task, workers[0].id);
  const ownCheckpoint = (cooperative as any).checkpointInputDigest(action.task, workers[1].id);
  await publish({ ...event, finding: { ...event.finding, argument: 'Different complete mathematical argument' } });
  expect((cooperative as any).planningInputDigest()).not.toBe(input);
  expect((cooperative as any).checkpointInputDigest(action.task, workers[0].id)).not.toBe(checkpoint);
  expect((cooperative as any).checkpointInputDigest(action.task, workers[1].id)).toBe(ownCheckpoint);
});

it('preserves notes-only Lean support under its actual commit independently of the published finding', async () => {
  const code = 'namespace Probe\nlemma retained : True := by trivial\nend Probe\n';
  fs.writeFileSync(path.join(workers[1].worktree, 'RESEARCH.md'), '```lean\n' + code + '```\n');
  const support = commitSolverSources(state.problem, workers[1].worktree);
  await publish({ kind: 'research', commit: support, finding: { ...finding(),
    leanChecks: [{ status: 'passed', path: 'RESEARCH.md', declarations: ['Probe.retained'] }] } });
  const [record] = state.cooperation!.deliveries!;
  expect(record.commit).not.toBe(support);
  expect(record.artifacts).toMatchObject({ commit: support, scope: 'advisory-unverified',
    artifacts: [{ kind: 'notes-lean', declarations: [{ name: 'Probe.retained', draft: false }] }],
    reportedChecks: [{ status: 'passed', path: 'RESEARCH.md' }] });
  expect(committedSource(workers[0].worktree, support, 'RESEARCH.md')).toContain(code);
  expect(committedSource(workers[0].worktree, record.commit!, 'RESEARCH.md')).toBe(record.finding);
});
