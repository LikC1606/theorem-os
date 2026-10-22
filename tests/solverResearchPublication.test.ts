import fs from 'node:fs';
import path from 'node:path';
import { afterEach, beforeEach, expect, it, vi } from 'vitest';
import type { SolverRunState } from '../src/solver/archive';
import type { TaskProof } from '../src/solver/cooperativeProof';
import { parseCooperationPlan, type CooperativeResearch } from '../src/solver/cooperation';
import { buildResearchContext } from '../src/solver/modules/context';
import type { ResearchWorker } from '../src/solver/modules/organization';
import { committedSource, commitSolverSources, git } from '../src/solver/problem';
import { pendingResearchChallenges } from '../src/solver/researchChallenges';
import { pendingResearchHandoffs } from '../src/solver/researchHandoffs';
import { assignmentDeliveryFile, taskVersion, type CooperativeAction } from '../src/solver/tasks';
import { deferred } from './helpers/async';
import { cooperativeResearch } from './helpers/cooperation';
import { leadWorker, localExample, peerWorker, solverState } from './helpers/solver';

let directory: string, state: SolverRunState, workers: ResearchWorker[], cooperative: CooperativeResearch;
let controller: AbortController, action: Extract<CooperativeAction, { kind: 'task' }>;
const finding = (summary = 'EXACT_LOCAL_COUNTEREXAMPLE') => ({ summary, conclusion: 'refuted', needsDecision: true,
  evidenceRefs: ['nine-listed-constraints-only'], remainingObligations: ['original_goal_1'] });
const publish = (value: unknown) => (cooperative as any).receive(workers[1], action, value, true);
const create = () => cooperativeResearch({ state, workers, retrievalRoot: directory, signal: controller.signal });
const blockedProof = () => {
  const node = state.cooperation!.tasks[0];
  const proof = { taskDigest: taskVersion(node.task), passed: false, commit: state.problem.baseCommit,
    sourceDigest: 'source', verification: { status: 'failed', targetCommit: state.problem.baseCommit, results: [] } } as unknown as TaskProof;
  node.status = 'blocked'; node.proof = proof;
  const checking = deferred<[]>();
  vi.spyOn(cooperative as any, 'knowledgeUses').mockReturnValue(checking.promise);
  return { node, proof, release: () => checking.resolve([]) };
};

beforeEach(() => {
  const example = localExample('research-publication-', 'lead'), { workspace, problem } = example;
  directory = example.directory;
  workers = [leadWorker(problem, workspace, 'lead'), ...['proof', 'other'].map(id => peerWorker(example, id))];
  const parsed = parseCooperationPlan(problem, { tasks: [{ id: 'helper', kind: 'lemma', objective: 'Prove the exact helper.',
    theoremName: 'Tutorial.helper', type: 'True', proofPath: 'Submission.lean', sharing: 'group' },
    { id: 'other', kind: 'research', objective: 'Independent route', groupId: 'other' },
    ...problem.targets.map((target, index) => ({ id: `original_goal_${index + 1}`, kind: 'goal', objective: 'Original goal',
      theoremName: target.theoremName, proofPath: target.proofPath, status: 'paused' }))],
    groups: [{ id: 'main', objective: 'Main route' }, { id: 'other', objective: 'Other route' }] });
  const task = parsed.tasks[0];
  action = { kind: 'task', task, assignment: { taskId: task.id, taskDigest: taskVersion(task), workerId: 'proof',
    seedCommit: problem.baseCommit, assignmentId: 'active-proof', dependencies: [] } };
  state = solverState(problem, workspace, { runId: 'publication-fixture', phase: 'running', cooperation: { canonicalCommit: problem.baseCommit,
      groups: parsed.groups.map(group => ({ group, turns: 0 })), tasks: parsed.tasks.map(task => ({ task, attempts: 1,
        status: task.id === 'helper' ? 'running' : 'pending', ...(task.id === 'helper' ? { assignment: action.assignment } : {}) })) } });
  controller = new AbortController(); cooperative = create();
});
afterEach(async () => {
  vi.restoreAllMocks();
  controller.abort(); await cooperative.stop(); fs.rmSync(directory, { recursive: true, force: true });
});

it.each(['task', 'status', 'assignment', 'proof', 'integrated-check', 'environment', 'removed'] as const)
('does not publish an old proof when %s changes during application checking', async change => {
  const { node, proof, release } = blockedProof();
  const pending = (cooperative as any).finishProofDelivery(workers[1], node, proof, 'Old proof result', {});
  if (change === 'task') node.task = { ...node.task, revision: node.task.revision + 1 };
  if (change === 'status') node.status = 'running';
  if (change === 'assignment') node.assignment = { ...node.assignment!, assignmentId: 'new-assignment' };
  if (change === 'proof') node.proof = { ...proof, commit: 'another-check' };
  if (change === 'integrated-check') node.integratedCheck = { ...proof };
  if (change === 'environment') state.environmentDigest = 'changed-environment';
  if (change === 'removed') state.cooperation!.tasks.shift();
  release(); await pending;
  expect(state.cooperation!.deliveries ?? []).toEqual([]);
});

it('publishes an unchanged proof once when duplicate application checks finish together', async () => {
  const { node, proof, release } = blockedProof();
  const publications = [1, 2].map(() => (cooperative as any).finishProofDelivery(workers[1], node, proof, 'Same proof', {}));
  release(); await Promise.all(publications);
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
  expect(state.cooperation!.deliveryReceipts).toEqual([expect.objectContaining({
    status: 'needs-correction', taskId: action.task.id, assignmentKey: assignmentDeliveryFile(action.assignment),
    issues: [{ path: 'conclusion', message: 'Use supporting, refuted, or inconclusive.' }],
  })]);
  expect(cooperative.contextState(action, workers[1]).deliveryReceipts).toHaveLength(1);
  expect(cooperative.contextState(undefined, workers[2]).deliveryReceipts).toEqual([]);
});

it('resolves the explicitly replaced receipt only after a corrected finding is recorded', async () => {
  const log = path.join(workers[1].worktree, assignmentDeliveryFile(action.assignment));
  fs.writeFileSync(log, JSON.stringify({ kind: 'research', finding: { summary: 'Invalid', conclusion: 'accepted' } }) + '\n');
  await (cooperative as any).readWorkerDeliveries(workers[1], action, {});
  const receipt = state.cooperation!.deliveryReceipts![0];
  await publish({ kind: 'research', finding: { ...finding(), replacesReceipt: receipt.id } });
  expect(receipt.status).toBe('recorded');
  expect(state.cooperation!.tasks[0].feedback).toBeUndefined();
  const contextFile = JSON.parse(fs.readFileSync(path.join(workers[1].worktree, 'COOPERATION.json'), 'utf8'));
  expect(contextFile.deliveryReceipts).toMatchObject([{ status: 'recorded' }]);
  expect(state.cooperation!.deliveries).toHaveLength(1);
  expect(state.cooperation!.tasks[0].status).toBe('running');
  expect(state.cooperation!.tasks[0].proof).toBeUndefined();
});

it.each(['environment', 'problem'] as const)('does not bind an old finding to a new %s after asynchronous application checking', async change => {
  const checking = deferred<[]>(), entered = deferred();
  vi.spyOn(cooperative as any, 'knowledgeUses').mockImplementation(() => { entered.resolve(); return checking.promise; });
  const pending = publish({ kind: 'research', finding: finding() });
  await entered.promise;
  if (change === 'environment') state.environmentDigest = 'replacement-environment';
  else state.problem = { ...state.problem, receiptDigest: 'replacement-problem' };
  checking.resolve([]); await pending;
  expect(state.cooperation!.deliveries ?? []).toEqual([]);
  expect(state.cooperation!.tasks[0].status).toBe('running');
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

it('keeps a malformed final research report on its original assignment and accepts its corrected finding', async () => {
  const node = state.cooperation!.tasks[0];
  const task = { ...node.task, kind: 'research' as const, theoremName: undefined, type: undefined, proofPath: undefined,
    objective: 'Retain the exact classification argument and remaining gap.' };
  action = { kind: 'task', task, assignment: { ...action.assignment, taskDigest: taskVersion(task) } };
  node.task = task; node.assignment = action.assignment; node.status = 'running';
  state.workers = workers.map(worker => ({ ...worker, phase: 'running', turns: 0,
    ...(worker.id === workers[1].id ? { threadId: 'original-research-thread', sessionTaskId: task.id,
      sessionTaskVersion: taskVersion(task), sessionAssignmentId: action.assignment.assignmentId } : {}) }));
  const originalAssignment = action.assignment;
  const saved: SolverRunState[] = [];
  (cooperative as any).input.save = () => saved.push(JSON.parse(JSON.stringify(state)));
  const notes = path.join(workers[1].worktree, 'RESEARCH.md');
  const ticks = String.fromCharCode(96).repeat(3);
  const malformed = ticks + 'math-result\n{"summary":\n' + ticks;
  fs.writeFileSync(notes, malformed);
  const invalidCommit = commitSolverSources(state.problem, workers[1].worktree);
  await expect(cooperative.deliver(workers[1], action, invalidCommit)).resolves.toEqual({ checkWhole: false });
  expect(node.status).toBe('pending'); expect(node.assignment).toBe(originalAssignment);
  expect(state.workers.find(worker => worker.id === workers[1].id)?.threadId).toBe('original-research-thread');
  expect(state.cooperation!.deliveryReceipts).toEqual([expect.objectContaining({ status: 'needs-correction',
    taskId: task.id, taskDigest: taskVersion(task), assignmentKey: assignmentDeliveryFile(originalAssignment),
    code: 'math_research_delivery_invalid', issues: [{ path: '$', message: 'The research control response must contain valid JSON.' }],
  })]);
  expect(saved.some(snapshot => snapshot.cooperation?.deliveryReceipts?.length === 1)).toBe(true);
  expect(state.cooperation!.deliveries?.filter(delivery => delivery.kind === 'research') ?? []).toEqual([]);
  expect(state.cooperation!.blockers ?? []).toEqual([]);
  const resumed = await cooperative.next(workers[1], { maxTurns: Infinity, remainingMs: Infinity, aborted: false });
  expect(resumed?.kind).toBe('task');
  if (!resumed || resumed.kind !== 'task') throw new Error('Expected the same research responsibility');
  expect(resumed.assignment).toBe(originalAssignment);
  expect(state.workers.find(worker => worker.id === workers[1].id)?.threadId).toBe('original-research-thread');
  expect(fs.readFileSync(notes, 'utf8')).toBe(malformed);
  const corrected = { summary: 'Exact boundary result retained; uniform classification remains unresolved.',
    conclusion: 'inconclusive', argument: 'Complete immutable argument with quantified remaining hypotheses.' };
  const finalNotes = '# Retained derivation\n\n' + ticks + 'json\n{"nodes":["boundary","uniform"]}\n' + ticks +
    '\n\n' + ticks + 'math-result\n' + JSON.stringify(corrected) + '\n' + ticks + '\n';
  fs.writeFileSync(notes, finalNotes);
  const validCommit = commitSolverSources(state.problem, workers[1].worktree);
  await expect(cooperative.deliver(workers[1], resumed, validCommit)).resolves.toEqual({ checkWhole: false });
  expect(node.status).toBe('completed'); expect(node.assignment).toBe(originalAssignment);
  expect(state.cooperation!.deliveryReceipts![0].status).toBe('recorded');
  const [delivery] = state.cooperation!.deliveries!.filter(item => item.kind === 'research');
  expect(JSON.parse(delivery.finding!)).toMatchObject({ ...corrected, taskId: task.id, taskDigest: taskVersion(task) });
  expect(delivery.commit).toBe(validCommit);
  expect(committedSource(workers[0].worktree, delivery.commit!, 'RESEARCH.md')).toBe(finalNotes);
  expect(node.proof).toBeUndefined(); expect(state.check).toBeUndefined();
});
