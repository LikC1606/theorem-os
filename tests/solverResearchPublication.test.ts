import fs from 'node:fs';
import path from 'node:path';
import { afterEach, beforeEach, expect, it, vi } from 'vitest';
import type { SolverRunState } from '../src/solver/archive';
import { parseCooperationPlan, type CooperativeResearch } from '../src/solver/cooperation';
import * as knowledgeApplications from '../src/solver/knowledgeApplications';
import { buildResearchContext } from '../src/solver/modules/context';
import type { ResearchWorker } from '../src/solver/modules/organization';
import { committedSource, commitSolverSources, git } from '../src/solver/problem';
import { pendingResearchChallenges } from '../src/solver/researchChallenges';
import { pendingResearchHandoffs } from '../src/solver/researchHandoffs';
import { captureResearchBasis, researchSourceDigest } from '../src/solver/researchRecords';
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
const freezeResearchBasis = () => action.assignment.researchBasis = captureResearchBasis(action.task, {
  problemReceiptDigest: state.problem.receiptDigest, environmentDigest: state.environmentDigest,
  sourceDigest: researchSourceDigest(Object.fromEntries(state.problem.ownedFiles.map(file => [file,
    committedSource(workers[1].worktree, action.assignment.seedCommit, `${state.problem.projectRelative}/${file}`)]))),
  tasks: state.cooperation!.tasks, deliveries: state.cooperation!.deliveries,
});
const ordinaryResearch = () => {
  const node = state.cooperation!.tasks[0];
  const task = { ...node.task, kind: 'research' as const, theoremName: undefined, type: undefined, proofPath: undefined,
    objective: 'Retain the exact classification argument and remaining gap.' };
  action = { kind: 'task', task, assignment: { ...action.assignment, taskDigest: taskVersion(task) } };
  node.task = task; node.assignment = action.assignment; node.status = 'running';
  return node;
};
const gateKnowledgeChecks = (count = 1) => {
  const checking = deferred<[]>(), entered = deferred();
  let calls = 0;
  vi.spyOn(knowledgeApplications, 'checkKnowledgeApplications').mockImplementation(() => {
    if (++calls === count) entered.resolve();
    return checking.promise;
  });
  return { entered: entered.promise, release: () => checking.resolve([]) };
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

it('publishes to mandatory Lead input while proof remains active, without touching live files or granting acceptance', async () => {
  const basis = freezeResearchBasis();
  const interrupt = vi.fn(async () => {});
  cooperative.activate(workers[1], action, interrupt, async () => {});
  const file = path.join(workers[1].worktree, 'RESEARCH.md');
  fs.writeFileSync(file, 'UNFINISHED_LIVE_PROOF_NOTES');
  git(workers[1].worktree, ['add', 'RESEARCH.md']);
  const index = git(workers[1].worktree, ['write-tree']);
  const head = git(workers[1].worktree, ['rev-parse', 'HEAD']);
  await publish({ kind: 'research', finding: finding() });
  const node = state.cooperation!.tasks[0], [delivery] = state.cooperation!.deliveries!;
  expect(cooperative.current(action)).toBe(true);
  expect(node.status).toBe('running'); expect(node.proof).toBeUndefined(); expect(node.finding).toBeUndefined();
  expect(state.cooperation!.blockers ?? []).toEqual([]); expect(interrupt).not.toHaveBeenCalled();
  expect(git(workers[1].worktree, ['rev-parse', 'HEAD'])).toBe(head);
  expect(git(workers[1].worktree, ['write-tree'])).toBe(index);
  expect(fs.readFileSync(file, 'utf8')).toBe('UNFINISHED_LIVE_PROOF_NOTES');
  expect(committedSource(workers[0].worktree, delivery.commit!, 'RESEARCH.md')).toBe(delivery.finding);
  expect(delivery.researchRecord).toMatchObject({ id: delivery.id, complete: false, basis,
    assignmentKey: assignmentDeliveryFile(action.assignment), seedCommit: action.assignment.seedCommit, commit: delivery.commit });
  expect(node.researchCompletion).toBeUndefined();
  expect(Object.isFrozen(delivery.researchRecord)).toBe(true);
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

it('resolves a gap correction that fails again before its complete replacement is recorded', async () => {
  const goal = state.cooperation!.tasks.find(node => node.task.kind === 'goal')!.task;
  const gap = { consumer: { taskId: goal.id, taskDigest: taskVersion(goal) }, previousGap: 'The original missing inference',
    reduced: 'The checked special case', remaining: 'The uniform classification', evidenceScope: 'Checked special-case sources',
    reconsiderWhen: ['A uniform classification lemma is available'] };
  const log = path.join(workers[1].worktree, assignmentDeliveryFile(action.assignment)), cursors = {};
  const append = (value: unknown) => fs.appendFileSync(log, JSON.stringify({ kind: 'research', finding: value }) + '\n');
  const poll = () => (cooperative as any).readWorkerDeliveries(workers[1], action, cursors);
  append({ ...finding(), mathematicalGap: { ...gap, previousDeliveryId: 'ordinary-research-is-not-a-gap' } });
  await poll();
  const first = state.cooperation!.deliveryReceipts![0];
  expect(first.issues[0].path).toBe('mathematicalGap.previousDeliveryId');
  const { previousGap: _omitted, ...incompleteGap } = gap;
  append({ ...finding(), replacesReceipt: first.id, mathematicalGap: incompleteGap });
  await poll();
  const second = state.cooperation!.deliveryReceipts![1];
  expect(second).toMatchObject({ status: 'needs-correction', replacesReceipt: first.id,
    issues: [{ path: 'mathematicalGap.previousGap' }] });
  expect(first.status).toBe('needs-correction');
  expect(state.cooperation!.deliveries ?? []).toEqual([]);
  // The verified link must survive durable archive serialization before correction.
  state.cooperation!.deliveryReceipts = JSON.parse(JSON.stringify(state.cooperation!.deliveryReceipts));
  append({ ...finding(), replacesReceipt: second.id, mathematicalGap: gap });
  await poll();
  expect(state.cooperation!.deliveryReceipts!.map(receipt => receipt.status)).toEqual(['recorded', 'recorded']);
  expect(state.cooperation!.tasks[0].feedback).toBeUndefined();
  expect(state.cooperation!.deliveries).toHaveLength(1);
  expect(state.cooperation!.deliveries![0].mathematicalGap).toEqual(gap);
  expect(state.cooperation!.tasks[0].status).toBe('running');
  expect(state.cooperation!.tasks[0].proof).toBeUndefined();
});

it.each(['environment', 'problem'] as const)('does not bind an old finding to a new %s after asynchronous application checking', async change => {
  const { entered, release } = gateKnowledgeChecks();
  const pending = publish({ kind: 'research', finding: finding() });
  await entered;
  if (change === 'environment') state.environmentDigest = 'replacement-environment';
  else state.problem = { ...state.problem, receiptDigest: 'replacement-problem' };
  release(); await pending;
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

it('freezes a complete source event larger than 114 KB without reading or changing its active writer', async () => {
  const relative = 'Submission.lean', file = path.join(workers[1].worktree, state.problem.projectRelative, relative);
  const original = fs.readFileSync(file, 'utf8');
  const saved = original + '\ntheorem retained_support : True := by\n' +
    ('  -- Complete supporting proof retained in this immutable event.\n'.repeat(2000)) + '  trivial\n';
  fs.writeFileSync(file, saved);
  const head = git(workers[1].worktree, ['rev-parse', 'HEAD']);
  const index = git(workers[1].worktree, ['write-tree']);
  const notes = path.join(workers[1].worktree, 'RESEARCH.md');
  fs.writeFileSync(notes, 'The active proof notes remain writable.');
  const event = { kind: 'research', sources: { [relative]: saved }, finding: {
    ...finding(), leanChecks: [{ status: 'passed', path: relative, declarations: ['retained_support'] }],
  } };
  const line = JSON.stringify(event) + '\n';
  expect(Buffer.byteLength(line)).toBeGreaterThan(114_000);
  fs.writeFileSync(path.join(workers[1].worktree, assignmentDeliveryFile(action.assignment)), line);
  const { entered, release } = gateKnowledgeChecks();
  const pending = (cooperative as any).readWorkerDeliveries(workers[1], action, {});
  await entered;
  const newer = saved + '\nlemma later_support : True := by trivial\n';
  fs.writeFileSync(file, newer);
  fs.writeFileSync(notes, 'Later live notes.');
  release(); await pending;
  const [record] = state.cooperation!.deliveries!;
  expect(committedSource(workers[0].worktree, record.commit!, `${state.problem.projectRelative}/${relative}`)).toBe(saved);
  expect(record.artifacts).toMatchObject({ scope: 'advisory-unverified', commit: record.commit,
    artifacts: [{ proofPath: relative, declarations: [{ name: 'retained_support', draft: false }] }],
    reportedChecks: [{ status: 'passed', path: relative, declarations: ['retained_support'] }] });
  expect(record.artifactWarning).toBeUndefined();
  expect(git(workers[1].worktree, ['rev-parse', 'HEAD'])).toBe(head);
  expect(git(workers[1].worktree, ['write-tree'])).toBe(index);
  expect(fs.readFileSync(file, 'utf8')).toBe(newer);
  expect(fs.readFileSync(notes, 'utf8')).toBe('Later live notes.');
  expect(state.cooperation!.tasks[0].status).toBe('running');
  expect(state.cooperation!.tasks[0].proof).toBeUndefined();
  expect(state.cooperation!.tasks[0].researchCompletion).toBeUndefined();
  expect(state.check).toBeUndefined();
});

it.each([null, [], {}, { 'Submission.lean': 42 }, { '../Submission.lean': 'outside' },
  { 'Submission.lean': '', 'Other.lean': '' }, { 'Submission.lean': '数'.repeat(333_334) }])(
  'rejects invalid or oversized source snapshots without changing the live writer (%#)', async sources => {
    const head = git(workers[1].worktree, ['rev-parse', 'HEAD']);
    await expect(publish({ kind: 'research', sources, finding: finding() })).rejects.toMatchObject({
      message: 'math_delivery_invalid', issues: [{ path: 'sources' }],
    });
    expect(git(workers[1].worktree, ['rev-parse', 'HEAD'])).toBe(head);
    expect(state.cooperation!.deliveries ?? []).toEqual([]);
  });

it('requires every owned Lean file and refuses to combine source bytes with a commit', async () => {
  const source = committedSource(workers[1].worktree, action.assignment.seedCommit, `${state.problem.projectRelative}/Submission.lean`);
  const sources = { 'Submission.lean': source };
  await expect(publish({ kind: 'research', sources, commit: action.assignment.seedCommit, finding: finding() }))
    .rejects.toMatchObject({ message: 'math_delivery_invalid', issues: [{ path: 'sources' }] });
  state.problem = { ...state.problem, ownedFiles: [...state.problem.ownedFiles, 'Submission/Helpers.lean'] };
  await expect(publish({ kind: 'research', sources, finding: finding() }))
    .rejects.toMatchObject({ message: 'math_delivery_invalid', issues: [{ path: 'sources' }] });
  expect(state.cooperation!.deliveries ?? []).toEqual([]);
});

it('checks the frozen original declarations before retaining an explicit source snapshot', async () => {
  const file = `${state.problem.projectRelative}/Submission.lean`;
  const original = committedSource(workers[1].worktree, action.assignment.seedCommit, file);
  await expect(publish({ kind: 'research', sources: { 'Submission.lean': original.replace('n + 0 = n', 'n + 0 = 0') },
    finding: finding() })).rejects.toThrow('math_original_declaration_changed');
  expect(committedSource(workers[1].worktree, git(workers[1].worktree, ['rev-parse', 'HEAD']), file)).toBe(original);
  expect(state.cooperation!.deliveries ?? []).toEqual([]);
});

it('keeps a malformed final research report on its original assignment and accepts its corrected finding', async () => {
  const node = ordinaryResearch(), task = node.task;
  freezeResearchBasis();
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
  expect(node.researchCompletion).toBe(delivery.researchRecord);
  expect(node.researchCompletion).toMatchObject({ id: delivery.id, complete: true,
    basis: originalAssignment.researchBasis, commit: validCommit });
  expect(committedSource(workers[0].worktree, delivery.commit!, 'RESEARCH.md')).toBe(finalNotes);
  expect(node.proof).toBeUndefined(); expect(state.check).toBeUndefined();
});

it('records complete notes with their frozen dispatch inputs and persists completion together with its pinned delivery', async () => {
  const node = ordinaryResearch(), basis = freezeResearchBasis();
  const { entered, release } = gateKnowledgeChecks();
  const notes = path.join(workers[1].worktree, 'RESEARCH.md');
  fs.writeFileSync(notes, JSON.stringify({ summary: 'A complete exact derivation.', conclusion: 'supporting' }));
  const commit = commitSolverSources(state.problem, workers[1].worktree);
  const snapshots: SolverRunState[] = [];
  (cooperative as any).input.save = () => snapshots.push(JSON.parse(JSON.stringify(state)));
  const pending = cooperative.deliver(workers[1], action, commit);
  await entered;
  action.assignment.researchBasis = captureResearchBasis(action.task, { ...basis, sourceDigest: 'newer-unrelated-context',
    tasks: state.cooperation!.tasks });
  release(); await pending;
  const [delivery] = state.cooperation!.deliveries!.filter(item => item.kind === 'research');
  expect(node.status).toBe('completed');
  expect(node.researchCompletion).toBe(delivery.researchRecord);
  expect(delivery.researchRecord).toMatchObject({ id: delivery.id, taskId: action.task.id, complete: true,
    seedCommit: action.assignment.seedCommit, commit, basis });
  expect(delivery.researchRecord!.basis.sourceDigest).not.toBe(action.assignment.researchBasis.sourceDigest);
  expect(Object.isFrozen(delivery.researchRecord)).toBe(true);
  expect(Object.isFrozen(delivery.researchRecord!.basis)).toBe(true);
  expect(git(workers[0].worktree, ['rev-parse', `refs/math/${state.runId}/evidence/${commit}`])).toBe(commit);
  expect(snapshots.some(snapshot => snapshot.cooperation!.tasks[0].status === 'completed')).toBe(true);
  for (const snapshot of snapshots) if (snapshot.cooperation!.tasks[0].status === 'completed') {
    const completion = snapshot.cooperation!.tasks[0].researchCompletion!;
    expect(snapshot.cooperation!.deliveries).toContainEqual(expect.objectContaining({ id: completion.id, researchRecord: completion }));
  }
});

it('does not complete a research assignment superseded while knowledge applications are checked', async () => {
  const node = ordinaryResearch(); freezeResearchBasis();
  const { entered, release } = gateKnowledgeChecks();
  fs.writeFileSync(path.join(workers[1].worktree, 'RESEARCH.md'), JSON.stringify({ summary: 'Old exact inputs.', conclusion: 'supporting' }));
  const pending = cooperative.deliver(workers[1], action, commitSolverSources(state.problem, workers[1].worktree));
  await entered;
  node.assignment = { ...action.assignment, assignmentId: 'replacement-responsibility' };
  release(); await pending;
  expect(node.status).toBe('running'); expect(node.finding).toBeUndefined(); expect(node.researchCompletion).toBeUndefined();
  expect(state.cooperation!.deliveries ?? []).toEqual([]);
});

it('does not invent a completion basis for legacy assignments when a newer context arrives during checking', async () => {
  const node = ordinaryResearch();
  expect(action.assignment.researchBasis).toBeUndefined();
  const { entered, release } = gateKnowledgeChecks();
  fs.writeFileSync(path.join(workers[1].worktree, 'RESEARCH.md'), JSON.stringify({ summary: 'Legacy saved work.', conclusion: 'inconclusive' }));
  const pending = cooperative.deliver(workers[1], action, commitSolverSources(state.problem, workers[1].worktree));
  await entered; freezeResearchBasis(); release(); await pending;
  expect(node.status).toBe('completed');
  expect(node.researchCompletion).toBeUndefined();
  expect(state.cooperation!.deliveries!.find(item => item.kind === 'research')!.researchRecord).toBeUndefined();
});

it('freezes explicit finding content before asynchronous checks', async () => {
  freezeResearchBasis();
  const { entered, release } = gateKnowledgeChecks();
  const output = { summary: 'Frozen exact argument.', conclusion: 'supporting', argument: { inference: 'Original inference' } };
  const pending = publish({ kind: 'research', finding: output });
  await entered;
  output.summary = 'Changed after submission'; output.argument.inference = 'Later unrelated inference';
  release(); await pending;
  const [delivery] = state.cooperation!.deliveries!;
  expect(JSON.parse(delivery.finding!)).toMatchObject({ summary: 'Frozen exact argument.', argument: { inference: 'Original inference' } });
  expect(committedSource(workers[0].worktree, delivery.commit!, 'RESEARCH.md')).toBe(delivery.finding);
  expect(delivery.researchRecord).toMatchObject({ complete: false, id: delivery.id });
});
