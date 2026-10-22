import fs from 'node:fs';
import path from 'node:path';
import { afterEach, beforeEach, expect, it, vi } from 'vitest';
import { mathDigest } from '../src/math/mathRuntimeIo';
import { readSolverRunState, writeSolverRunState, type SolverRunState } from '../src/solver/archive';
import { parseCooperationPlan, type CooperativeResearch } from '../src/solver/cooperation';
import { MATHEMATICAL_GAP_CONTEXT_MAX_BYTES, mathematicalGapContext, type MathematicalGap } from '../src/solver/mathematicalGaps';
import { buildResearchContext } from '../src/solver/modules/context';
import type { ResearchWorker } from '../src/solver/modules/organization';
import { committedSource, commitSolverSources } from '../src/solver/problem';
import { taskVersion, type CooperativeAction } from '../src/solver/tasks';
import { importKnowledgeRuns } from '../src/solver/theoremKnowledgeRuns';
import { deferred } from './helpers/async';
import { cooperativeResearch } from './helpers/cooperation';
import { leadWorker, localExample, peerWorker, solverState } from './helpers/solver';

let directory: string, state: SolverRunState, workers: ResearchWorker[], cooperative: CooperativeResearch;
let controller: AbortController, action: Extract<CooperativeAction, { kind: 'task' }>;
const create = () => cooperativeResearch({ state, workers, retrievalRoot: directory, signal: controller.signal });
const gap = (): MathematicalGap => {
  const consumer = state.cooperation!.tasks.find(node => node.task.kind === 'goal')!.task;
  return { consumer: { taskId: consumer.id, taskDigest: taskVersion(consumer) }, previousGap: 'Need a uniform nondegenerate count',
    reduced: 'Only a degenerate count established', remaining: 'PRIVATE_GAP_REMAINDER: c > 0 independent of q for arbitrary k',
    evidenceScope: 'A local advisory argument only', reconsiderWhen: ['An exact uniform removal input becomes available'] };
};
const publish = (value: unknown) => (cooperative as any).receive(workers[1], action, value, true);
const complete = async (extra: Record<string, unknown> = {}, render: (value: Record<string, unknown>) => string = JSON.stringify) => {
  fs.writeFileSync(path.join(workers[1].worktree, 'RESEARCH.md'), render({ summary: 'Retained exact mathematical gap',
    conclusion: 'inconclusive', mathematicalGap: gap(), ...extra }));
  const commit = commitSolverSources(state.problem, workers[1].worktree);
  await cooperative.deliver(workers[1], action, commit);
};
const leadContext = () => buildResearchContext(state.problem, { ...state, cooperation: cooperative.contextState() }, {
  taskText: 'Frozen original problem', root: directory, worktree: workers[0].worktree, environment: {}, retrievalRoot: directory,
  assignment: { kind: 'lead', seedCommit: state.problem.baseCommit }, maxOptionalContextBytes: 0,
  frozenContexts: Object.fromEntries(state.problem.ownedFiles.filter(file => file.endsWith('.lean')).map(file => [file,
    committedSource(workers[0].worktree, state.problem.baseCommit, `${state.problem.projectRelative}/${file}`)])),
});
const otherAction = (): Extract<CooperativeAction, { kind: 'task' }> => {
  const task = state.cooperation!.tasks.find(node => node.task.id === 'other')!.task;
  return { kind: 'task', task, assignment: { taskId: task.id, taskDigest: taskVersion(task), workerId: workers[2].id,
    seedCommit: state.problem.baseCommit } };
};

beforeEach(() => {
  const example = localExample('solver-gap-', 'lead'), { workspace, problem } = example;
  directory = example.directory;
  workers = [leadWorker(problem, workspace, 'lead'), ...['proof', 'other'].map(id => peerWorker(example, id))];
  const parsed = parseCooperationPlan(problem, { tasks: [{ id: 'core', kind: 'research', objective: 'Public uniform-count investigation', sharing: 'problem' },
    { id: 'other', kind: 'research', objective: 'Independent route', groupId: 'other' },
    ...problem.targets.map((target, index) => ({ id: `original_goal_${index + 1}`, kind: 'goal',
      objective: 'PRIVATE_CONSUMER_CONTRACT', theoremName: target.theoremName, proofPath: target.proofPath,
      status: 'paused', sharing: 'problem' }))],
    groups: [{ id: 'main', objective: 'Main route' }, { id: 'other', objective: 'Other route' }] });
  const task = parsed.tasks[0];
  action = { kind: 'task', task, assignment: { taskId: task.id, taskDigest: taskVersion(task), workerId: workers[1].id,
    seedCommit: problem.baseCommit, assignmentId: 'gap-assignment', dependencies: [] } };
  state = solverState(problem, workspace, { runId: 'gap-fixture', phase: 'running', cooperation: { canonicalCommit: problem.baseCommit,
      groups: parsed.groups.map(group => ({ group, turns: 0 })), tasks: parsed.tasks.map(task => ({ task, attempts: 1,
        status: task.id === 'core' ? 'running' : 'pending', ...(task.id === 'core' ? { assignment: action.assignment } : {}) })) } });
  controller = new AbortController(); cooperative = create();
});
afterEach(async () => {
  controller.abort(); await cooperative.stop(); fs.rmSync(directory, { recursive: true, force: true });
});

it('publishes a gap through the host and restores its mandatory mathematical scope after a route revision', async () => {
  await publish({ kind: 'research', finding: { summary: 'Exact current gap', conclusion: 'inconclusive', mathematicalGap: gap() } });
  const delivery = state.cooperation!.deliveries![0];
  expect(cooperative.contextState().mathematicalGaps?.[0]).toMatchObject({ deliveryId: delivery.id,
    scopeStatus: 'current-contracts', evidence: 'model-reported-advisory' });
  const context = leadContext();
  expect(context.manifest!.included).toContainEqual(expect.objectContaining({ id: 'mathematical-gaps', required: true }));
  expect(context.message).toContain('independent of q for arbitrary k');
  expect(state.cooperation!.tasks[0].proof).toBeUndefined();
  await cooperative.stop();
  state.cooperation!.tasks[0].task = { ...action.task, objective: 'A revised route', revision: 1 };
  const checkpoint = path.join(directory, 'state.json'); writeSolverRunState(checkpoint, state); state = readSolverRunState(checkpoint);
  cooperative = create();
  const history = cooperative.contextState().mathematicalGaps!;
  expect(history[0]).toMatchObject({ deliveryId: delivery.id, scopeStatus: 'historical-scope',
    remaining: 'PRIVATE_GAP_REMAINDER: c > 0 independent of q for arbitrary k' });
  expect(leadContext().message).toContain('historical-scope');
  (cooperative as any).changed();
  const file = JSON.parse(fs.readFileSync(path.join(workers[0].worktree, 'COOPERATION.json'), 'utf8'));
  expect(file.mathematicalGaps[0].scope.source.revision).toBe(0);
});

it.each(['recorded-private', 'currently-private'] as const)('hides %s consumers from peer deliveries, findings, history, files and imports', async privacy => {
  const consumer = state.cooperation!.tasks.find(node => node.task.kind === 'goal')!;
  if (privacy === 'recorded-private') consumer.task = { ...consumer.task, sharing: 'group' };
  await complete();
  expect(state.cooperation!.tasks[0].status).toBe('completed');
  state.cooperation!.history = [{ task: action.task, finding: state.cooperation!.tasks[0].finding }];
  if (privacy === 'currently-private') {
    state.cooperation!.history.push({ task: consumer.task });
    consumer.task = { ...consumer.task, sharing: 'group', revision: 1 };
  }
  const scoped = cooperative.contextState(otherAction(), workers[2]);
  expect(scoped.mathematicalGaps).toEqual([]); expect(scoped.deliveries).toEqual([]);
  expect(scoped.tasks.find(node => node.task.id === action.task.id)?.finding).toBeUndefined();
  expect(scoped.history?.find(node => node.task.id === action.task.id)?.finding).toBeUndefined();
  expect(JSON.stringify(scoped)).not.toContain('PRIVATE_GAP_REMAINDER');
  expect(cooperative.contextState(undefined, workers[2]).mathematicalGaps).toEqual([]);
  (cooperative as any).changed();
  expect(fs.readFileSync(path.join(workers[2].worktree, 'COOPERATION.json'), 'utf8')).not.toContain('PRIVATE_CONSUMER_CONTRACT');
  expect(fs.readFileSync(path.join(workers[2].worktree, 'COOPERATION.json'), 'utf8')).not.toContain('PRIVATE_GAP_REMAINDER');
  const checkpoint = path.join(directory, 'state.json'); writeSolverRunState(checkpoint, state);
  const imported = importKnowledgeRuns([checkpoint], { includeFindings: true });
  expect(imported.findings).toEqual([]);
  expect(imported.skipped.some(item => item.reason === 'math_knowledge_run_finding_private')).toBe(true);
});

it('keeps original-problem deliveries visible to idle workers while applying separate gap privacy', () => {
  const delivery = (cooperative as any).record(workers[0], undefined, 'progress', 'advisory', 'Original problem update');
  expect(cooperative.contextState(undefined, workers[2]).deliveries?.map(item => item.id)).toContain(delivery.id);
  expect(cooperative.contextState(otherAction(), workers[2]).deliveries?.map(item => item.id)).not.toContain(delivery.id);
});

it('imports a public consumer contract from immutable finding evidence and rejects detached gap metadata', async () => {
  await complete();
  const checkpoint = path.join(directory, 'state.json'); writeSolverRunState(checkpoint, state);
  const imported = importKnowledgeRuns([checkpoint], { includeFindings: true });
  expect(imported.skipped).toEqual([]);
  expect(imported.findings?.[0]).toMatchObject({ mathematicalGap: gap(),
    scope: { originalConsumer: { kind: 'goal', statementKind: 'source-header' } } });
  state.cooperation!.deliveries![0].mathematicalGap = { ...gap(), remaining: 'Forged independent metadata' };
  writeSolverRunState(checkpoint, state);
  expect(importKnowledgeRuns([checkpoint], { includeFindings: true }).skipped[0].reason).toBe('math_knowledge_run_finding_gap_scope_invalid');
});

it.each(['json', 'math-result'] as const)('imports host-normalized %s findings from immutable notes with the same admission rules', async format => {
  const fence = String.fromCharCode(96).repeat(3);
  await complete({ mathematicalGap: { ...gap(), reduced: '  Only a degenerate count established  ' } }, value => format === 'json'
    ? JSON.stringify(value)
    : 'Explanation and an illustrative JSON object:\n' + fence + 'json\n{"example":true}\n' + fence + '\n\n' +
      fence + 'math-result\n' + JSON.stringify(value) + '\n' + fence);
  const delivery = state.cooperation!.deliveries![0], normalized = state.cooperation!.tasks[0].finding!;
  const notes = committedSource(workers[1].worktree, delivery.commit!, 'RESEARCH.md');
  expect(notes).not.toContain(action.assignment.taskDigest);
  expect(JSON.parse(normalized)).toMatchObject({ taskDigest: action.assignment.taskDigest, mathematicalGap: gap() });
  fs.writeFileSync(path.join(workers[1].worktree, 'RESEARCH.md'), 'A changed live journal must not be imported.');
  const checkpoint = path.join(directory, 'state.json'); writeSolverRunState(checkpoint, state);
  const imported = importKnowledgeRuns([checkpoint], { includeFindings: true });
  expect(imported.skipped).toEqual([]);
  expect(imported.findings).toMatchObject([{ finding: normalized, notes, mathematicalGap: gap(),
    provenance: { findingDigest: mathDigest(normalized), notesDigest: mathDigest(notes), sourceCommit: delivery.commit } }]);
});

it.each(['summary', 'taskDigest', 'extra-field'] as const)('rejects a forged normalized finding %s even with a recomputed finding digest', async field => {
  await complete();
  const node = state.cooperation!.tasks[0], delivery = state.cooperation!.deliveries![0];
  const finding = JSON.parse(node.finding!);
  if (field === 'summary') finding.summary = 'Forged independently edited evidence';
  else if (field === 'taskDigest') finding.taskDigest = 'f'.repeat(64);
  else finding.unrecordedEvidence = 'This claim was never present in immutable notes';
  node.finding = JSON.stringify(finding); delivery.finding = node.finding; delivery.findingDigest = mathDigest(node.finding);
  const checkpoint = path.join(directory, 'state.json'); writeSolverRunState(checkpoint, state);
  const imported = importKnowledgeRuns([checkpoint], { includeFindings: true });
  expect(imported.findings).toEqual([]);
  expect(imported.skipped).toMatchObject([{ reason: 'math_knowledge_run_finding_source_mismatch' }]);
});

it('rejects an invalid progress consumer before writing a blocker or delivery', async () => {
  await expect(publish({ kind: 'progress', summary: 'Invalid binding',
    mathematicalGap: { ...gap(), consumer: { ...gap().consumer, taskDigest: 'f'.repeat(64) } },
    blockers: [{ mechanism: 'Spurious blocker', scope: 'A claimed local obstruction', evidenceRefs: [] }] })).rejects.toThrow('gap_consumer');
  expect(state.cooperation!.blockers ?? []).toEqual([]);
  expect(state.cooperation!.deliveries ?? []).toEqual([]);
  expect(state.cooperation!.tasks[0].status).toBe('running');
});

it('revalidates the consumer after asynchronous knowledge checks before mutating research publication state', async () => {
  const ready = deferred(), waiting = deferred();
  vi.spyOn(cooperative as any, 'knowledgeUses').mockImplementation(async () => { ready.resolve(); await waiting.promise; return []; });
  const pending = publish({ kind: 'research', finding: { summary: 'Consumer changed during verification',
    conclusion: 'inconclusive', mathematicalGap: gap(),
    blockers: [{ mechanism: 'Must not persist', scope: 'A claimed local obstruction', evidenceRefs: [] }] } });
  await ready.promise;
  const consumer = state.cooperation!.tasks.find(node => node.task.kind === 'goal')!;
  consumer.task = { ...consumer.task, objective: 'Revised original consumer', revision: 1 };
  expect(cooperative.current(action)).toBe(true);
  waiting.resolve();
  await expect(pending).rejects.toThrow('gap_consumer');
  expect(state.cooperation!.blockers ?? []).toEqual([]);
  expect(state.cooperation!.deliveries ?? []).toEqual([]);
  expect(state.cooperation!.tasks[0].status).toBe('running');
  expect(state.cooperation!.tasks[0].finding).toBeUndefined();
});

it('retains long valid evidence by reference while mandatory context stays within its byte budget', async () => {
  const reference = 'x'.repeat(800_000);
  await complete({ evidenceRefs: [reference] });
  const scoped = cooperative.contextState();
  const packet = mathematicalGapContext(scoped.mathematicalGaps!);
  expect(Buffer.byteLength(JSON.stringify(packet))).toBeLessThanOrEqual(MATHEMATICAL_GAP_CONTEXT_MAX_BYTES);
  expect(packet.entries[0]).toMatchObject({ complete: false,
    evidenceRefs: [{ complete: false, bytes: 800_000 }], read: { file: 'COOPERATION.json', collection: 'mathematicalGaps' } });
  const context = leadContext();
  expect(context.manifest!.usedBytes).toBeLessThanOrEqual(context.manifest!.maxBytes);
  expect(context.manifest!.included).toContainEqual(expect.objectContaining({ id: 'mathematical-gaps', required: true }));
  const file = JSON.parse(fs.readFileSync(path.join(workers[0].worktree, 'COOPERATION.json'), 'utf8'));
  expect(file.mathematicalGaps[0].evidenceRefs[0]).toBe(reference);
});
