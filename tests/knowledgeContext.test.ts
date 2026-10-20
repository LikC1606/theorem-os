import { afterEach, describe, expect, it, vi } from 'vitest';
import { mathDigest } from '../src/math/mathRuntimeIo';
import type { SolverRunState } from '../src/solver/archive';
import * as contextCompiler from '../src/solver/contextCompiler';
import type { CooperationState } from '../src/solver/cooperation';
import { knowledgeContextConsumers, knowledgeContextSections, type KnowledgeContextSnapshot } from '../src/solver/knowledgeContext';
import { buildResearchContext, buildStatementReviewContext, type ContextAccess } from '../src/solver/modules/context';
import type { SolverProblem } from '../src/solver/problem';
import type { StatementAction, StatementReview } from '../src/solver/statementReview';
import { taskVersion, type CooperativeAction, type CooperativeTask, type TaskRecord } from '../src/solver/tasks';
import type { TheoremKnowledgeEntry } from '../src/solver/theoremKnowledge';
import { buildKnowledgeRouteFindings } from '../src/solver/theoremKnowledgeFindings';
import type { LeanResidualGoal } from '../src/math/leanResidualGoals';
import * as residualReader from '../src/math/leanResidualGoals';

const seedCommit = 'a'.repeat(40), environmentDigest = mathDigest('current-environment');
const exactType = 'forall (q : Nat) (character : DirichletCharacter Complex q), character.IsPrimitive -> character.rootNumber = 1';
const formal = `namespace Original\ntheorem target : ${exactType} := by sorry\nend Original`;
const problem = {
  projectRelative: 'generated/p', ownedFiles: ['Submission.lean'],
  declarations: { 'Submission.lean': [{ name: 'target', header: `target : ${exactType}` }] },
  sourceImports: { 'Submission.lean': ['Mathlib.Data.Nat.Basic'] },
  sourceStructure: { 'Submission.lean': 'context' },
  targets: [{ proofPath: 'Submission.lean', theoremName: 'Original.target', declarationHash: mathDigest(exactType) }],
  receiptDigest: mathDigest('original-problem'), baseCommit: seedCommit,
  contract: { formalStatement: formal, informalStatement: 'Prove the character identity.', assumptions: [],
    statementHash: mathDigest('statement'), leanStatementHash: mathDigest('lean-statement') },
} as unknown as SolverProblem;

function entry(name: string, type = exactType, extra: Partial<TheoremKnowledgeEntry> = {}): TheoremKnowledgeEntry {
  return { id: mathDigest(name + type), contextDigest: mathDigest('archived-context'), name,
    file: 'Archived/Helpers.lean', type, typeKind: 'closed-task-type', kind: 'lemma',
    description: '', premises: [], declaration: `theorem ${name.split('.').at(-1)} : ${type} := by exact archivedProofMarker`,
    dependencies: { statement: [], proof: [], tasks: [], coverage: 'unavailable' },
    provenance: [{ kind: 'solver-check', problemId: 'previous-problem', source: '/archive/run-state.json',
      sourceDigest: mathDigest('historical-state'), receiptIds: ['historical-receipt-marker'] }], ...extra };
}
const saved = entry('Archived.character_root_identity');
const distractor = entry('Archived.measure_pushforward', 'forall (m : MeasureSpace Real), Measure.map m = m');
const snapshot = (...entries: TheoremKnowledgeEntry[]): KnowledgeContextSnapshot => ({
  digest: mathDigest('pinned-catalog'), base: { entries, evidence: 'recorded-not-replayed' },
});
function savedRouteFindings(...statements: string[]) {
  const finding = 'Archived advisory reasoning', notes = 'Archived advisory notes';
  return buildKnowledgeRouteFindings(statements.map((statement, index) => ({
    evidence: 'recorded-advisory-not-replayed', acceptance: 'not-assessed', conclusion: 'supporting',
    summary: `Saved ${statement}`, finding, notes,
    scope: { problemId: 'previous-problem', problemReceiptDigest: problem.receiptDigest, environmentDigest,
      source: { kind: 'lemma', statement, statementKind: 'closed-task-type', premises: [] }, dependencies: [] },
    evidenceRefs: [], obstructions: [], remainingObligations: [], reconsiderWhen: [],
    provenance: { source: '/archive/state.json', sourceDigest: mathDigest('archived-state'), runId: 'old-run',
      taskId: `old_${index}`, taskDigest: mathDigest(statement), groupId: 'main', deliveryId: `delivery_${index}`,
      sourceCommit: seedCommit, findingDigest: mathDigest(finding), notesDigest: mathDigest(notes) },
  })));
}
function node(id: string, kind: CooperativeTask['kind'] = 'lemma', dependsOn: string[] = [], type = exactType): TaskRecord {
  return { task: { id, kind, dependsOn, revision: 0, objective: 'Find a measure pushforward formula',
    ...(['goal', 'lemma'].includes(kind) ? { type, proofPath: 'Submission.lean',
      theoremName: kind === 'goal' ? 'Original.target' : `Original.${id}` } : {}) }, status: 'pending', attempts: 0 };
}
function routedFrontier() {
  const inputs = Array.from({ length: 4 }, (_, index) => node(`input_${index}`));
  inputs.slice(0, 3).forEach(input => { input.status = 'blocked'; });
  const closing = inputs.map(input => node(`closing_${input.task.id}`, 'lemma', [input.task.id]));
  const goal = node('original_goal', 'goal');
  goal.alternativeRoutes = inputs.map((input, index) => ({ id: `route_${index}`, targetTaskId: goal.task.id,
    prerequisiteTaskIds: [input.task.id], closingTaskId: closing[index]!.task.id }));
  const cooperation: CooperationState = { canonicalCommit: seedCommit,
    tasks: [...inputs, ...closing, goal], proofRoutes: goal.alternativeRoutes };
  return { inputs, goal, cooperation };
}
const actionFor = (record: TaskRecord): CooperativeAction => ({ kind: 'task', task: record.task,
  assignment: { taskId: record.task.id, taskDigest: taskVersion(record.task), workerId: 'researcher', seedCommit } });
const packet = (text: string) => JSON.parse(text.slice(text.indexOf('\n') + 1));
const packets = (message: string) => message.split('\n\n').filter(text => text.startsWith('Saved theorem candidates ')).map(packet);
function sections(record: TaskRecord, knowledge = snapshot(saved, distractor)) {
  return knowledgeContextSections({ problem, action: actionFor(record), knowledge, environmentDigest });
}
function build(record: TaskRecord, options: { cooperation?: CooperationState; action?: CooperativeAction;
  knowledge?: KnowledgeContextSnapshot; access?: Partial<ContextAccess>; state?: Partial<SolverRunState> } = {}) {
  const knowledge = options.knowledge ?? snapshot(saved, distractor);
  const cooperation = options.cooperation ?? { canonicalCommit: seedCommit, tasks: [record] };
  return buildResearchContext(problem, { problem, cooperation, environmentDigest, knowledgeDigest: knowledge.digest,
    ...options.state } as SolverRunState, {
    root: '/runtime', worktree: '/proof', environment: {}, taskText: 'Prove the original target.', retrievalRoot: '/library',
    assignment: options.action ?? actionFor(record), knowledgeFile: '/catalog/pinned.json', knowledgeDigest: knowledge.digest,
    knowledgeSnapshot: knowledge,
    frozenContexts: { 'Submission.lean': contextCompiler.frozenSourceContext(problem, 'Submission.lean', formal) },
    ...options.access,
  });
}

afterEach(() => vi.restoreAllMocks());

describe('automatic knowledge context', () => {
  const residualFor = (record: TaskRecord, extra: Partial<LeanResidualGoal> = {}): LeanResidualGoal => ({
    authority: 'advisory-lean-process', consumer: { taskId: record.task.id, taskDigest: taskVersion(record.task),
      theoremName: record.task.theoremName!, proofPath: record.task.proofPath! },
    goalText: 'm : MeasureSpace Real\n|- Measure.map m = m', sourceDigest: mathDigest('current-source'),
    environmentDigest, toolIdentity: mathDigest('current-tool'), file: 'Submission.lean', line: 2, column: 0,
    artifact: { path: `.lake/diagnostic-artifacts/${mathDigest('diagnostic')}.json`, digest: mathDigest('diagnostic') }, ...extra,
  });
  it('retrieves from the actual residual goal and retains exact diagnostic provenance in the retrieval ledger', () => {
    const record = node('primitive_bridge'), residual = residualFor(record);
    const sections = knowledgeContextSections({ problem, action: actionFor(record), knowledge: snapshot(saved, distractor),
      residualGoals: [residual], environmentDigest });
    expect(packet(sections[0].text)).toMatchObject({ searchSource: 'residual-goal', candidates: [{ id: distractor.id }],
      diagnostic: { artifact: residual.artifact, sourceDigest: residual.sourceDigest }, requiresFreshCheck: true });
    expect(packet(sections[0].text).candidates[0].consumers).toEqual({ command: 'knowledge consumers', id: distractor.id });
    expect(sections[0].knowledge).toMatchObject({ searchSource: 'residual-goal', diagnostic: { toolIdentity: residual.toolIdentity } });
    expect(Buffer.byteLength(sections[0].text)).toBeLessThanOrEqual(4096);
    expect(record.status).toBe('pending'); expect(record.integratedCheck).toBeUndefined();
  });

  it.each([false, true])('searches every independent case and diagnostic with its own hypotheses, reversed=%s', reversed => {
    const record = node('primitive_bridge');
    const connected = entry('Saved.connected', 'ConnectedSpace M'), prime = entry('Saved.prime', 'Nat.Prime n');
    const cases = ['case connected\nM : Type\n⊢ ConnectedSpace M', 'case prime\nn : Nat\n⊢ Nat.Prime n'];
    if (reversed) cases.reverse();
    const residuals = [residualFor(record, { goalText: cases.join('\n\n') }),
      residualFor(record, { goalText: 'x y : ℝ\n⊢ x + y = y + x', line: 3 })];
    const comm = entry('Saved.comm', '∀ (a b : ℝ), a + b = b + a');
    const [section] = knowledgeContextSections({ problem, action: actionFor(record),
      knowledge: snapshot(connected, prime, comm), residualGoals: residuals, environmentDigest });
    expect(new Set(section!.knowledge.candidateIds)).toEqual(new Set([connected.id, prime.id, comm.id]));
    expect(section!.knowledge.residualSearches).toHaveLength(3);
    const value = packet(section!.text);
    expect(value.residualCoverage).toMatchObject({ total: 3, searched: 3, omittedForRequestBudget: 0 });
    expect(section!.knowledge.residualSearches!.every(search => search.diagnostic.artifact.digest === residuals[0]!.artifact.digest)).toBe(true);
    expect(Buffer.byteLength(section!.text)).toBeLessThanOrEqual(4096);
  });

  it('reports independent residuals omitted by the batch budget with stable selection', () => {
    const record = node('primitive_bridge');
    const residual = residualFor(record, { goalText: Array.from({ length: 11 }, (_, i) => `case c${i}\nn : Nat\n⊢ Nat.Prime ${i}`).join('\n\n') });
    const run = (goalText: string) => knowledgeContextSections({ problem, action: actionFor(record), knowledge: snapshot(saved),
      residualGoals: [{ ...residual, goalText }] })[0]!;
    const forward = run(residual.goalText), reverse = run(residual.goalText.split('\n\n').reverse().join('\n\n'));
    expect(packet(forward.text).residualCoverage).toMatchObject({ total: 11, searched: 8, omittedForRequestBudget: 3 });
    expect(forward.knowledge.residualSearches).toEqual(reverse.knowledge.residualSearches);
  });

  it('retains reader omissions and search hits separately from candidates that fit the packet', () => {
    const record = node('primitive_bridge'), residual = residualFor(record);
    const large = entry('Saved.large', 'Measure.map m = m', { description: 'x'.repeat(10000) });
    const [section] = knowledgeContextSections({ problem, action: actionFor(record), knowledge: snapshot(large, distractor),
      residualGoals: [residual], residualOmissions: [{ consumer: residual.consumer, count: 3, reason: 'diagnostic-reader-budget' }] });
    expect(section!.knowledge.searchCandidateIds).toEqual(expect.arrayContaining([large.id, distractor.id]));
    expect(section!.knowledge.residualOmissions).toEqual([{ count: 3, reason: 'diagnostic-reader-budget' }]);
    expect(packet(section!.text).residualCoverage).toMatchObject({ omittedDiagnosticsAtReader: 3 });
    expect(Buffer.byteLength(section!.text)).toBeLessThanOrEqual(4096);
  });

  it('ignores another consumer, another task version and oversized goals without mutating the saved interface', () => {
    const record = node('primitive_bridge'), residual = residualFor(record);
    for (const value of [{ ...residual, consumer: { ...residual.consumer, taskId: 'private-other' } },
      { ...residual, consumer: { ...residual.consumer, taskDigest: 'old-task' } },
      { ...residual, goalText: 'x'.repeat(16001) }]) {
      const result = knowledgeContextSections({ problem, action: actionFor(record), knowledge: snapshot(saved, distractor), residualGoals: [value] });
      expect(packet(result[0].text)).toMatchObject({ searchSource: 'closed-task-type', candidates: [{ id: saved.id }] });
    }
    expect(record.task.type).toBe(exactType);
  });

  it('includes one complete scoped residual in actual context and records an optional budget omission', () => {
    const record = node('primitive_bridge'), residual = residualFor(record);
    const read = vi.spyOn(residualReader, 'readLeanResidualGoalSnapshot').mockReturnValue({ goals: [residual], omissions: [] });
    const included = build(record);
    expect(read).toHaveBeenCalledWith({ projectRoot: '/proof/generated/p', env: {}, consumers: [residual.consumer] });
    expect(included.message).toContain(residual.goalText);
    expect(included.message).toContain('advisory; not proof acceptance');
    expect(included.manifest!.included).toContainEqual(expect.objectContaining({ id: expect.stringMatching(/^residual-goal:/u), required: false }));
    expect(included.knowledgeRetrievals).toEqual([expect.objectContaining({ searchSource: 'residual-goal', included: true,
      candidateIds: [distractor.id], diagnostic: expect.objectContaining({ artifact: residual.artifact }) })]);
    const omitted = build(record, { access: { maxOptionalContextBytes: 0 } });
    expect(omitted.message).not.toContain(residual.goalText);
    expect(omitted.manifest!.omitted).toContainEqual(expect.objectContaining({ id: expect.stringMatching(/^residual-goal:/u), reason: 'optional-budget' }));
    expect(omitted.knowledgeRetrievals).toEqual([expect.objectContaining({ searchSource: 'residual-goal', included: false,
      omissionReason: 'optional-budget', diagnostic: expect.objectContaining({ artifact: residual.artifact }) })]);
    expect(omitted.message).toContain(JSON.stringify(exactType));
    expect(record.integratedCheck).toBeUndefined();
  });

  it('finds the assigned closed lemma type instead of its unrelated objective and binds the actual consumer', () => {
    const record = node('primitive_bridge'), before = structuredClone(record);
    const result = sections(record);
    expect(result).toHaveLength(1);
    expect(packet(result[0]!.text)).toMatchObject({ searchSource: 'closed-task-type',
      consumer: { taskId: record.task.id, taskDigest: taskVersion(record.task), theoremName: 'Original.primitive_bridge',
        proofPath: 'Submission.lean' }, candidates: [{ id: saved.id }] });
    expect(result[0]!.text).not.toContain(distractor.id);
    expect(record).toEqual(before);
  });

  it('uses the frozen original declaration even when a goal task claims a different type', () => {
    const original = node('original_goal', 'goal', [], distractor.type);
    const result = packet(sections(original)[0]!.text);
    expect(result).toMatchObject({ searchSource: 'frozen-source-header',
      consumer: { taskId: original.task.id, taskDigest: taskVersion(original.task), theoremName: 'Original.target' },
      candidates: [{ id: saved.id }] });
    expect(result.candidates.some((candidate: { id: string }) => candidate.id === distractor.id)).toBe(false);
  });

  it('finds the corresponding closed theorem from original header binders rather than the theorem name', () => {
    const boundProblem = structuredClone(problem);
    boundProblem.declarations['Submission.lean'] = [{ ...problem.declarations['Submission.lean']![0]!,
      header: 'target (q : Nat) (character : DirichletCharacter Complex q) : character.IsPrimitive -> character.rootNumber = 1' }];
    const original = node('original_goal', 'goal', [], distractor.type);
    const result = knowledgeContextSections({ problem: boundProblem, action: actionFor(original), knowledge: snapshot(distractor, saved) });
    expect(packet(result[0]!.text).candidates[0].id).toBe(saved.id);
  });

  it.each(['research', 'sketch'] as const)('searches the actual %s question without treating it as a proved premise', kind => {
    const record = node('investigation', kind);
    const result = packet(sections(record)[0]!.text);
    expect(result).toMatchObject({ searchSource: 'research-objective', requiresFreshCheck: true,
      consumer: { taskId: record.task.id, taskDigest: taskVersion(record.task) }, candidates: [{ id: distractor.id }] });
    expect(result.consumer).not.toHaveProperty('theoremName');
    expect(record.status).toBe('pending');
    expect(record.integratedCheck).toBeUndefined();
  });

  it('gives Lead the substantive unresolved premises and moves to their consumer when they become checked', () => {
    const core = node('core'), goal = node('original_goal', 'goal', ['core']);
    const checked = node('already_proved');
    checked.status = 'integrated';
    checked.integratedCheck = { passed: true, taskDigest: taskVersion(checked.task), conditions: [],
      verification: { status: 'kernel_verified', targetCommit: seedCommit, results: [
        { status: 'kernel_verified', targetCommit: seedCommit, receiptId: 'local-receipt' },
      ] } } as TaskRecord['integratedCheck'];
    const cooperation: CooperationState = { canonicalCommit: seedCommit, tasks: [checked, goal, core] };
    const input = { problem, cooperation, action: { kind: 'lead', seedCommit } as CooperativeAction,
      knowledge: snapshot(saved) };
    expect(knowledgeContextSections(input).map(item => packet(item.text).consumer.taskId)).toEqual(['core']);
    core.status = 'integrated'; core.integratedCheck = { ...checked.integratedCheck, taskDigest: taskVersion(core.task) };
    expect(knowledgeContextSections(input).map(item => packet(item.text).consumer.taskId)).toEqual(['original_goal']);
    expect(goal.status).toBe('pending');
  });

  it('bounds Lead frontier lookups without filling the batch with unrelated auxiliary tasks', () => {
    const cores = Array.from({ length: 5 }, (_, index) => node(`premise_${index}`));
    const goal = node('original_goal', 'goal', cores.map(item => item.task.id));
    const cooperation: CooperationState = { canonicalCommit: seedCommit, tasks: [node('unrelated'), goal, ...cores] };
    const result = knowledgeContextSections({ problem, cooperation, action: { kind: 'lead', seedCommit }, knowledge: snapshot(saved) });
    expect(result.map(item => packet(item.text).consumer.taskId)).toEqual(['premise_0', 'premise_1', 'premise_2']);
  });

  it('prepares the catalog once for distinct Lead goals while preserving each independent packet', () => {
    const types = ['NatBound', 'RealEstimate', 'MeasurePushforward'];
    const entries = types.map((type, index) => entry(`Archived.result_${index}`, type));
    let reads = 0;
    for (const item of entries) {
      const declaration = item.declaration;
      Object.defineProperty(item, 'declaration', { get: () => { reads++; return declaration; } });
    }
    const cores = types.map((type, index) => node(`core_${index}`, 'lemma', [], type));
    const goal = node('original_goal', 'goal', cores.map(item => item.task.id));
    const cooperation: CooperationState = { canonicalCommit: seedCommit, tasks: [goal, ...cores] };
    const knowledge = snapshot(...entries), expected = cores.map(record => sections(record, knowledge)[0]!);
    reads = 0;
    const result = knowledgeContextSections({ problem, cooperation, action: { kind: 'lead', seedCommit },
      knowledge, environmentDigest });
    expect(result).toEqual(expected);
    expect(result.map(item => packet(item.text).candidates[0].id)).toEqual(entries.map(item => item.id));
    expect(reads).toBe(entries.length);
  });

  it('prepares route findings once for distinct Lead goals while preserving each independent packet', () => {
    const types = ['NatBound', 'RealEstimate', 'MeasurePushforward'], knowledge = snapshot();
    knowledge.base.routeFindings = savedRouteFindings(...types);
    let reads = 0;
    for (const item of knowledge.base.routeFindings) {
      const statement = item.scope.source.statement;
      Object.defineProperty(item.scope.source, 'statement', { get: () => { reads++; return statement; } });
    }
    const cores = types.map((type, index) => node(`core_${index}`, 'lemma', [], type));
    const goal = node('original_goal', 'goal', cores.map(item => item.task.id));
    const cooperation: CooperationState = { canonicalCommit: seedCommit, tasks: [goal, ...cores] };
    const expected = cores.map(record => sections(record, knowledge)[0]!);
    expect(reads).toBe(9); reads = 0;
    const result = knowledgeContextSections({ problem, cooperation, action: { kind: 'lead', seedCommit }, knowledge, environmentDigest });
    expect(result).toEqual(expected);
    expect(new Set(result.flatMap(item => item.knowledge.routeFindingIds)).size).toBe(3);
    expect(reads).toBe(3);
  });

  it('retains unsearched consumers without displacing another frontier goal result', () => {
    const oversized = node('oversized', 'lemma', [], 'x'.repeat(16001));
    const empty = node('empty', 'research'); empty.task.objective = '';
    const valid = node('valid', 'lemma', [], distractor.type);
    const goal = node('original_goal', 'goal', [oversized.task.id, empty.task.id, valid.task.id]);
    const cooperation: CooperationState = { canonicalCommit: seedCommit, tasks: [goal, oversized, empty, valid] };
    const knowledge = snapshot(saved, distractor); knowledge.base.routeFindings = savedRouteFindings(distractor.type);
    const findingId = knowledge.base.routeFindings[0]!.id;
    const result = knowledgeContextSections({ problem, cooperation, action: { kind: 'lead', seedCommit },
      knowledge, environmentDigest });
    expect(result.map(item => packet(item.text))).toMatchObject([
      { consumer: { taskId: oversized.task.id }, status: 'input-not-searched', reason: 'input-too-large', candidates: [], routeFindings: [] },
      { consumer: { taskId: empty.task.id }, status: 'input-not-searched', reason: 'empty-input', candidates: [], routeFindings: [] },
      { consumer: { taskId: valid.task.id }, status: 'searched', candidates: [{ id: distractor.id }], routeFindings: [{ id: findingId }] },
    ]);
    expect(result[2]).toEqual(sections(valid, knowledge)[0]);
    expect(new Set(result.map(item => item.id)).size).toBe(3);
    expect(result.every(item => Buffer.byteLength(item.text) <= 4096)).toBe(true);
  });

  it('searches the preferred route first while retaining alternative frontiers within the same allowance', () => {
    const { cooperation } = routedFrontier(), before = structuredClone(cooperation);
    const input = { problem, cooperation, action: { kind: 'lead', seedCommit } as CooperativeAction,
      knowledge: snapshot(saved), environmentDigest };
    const result = knowledgeContextSections(input);
    expect(result.map(item => packet(item.text).consumer.taskId)).toEqual(['input_3', 'input_0', 'input_1']);
    expect(knowledgeContextConsumers(problem, cooperation, input.action, environmentDigest).map(item => item.taskId))
      .toEqual(result.map(item => item.knowledge.consumer.taskId));
    expect(knowledgeContextSections(input)).toEqual(result);
    expect(cooperation).toEqual(before);
    expect(result.every(item => Buffer.byteLength(item.text) <= 4096)).toBe(true);
  });

  it('updates both retrieval and diagnostic consumers when a preferred route changes or is parked', () => {
    const { inputs, goal, cooperation } = routedFrontier();
    const action: CooperativeAction = { kind: 'lead', seedCommit };
    const selected = () => knowledgeContextSections({ problem, cooperation, action,
      knowledge: snapshot(saved), environmentDigest }).map(item => item.knowledge.consumer.taskId);
    const consumers = () => knowledgeContextConsumers(problem, cooperation, action, environmentDigest).map(item => item.taskId);
    inputs[3]!.status = 'blocked'; inputs[2]!.status = 'pending';
    expect(selected()).toEqual(['input_2', 'input_0', 'input_1']);
    expect(consumers()).toEqual(selected());
    goal.parkedRoutes = { route_2: ['recorded-obstruction'] };
    expect(selected()).toEqual(['input_0', 'input_1', 'input_3']);
    expect(consumers()).toEqual(selected());
    expect(inputs[2]!.status).toBe('pending');
    expect(goal.parkedRoutes).toEqual({ route_2: ['recorded-obstruction'] });
  });

  it('delivers the preferred route residual to Lead through the same diagnostic consumer selection', () => {
    const { inputs, cooperation } = routedFrontier(), residual = residualFor(inputs[3]!);
    const read = vi.spyOn(residualReader, 'readLeanResidualGoalSnapshot').mockImplementation(input => ({
      goals: input.consumers.some(consumer => consumer.taskId === residual.consumer.taskId) ? [residual] : [], omissions: [] }));
    const result = build(inputs[3]!, { cooperation, action: { kind: 'lead', seedCommit } });
    expect(read.mock.calls[0]![0].consumers.map(item => item.taskId)).toEqual(['input_3', 'input_0', 'input_1']);
    expect(packets(result.message).find(item => item.consumer.taskId === 'input_3')).toMatchObject({
      searchSource: 'residual-goal', candidates: [{ id: distractor.id }], diagnostic: { artifact: residual.artifact } });
    expect(result.message).toContain(residual.goalText);
    expect(result.knowledgeRetrievals?.[0]).toMatchObject({ searchSource: 'residual-goal', included: true,
      consumer: { taskId: 'input_3' }, candidateIds: [distractor.id] });
    expect(inputs[3]!.status).toBe('pending');
  });

  it.each([true, false])('uses the current environment for both Lead search and diagnostics, matching=%s', matching => {
    const core = node('environment_core'), goal = node('original_goal', 'goal', [core.task.id]);
    core.status = 'integrated';
    core.integratedCheck = { passed: true, taskDigest: taskVersion(core.task), conditions: [],
      verification: { status: 'kernel_verified', targetCommit: seedCommit, results: [
        { status: 'kernel_verified', targetCommit: seedCommit, receiptId: 'recorded-receipt' },
      ] }, references: { root: { file: core.task.proofPath!, name: core.task.theoremName! }, sourceCommit: seedCommit,
        environmentDigest: matching ? environmentDigest : mathDigest('old-environment'), contextDigest: mathDigest('context'),
        inputs: [], statement: [], proof: [], tasks: [] } } as TaskRecord['integratedCheck'];
    const cooperation: CooperationState = { canonicalCommit: seedCommit, tasks: [goal, core] };
    const read = vi.spyOn(residualReader, 'readLeanResidualGoalSnapshot').mockReturnValue({ goals: [], omissions: [] });
    const action: CooperativeAction = { kind: 'lead', seedCommit };
    const expectedId = matching ? goal.task.id : core.task.id;
    expect(knowledgeContextSections({ problem, cooperation, action, knowledge: snapshot(saved), environmentDigest })
      .map(item => item.knowledge.consumer.taskId)).toEqual([expectedId]);
    expect(knowledgeContextConsumers(problem, cooperation, action, environmentDigest).map(item => item.taskId)).toEqual([expectedId]);
    if (matching) expect(packets(build(core, { cooperation, action }).message).map(item => item.consumer.taskId)).toEqual([expectedId]);
    else expect(() => build(core, { cooperation, action })).toThrow('math_context_stale_required:evidence:environment_core');
    expect(read.mock.calls[0]![0].consumers.map(item => item.taskId)).toEqual([expectedId]);
    expect(core.status).toBe('integrated');
    expect(core.integratedCheck!.verification.results[0]!.receiptId).toBe('recorded-receipt');
  });

  it('prefers the requested environment and problem version while keeping the result advisory', () => {
    const old = entry(saved.name, exactType, { id: '1'.repeat(64), environmentDigest: mathDigest('old-environment') });
    const current = entry(saved.name, exactType, { id: '2'.repeat(64), environmentDigest,
      contextDigest: mathDigest('current-context') });
    current.provenance = [{ ...current.provenance[0]!, environmentDigest, problemReceiptDigest: problem.receiptDigest }];
    const result = packet(sections(node('core'), snapshot(old, current))[0]!.text);
    expect(result).toMatchObject({ evidence: 'recorded-not-replayed', requiresFreshCheck: true,
      candidates: [{ id: current.id, versionCount: 2, environmentMatch: 'match', problemReceiptMatch: 'match' }] });
    expect(result.candidates[0]).not.toHaveProperty('receiptIds');
    expect(result.candidates[0]).not.toHaveProperty('declaration');
  });

  it('reserves automatic recommendation slots for distinct exact interfaces rather than proof-body variants', () => {
    const variants = Array.from({ length: 35 }, (_, index) => entry(saved.name, exactType, {
      id: index.toString(16).padStart(64, '0'), declaration: `theorem character_root_identity := by exact archivedProofMarker_${index}`,
    }));
    const alternate = entry('Archived.character_root_alternate'), transport = entry('Archived.character_root_transport');
    const knowledge = snapshot(...variants, alternate, transport), before = structuredClone(knowledge);
    const result = packet(sections(node('core'), knowledge)[0]!.text);
    expect(result).toMatchObject({ candidateGrouping: 'exact-name-type-typeKind-display-only',
      variantCountEvidence: 'distinct-recorded-declarations-not-interchangeable', totalMatches: 37, totalInterfaces: 3,
      evidence: 'recorded-not-replayed', requiresFreshCheck: true, candidateLimit: 3 });
    expect(new Set(result.candidates.map((candidate: { name: string }) => candidate.name)))
      .toEqual(new Set([saved.name, alternate.name, transport.name]));
    expect(result.candidates.find((candidate: { name: string }) => candidate.name === saved.name))
      .toMatchObject({ declarationVariantCount: 35, versionCount: 1 });
    expect(result.candidates.every((candidate: { id: string }) => knowledge.base.entries.some(item => item.id === candidate.id))).toBe(true);
    expect(knowledge).toEqual(before);
    expect(JSON.stringify(result)).not.toContain('archivedProofMarker');
  });

  it('chooses the current environment across displayed proof variants without changing their identity', () => {
    const old = entry(saved.name, exactType, { id: '1'.repeat(64), environmentDigest: mathDigest('old-environment') });
    const current = entry(saved.name, exactType, { id: '2'.repeat(64), environmentDigest,
      declaration: 'theorem character_root_identity := by exact currentProofMarker' });
    current.provenance = [{ ...current.provenance[0]!, environmentDigest, problemReceiptDigest: problem.receiptDigest }];
    const result = packet(sections(node('core'), snapshot(old, current))[0]!.text);
    expect(result).toMatchObject({ totalMatches: 2, totalInterfaces: 1, candidates: [{ id: current.id,
      declarationVariantCount: 2, versionCount: 1, environmentMatch: 'match', problemReceiptMatch: 'match' }] });
    expect(result.candidates).toHaveLength(1);
  });

  it('does not include archived proof bodies, descriptions, receipts or unbounded dependency data', () => {
    const candidate = entry(saved.name, exactType, { description: 'privateDescriptionMarker', premises: ['privatePremiseMarker'],
      dependencies: { statement: [{ file: 'Archived/Private.lean', name: 'privateDependencyMarker' }],
        proof: [], tasks: [], coverage: 'recorded' } });
    const result = sections(node('core'), snapshot(candidate))[0]!.text;
    expect(packet(result).candidates[0].id).toBe(candidate.id);
    for (const hidden of ['archivedProofMarker', 'privateDescriptionMarker', 'privatePremiseMarker',
      'privateDependencyMarker', 'historical-receipt-marker', '/archive/run-state.json']) expect(result).not.toContain(hidden);
  });

  it('keeps whole candidate identities and usable previews under a UTF-8 byte budget', () => {
    const longType = 'forall (character : DirichletCharacter Complex 7), ' + '\u03b1'.repeat(900);
    const entries = Array.from({ length: 5 }, (_, index) => entry(`Archived.character_candidate_${index}`, longType));
    const result = sections(node('core', 'lemma', [], longType), snapshot(...entries))[0]!;
    const value = packet(result.text);
    expect(Buffer.byteLength(result.text)).toBeLessThanOrEqual(4096);
    expect(value.totalMatches).toBe(5);
    expect(value.candidates.length).toBeGreaterThan(0);
    expect(value.candidates.length).toBeLessThan(3);
    expect(value.omittedForBytes).toBeGreaterThan(0);
    for (const candidate of value.candidates) {
      const original = entries.find(item => item.id === candidate.id)!;
      expect(original).toBeDefined();
      expect(candidate.typePreview).toBe(original.type.slice(0, 800));
      expect(candidate.typeTruncated).toBe(true);
    }
  });

  it.each([
    { kind: 'research' as const, input: '\u754c'.repeat(1334) },
    { kind: 'lemma' as const, input: '\u754c'.repeat(5334) },
  ])('reports oversized UTF-8 $kind input without throwing away the consumer identity', ({ kind, input }) => {
    const record = node('oversized', kind, [], input);
    if (kind === 'research') record.task = { ...record.task, objective: input };
    const result = packet(sections(record)[0]!.text);
    expect(result).toMatchObject({ status: 'input-not-searched', reason: 'input-too-large',
      consumer: { taskId: record.task.id, taskDigest: taskVersion(record.task) }, candidates: [] });
  });

  it.each([
    { kind: 'research' as const, input: 'measure pushforward'.padEnd(4000, ' ') },
    { kind: 'lemma' as const, input: exactType.padEnd(16000, ' ') },
  ])('still searches a $kind input at its inclusive byte limit', ({ kind, input }) => {
    const record = node('at_limit', kind, [], input);
    if (kind === 'research') record.task = { ...record.task, objective: input };
    const result = packet(sections(record)[0]!.text);
    expect(result.status).toBe('searched');
    expect(result.candidates[0].id).toBe(kind === 'research' ? distractor.id : saved.id);
  });

  it('reconstructs the same hints from serialized state and catalog metadata without mutating them', () => {
    const record = node('core'), knowledge = snapshot(saved, distractor);
    const cooperation: CooperationState = { canonicalCommit: seedCommit, tasks: [record] };
    const input = { problem, cooperation, action: actionFor(record), knowledge, environmentDigest };
    const restored = JSON.parse(JSON.stringify(input));
    const before = structuredClone(input);
    expect(knowledgeContextSections(restored)).toEqual(knowledgeContextSections(input));
    expect(input).toEqual(before);
    expect(restored.cooperation.tasks[0].integratedCheck).toBeUndefined();
  });
});

describe('knowledge context dispatch integration', () => {
  it('retrieves scoped route findings into the actual context and records budget omissions without importing their notes', () => {
    const knowledge = snapshot(saved), finding = JSON.stringify({ conclusion: 'refuted', summary: 'A character boundary counterexample.' });
    const notes = 'Full historical counterexample and assumptions remain behind the explicit finding reader.';
    knowledge.base.routeFindings = buildKnowledgeRouteFindings([{
      evidence: 'recorded-advisory-not-replayed', acceptance: 'not-assessed', conclusion: 'refuted',
      summary: 'The character bridge needs an additional boundary hypothesis.', finding, notes,
      scope: { problemId: 'previous-problem', problemReceiptDigest: problem.receiptDigest, environmentDigest,
        source: { kind: 'research', statement: 'Challenge the character bridge.', statementKind: 'research-objective', premises: [] },
        dependencies: [{ kind: 'lemma', statement: exactType, statementKind: 'closed-task-type', premises: [] }] },
      evidenceRefs: ['RESEARCH.md: boundary case'], obstructions: [], remainingObligations: ['Check the missing hypothesis.'],
      reconsiderWhen: ['The boundary assumption changes.'], provenance: { source: '/archive/state.json',
        sourceDigest: mathDigest('archived-state'), runId: 'old-run', taskId: 'old-question', taskDigest: mathDigest('old-task'),
        groupId: 'main', deliveryId: 'old-delivery', sourceCommit: seedCommit, findingDigest: mathDigest(finding), notesDigest: mathDigest(notes) },
    }]);
    const id = knowledge.base.routeFindings[0]!.id, record = node('renamed_consumer');
    const included = build(record, { knowledge });
    expect(packets(included.message)[0].routeFindings).toEqual([expect.objectContaining({ id,
      statementMatch: 'exact-recorded-text', requiresScopeReview: true, acceptance: 'not-assessed' })]);
    expect(included.knowledgeRetrievals).toEqual([expect.objectContaining({ included: true, routeFindingIds: [id] })]);
    expect(included.message).not.toContain(notes);
    const omitted = build(record, { knowledge, access: { maxOptionalContextBytes: 0 } });
    expect(packets(omitted.message)).toEqual([]);
    expect(omitted.knowledgeRetrievals).toEqual([expect.objectContaining({ included: false,
      omissionReason: 'optional-budget', routeFindingIds: [id] })]);
    expect(record.status).toBe('pending');
    expect(record.integratedCheck).toBeUndefined();
  });

  it('records exact candidates and whether they actually survived the optional context budget', () => {
    const included = build(node('core'));
    expect(included.knowledgeRetrievals).toEqual([expect.objectContaining({ included: true,
      catalogDigest: snapshot(saved).digest, candidateIds: [saved.id], routeFindingIds: [], consumer: { taskId: 'core',
        taskDigest: taskVersion(node('core').task), theoremName: 'Original.core', proofPath: 'Submission.lean' } })]);
    const omitted = build(node('core'), { access: { maxOptionalContextBytes: 0 } });
    expect(omitted.knowledgeRetrievals).toEqual([expect.objectContaining({ included: false, omissionReason: 'optional-budget', candidateIds: [saved.id] })]);
  });
  it('includes automatically found candidates in the actual worker prompt with its exact contract', () => {
    const record = node('core'), result = build(record);
    expect(packets(result.message)).toHaveLength(1);
    expect(packets(result.message)[0]).toMatchObject({ consumer: { taskId: 'core', taskDigest: taskVersion(record.task) },
      candidates: [{ id: saved.id }] });
    expect(result.message).toContain(JSON.stringify(exactType));
    expect(result.manifest!.included).toContainEqual(expect.objectContaining({ id: expect.stringMatching(/^knowledge:/u), required: false }));
    expect(result.message).not.toContain('archivedProofMarker');
  });

  it('can omit every retrieval hint for budget while preserving the exact assigned mathematical interface', () => {
    const compile = contextCompiler.compileTaskContext;
    vi.spyOn(contextCompiler, 'compileTaskContext').mockImplementation(input => compile({ ...input, maxOptionalContextBytes: 0 }));
    const record = node('core'), result = build(record);
    expect(packets(result.message)).toEqual([]);
    expect(result.manifest!.omitted).toContainEqual(expect.objectContaining({ id: expect.stringMatching(/^knowledge:/u), reason: 'optional-budget' }));
    expect(result.manifest!.requiredTaskIds).toContain(record.task.id);
    expect(result.message).toContain(JSON.stringify(exactType));
    expect(result.message).toContain(taskVersion(record.task));
  });

  it.each([
    { knowledgeFile: undefined },
    { knowledgeDigest: undefined },
    { knowledgeDigest: mathDigest('different-catalog') },
    { knowledgeSnapshot: { ...snapshot(saved), digest: mathDigest('different-snapshot') } },
  ])('refuses unpinned or mismatched knowledge inputs before dispatch: %j', access => {
    expect(() => build(node('core'), { access })).toThrow(/math_knowledge_identity_(missing|changed)/u);
  });

  it('rejects a snapshot that differs from the run pin while permitting a matching snapshot when no prior pin exists', () => {
    expect(() => build(node('core'), { state: { knowledgeDigest: mathDigest('other-run-pin') } }))
      .toThrow('math_knowledge_identity_changed');
    expect(packets(build(node('core'), { state: { knowledgeDigest: undefined } }).message)[0].candidates[0].id).toBe(saved.id);
  });

  it.each(['review', 'assemble'] as const)('does not feed theorem candidates to a fixed %s dispatch', kind => {
    const action: CooperativeAction = kind === 'review' ? { kind, seedCommit, sourceDigest: mathDigest('fixed-proof') } : { kind, seedCommit };
    const result = build(node('core'), { action });
    expect(packets(result.message)).toEqual([]);
    expect(result.message).not.toContain(saved.id);
    expect(result.manifest!.included.some(item => item.id.startsWith('knowledge:'))).toBe(false);
  });

  it.each(['explicit', 'legacy'] as const)('keeps candidates out of an advisory final-candidate review identified by %s policy', policy => {
    const record = node(policy === 'legacy' ? 'independent_candidate_review' : 'candidate_review', 'research');
    if (policy === 'explicit') record.task = { ...record.task, reviewScope: 'final-candidate' };
    expect(sections(record)).toEqual([]);
    expect(packets(build(record).message)).toEqual([]);
  });

  it('keeps automatic retrieval outside independent blind translation and statement comparison', () => {
    const review = { intendedStatement: 'A character has normalized root number.', premises: [],
      translation: { mathematics: 'A root number identity.', assumptions: [], definitions: [], evidenceRefs: [] } } as unknown as StatementReview;
    for (const kind of ['backtranslate', 'statement-review'] as const) {
      const action: StatementAction = { kind, reviewId: 'review', taskId: 'core', taskDigest: 'task',
        snapshotDigest: 'snapshot', seedCommit, workspace: '/fixed-statement' };
      expect(knowledgeContextSections({ problem, action, knowledge: snapshot(saved) })).toEqual([]);
      const result = buildStatementReviewContext(review, action, problem.receiptDigest);
      expect(result.message).not.toContain(saved.name);
      expect(result.instructions).not.toContain('knowledge search');
      expect(result.scope).toBe('fixed-statement');
    }
  });

  it('prefers bounded metadata and source continuations while requiring complete types and premises', () => {
    const result = build(node('core'));
    expect(result.instructions).toContain("--id 'THEOREM_ID' --metadata --max-bytes 16000");
    expect(result.instructions).toContain("--field 'FIELD_NAME' --offset OFFSET");
    expect(result.instructions).toContain('Read the complete type and premises before applying a candidate.');
    expect(result.instructions).toContain('parse JSON fields only after all pages are joined');
    expect(result.instructions).toContain("--name 'QUALIFIED_DECLARATION' --max-bytes 16000");
    expect(result.instructions).not.toContain('add --source');
  });
});
