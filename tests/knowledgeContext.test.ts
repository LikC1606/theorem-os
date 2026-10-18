import { afterEach, describe, expect, it, vi } from 'vitest';
import { mathDigest } from '../src/math/mathRuntimeIo';
import type { SolverRunState } from '../src/solver/archive';
import * as contextCompiler from '../src/solver/contextCompiler';
import type { CooperationState } from '../src/solver/cooperation';
import { knowledgeContextSections, type KnowledgeContextSnapshot } from '../src/solver/knowledgeContext';
import { buildResearchContext, buildStatementReviewContext, type ContextAccess } from '../src/solver/modules/context';
import type { SolverProblem } from '../src/solver/problem';
import type { StatementAction, StatementReview } from '../src/solver/statementReview';
import { taskVersion, type CooperativeAction, type CooperativeTask, type TaskRecord } from '../src/solver/tasks';
import type { TheoremKnowledgeEntry } from '../src/solver/theoremKnowledge';

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
function node(id: string, kind: CooperativeTask['kind'] = 'lemma', dependsOn: string[] = [], type = exactType): TaskRecord {
  return { task: { id, kind, dependsOn, revision: 0, objective: 'Find a measure pushforward formula',
    ...(['goal', 'lemma'].includes(kind) ? { type, proofPath: 'Submission.lean',
      theoremName: kind === 'goal' ? 'Original.target' : `Original.${id}` } : {}) }, status: 'pending', attempts: 0 };
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
});
