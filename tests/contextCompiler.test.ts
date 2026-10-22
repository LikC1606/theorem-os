import { expect, it } from 'vitest';
import path from 'node:path';
import { compileTaskContext, DEFAULT_OPTIONAL_TASK_CONTEXT_BYTES, DEFAULT_TASK_CONTEXT_BYTES,
  frozenSourceContext, type TaskContextInput } from '../src/solver/contextCompiler';
import { buildResearchContext } from '../src/solver/modules/context';
import { cooperativeWorkContract } from '../src/solver/modules/contracts';
import { hasTaskAcceptance, markTaskAcceptance, taskVersion, type CooperativeAction, type CooperativeTask, type TaskRecord } from '../src/solver/tasks';
import type { SolverProblem } from '../src/solver/problem';
import type { SolverRunState } from '../src/solver/archive';
import type { TaskProof } from '../src/solver/cooperativeProof';
import type { DeliveryRecord } from '../src/solver/deliveries';
import { canonicalMathJson, mathDigest } from '../src/math/mathRuntimeIo';
import { buildProofContinuation } from '../src/solver/progress';
import { pendingResearchHandoffs } from '../src/solver/researchHandoffs';
import { pendingResearchChallenges } from '../src/solver/researchChallenges';

const baseCommit = 'a'.repeat(40), proofCommit = 'b'.repeat(40);
const formal = 'namespace Original\nvariable (n : Nat)\ntheorem target (h : n > 0) : n > 0 := by sorry\nend Original';
const problem = { projectRelative: 'generated/p', ownedFiles: ['Submission.lean'],
  declarations: { 'Submission.lean': [{ name: 'target', header: 'target (h : n > 0) : n > 0' }] },
  sourceImports: { 'Submission.lean': ['Mathlib.Data.Nat.Basic'] }, sourceStructure: { 'Submission.lean': 'frozen-context' },
  targets: [{ proofPath: 'Submission.lean', theoremName: 'Original.target', declarationHash: 'original-type' }],
  receiptDigest: 'problem-receipt', baseCommit,
  contract: { formalStatement: formal, informalStatement: 'Positive n remains positive.', assumptions: ['n is a natural number', 'n > 0'],
    statementHash: 'statement', leanStatementHash: 'lean-statement' } } as unknown as SolverProblem;
const lemma = (id: string, dependsOn: readonly string[] = [], type = '∀ n : Nat, n = n'): CooperativeTask =>
  ({ id, kind: 'lemma', objective: `Prove ${id}`, theoremName: `Original.${id}`, type,
    proofPath: 'Submission.lean', revision: 0, dependsOn });
const node = (task: CooperativeTask): TaskRecord => ({ task, status: 'pending', attempts: 0 });
const assign = (task: CooperativeTask): Extract<CooperativeAction, { kind: 'task' }> => ({ kind: 'task', task,
  assignment: { taskId: task.id, taskDigest: taskVersion(task), workerId: 'researcher', seedCommit: proofCommit } });
const input = (tasks: readonly TaskRecord[], action?: CooperativeAction): TaskContextInput => ({
  problem, cooperation: { tasks: [...tasks] }, action, instructions: 'Strict Lean proof rules.', taskText: 'Prove the original target.',
  frozenContexts: { 'Submission.lean': frozenSourceContext(problem, 'Submission.lean', formal) } });
const checked = (task: CooperativeTask, conditions: TaskProof['conditions'] = []): TaskProof => ({
  commit: proofCommit, sourceDigest: 'checked-source', passed: true, seedCommit: baseCommit,
  taskDigest: taskVersion(task), conditions, changes: [{ file: 'Submission.lean', name: task.theoremName!, after: 'PRIVATE_PROOF_BODY' }],
  verification: { status: 'kernel_verified', targetCommit: proofCommit, results: [{
    receiptId: 'kernel-receipt', status: 'kernel_verified', targetCommit: proofCommit }] } as TaskProof['verification'],
});
const delivery = (task: CooperativeTask, id: string, summary = id): DeliveryRecord => ({
  id, taskId: task.id, taskDigest: taskVersion(task), kind: 'failure', status: 'failed', groupId: task.groupId,
  producer: 'peer', statement: '', premises: [], dependencies: [], remainingObligations: [], summary, evidenceRefs: [], createdAt: 1 });

it.each(['lead'] as const)('keeps reverse feasibility refutations mandatory for %s with no optional context', kind => {
  const core = lemma('core'), goal: CooperativeTask = { id: 'goal', kind: 'goal', objective: 'Original target', revision: 0,
    dependsOn: ['core'], proofPath: 'Submission.lean', theoremName: 'Original.target' };
  const review: CooperativeTask = { id: 'feasibility', kind: 'research', objective: 'Challenge the core', revision: 0,
    dependsOn: ['goal', 'core'], reviewScope: 'feasibility' };
  const finding = JSON.stringify({ taskId: review.id, conclusion: 'refuted', needsDecision: true,
    summary: 'COUNTEREXAMPLE_SENTINEL', evidenceRefs: ['FIXED_COUNTEREXAMPLE_REF'] });
  const tasks = [node(core), node(goal), { ...node(review), status: 'completed' as const, finding }];
  const cooperation = { tasks, deliveries: [{ ...delivery(review, 'refutation', 'COUNTEREXAMPLE_SENTINEL'),
    kind: 'research' as const, status: 'advisory' as const, findingDigest: mathDigest(finding), commit: proofCommit,
    evidenceRefs: ['FIXED_COUNTEREXAMPLE_REF'], dependencies: [goal, core].map(task => ({ taskId: task.id, taskDigest: taskVersion(task) })) }] };
  const challenge = pendingResearchChallenges(cooperation)[0];
  const context = compileTaskContext({ ...input(tasks, { kind, seedCommit: baseCommit, challengeIds: [challenge.id],
    challengeActivations: { [challenge.id]: challenge.activationDigest } }), cooperation, maxOptionalContextBytes: 0 });
  expect(context.manifest.included).toContainEqual(expect.objectContaining({ id: 'research-challenges', required: true }));
  expect(context.message).toContain('COUNTEREXAMPLE_SENTINEL');
  expect(context.message).toContain('FIXED_COUNTEREXAMPLE_REF');
  const late = compileTaskContext({ ...input(tasks, { kind, seedCommit: baseCommit, challengeIds: [] }),
    cooperation, maxOptionalContextBytes: 0 });
  expect(late.manifest.included.some(item => item.id === 'research-challenges')).toBe(false);
});

it('bounds challenge dispatches without expanding repeated-source backlog into the mandatory prompt', () => {
  const review: CooperativeTask = { id: 'feasibility', kind: 'research', objective: 'Challenge the core', revision: 0, dependsOn: [] };
  const finding = JSON.stringify({ conclusion: 'refuted', summary: 'A boundary witness.' });
  const tasks = [{ ...node(review), status: 'completed' as const, finding }];
  const cooperation = { tasks, deliveries: Array.from({ length: 1000 }, (_, index) => ({
    ...delivery(review, `challenge_${index}`), kind: 'research' as const, status: 'advisory' as const,
    findingDigest: mathDigest(finding), commit: proofCommit,
  })) };
  const before = structuredClone(cooperation);
  const context = compileTaskContext({ ...input(tasks, { kind: 'lead', seedCommit: baseCommit }), cooperation,
    maxOptionalContextBytes: 0, maxContextBytes: 32 * 1024 });
  const shown = JSON.parse(context.message.match(/Research challenges requiring a route decision[^\n]*\n([^\n]+)/u)![1]);
  expect(shown).toHaveLength(8);
  expect(context.message).toContain('"pending":1000,"shown":8,"remaining":992');
  expect(context.message).toContain('"remaining":992}');
  expect(context.manifest.mandatoryBytes).toBeLessThan(32 * 1024);
  expect(cooperation).toEqual(before);
});

it('dispatches the full frozen problem and exact dependency interfaces even when resuming from feedback', () => {
  const exactType = '∀ (n : Nat), ' + 'n = n ∧ '.repeat(3000) + 'True';
  const root = lemma('root', ['bridge']), bridge = lemma('bridge', ['base'], exactType), base = lemma('base');
  const state = { environmentDigest: 'environment', cooperation: { tasks: [node(root), node(bridge), node(base)] } } as SolverRunState;
  const context = buildResearchContext(problem, state, { root: '/runtime', worktree: '/proof', environment: {},
    taskText: 'Original task instructions.', retrievalRoot: '/library', sourceFeedback: 'Repair the current consumer.', assignment: assign(root),
    frozenContexts: input([]).frozenContexts });
  expect(context.message).toContain(formal);
  expect(context.message).toContain('n is a natural number');
  expect(context.message).toContain(JSON.stringify(exactType));
  expect(context.message).toContain('Mathlib.Data.Nat.Basic');
  expect(context.message).toContain('generated/p/Submission.lean');
  expect(context.message).toContain(baseCommit);
  expect(context.message).toContain(taskVersion(bridge));
  expect(context.manifest?.requiredTaskIds).toEqual(['root', 'bridge', 'base']);
  expect(context.manifest?.included.find(item => item.id === 'task-interfaces')?.required).toBe(true);
  expect(context.manifest?.evidence).toBe('recorded-not-replayed');
});

it('rejects a missing direct prerequisite and a changed assignment before model dispatch', () => {
  const task = lemma('consumer', ['absent']);
  expect(() => compileTaskContext(input([node(task)], assign(task)))).toThrow('math_context_missing_required:dependency:absent');
  const action = assign(task); action.assignment.taskDigest = 'old-version';
  expect(() => compileTaskContext(input([node(task)], action))).toThrow('math_context_stale_required:assignment:consumer');
});

it('retains complete current host and assigned-task failures with no optional allowance', () => {
  const task = lemma('current'), peer = lemma('peer');
  const feedback = 'Repair the failed source check.\n' + 'Lean diagnostic context.\n'.repeat(700) + 'EXACT_FINAL_GOAL';
  const context = compileTaskContext({ ...input([{ ...node(task), feedback },
    { ...node(peer), feedback: 'UNRELATED_PEER_FAILURE' }], assign(task)),
    feedback: 'CURRENT_HOST_FAILURE', maxOptionalContextBytes: 0 });
  expect(context.message).toContain(feedback);
  expect(context.message).toContain('CURRENT_HOST_FAILURE');
  expect(context.message).not.toContain('UNRELATED_PEER_FAILURE');
  expect(context.manifest.included).toEqual(expect.arrayContaining([
    expect.objectContaining({ id: 'feedback:current', kind: 'feedback', required: true }),
    expect.objectContaining({ id: 'current-feedback', kind: 'feedback', required: true }),
  ]));
  expect(context.manifest.included.filter(item => item.id === 'feedback:current')).toHaveLength(1);
  expect(context.manifest.omitted).toContainEqual({ id: 'feedback:peer', kind: 'feedback', reason: 'optional-budget' });
  expect(context.manifest.optionalBytes).toBe(0);
});

it('retains current original-problem feedback without a cooperative assignment', () => {
  const context = compileTaskContext({ ...input([]), feedback: 'S3_CURRENT_FAILURE', maxOptionalContextBytes: 0 });
  expect(context.message).toContain('S3_CURRENT_FAILURE');
  expect(context.manifest.included).toContainEqual(expect.objectContaining({ id: 'current-feedback', required: true }));
});

it.each([1, 1000])('shows a bounded search hint for %i repeated local failures without authorizing cached verification', count => {
  const task = lemma('current'), source = input([node(task)], assign(task));
  const failure = { id: 'new-failure', taskId: task.id, taskDigest: taskVersion(task),
    inputDigest: 'mathematical-inputs', basis: { contractDigest: 'contract', environmentDigest: 'environment', dependencies: {} },
    attemptFingerprint: 'same-local-attempt', relatedFailureIds: ['old-failure'], sourceDigest: 'changed-full-source',
    targetDigest: 'moved-target', seedSourceDigest: 'seed', seedTargetDigest: 'seed-target', canonicalSourceDigest: 'canonical',
    canonicalTargetDigest: 'canonical-target', feedback: 'Existing diagnostic.' };
  source.cooperation!.failedTaskInputs = Array.from({ length: count }, (_, index) => ({ ...failure,
    id: `failure-${index}`, attemptFingerprint: `same-local-attempt-${index}` }));
  const context = compileTaskContext({ ...source, maxContextBytes: 16 * 1024, maxOptionalContextBytes: 0 });
  expect(context.manifest.included).toContainEqual(expect.objectContaining({ id: 'repeated-attempts', required: true }));
  expect(context.message).toContain('same-local-attempt');
  expect(context.message).toContain('not mathematical equivalence or permission to reuse a verification result');
  expect(context.message).toContain(`"relatedAttemptFingerprints":${count}`);
  expect(context.manifest.omitted.filter(item => item.id === 'repeated-attempt-history')).toHaveLength(count > 1 ? 1 : 0);
  expect(source.cooperation!.failedTaskInputs).toHaveLength(count);
  expect(source.cooperation!.tasks[0].status).toBe('pending');
});

it('reports mandatory overflow instead of silently discarding the current failed goal', () => {
  const task = lemma('current');
  expect(() => compileTaskContext({ ...input([{ ...node(task), feedback: 'EXACT_FAILURE'.repeat(10000) }], assign(task)),
    maxContextBytes: 12000, maxOptionalContextBytes: 0 })).toThrow('math_context_mandatory_overflow:');
});

it('keeps a rejected planning decision mandatory when optional context does not fit', () => {
  const action = { kind: 'lead' as const, seedCommit: baseCommit };
  const cooperation = { tasks: [], error: 'math_plan_invalid_proof_target: task k0, field theoremName',
    planRejection: { proposalDigest: 'proposal', inputDigest: 'inputs', error: 'invalid', stalled: false } };
  const context = compileTaskContext({ ...input([], action), cooperation, maxContextBytes: 6000,
    optional: [{ id: 'oversized-hint', kind: 'feedback', text: 'OPTIONAL_HINT '.repeat(10000) }] });
  expect(context.message).toContain(cooperation.error);
  expect(context.message).toContain('Original.target');
  expect(context.manifest.included.find(item => item.id === 'plan-rejection')?.required).toBe(true);
  expect(context.manifest.omitted).toContainEqual({ id: 'oversized-hint', kind: 'feedback', reason: 'budget' });
});

it('keeps exact unresolved research proposals mandatory after optional delivery selection and budget limits', () => {
  const research: CooperativeTask = { id: 'investigate', kind: 'research', objective: 'Find a bridge', dependsOn: [], revision: 0 };
  const tasks = [{ ...node(research), status: 'completed' as const }];
  const proposal = lemma('proposed_bridge', [], '∀ n : Nat, n + 0 = n');
  const proposalDelivery: DeliveryRecord = { ...delivery(research, 'proposal'), kind: 'research', status: 'advisory',
    lemmaRequests: [proposal], commit: proofCommit };
  const cooperation = { tasks, deliveries: [proposalDelivery, ...Array.from({ length: 9 }, (_, index) =>
    ({ ...delivery(research, `later-${index}`), producer: `other-${index}` }))] };
  const handoff = pendingResearchHandoffs(cooperation)[0];
  const context = compileTaskContext({ ...input(tasks, { kind: 'lead', seedCommit: baseCommit, handoffIds: [handoff.id] }),
    cooperation, maxOptionalContextBytes: 0 });
  expect(context.manifest.included).toContainEqual(expect.objectContaining({ id: 'research-handoffs', required: true }));
  expect(context.manifest.omitted).toContainEqual({ id: 'delivery:proposal', kind: 'delivery', reason: 'selection-limit' });
  expect(context.message).toContain(JSON.stringify(proposal.type));
  expect(context.message).toContain(handoff.id);
  expect(context.message).toContain(proofCommit);
  expect(context.message).toContain('advisory; not checked lemmas');
});

it('does not require proposals that arrived after the Lead dispatch', () => {
  const research: CooperativeTask = { id: 'investigate', kind: 'research', objective: 'Find a bridge', dependsOn: [], revision: 0 };
  const tasks = [node(research)], proposal = lemma('late_proposal');
  const context = compileTaskContext({ ...input(tasks, { kind: 'lead', seedCommit: baseCommit, handoffIds: [] }),
    cooperation: { tasks, deliveries: [{ ...delivery(research, 'late'), kind: 'research', status: 'advisory', lemmaRequests: [proposal] }] },
    maxOptionalContextBytes: 0 });
  expect(context.manifest.included.some(item => item.id === 'research-handoffs')).toBe(false);
  expect(context.message).not.toContain(proposal.theoremName);
});

it.each(['lead'] as const)('compacts repeated provenance and resolves a legacy %s handoff alias', kind => {
  const research: CooperativeTask = { id: 'investigate', kind: 'research', objective: 'Find a bridge', dependsOn: [], revision: 0 };
  const tasks = [{ ...node(research), status: 'completed' as const }], proposal = lemma('unique_bridge');
  const deliveries = Array.from({ length: 1000 }, (_, index) => ({ ...delivery(research, `source-${index}`),
    kind: 'research' as const, status: 'advisory' as const, lemmaRequests: [proposal], commit: proofCommit }));
  const cooperation = { tasks, deliveries }, handoff = pendingResearchHandoffs(cooperation)[0];
  const context = compileTaskContext({ ...input(tasks, { kind, seedCommit: baseCommit,
    handoffIds: [handoff.sources.at(-1)!.handoffId] }), cooperation, maxOptionalContextBytes: 0 });
  const shown = JSON.parse(context.message.match(/Pending research proposals requiring a Lead decision[^\n]*\n([^\n]+)/u)![1]);
  expect(shown).toHaveLength(1);
  expect(shown[0]).toMatchObject({ id: handoff.id, proposal, sourceSet: { count: 1000,
    digest: mathDigest(canonicalMathJson(handoff.sources)), reference: { path: 'COOPERATION.json',
      handoffId: handoff.id, contextDigest: handoff.contextDigest } } });
  expect(shown[0]).not.toHaveProperty('sources');
  expect(Buffer.byteLength(JSON.stringify(shown))).toBeLessThan(2048);
  expect(context.manifest.included.some(item => item.id === 'research-handoff-backlog')).toBe(false);
  expect(handoff.sources).toHaveLength(1000);
});

it.each(['lead'] as const)('keeps a thousand proposals in bounded %s batches with zero optional allowance', kind => {
  const research: CooperativeTask = { id: 'investigate', kind: 'research', objective: 'Find exact bridges', dependsOn: [], revision: 0 };
  const tasks = [{ ...node(research), status: 'completed' as const }];
  const proposals = Array.from({ length: 1000 }, (_, index) => lemma(`proposal_${index}`, [], 'True'));
  const cooperation = { tasks, deliveries: [{ ...delivery(research, 'many-proposals'), kind: 'research' as const,
    status: 'advisory' as const, lemmaRequests: proposals, commit: proofCommit }] };
  const before = structuredClone(cooperation);
  const context = compileTaskContext({ ...input(tasks, { kind, seedCommit: baseCommit }), cooperation, maxOptionalContextBytes: 0 });
  const shown = JSON.parse(context.message.match(/Pending research proposals requiring a Lead decision[^\n]*\n([^\n]+)/u)![1]);
  expect(shown).toHaveLength(8);
  expect(shown.map((item: any) => item.proposal)).toEqual(proposals.slice(0, 8));
  expect(context.manifest.mandatoryBytes).toBeLessThan(32 * 1024);
  expect(context.message).toContain('"pending":1000,"shown":8,"remaining":992');
  expect(context.message).not.toContain(proposals[999].theoremName);
  expect(cooperation).toEqual(before);
});

it('dispatches one explicit work contract while retaining exact proof inputs and host acceptance', () => {
  const task = lemma('typed_bridge'), state = { environmentDigest: 'environment', cooperation: { tasks: [node(task)] } } as SolverRunState;
  const context = buildResearchContext(problem, state, { root: '/runtime', worktree: '/proof', environment: {},
    taskText: 'Prove the original target', retrievalRoot: '/library', assignment: assign(task), frozenContexts: input([]).frozenContexts });
  expect(context.workContract).toMatchObject({ stage: 'formal-proof', owner: 'proof-worker', output: 'saved-exact-typed-declaration',
    consumer: 'M2-then-canonical-integration', acceptance: 'independent-exact-source-check', input: { taskId: task.id, taskDigest: taskVersion(task) } });
  expect(context.manifest?.included).toContainEqual(expect.objectContaining({ id: 'work-contract', required: true }));
  expect(context.message).toContain(JSON.stringify(task.type));
  expect(cooperativeWorkContract({ kind: 'assemble', seedCommit: proofCommit }, [node(task)]))
    .toMatchObject({ stage: 'integration', owner: 'host', output: 'fixed-original-proof-check', sourcePolicy: 'read-only',
      acceptance: 'independent-exact-source-check', input: { seedCommit: proofCommit } });
});

it('keeps a goal worker on its assigned proof when unrelated seed goals are unfinished', () => {
  const task: CooperativeTask = { id: 'goal', kind: 'goal', objective: 'Prove the original target',
    proofPath: 'Submission.lean', theoremName: 'Original.target', dependsOn: [], revision: 0 };
  const state = { environmentDigest: 'environment', cooperation: { tasks: [node(task)] } } as SolverRunState;
  const context = buildResearchContext(problem, state, { root: '/runtime', worktree: '/proof', environment: {},
    taskText: 'Prove the original target', retrievalRoot: '/library', assignment: assign(task), frozenContexts: input([]).frozenContexts });
  expect(context.instructions).toContain('This assignment proves only Original.target');
  expect(context.instructions).toContain('including existing sorry placeholders');
  expect(context.instructions).toContain('do not prove or rewrite them to make the whole file pass');
  expect(context.instructions).toContain('checks the full candidate after integration');
  expect(context.instructions).not.toContain('Check the complete saved target file and its local imports before delivery');
});

it('rejects mismatched mandatory dependency and proof evidence versions', () => {
  const prerequisite = lemma('prerequisite'), consumer = lemma('consumer', [prerequisite.id]), action = assign(consumer);
  action.assignment.dependencies = [{ taskId: prerequisite.id, taskDigest: 'old-version' }];
  expect(() => compileTaskContext(input([node(consumer), node(prerequisite)], action)))
    .toThrow('math_context_stale_required:dependency:prerequisite');
  const proof = { ...checked(prerequisite), taskDigest: 'old-version' };
  expect(() => compileTaskContext(input([node(consumer), { ...node(prerequisite), status: 'integrated', integratedCheck: proof }], assign(consumer))))
    .toThrow('math_context_stale_required:evidence:prerequisite');
});

it('retains the parked original-goal frontier and its reopening conditions when advisory notes do not fit', () => {
  const core = node(lemma('core'));
  core.status = 'blocked'; core.routeParking = ['core-blocker']; core.feedback = 'The assigned analytic declaration is missing.';
  const goal = node({ ...lemma('goal', ['core']), kind: 'goal', theoremName: 'Original.target' });
  const blocker = { id: 'core-blocker', taskId: 'core', groupId: 'main', taskDigest: taskVersion(core.task),
    mechanism: 'No uniform critical-line cancellation estimate.', scope: 'The combined-conductor inference.',
    status: 'parked', evidenceStatus: 'advisory', reopenOn: [{ kind: 'contract-changed' }],
    basis: { secret: 'PRIVATE_RECURRENCE_BASIS' } };
  const context = compileTaskContext({ ...input([core, goal], { kind: 'lead', seedCommit: baseCommit }),
    cooperation: { tasks: [core, goal], blockers: [blocker] } as TaskContextInput['cooperation'], maxContextBytes: 8000,
    optional: [{ id: 'long-research-note', kind: 'finding', text: 'OPTIONAL_NOTE '.repeat(2000) }] });
  expect(context.manifest.included).toContainEqual(expect.objectContaining({ id: 'original-goal-frontier', required: true }));
  expect(context.message).toContain(blocker.mechanism);
  expect(context.message).toContain('contract-changed');
  expect(context.message).toContain(core.feedback);
  expect(context.message).not.toContain('PRIVATE_RECURRENCE_BASIS');
  expect(context.manifest.omitted).toContainEqual({ id: 'long-research-note', kind: 'finding', reason: 'budget' });
});

it('omits stale and unrelated blockers from the mandatory original-goal frontier', () => {
  const core = node(lemma('core')); core.status = 'blocked';
  const goal = node({ ...lemma('goal', ['core']), kind: 'goal', theoremName: 'Original.target' });
  const blocker = { id: 'old', taskId: core.task.id, groupId: 'main', taskDigest: 'old-version',
    mechanism: 'STALE_BLOCKER', scope: 'stale inference', status: 'parked' };
  const hidden = { ...blocker, id: 'unrelated', taskId: 'absent', mechanism: 'UNRELATED_PRIVATE_BLOCKER' };
  const context = compileTaskContext({ ...input([core, goal], { kind: 'lead', seedCommit: baseCommit }),
    cooperation: { tasks: [core, goal], blockers: [blocker, hidden] } as TaskContextInput['cooperation'] });
  expect(context.message).not.toContain('STALE_BLOCKER');
  expect(context.message).not.toContain('UNRELATED_PRIVATE_BLOCKER');
});

it('keeps goal-owned OR-route blockers mandatory when the frontier consists of route prerequisites', () => {
  const a = node(lemma('a')), b = node(lemma('b'));
  const closeA = node(lemma('close_a', ['a'])), closeB = node(lemma('close_b', ['b']));
  const goal = node({ ...lemma('goal'), kind: 'goal', theoremName: 'Original.target' });
  const routes = [{ id: 'route_a', targetTaskId: 'goal', prerequisiteTaskIds: ['a'], closingTaskId: 'close_a' },
    { id: 'route_b', targetTaskId: 'goal', prerequisiteTaskIds: ['b'], closingTaskId: 'close_b' }];
  goal.alternativeRoutes = routes; goal.parkedRoutes = { route_a: ['route-a-blocker'], route_b: ['route-b-blocker'] };
  const blockers = routes.map(route => ({ id: `${route.id}-blocker`, taskId: 'goal', groupId: 'main', routeId: route.id,
    taskDigest: taskVersion(goal.task), mechanism: `Missing local input for ${route.id}.`, scope: 'Route closing inference.',
    status: 'parked', evidenceStatus: 'advisory', reopenOn: [{ kind: 'contract-changed' }] }));
  const tasks = [goal, a, b, closeA, closeB];
  const context = compileTaskContext({ ...input(tasks, { kind: 'lead', seedCommit: baseCommit }),
    cooperation: { tasks, proofRoutes: routes, blockers } as TaskContextInput['cooperation'], maxContextBytes: 11000,
    optional: [{ id: 'long-note', kind: 'finding', text: 'OPTIONAL_OR_ROUTE_NOTE '.repeat(2000) }] });
  const mandatory = context.message.split('Unfinished original goals and their current frontier')[1].split('\n\n')[0];
  for (const blocker of blockers) expect(mandatory).toContain(blocker.mechanism);
  expect(mandatory).toContain('contract-changed');
  expect(context.manifest.included).toContainEqual(expect.objectContaining({ id: 'original-goal-frontier', required: true }));
  expect(context.manifest.omitted).toContainEqual({ id: 'long-note', kind: 'finding', reason: 'budget' });
});

it('fails explicitly when mandatory Unicode mathematics exceeds the byte allowance', () => {
  const task = lemma('large', [], '∀ n : ℕ, ' + 'n ∈ ℕ ∧ '.repeat(3000) + 'True');
  expect(() => compileTaskContext({ ...input([node(task)], assign(task)), maxContextBytes: 5000 }))
    .toThrow('math_context_mandatory_overflow');
});

it('omits oversized optional notes with a manifest while preserving the complete mandatory interface', () => {
  const task = lemma('consumer');
  const context = compileTaskContext({ ...input([{ ...node(task), finding: 'TOO_LARGE_OPTIONAL_NOTE '.repeat(1000) }], assign(task)),
    instructions: 'Rules in Chinese: 严格检查。', maxContextBytes: 8500 });
  expect(context.message).toContain(JSON.stringify(task.type));
  expect(context.message).not.toContain('TOO_LARGE_OPTIONAL_NOTE');
  expect(context.manifest.omitted).toContainEqual({ id: 'finding:consumer', kind: 'finding', reason: 'budget' });
  expect(context.manifest.usedBytes).toBe(Buffer.byteLength(context.message) + Buffer.byteLength('Rules in Chinese: 严格检查。'));
  expect(context.manifest.usedBytes).toBeLessThanOrEqual(8500);
  expect(context.manifest.mandatoryBytes).toBeLessThanOrEqual(context.manifest.usedBytes);
});

it('prefers failures on this task and its dependencies over unrelated deliveries', () => {
  const prerequisite = lemma('prerequisite'), task = lemma('consumer', [prerequisite.id]);
  const others = Array.from({ length: 10 }, (_, index) => lemma(`other${index}`));
  const records = [delivery(task, 'own-failure'), delivery(prerequisite, 'dependency-failure'),
    ...others.map(item => delivery(item, `unrelated-${item.id}`))];
  const context = compileTaskContext({ ...input([node(task), node(prerequisite), ...others.map(node)], assign(task)),
    cooperation: { tasks: [node(task), node(prerequisite), ...others.map(node)], deliveries: records } });
  expect(context.manifest.included.filter(item => item.kind === 'delivery').slice(0, 2).map(item => item.id))
    .toEqual(['delivery:own-failure', 'delivery:dependency-failure']);
  expect(context.manifest.omitted.filter(item => item.reason === 'selection-limit')).toHaveLength(4);
});

it('accounts for stale, superseded and repeated optional deliveries explicitly', () => {
  const task = lemma('task'), stale = { ...delivery(task, 'stale'), taskDigest: 'stale' };
  const superseded = { ...delivery(task, 'superseded'), status: 'superseded' as const };
  const context = compileTaskContext({ ...input([node(task)], assign(task)),
    cooperation: { tasks: [node(task)], deliveries: [delivery(task, 'old'), stale, superseded, delivery(task, 'new')] } });
  expect(context.manifest.omitted).toEqual(expect.arrayContaining([
    { id: 'delivery:old', kind: 'delivery', reason: 'duplicate' },
    { id: 'delivery:stale', kind: 'delivery', reason: 'stale-version' },
    { id: 'delivery:superseded', kind: 'delivery', reason: 'superseded' },
  ]));
  expect(context.manifest.included.some(item => item.id === 'delivery:new')).toBe(true);
});

it('keeps exact mathematical contracts larger than the separate optional allowance', () => {
  const task = lemma('large_contract', [], '∀ n : Nat, ' + 'n = n ∧ '.repeat(10000) + 'True');
  const context = compileTaskContext({ ...input([node(task)], assign(task)), maxOptionalContextBytes: 0,
    optional: [{ id: 'unneeded-hint', kind: 'finding', text: 'OPTIONAL_UNNEEDED_HINT' }] });
  expect(context.message).toContain(JSON.stringify(task.type));
  expect(context.manifest.mandatoryBytes).toBeGreaterThan(DEFAULT_OPTIONAL_TASK_CONTEXT_BYTES);
  expect(context.manifest.maxBytes).toBe(DEFAULT_TASK_CONTEXT_BYTES);
  expect(context.manifest.optionalBytes).toBe(0);
  expect(context.manifest.omitted).toContainEqual({ id: 'unneeded-hint', kind: 'finding', reason: 'optional-budget' });
});

it('does not fill the hard context budget with optional history and records why each hint was skipped', () => {
  const task = lemma('consumer'), context = compileTaskContext({ ...input([node(task)], assign(task)),
    optional: Array.from({ length: 10 }, (_, i) => ({ id: `hint-${i}`, kind: 'history' as const,
      text: `HINT_${i}\n` + 'advisory detail '.repeat(1000) })) });
  expect(context.manifest.maxOptionalBytes).toBe(DEFAULT_OPTIONAL_TASK_CONTEXT_BYTES);
  expect(context.manifest.optionalBytes).toBeGreaterThan(0);
  expect(context.manifest.optionalBytes).toBeLessThanOrEqual(DEFAULT_OPTIONAL_TASK_CONTEXT_BYTES);
  expect(context.manifest.usedBytes).toBeLessThan(DEFAULT_TASK_CONTEXT_BYTES / 2);
  const included = new Set(context.manifest.included.map(item => item.id));
  for (let i = 0; i < 10; i++) if (!included.has(`hint-${i}`))
    expect(context.manifest.omitted).toContainEqual({ id: `hint-${i}`, kind: 'history', reason: 'optional-budget' });
  expect(context.manifest.usedBytes).toBe(Buffer.byteLength(context.message) + Buffer.byteLength(input([]).instructions));
});

it.each([17, 32, 1000])('keeps a full %i-item omission manifest with a bounded and verifiable inline preview', count => {
  const task = lemma('consumer');
  const context = compileTaskContext({ ...input([node(task)], assign(task)), maxOptionalContextBytes: 0,
    optional: Array.from({ length: count }, (_, index) => ({ id: `hint-${index}`, kind: 'history' as const, text: 'Advisory history.' })) });
  const inline = JSON.parse(context.message.split('Context compilation manifest:\n')[1]);
  expect(context.manifest.omitted).toHaveLength(count);
  expect(inline.omitted).toEqual(context.manifest.omitted.slice(0, 16));
  expect(inline.omissionSet).toMatchObject({ selection: 'bounded-preview', count,
    digest: mathDigest(canonicalMathJson(context.manifest.omitted)),
    reference: { path: 'CONTEXT-MANIFEST.json', field: 'omitted' } });
  expect(context.manifest.usedBytes).toBe(Buffer.byteLength(context.message) + Buffer.byteLength(input([]).instructions));
  expect(context.manifest.mandatoryBytes).toBeLessThan(8 * 1024);
});

it.each([-1, NaN, Infinity, 1.5])('rejects invalid optional byte allowance %s', maxOptionalContextBytes => {
  expect(() => compileTaskContext({ ...input([]), maxOptionalContextBytes }))
    .toThrow('math_context_invalid_budget:maxOptionalContextBytes');
});

it('projects advisory deliveries into recoverable references without duplicating proof inventories or artifact headers', () => {
  const task = lemma('consumer'), proof = referenceProof(task), proposed = lemma('proposed_helper', [], '∀ n : Nat, n + 0 = n');
  const record: DeliveryRecord = { ...delivery(task, 'recoverable'), kind: 'proof', status: 'verified',
    commit: proofCommit, sourceDigest: proof.sourceDigest, actualReferences: proof.references,
    evidence: { passed: true, verification: { status: 'kernel_verified', targetCommit: proofCommit,
      results: [{ receiptId: 'DUPLICATE_DELIVERY_RECEIPT' }] } },
    summary: 'The helper is available for the consumer.', remainingObligations: ['The original target remains open.'],
    lemmaRequests: [proposed], artifacts: { schema: 'theorem-os.delivery-artifacts.v1', scope: 'advisory-unverified',
      problemReceiptDigest: problem.receiptDigest, taskId: task.id, taskDigest: taskVersion(task), seedCommit: baseCommit,
      commit: proofCommit, artifacts: [{ id: 'artifact-id', kind: 'owned-source', file: 'generated/p/Submission.lean',
        proofPath: 'Submission.lean', fileSha256: 'file-hash', sha256: 'code-hash', bytes: 120000,
        declarations: [{ name: 'Original.consumer', header: 'LOCAL_ONLY_ARTIFACT_HEADER '.repeat(5000), sha256: 'declaration-hash', draft: false }] }] } };
  Object.assign(record, { diagnostics: { stdoutPreview: 'LOCAL_ONLY_DIAGNOSTICS' } });
  const original = structuredClone(record), context = compileTaskContext({ ...input([], assign(task)),
    cooperation: { tasks: [{ ...node(task), status: 'integrated', integratedCheck: proof }], deliveries: [record] } });
  const visible = contextLine(context.message, 'Current-version delivery selected for this task (advisory; retain unproved obligations):');
  expect(visible.savedSource).toEqual({ commit: proofCommit, notesPath: 'RESEARCH.md', proofPath: 'generated/p/Submission.lean' });
  expect(visible.artifacts.artifacts[0]).toMatchObject({ file: 'generated/p/Submission.lean', fileSha256: 'file-hash', sha256: 'code-hash',
    declarations: [{ name: 'Original.consumer', sha256: 'declaration-hash', draft: false }] });
  expect(visible.summary).toBe(record.summary);
  expect(visible.remainingObligations).toEqual(record.remainingObligations);
  expect(visible.lemmaRequests).toEqual([proposed]);
  expect(visible.actualReferences).toBeUndefined();
  expect(visible.actualReferenceSource.sourceCommit).toBe(proof.references!.sourceCommit);
  expect(context.message).not.toMatch(/LOCAL_ONLY_ARTIFACT_HEADER|LOCAL_ONLY_DIAGNOSTICS|DUPLICATE_DELIVERY_RECEIPT/u);
  expect(compiledGraph(context.message)[0].evidence.references.inputs).toHaveLength(proof.references!.inputs.length);
  expect(compiledDictionary(context.message).entries).toHaveLength(2);
  expect(context.manifest.omitted).toContainEqual({ id: 'delivery:recoverable:details', kind: 'delivery', reason: 'advisory-details-by-reference' });
  expect(context.manifest.usedBytes).toBeLessThan(16000);
  expect(record).toEqual(original);
});

it('preserves a complete shared research finding once, with its immutable notes source', () => {
  const task: CooperativeTask = { id: 'research', kind: 'research', objective: 'Find the missing inference', dependsOn: [], revision: 0 };
  const finding = 'Intermediate estimate. '.repeat(200) + 'TAIL_MATHEMATICAL_ARGUMENT';
  const record: DeliveryRecord = { ...delivery(task, 'research-finding', finding), kind: 'research', status: 'advisory',
    commit: proofCommit, sourceDigest: 'finding-source' };
  const context = compileTaskContext({ ...input([], assign(task)),
    cooperation: { tasks: [{ ...node(task), finding }], deliveries: [record] } });
  const visible = contextLine(context.message, 'Advisory finding for research:');
  expect(visible).toEqual({ taskId: task.id, taskDigest: taskVersion(task), finding,
    savedSource: { deliveryId: record.id, commit: proofCommit, notesPath: 'RESEARCH.md', sourceDigest: 'finding-source' } });
  expect(context.message.match(/TAIL_MATHEMATICAL_ARGUMENT/gu)).toHaveLength(1);
  const delivered = contextLine(context.message, 'Current-version delivery selected for this task (advisory; retain unproved obligations):');
  expect(delivered.summary).toBeUndefined();
  expect(delivered.summarySource).toBe('finding:research');
  expect(context.manifest.omitted.some(item => item.id.endsWith(':summary-tail'))).toBe(false);
});

it('binds a complete JSON research finding to its short delivery summary using the host digest', () => {
  const task: CooperativeTask = { id: 'research', kind: 'research', objective: 'Find the missing inference', dependsOn: [], revision: 0 };
  const summary = 'A new exact bridge is available.';
  const finding = JSON.stringify({ taskId: task.id, summary, argument: 'A full mathematical step. '.repeat(400),
    remainingObligations: ['TAIL_REQUIRED_ANALYTIC_PREMISE'] });
  const record: DeliveryRecord = { ...delivery(task, 'host-bound-finding', summary), kind: 'research', status: 'advisory',
    commit: proofCommit, findingDigest: mathDigest(finding) };
  const context = compileTaskContext({ ...input([], assign(task)),
    cooperation: { tasks: [{ ...node(task), finding }], deliveries: [record] } });
  expect(contextLine(context.message, 'Advisory finding for research:')).toEqual({ taskId: task.id, taskDigest: taskVersion(task), finding,
    savedSource: { deliveryId: record.id, commit: proofCommit, notesPath: 'RESEARCH.md' } });
  expect(context.message.match(/TAIL_REQUIRED_ANALYTIC_PREMISE/gu)).toHaveLength(1);
  expect(contextLine(context.message, 'Current-version delivery selected for this task (advisory; retain unproved obligations):'))
    .toMatchObject({ findingDigest: record.findingDigest, summarySource: 'finding:research' });
});

it('does not fall back to equal summary text when a supplied finding digest mismatches', () => {
  const task = lemma('consumer'), finding = 'A current mathematical observation.';
  const record: DeliveryRecord = { ...delivery(task, 'mismatched-finding', finding), kind: 'research', status: 'advisory',
    commit: proofCommit, findingDigest: mathDigest('an earlier finding') };
  const context = compileTaskContext({ ...input([], assign(task)),
    cooperation: { tasks: [{ ...node(task), finding }], deliveries: [record] } });
  expect(contextLine(context.message, 'Advisory finding for consumer:')).toEqual({ taskId: task.id, taskDigest: taskVersion(task), finding });
  const visible = contextLine(context.message, 'Current-version delivery selected for this task (advisory; retain unproved obligations):');
  expect(visible.summarySource).toBeUndefined();
  expect(visible.summary).toBe(finding);
});

it.each(['', '   ', undefined])('does not refer to a nonexistent finding section for an empty finding %s', finding => {
  const task = lemma('consumer'), record: DeliveryRecord = { ...delivery(task, 'empty-finding', finding ?? ''), kind: 'research',
    status: 'advisory', commit: proofCommit, findingDigest: mathDigest(finding ?? '') };
  const context = compileTaskContext({ ...input([], assign(task)),
    cooperation: { tasks: [{ ...node(task), finding }], deliveries: [record] } });
  const visible = contextLine(context.message, 'Current-version delivery selected for this task (advisory; retain unproved obligations):');
  expect(visible.summarySource).toBeUndefined();
  expect(visible.summary).toBe(finding ?? '');
  expect(context.manifest.included.some(item => item.id === 'finding:consumer')).toBe(false);
  expect(context.message).not.toContain('Advisory finding for consumer:');
});

it('preserves a nonduplicate delivery summary in full instead of clipping its mathematical tail', () => {
  const task = lemma('consumer'), summary = 'A substantive argument. '.repeat(150) + 'EXACT_CLOSING_INFERENCE';
  const record: DeliveryRecord = { ...delivery(task, 'complete-summary', summary), kind: 'research', status: 'advisory' };
  const context = compileTaskContext({ ...input([], assign(task)),
    cooperation: { tasks: [{ ...node(task), finding: 'A distinct observation.' }], deliveries: [record] } });
  expect(contextLine(context.message, 'Current-version delivery selected for this task (advisory; retain unproved obligations):').summary).toBe(summary);
  expect(context.message).toContain('A distinct observation.');
  expect(context.manifest.omitted.some(item => item.id.endsWith(':summary-tail'))).toBe(false);
});

it('retains the full finding when its delivery metadata exceeds the optional allowance', () => {
  const task = lemma('consumer'), finding = 'The key inference is now explicit.';
  const record: DeliveryRecord = { ...delivery(task, 'large-metadata', finding), kind: 'research', status: 'advisory',
    statement: 'LARGE_OPTIONAL_METADATA '.repeat(4000), commit: proofCommit };
  const context = compileTaskContext({ ...input([], assign(task)),
    cooperation: { tasks: [{ ...node(task), finding }], deliveries: [record] } });
  expect(contextLine(context.message, 'Advisory finding for consumer:')).toMatchObject({ finding,
    savedSource: { deliveryId: record.id, commit: proofCommit, notesPath: 'RESEARCH.md' } });
  expect(context.manifest.omitted).toContainEqual({ id: 'delivery:large-metadata', kind: 'delivery', reason: 'optional-budget' });
  expect(context.manifest.optionalBytes).toBeLessThanOrEqual(DEFAULT_OPTIONAL_TASK_CONTEXT_BYTES);
});

it('prioritizes mathematical findings ahead of duplicate delivery metadata', () => {
  const task = lemma('consumer'), finding = 'SUBSTANTIVE_PROOF_STEP '.repeat(40);
  const record: DeliveryRecord = { ...delivery(task, 'competing-metadata', finding), kind: 'research', status: 'advisory',
    statement: 'OPTIONAL_METADATA '.repeat(100), commit: proofCommit };
  const context = compileTaskContext({ ...input([], assign(task)), maxOptionalContextBytes: 3000,
    cooperation: { tasks: [{ ...node(task), finding }], deliveries: [record] } });
  expect(contextLine(context.message, 'Advisory finding for consumer:').finding).toBe(finding);
  expect(context.manifest.omitted).toContainEqual({ id: 'delivery:competing-metadata', kind: 'delivery', reason: 'optional-budget' });
  expect(context.manifest.optionalBytes).toBeLessThanOrEqual(3000);
});

it('omits an oversized finding as a whole and records its source and omitted manifest id', () => {
  const task = lemma('consumer'), finding = 'DO_NOT_SHOW_A_PARTIAL_ARGUMENT '.repeat(1000);
  const record: DeliveryRecord = { ...delivery(task, 'oversized-finding', finding), kind: 'research', status: 'advisory', commit: proofCommit };
  const context = compileTaskContext({ ...input([], assign(task)), maxOptionalContextBytes: 2000,
    cooperation: { tasks: [{ ...node(task), finding }], deliveries: [record] } });
  expect(context.message).not.toContain('DO_NOT_SHOW_A_PARTIAL_ARGUMENT');
  expect(context.manifest.omitted).toContainEqual({ id: 'finding:consumer', kind: 'finding', reason: 'optional-budget' });
  expect(contextLine(context.message, 'Current-version delivery selected for this task (advisory; retain unproved obligations):'))
    .toMatchObject({ summarySource: 'finding:consumer', savedSource: { commit: proofCommit, notesPath: 'RESEARCH.md' } });
});

it.each(['superseded', 'stale-task', 'stale-dependency'] as const)('does not attribute a current finding to a %s research source', variant => {
  const dependency = lemma('dependency'), task = lemma('consumer', [dependency.id]), finding = JSON.stringify({ summary: 'Current mathematical observation.' });
  const record: DeliveryRecord = { ...delivery(task, 'invalid-source', 'Current mathematical observation.'), kind: 'research', status: 'advisory',
    commit: proofCommit, findingDigest: mathDigest(finding),
    ...(variant === 'superseded' ? { status: 'superseded' } : variant === 'stale-task' ? { taskDigest: 'old-task-version' } :
      { dependencies: [{ taskId: dependency.id, taskDigest: 'old-dependency-version' }] }) };
  const context = compileTaskContext({ ...input([], assign(task)),
    cooperation: { tasks: [{ ...node(task), finding }, node(dependency)], deliveries: [record] } });
  expect(contextLine(context.message, 'Advisory finding for consumer:')).toEqual({ taskId: task.id, taskDigest: taskVersion(task), finding });
  expect(context.manifest.omitted).toContainEqual({ id: 'delivery:invalid-source', kind: 'delivery',
    reason: variant === 'superseded' ? 'superseded' : 'stale-version' });
});

it('uses an unconditional shared wrapper as the boundary for hidden implementation prerequisites', () => {
  const wrapper = { ...lemma('wrapper', ['private_implementation']), sharing: 'problem' as const },
    consumer = lemma('consumer', [wrapper.id]), action = assign(consumer);
  action.assignment.dependencies = [{ taskId: wrapper.id, taskDigest: taskVersion(wrapper) },
    { taskId: 'private_implementation', taskDigest: 'host-pinned-private-version' }];
  const context = compileTaskContext(input([node(consumer), { ...node(wrapper), status: 'integrated', integratedCheck: checked(wrapper) }], action));
  expect(context.manifest.requiredTaskIds).toEqual(['consumer', 'wrapper']);
  expect(context.manifest.omitted).toContainEqual({ id: 'interface:private_implementation', kind: 'interfaces', reason: 'encapsulated-private-dependency' });
  expect(context.message).toContain('kernel-receipt');
  expect(context.message).toContain(proofCommit);
  expect(context.message).not.toContain('PRIVATE_PROOF_BODY');
});

it('keeps submitted-source and disposable verifier projection commits distinct for shared wrappers', () => {
  const wrapper = { ...lemma('wrapper', ['private_implementation']), sharing: 'problem' as const }, consumer = lemma('consumer', [wrapper.id]);
  const projectionCommit = 'c'.repeat(40), proof = checked(wrapper);
  const projected = { ...proof, verification: { ...proof.verification, targetCommit: projectionCommit,
    results: proof.verification.results.map(result => ({ ...result, targetCommit: projectionCommit })) } };
  const context = compileTaskContext(input([node(consumer), { ...node(wrapper), status: 'integrated', integratedCheck: projected }], assign(consumer)));
  expect(context.message).toContain(proofCommit);
  expect(context.message).toContain(projectionCommit);
  expect(context.manifest.omitted).toContainEqual({ id: 'interface:private_implementation', kind: 'interfaces', reason: 'encapsulated-private-dependency' });
});

it('does not let one closed wrapper hide an unrelated missing assignment input', () => {
  const wrapper = { ...lemma('wrapper', ['private_implementation']), sharing: 'problem' as const },
    consumer = lemma('consumer', [wrapper.id]), action = assign(consumer);
  action.assignment.dependencies = [{ taskId: 'private_implementation', taskDigest: 'host-pinned-private-version' },
    { taskId: 'unrelated_missing_input', taskDigest: 'unrelated-version' }];
  expect(() => compileTaskContext(input([node(consumer), { ...node(wrapper), status: 'integrated', integratedCheck: checked(wrapper) }], action)))
    .toThrow('math_context_missing_required:dependency:unrelated_missing_input');
});

it('retains an entire fitting checkpoint and its required mathematical interfaces', () => {
  const task = lemma('current', [], '∀ n : Nat, ' + 'n = n ∧ '.repeat(1000) + 'True');
  const checkpoint = 'Current proof checkpoint.\n' + 'details '.repeat(3000) + 'NEXT_MATHEMATICAL_STEP';
  const context = compileTaskContext({ ...input([node(task)], assign(task)), checkpoint });
  expect(context.message).toContain(JSON.stringify(task.type));
  expect(context.message).toContain(checkpoint);
  expect(context.manifest.included).toContainEqual(expect.objectContaining({ id: 'checkpoint-source', required: true }));
  expect(context.manifest.omitted.some(item => item.id.startsWith('checkpoint'))).toBe(false);
});

it('refuses to hide an unresolved condition behind a shared wrapper', () => {
  const wrapper = { ...lemma('wrapper', ['private_implementation']), sharing: 'problem' as const }, consumer = lemma('consumer', [wrapper.id]);
  expect(() => compileTaskContext(input([node(consumer), { ...node(wrapper), status: 'integrated',
    integratedCheck: checked(wrapper, [{ taskId: 'private_implementation', taskDigest: 'private-version' }]) }], assign(consumer))))
    .toThrow('math_context_missing_required:condition:private_implementation');
});

it('does not expose an unrelated private blocker or recurrence basis in a scoped prompt', () => {
  const task = { ...lemma('task'), groupId: 'public' }, base = input([node(task)], assign(task));
  const blocker = { id: 'private-blocker', taskId: 'private-task', groupId: 'private', taskDigest: 'private-version',
    mechanism: 'PRIVATE_MECHANISM', scope: 'PRIVATE_SCOPE', basis: { secret: 'PRIVATE_BASIS' }, status: 'parked' };
  const context = compileTaskContext({ ...base, cooperation: { ...base.cooperation!, blockers: [blocker] } as TaskContextInput['cooperation'] });
  expect(context.message).not.toMatch(/PRIVATE_(?:MECHANISM|SCOPE|BASIS)/u);
  expect(context.manifest.omitted).toContainEqual({ id: 'blocker:private-blocker', kind: 'blocker', reason: 'outside-task-scope' });
});

it('requires immutable source retrieval and exact original target headers', () => {
  const task: CooperativeTask = { id: 'goal', kind: 'goal', objective: 'Prove target', dependsOn: [], revision: 0,
    theoremName: 'Original.target', proofPath: 'Submission.lean' };
  const context = compileTaskContext(input([node(task)], assign(task)));
  expect(context.message).toContain('theorem target (h : n > 0) : n > 0');
  expect(() => compileTaskContext({ ...input([node(task)], assign(task)), problem: { ...problem, baseCommit: '' } }))
    .toThrow('math_context_missing_required:frozen-source-commit');
});

it('preserves source variables, scopes, instances and frozen definitions while removing original proof bodies', () => {
  const source = 'import Mathlib.Data.Nat.Basic\nnamespace Frozen\nsection WithVariables\nvariable (n : Nat)\n' +
    'local instance localNat : Inhabited Nat := ⟨17⟩\n' +
    'def fixedValue : Nat := 17\n' +
    'theorem previous : True := by\n  -- ORIGINAL_PROOF_BODY\n  trivial\n' +
    'def target : Nat := by\n  exact 99 -- ORIGINAL_TARGET_BODY\nend WithVariables\nend Frozen\n';
  const projected = frozenSourceContext({ ...problem, declarations: {}, targets: [{ proofPath: 'Submission.lean',
    theoremName: 'Frozen.target', declarationHash: 'frozen-target' }] }, 'Submission.lean', source);
  expect(projected).toContain('namespace Frozen\nsection WithVariables\nvariable (n : Nat)');
  expect(projected).toContain('local instance localNat : Inhabited Nat := ⟨17⟩');
  expect(projected).toContain('def fixedValue : Nat := 17');
  expect(projected).not.toContain('ORIGINAL_PROOF_BODY');
  expect(projected).not.toContain('ORIGINAL_TARGET_BODY');
  expect(projected).not.toContain('exact 99');
  expect(projected).toContain('end WithVariables\nend Frozen');
});

it('requires the selected alternative route closing and prerequisite interfaces beyond ordinary dependsOn', () => {
  const target: CooperativeTask = { id: 'target', kind: 'goal', objective: 'Prove target', dependsOn: [], revision: 0,
    theoremName: 'Original.target', proofPath: 'Submission.lean' };
  const premise = lemma('route_premise'), closing = lemma('route_closing', [premise.id], '∀ n : Nat, n > 0 → n > 0');
  const route = { id: 'selected', targetTaskId: target.id, prerequisiteTaskIds: [premise.id], closingTaskId: closing.id };
  const action = assign(target); action.assignment.routeId = route.id;
  const context = compileTaskContext({ ...input([node(target), node(premise), node(closing)], action),
    cooperation: { tasks: [{ ...node(target), alternativeRoutes: [route] }, node(premise), node(closing)], proofRoutes: [route] } });
  expect(context.manifest.requiredTaskIds).toEqual(['target', 'route_premise', 'route_closing']);
  expect(context.manifest.included).toContainEqual(expect.objectContaining({ id: 'route:selected', required: true }));
  expect(context.message).toContain(JSON.stringify(closing.type));
});

it('includes every visible version-bound assignment input as a mandatory interface', () => {
  const consumer = lemma('consumer'), inputTask = lemma('actual_lean_input'), action = assign(consumer);
  action.assignment.dependencies = [{ taskId: inputTask.id, taskDigest: taskVersion(inputTask) }];
  const context = compileTaskContext(input([node(consumer), node(inputTask)], action));
  expect(context.manifest.requiredTaskIds).toEqual(['consumer', 'actual_lean_input']);
});

it('fails closed for unavailable frozen context instead of substituting a context digest', () => {
  expect(() => compileTaskContext({ ...input([]), frozenContexts: undefined }))
    .toThrow('math_context_missing_required:frozen-context:Submission.lean');
  expect(() => buildResearchContext({ ...problem, workspace: '/unavailable-frozen-repository' }, {} as SolverRunState,
    { root: '/runtime', worktree: '/unavailable-frozen-worktree', environment: {}, taskText: 'Prove', retrievalRoot: '/library' }))
    .toThrow('math_context_missing_required:frozen-source:Submission.lean');
});

const contextLine = (message: string, label: string) => JSON.parse(message.split(`${label}\n`)[1].split('\n')[0]);
const encodedGraph = (message: string): any[] => contextLine(message, 'Lead task graph and host feedback:');
const compiledGraph = (message: string): any[] => {
  const dictionary = message.includes('Complete evidence reference dictionary (mandatory, recorded-not-replayed):')
    ? compiledDictionary(message) : undefined;
  return encodedGraph(message).map(row => {
    if (!row.evidence) return row;
    if (row.evidence.taskDigest === null) row.evidence.taskDigest = row.taskDigest;
    if (row.integratedCommit === null) row.integratedCommit = row.evidence.commit;
    if (row.checkedSourceDigest === null) row.checkedSourceDigest = row.evidence.sourceDigest;
    for (const receipt of row.evidence.verification.receipts)
      if (receipt.targetCommit === null) receipt.targetCommit = row.evidence.verification.targetCommit;
    if (row.evidence.references?.tasks) row.evidence.references.tasks = row.evidence.references.tasks.map((entry: number) => dictionary!.entries[entry]);
    return row;
  });
};
const compiledDictionary = (message: string): { entries: any[]; digests: string[]; projectRelative: string;
  encoding: string; digestExpansion: string } =>
  contextLine(message, 'Complete evidence reference dictionary (mandatory, recorded-not-replayed):');
const expandedProofSource = (row: any) => row.source && { commit: row.evidence.commit, path: row.source.path,
  sourceDigest: row.evidence.sourceDigest, ...(row.evidence.references ? { inputsFrom: 'evidence.references.inputs' } : {}) };

function referenceProof(task: CooperativeTask, sourceCommit = proofCommit): TaskProof {
  const input = { file: 'Submission.lean', name: 'shared_support', digest: 'same-interface-digest' },
    declaration = { file: input.file, name: input.name }, references = { sourceCommit,
      environmentDigest: 'fixed-environment', contextDigest: 'fixed-context',
      root: { file: 'Submission.lean', name: task.theoremName! },
      inputs: [input, input], proof: [declaration, declaration], statement: [declaration], tasks: [] };
  return { ...checked(task), references, conditions: [], verification: { ...checked(task).verification,
    targetCommit: 'd'.repeat(40), results: checked(task).verification.results.map(result =>
      ({ ...result, receiptId: `receipt-${task.id}`, targetCommit: 'd'.repeat(40) })) } };
}

it('losslessly expands deduplicated references, their order, proof source paths and all mandatory evidence identities', () => {
  const tasks = [lemma('first'), lemma('second')], proofs = tasks.map(task => referenceProof(task));
  // Equal objects with different property insertion order still share one dictionary entry.
  proofs[1].references!.inputs[0] = { digest: 'same-interface-digest', name: 'shared_support', file: 'Submission.lean' };
  const context = compileTaskContext(input(tasks.map((task, index) => ({ ...node(task), status: 'integrated', integratedCheck: proofs[index] }))));
  const graph = compiledGraph(context.message), dictionary = compiledDictionary(context.message);
  expect(dictionary.entries).toHaveLength(2);
  expect(context.manifest.included).toContainEqual(expect.objectContaining({ id: 'evidence-reference-dictionary', required: true }));
  expect(context.manifest.included).toContainEqual(expect.objectContaining({ id: 'proof-source-reference-encoding', required: true }));
  for (const [index, row] of graph.entries()) {
    const references = row.evidence.references, original = proofs[index].references!;
    for (const key of ['inputs', 'proof', 'statement'] as const)
      expect(references[key].map((id: number) => dictionary.entries[id])).toEqual(original[key]);
    expect(references.inputs[0]).toBe(references.inputs[1]);
    expect(references.sourceCommit).toBe(original.sourceCommit);
    expect(dictionary.digests[references.contextDigest]).toBe(original.contextDigest);
    expect(dictionary.digests[references.environmentDigest]).toBe(original.environmentDigest);
    expect(references.root).toEqual(original.root);
    expect(references.tasks).toEqual(original.tasks);
    expect(row.type).toBe(tasks[index].type);
    expect(row.evidence.conditions).toEqual(proofs[index].conditions);
    expect(row.evidence.verification.receipts).toEqual(proofs[index].verification.results);
    expect(row.source.inputs).toBeUndefined();
    expect(row.source.evidenceFrom).toBe('evidence');
    expect(expandedProofSource(row)).toEqual({ commit: proofs[index].commit,
      path: `${problem.projectRelative}/${tasks[index].proofPath}`, sourceDigest: proofs[index].sourceDigest,
      inputsFrom: 'evidence.references.inputs' });
    const expandedSources = references.inputs.map((id: number) => ({ ...dictionary.entries[id],
      commit: references.sourceCommit, path: `${dictionary.projectRelative}/${dictionary.entries[id].file}` }));
    expect(expandedSources).toEqual(original.inputs.map(item => ({ ...item, commit: original.sourceCommit,
      path: `${problem.projectRelative}/${item.file}` })));
  }
});

it('renders a mandatory digest dictionary when all declaration reference arrays are empty', () => {
  const task = lemma('empty_references'), proof = referenceProof(task);
  proof.references = { ...proof.references!, inputs: [], statement: [], proof: [] };
  const original = structuredClone(proof), context = compileTaskContext(input([
    { ...node(task), status: 'integrated', integratedCheck: proof },
  ])), dictionary = compiledDictionary(context.message), references = compiledGraph(context.message)[0].evidence.references;
  expect(dictionary.encoding).toBe('evidence-reference-indices-v3');
  expect(dictionary.entries).toEqual([]);
  expect(dictionary.digests).toEqual([proof.references.environmentDigest, proof.references.contextDigest]);
  expect(dictionary.digestExpansion).toContain('environmentDigest or contextDigest');
  expect(dictionary.digestExpansion).toContain('exact original digest string');
  expect(context.manifest.included).toContainEqual(expect.objectContaining({ id: 'evidence-reference-dictionary', required: true }));
  expect({ ...references, environmentDigest: dictionary.digests[references.environmentDigest],
    contextDigest: dictionary.digests[references.contextDigest] }).toEqual(proof.references);
  expect(proof).toEqual(original);
});

it('restores identical and distinct environment and context digests without changing any evidence identity', () => {
  const tasks = [lemma('shared'), lemma('distinct_context'), lemma('distinct_environment')],
    proofs = tasks.map((task, index) => referenceProof(task, String(index + 1).repeat(40)));
  proofs[0].references = { ...proofs[0].references!, environmentDigest: 'a'.repeat(64), contextDigest: 'a'.repeat(64) };
  proofs[1].references = { ...proofs[1].references!, environmentDigest: 'a'.repeat(64), contextDigest: 'b'.repeat(64) };
  proofs[2].references = { ...proofs[2].references!, environmentDigest: 'c'.repeat(64), contextDigest: 'b'.repeat(64) };
  const original = structuredClone(proofs), context = compileTaskContext(input(tasks.map((task, index) =>
    ({ ...node(task), status: 'integrated', integratedCheck: proofs[index] })))),
    graph = compiledGraph(context.message), dictionary = compiledDictionary(context.message);
  expect(dictionary.digests).toEqual(['a'.repeat(64), 'b'.repeat(64), 'c'.repeat(64)]);
  expect(graph[0].evidence.references.environmentDigest).toBe(graph[0].evidence.references.contextDigest);
  for (const [index, row] of graph.entries()) {
    const references = row.evidence.references;
    expect({ ...references, environmentDigest: dictionary.digests[references.environmentDigest],
      contextDigest: dictionary.digests[references.contextDigest],
      ...Object.fromEntries(['inputs', 'statement', 'proof'].map(key =>
        [key, references[key].map((id: number) => dictionary.entries[id])])),
    }).toEqual(proofs[index].references);
    expect(row.evidence.commit).toBe(proofs[index].commit);
    expect(row.evidence.verification.targetCommit).toBe(proofs[index].verification.targetCommit);
    expect(row.evidence.verification.receipts).toEqual(proofs[index].verification.results);
    expect(row.evidence.conditions).toEqual(proofs[index].conditions);
  }
  expect(proofs).toEqual(original);
});

it('expands shared source metadata for conditional and unconditional proofs without conflating the source or verifier commits', () => {
  const dependency = lemma('condition'), conditional = { ...lemma('conditional', [dependency.id]), conditional: true },
    unconditional = lemma('unconditional'), withReferences = referenceProof(unconditional, '1'.repeat(40)),
    withoutReferences = checked(conditional, [{ taskId: dependency.id, taskDigest: taskVersion(dependency) }]);
  const context = compileTaskContext(input([{ ...node(unconditional), status: 'integrated', integratedCheck: withReferences },
    { ...node(conditional), status: 'conditional', proof: withoutReferences }, node(dependency)]));
  const encoding = contextLine(context.message, 'Complete proof source reference encoding (mandatory, recorded-not-replayed):'),
    graph = compiledGraph(context.message);
  expect(encoding.encoding).toBe('proof-source-evidence-v2');
  expect(encoding.expansion).toContain('row.evidence.commit');
  expect(encoding.expansion).toContain('otherwise omit inputsFrom');
  expect(expandedProofSource(graph[0])).toEqual({ commit: withReferences.commit, sourceDigest: withReferences.sourceDigest,
    path: `${problem.projectRelative}/${unconditional.proofPath}`, inputsFrom: 'evidence.references.inputs' });
  expect(expandedProofSource(graph[1])).toEqual({ commit: withoutReferences.commit, sourceDigest: withoutReferences.sourceDigest,
    path: `${problem.projectRelative}/${conditional.proofPath}` });
  expect(graph[0].evidence.references.sourceCommit).toBe('1'.repeat(40));
  expect(graph[0].evidence.verification.targetCommit).toBe('d'.repeat(40));
  expect(expandedProofSource(graph[0]).commit).toBe(proofCommit);
  expect(graph[1].evidence.conditions).toEqual(withoutReferences.conditions);
  expect(graph[1].status).toBe('conditional');
});

it('shares identical reference metadata without conflating distinct source commits or changed input digests', () => {
  const tasks = [lemma('one'), lemma('two'), lemma('three')], commits = ['1'.repeat(40), '2'.repeat(40), '3'.repeat(40)],
    proofs = tasks.map((task, index) => referenceProof(task, commits[index]));
  proofs[2].references!.inputs = proofs[2].references!.inputs.map(item => ({ ...item, digest: 'changed-interface-digest' }));
  const context = compileTaskContext(input(tasks.map((task, index) => ({ ...node(task), status: 'integrated', integratedCheck: proofs[index] }))));
  const graph = compiledGraph(context.message), dictionary = compiledDictionary(context.message);
  expect(graph[0].evidence.references.inputs).toEqual(graph[1].evidence.references.inputs);
  expect(graph[0].evidence.references.sourceCommit).not.toBe(graph[1].evidence.references.sourceCommit);
  expect(graph.map(row => row.evidence.references.sourceCommit)).toEqual(commits);
  expect(graph[0].evidence.references.inputs).not.toEqual(graph[2].evidence.references.inputs);
  expect(dictionary.entries[graph[2].evidence.references.inputs[0]].digest).toBe('changed-interface-digest');
  expect(graph[0].evidence.commit).toBe(proofCommit);
  expect(graph[0].evidence.verification.targetCommit).toBe('d'.repeat(40));
});

it.each(['.', 'generated\\p\\'])('reconstructs source paths with the original POSIX join rule for project %s', projectRelative => {
  const task = lemma('source_path'), proof = referenceProof(task);
  const context = compileTaskContext({ ...input([{ ...node(task), status: 'integrated', integratedCheck: proof }]),
    problem: { ...problem, projectRelative } });
  const row = compiledGraph(context.message)[0], dictionary = compiledDictionary(context.message);
  expect(dictionary.projectRelative).toBe(projectRelative.replaceAll('\\', '/'));
  expect(row.source.path).toBe(path.posix.join(dictionary.projectRelative, task.proofPath!));
  for (const id of row.evidence.references.inputs) {
    const restoredPath = path.posix.join(dictionary.projectRelative, dictionary.entries[id].file);
    expect(restoredPath).toBe(path.posix.join(projectRelative.replaceAll('\\', '/'), proof.references!.inputs[0].file));
  }
});

it('fits a large repeated-reference graph in the unchanged byte budget while preserving every exact task interface', () => {
  const tasks = Array.from({ length: 60 }, (_, index) => lemma(`checkpoint${index}`, [],
    `∀ n : Nat, ${'n = n ∧ '.repeat(80)}True`));
  const inputs = Array.from({ length: 60 }, (_, index) => ({ file: 'Submission.lean',
    name: `shared_long_declaration_name_${index}`, digest: String(index).padStart(64, '0') })),
    declarationRefs = inputs.map(({ file, name }) => ({ file, name }));
  const records = tasks.map(task => ({ ...node(task), status: 'integrated' as const, integratedCheck: {
    ...referenceProof(task), references: { ...referenceProof(task).references!, inputs, proof: declarationRefs, statement: declarationRefs },
  } }));
  const context = compileTaskContext(input(records)), graph = compiledGraph(context.message),
    dictionary = compiledDictionary(context.message);
  expect(context.manifest.usedBytes).toBeLessThanOrEqual(DEFAULT_TASK_CONTEXT_BYTES);
  expect(context.manifest.requiredTaskIds).toHaveLength(tasks.length);
  expect(graph.map(row => row.type)).toEqual(tasks.map(task => task.type));
  const expanded = graph.map(row => {
    const references = row.evidence.references;
    const arrays = Object.fromEntries(['inputs', 'proof', 'statement'].map(key =>
      [key, references[key].map((id: number) => dictionary.entries[id])]));
    return { ...row, evidence: { ...row.evidence, references: { ...references, ...arrays,
      environmentDigest: dictionary.digests[references.environmentDigest],
      contextDigest: dictionary.digests[references.contextDigest] } }, source: {
      ...expandedProofSource(row),
      inputs: arrays.inputs.map((item: any) => ({ ...item, commit: references.sourceCommit,
        path: `${dictionary.projectRelative}/${item.file}` })),
    } };
  });
  expect(Buffer.byteLength(canonicalMathJson(expanded))).toBeGreaterThan(DEFAULT_TASK_CONTEXT_BYTES);
  expect(dictionary.entries).toHaveLength(inputs.length + declarationRefs.length);
});

it('shares exact task reference metadata and proof fields without losing receipt targets or array order', () => {
  const tasks = [lemma('first'), lemma('second')], proofs = tasks.map(task => referenceProof(task));
  const references = [{ taskId: tasks[0].id, taskDigest: taskVersion(tasks[0]) },
    { taskId: tasks[1].id, taskDigest: taskVersion(tasks[1]) }];
  for (const proof of proofs) proof.references!.tasks = [references[1], references[0], references[1]];
  const context = compileTaskContext(input(tasks.map((task, index) => ({ ...node(task), status: 'integrated', integratedCheck: proofs[index] })))),
    raw = encodedGraph(context.message), dictionary = compiledDictionary(context.message), graph = compiledGraph(context.message);
  expect(dictionary.entries.filter(entry => 'taskId' in entry)).toEqual([references[1], references[0]]);
  for (const [index, row] of raw.entries()) {
    expect(row.evidence.references.tasks).toEqual(raw[0].evidence.references.tasks);
    expect(row.evidence.references.tasks[0]).toBe(row.evidence.references.tasks[2]);
    expect(row.evidence.taskDigest).toBeNull();
    expect(row.integratedCommit).toBeNull();
    expect(row.checkedSourceDigest).toBeNull();
    expect(row.evidence.verification.receipts[0].targetCommit).toBeNull();
    expect(graph[index].evidence.references.tasks).toEqual(proofs[index].references!.tasks);
    expect(graph[index].evidence.taskDigest).toBe(proofs[index].taskDigest);
    expect(graph[index].integratedCommit).toBe(proofs[index].commit);
    expect(graph[index].checkedSourceDigest).toBe(proofs[index].sourceDigest);
    expect(graph[index].evidence.verification.receipts).toEqual(proofs[index].verification.results);
  }
});

it('does not replace distinct or absent failed receipt targets with an enclosing verifier commit', () => {
  const task = lemma('failed'), proof = checked(task);
  proof.passed = false;
  proof.verification.results = [{ receiptId: 'distinct', status: 'kernel_rejected', targetCommit: 'e'.repeat(40) },
    { receiptId: 'absent', status: 'kernel_rejected' }] as TaskProof['verification']['results'];
  const context = compileTaskContext(input([{ ...node(task), proof }])), row = encodedGraph(context.message)[0];
  expect(row.evidence.verification.receipts).toEqual(proof.verification.results);
  expect(compiledGraph(context.message)[0].evidence.verification.receipts).toEqual(proof.verification.results);
  expect(row.integratedCommit).toBeUndefined();
  expect(row.checkedSourceDigest).toBeUndefined();
});

const lead = { kind: 'lead' as const, seedCommit: baseCommit };
const originalGoal = (dependencies: readonly string[] = []) => node({ ...lemma('original_goal', dependencies),
  kind: 'goal', theoremName: 'Original.target' });
function freshlyChecked(task: CooperativeTask, conditions: TaskProof['conditions'] = []): TaskRecord {
  const proof = referenceProof(task);
  proof.conditions = conditions;
  markTaskAcceptance(proof);
  return { ...node(task), status: 'integrated', integratedCheck: proof };
}
const helperCatalog = (message: string): any[] => contextLine(message,
  'Checked helpers outside the current open-task closure (retrieve before using; recorded, not replayed):').helpers;

it('keeps the open Lead frontier complete while encapsulating freshly checked unconditional implementation helpers', () => {
  const implementation = freshlyChecked(lemma('implementation', [], '∀ n : Nat, n + 0 = n')),
    wrapper = freshlyChecked(lemma('wrapper', ['implementation'])), goal = originalGoal(['wrapper']);
  const research = node({ ...lemma('open_research'), kind: 'research' as const,
    objective: 'FULL_UNFINISHED_RESEARCH_DESCRIPTION', type: undefined });
  const current = node({ ...lemma('open_proof'), objective: 'FULL_UNFINISHED_PROOF_DESCRIPTION',
    premises: ['FULL_UNFINISHED_MATHEMATICAL_PREMISE'] });
  const context = compileTaskContext({ ...input([implementation, wrapper, goal, research, current], lead), maxOptionalContextBytes: 0 }),
    catalog = helperCatalog(context.message), graph = compiledGraph(context.message);
  expect(new Set(context.manifest.requiredTaskIds)).toEqual(new Set(['wrapper', 'original_goal', 'open_research', 'open_proof']));
  expect(graph.map(row => row.id)).toEqual(['wrapper', 'original_goal', 'open_research', 'open_proof']);
  expect(graph.find(row => row.id === wrapper.task.id).type).toBe(wrapper.task.type);
  expect(context.message).toContain('FULL_UNFINISHED_RESEARCH_DESCRIPTION');
  expect(context.message).toContain('FULL_UNFINISHED_PROOF_DESCRIPTION');
  expect(context.message).toContain('FULL_UNFINISHED_MATHEMATICAL_PREMISE');
  expect(catalog).toHaveLength(1);
  expect(catalog[0]).toMatchObject({ id: implementation.task.id, taskDigest: taskVersion(implementation.task),
    theoremName: implementation.task.theoremName, proofPath: implementation.task.proofPath,
    objectiveDigest: mathDigest(implementation.task.objective), source: { commit: implementation.integratedCheck!.commit,
      path: `${problem.projectRelative}/${implementation.task.proofPath}`, sourceDigest: implementation.integratedCheck!.sourceDigest },
    verification: { status: implementation.integratedCheck!.verification.status,
      targetCommit: implementation.integratedCheck!.verification.targetCommit,
      receipts: implementation.integratedCheck!.verification.results } });
  expect(context.message).toContain('taskDigest matches this row');
  expect(context.message).toContain('not an immutable proof source');
  expect(context.manifest.included).toContainEqual(expect.objectContaining({ id: 'checked-helper-catalog', required: true }));
  expect(context.manifest.omitted).toContainEqual({ id: `interface:${implementation.task.id}`, kind: 'interfaces', reason: 'optional-budget' });
});

it('preserves an integrated helper interface when it is a direct input of any unfinished task', () => {
  const first = freshlyChecked(lemma('first')), second = freshlyChecked(lemma('second', ['first'])),
    current = node({ ...lemma('current', ['first']), objective: 'This unfinished task still needs first.' });
  const context = compileTaskContext({ ...input([first, second, originalGoal(['second']), current], lead), maxOptionalContextBytes: 0 });
  expect(context.manifest.requiredTaskIds).toContain('first');
  expect(compiledGraph(context.message).find(row => row.id === first.task.id).type).toBe(first.task.type);
  expect(context.manifest.included.some(section => section.id === 'checked-helper-catalog')).toBe(false);
});

it('preserves the original-goal frontier without reporting encapsulated helper internals as missing', () => {
  const implementation = freshlyChecked(lemma('implementation')), wrapper = freshlyChecked(lemma('wrapper', ['implementation'])),
    consumer = node(lemma('consumer', ['wrapper'])), goal = originalGoal(['consumer']), records = [implementation, wrapper, consumer, goal];
  const baseline = buildProofContinuation(records), context = compileTaskContext({ ...input(records, lead), maxOptionalContextBytes: 0 }),
    continuation = contextLine(context.message, 'Unfinished original goals and their current frontier (recorded, not proof acceptance):');
  expect(continuation.goals).toEqual(baseline.goals.map(({ taskId, frontier, missingDependencies }) => ({ taskId, frontier, missingDependencies })));
  expect(continuation.goals[0].missingDependencies).toEqual([]);
  expect(continuation.frontier).toEqual(baseline.frontier);
  expect(helperCatalog(context.message).map(row => row.id)).toEqual(['implementation']);
});

it('does not add a Lead helper catalog to an ordinary worker task context', () => {
  const unrelated = freshlyChecked(lemma('unrelated')), task = lemma('current');
  const context = compileTaskContext({ ...input([unrelated, node(task)], assign(task)), maxOptionalContextBytes: 0 });
  expect(context.manifest.requiredTaskIds).toEqual(['current']);
  expect(context.manifest.included.some(section => section.id === 'checked-helper-catalog')).toBe(false);
  expect(compiledGraph(context.message).map(row => row.id)).toEqual(['current']);
});

it.each(['restored', 'conditional', 'failed'] as const)('keeps %s helper contracts and all unresolved conditions mandatory', kind => {
  const implementation = freshlyChecked(lemma('implementation')), wrapper = freshlyChecked(lemma('wrapper', ['implementation']),
    kind === 'conditional' ? [{ taskId: implementation.task.id, taskDigest: taskVersion(implementation.task) }] : []);
  if (kind === 'restored') {
    wrapper.integratedCheck = structuredClone(wrapper.integratedCheck!);
    expect(hasTaskAcceptance(wrapper.integratedCheck)).toBe(false);
  }
  if (kind === 'failed') { wrapper.integratedCheck!.passed = false; markTaskAcceptance(wrapper.integratedCheck!); }
  const context = compileTaskContext({ ...input([implementation, wrapper, originalGoal(['wrapper'])], lead), maxOptionalContextBytes: 0 });
  expect(context.manifest.requiredTaskIds).toContain('implementation');
  expect(context.manifest.requiredTaskIds).toContain('wrapper');
  expect(context.manifest.included.some(section => section.id === 'checked-helper-catalog')).toBe(false);
});

it('retains every original-goal alternative route input even when all route helpers are already checked', () => {
  const prerequisite = freshlyChecked(lemma('prerequisite')), closing = freshlyChecked(lemma('closing', ['prerequisite'])), goal = originalGoal();
  const route = { id: 'route', targetTaskId: goal.task.id, prerequisiteTaskIds: ['prerequisite'], closingTaskId: 'closing' };
  goal.alternativeRoutes = [route];
  const context = compileTaskContext({ ...input([prerequisite, closing, goal], lead), maxOptionalContextBytes: 0 });
  expect(context.manifest.requiredTaskIds).toEqual(['original_goal', 'prerequisite', 'closing']);
  expect(compiledGraph(context.message).map(row => row.type).filter(Boolean)).toEqual([prerequisite.task.type, closing.task.type, goal.task.type]);
});

it('keeps a growing historical helper graph below the unchanged budget without truncating the open contracts', () => {
  const tasks = Array.from({ length: 200 }, (_, index) => ({ ...lemma(`history${index}`, index ? [`history${index - 1}`] : [],
    `∀ n : Nat, ${'n = n ∧ '.repeat(200)}True`), objective: `Earlier helper ${index}. ${'Saved planning context. '.repeat(50)}` })),
    records = tasks.map(task => freshlyChecked(task)), current = node({ ...lemma('frontier', ['history199']),
      objective: 'COMPLETE_CURRENT_FRONTIER_DESCRIPTION', premises: ['COMPLETE_CURRENT_PREMISE'] }), goal = originalGoal(['frontier']);
  const context = compileTaskContext({ ...input([...records, current, goal], lead), maxOptionalContextBytes: 0 });
  expect(context.manifest.maxBytes).toBe(DEFAULT_TASK_CONTEXT_BYTES);
  expect(context.manifest.mandatoryBytes).toBeLessThan(DEFAULT_TASK_CONTEXT_BYTES * 0.7);
  expect(helperCatalog(context.message)).toHaveLength(199);
  expect(new Set(context.manifest.requiredTaskIds)).toEqual(new Set(['original_goal', 'frontier', 'history199']));
  expect(compiledGraph(context.message).find(row => row.id === 'history199').type).toBe(tasks.at(-1)!.type);
  expect(context.message).toContain('COMPLETE_CURRENT_FRONTIER_DESCRIPTION');
  expect(context.message).toContain('COMPLETE_CURRENT_PREMISE');
  expect(() => compileTaskContext({ ...input([...records, current, goal]), maxOptionalContextBytes: 0 }))
    .toThrow('math_context_mandatory_overflow');
});

it('keeps exact checked helper contracts and evidence inline while making long finished objectives retrievable by digest', () => {
  const helper = freshlyChecked({ ...lemma('shared_input'), objective: 'FINISHED_HELPER_PLAN '.repeat(150),
    premises: ['EXACT_HELPER_PREMISE'] }), goal = originalGoal(['shared_input']), records = [helper, goal],
    original = structuredClone(records);
  const context = compileTaskContext({ ...input(records, lead), maxOptionalContextBytes: 0 }),
    graph = compiledGraph(context.message), row = graph.find(item => item.id === helper.task.id),
    encoding = contextLine(context.message,
      'Finished task objective references (advisory prose by reference; exact interfaces remain mandatory):');
  expect(context.manifest.requiredTaskIds).toContain(helper.task.id);
  expect(row).toMatchObject({ id: helper.task.id, type: helper.task.type, premises: helper.task.premises,
    dependsOn: helper.task.dependsOn, taskDigest: taskVersion(helper.task),
    objectiveDigest: mathDigest(helper.task.objective), evidence: { taskDigest: helper.integratedCheck!.taskDigest,
      commit: helper.integratedCheck!.commit, sourceDigest: helper.integratedCheck!.sourceDigest,
      verification: { receipts: helper.integratedCheck!.verification.results } } });
  expect(row.objective).toBeUndefined();
  expect(context.message).not.toContain('FINISHED_HELPER_PLAN');
  expect(context.message).toContain(goal.task.objective);
  expect(encoding.retrieval).toContain('COOPERATION.json peers by id');
  expect(encoding.retrieval).toContain('UTF-8 SHA-256');
  expect(encoding.retrieval).toContain('not an immutable proof source');
  expect(context.manifest.omitted).toContainEqual({ id: `objective:${helper.task.id}`, kind: 'interfaces',
    reason: 'advisory-details-by-reference' });
  expect(records).toEqual(original);
});

it.each(['restored', 'conditional', 'failed'] as const)('never replaces a %s proof task objective with a finished-task reference', kind => {
  const helper = freshlyChecked({ ...lemma('required_input'), objective: 'UNRESOLVED_PROOF_PLAN '.repeat(150) });
  if (kind === 'restored') helper.integratedCheck = structuredClone(helper.integratedCheck!);
  if (kind === 'conditional') helper.integratedCheck!.conditions = [{ taskId: 'condition', taskDigest: taskVersion(lemma('condition')) }];
  if (kind === 'failed') helper.integratedCheck!.passed = false;
  const context = compileTaskContext({ ...input([helper, node(lemma('condition')), originalGoal(['required_input'])], lead),
    maxOptionalContextBytes: 0 }), row = compiledGraph(context.message).find(item => item.id === helper.task.id);
  expect(row.objective).toBe(helper.task.objective);
  expect(row.objectiveDigest).toBeUndefined();
  expect(context.message).toContain('UNRESOLVED_PROOF_PLAN');
});

it('retains unfinished advisory objectives and leaves worker dependency descriptions complete', () => {
  const completed = node({ ...lemma('completed_research'), kind: 'research' as const, type: undefined,
    objective: 'COMPLETED_RESEARCH_OBJECTIVE '.repeat(100) });
  completed.status = 'completed';
  const blocked = node({ ...lemma('blocked_research'), kind: 'research' as const, type: undefined,
    objective: 'OPEN_RESEARCH_OBJECTIVE '.repeat(100) });
  blocked.status = 'blocked';
  const helper = freshlyChecked({ ...lemma('worker_input'), objective: 'WORKER_DEPENDENCY_OBJECTIVE '.repeat(100) }),
    current = node(lemma('current', ['worker_input'])), records = [completed, blocked, helper, current, originalGoal(['current'])];
  const leadContext = compileTaskContext({ ...input(records, lead), maxOptionalContextBytes: 0 }),
    graph = compiledGraph(leadContext.message);
  expect(graph.find(row => row.id === completed.task.id)).toMatchObject({ status: 'completed',
    objectiveDigest: mathDigest(completed.task.objective) });
  expect(leadContext.message).not.toContain('COMPLETED_RESEARCH_OBJECTIVE');
  expect(graph.find(row => row.id === blocked.task.id).objective).toBe(blocked.task.objective);
  const workerContext = compileTaskContext({ ...input(records, assign(current.task)), maxOptionalContextBytes: 0 });
  expect(compiledGraph(workerContext.message).find(row => row.id === helper.task.id).objective).toBe(helper.task.objective);
  expect(workerContext.manifest.included.some(item => item.id === 'task-objective-reference-encoding')).toBe(false);
});

it('fits a mature Lead graph with many direct checked inputs without raising the fixed context allowance', () => {
  const helpers = Array.from({ length: 60 }, (_, index) => freshlyChecked({
    ...lemma(`direct_input_${index}`, [], `∀ n : Nat, ${'n = n ∧ '.repeat(80)}True`),
    objective: `Finished supporting argument ${index}. ${'Advisory implementation narrative. '.repeat(220)}`,
  }));
  const research = Array.from({ length: 31 }, (_, index) => ({
    ...node({ ...lemma(`finished_research_${index}`), kind: 'research' as const, type: undefined,
      objective: `Historical investigation ${index}. ${'Saved advisory research context. '.repeat(120)}` }), status: 'completed' as const,
  }));
  const current = node({ ...lemma('current_frontier', helpers.map(node => node.task.id)),
    objective: 'COMPLETE_OPEN_TASK_DESCRIPTION', premises: ['COMPLETE_OPEN_TASK_PREMISE'] }),
    records = [...helpers, ...research, current, originalGoal(['current_frontier'])];
  expect(Buffer.byteLength(canonicalMathJson(records.map(node => node.task)))).toBeGreaterThan(DEFAULT_TASK_CONTEXT_BYTES);
  const context = compileTaskContext({ ...input(records, lead), maxOptionalContextBytes: 0 }), graph = compiledGraph(context.message);
  expect(context.manifest.maxBytes).toBe(DEFAULT_TASK_CONTEXT_BYTES);
  expect(context.manifest.usedBytes).toBeLessThan(DEFAULT_TASK_CONTEXT_BYTES * 0.65);
  expect(new Set(context.manifest.requiredTaskIds)).toEqual(new Set(records.map(node => node.task.id)));
  expect(graph.filter(row => row.kind === 'lemma').map(row => row.type)).toEqual([...helpers.map(node => node.task.type), current.task.type]);
  for (const helper of helpers) {
    const row = graph.find(row => row.id === helper.task.id);
    expect(row.evidence.verification.receipts).toEqual(helper.integratedCheck!.verification.results);
    expect(expandedProofSource(row)).toMatchObject({ commit: helper.integratedCheck!.commit,
      sourceDigest: helper.integratedCheck!.sourceDigest });
  }
  expect(context.message).toContain('COMPLETE_OPEN_TASK_DESCRIPTION');
  expect(context.message).toContain('COMPLETE_OPEN_TASK_PREMISE');
});
