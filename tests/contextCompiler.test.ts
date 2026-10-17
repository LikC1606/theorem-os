import { expect, it } from 'vitest';
import path from 'node:path';
import { compileTaskContext, DEFAULT_TASK_CONTEXT_BYTES, frozenSourceContext, type TaskContextInput } from '../src/solver/contextCompiler';
import { buildResearchContext } from '../src/solver/modules/context';
import { taskVersion, type CooperativeAction, type CooperativeTask, type TaskRecord } from '../src/solver/tasks';
import type { SolverProblem } from '../src/solver/problem';
import type { SolverRunState } from '../src/solver/archive';
import type { TaskProof } from '../src/solver/cooperativeProof';
import type { DeliveryRecord } from '../src/solver/deliveries';
import { canonicalMathJson } from '../src/math/mathRuntimeIo';

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

it('rejects mismatched mandatory dependency and proof evidence versions', () => {
  const prerequisite = lemma('prerequisite'), consumer = lemma('consumer', [prerequisite.id]), action = assign(consumer);
  action.assignment.dependencies = [{ taskId: prerequisite.id, taskDigest: 'old-version' }];
  expect(() => compileTaskContext(input([node(consumer), node(prerequisite)], action)))
    .toThrow('math_context_stale_required:dependency:prerequisite');
  const proof = { ...checked(prerequisite), taskDigest: 'old-version' };
  expect(() => compileTaskContext(input([node(consumer), { ...node(prerequisite), status: 'integrated', integratedCheck: proof }], assign(consumer))))
    .toThrow('math_context_stale_required:evidence:prerequisite');
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

it('records a shortened advisory checkpoint without shortening its required mathematical interfaces', () => {
  const task = lemma('current', [], '∀ n : Nat, ' + 'n = n ∧ '.repeat(1000) + 'True');
  const context = compileTaskContext({ ...input([node(task)], assign(task)), checkpoint: 'Current proof checkpoint.\n' + 'details '.repeat(3000) });
  expect(context.message).toContain(JSON.stringify(task.type));
  expect(context.message).toContain('Current proof checkpoint.');
  expect(context.message).toContain('read worktree-root RESEARCH.md for the complete checkpoint');
  expect(context.manifest.omitted).toContainEqual({ id: 'checkpoint:tail', kind: 'checkpoint', reason: 'advisory-summary-limit' });
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
const compiledGraph = (message: string): any[] => contextLine(message, 'Lead task graph and host feedback:');
const compiledDictionary = (message: string): { entries: any[]; projectRelative: string } =>
  contextLine(message, 'Complete evidence reference dictionary (mandatory, recorded-not-replayed):');

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
  for (const [index, row] of graph.entries()) {
    const references = row.evidence.references, original = proofs[index].references!;
    for (const key of ['inputs', 'proof', 'statement'] as const)
      expect(references[key].map((id: number) => dictionary.entries[id])).toEqual(original[key]);
    expect(references.inputs[0]).toBe(references.inputs[1]);
    expect(references.sourceCommit).toBe(original.sourceCommit);
    expect(references.contextDigest).toBe(original.contextDigest);
    expect(references.environmentDigest).toBe(original.environmentDigest);
    expect(references.root).toEqual(original.root);
    expect(references.tasks).toEqual(original.tasks);
    expect(row.type).toBe(tasks[index].type);
    expect(row.evidence.conditions).toEqual(proofs[index].conditions);
    expect(row.evidence.verification.receipts).toEqual(proofs[index].verification.results);
    expect(row.source.inputs).toBeUndefined();
    expect(row.source.inputsFrom).toBe('evidence.references.inputs');
    const expandedSources = references.inputs.map((id: number) => ({ ...dictionary.entries[id],
      commit: references.sourceCommit, path: `${dictionary.projectRelative}/${dictionary.entries[id].file}` }));
    expect(expandedSources).toEqual(original.inputs.map(item => ({ ...item, commit: original.sourceCommit,
      path: `${problem.projectRelative}/${item.file}` })));
  }
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
    return { ...row, evidence: { ...row.evidence, references: { ...references, ...arrays } }, source: {
      commit: row.source.commit, path: row.source.path, sourceDigest: row.source.sourceDigest,
      inputs: arrays.inputs.map((item: any) => ({ ...item, commit: references.sourceCommit,
        path: `${dictionary.projectRelative}/${item.file}` })),
    } };
  });
  expect(Buffer.byteLength(canonicalMathJson(expanded))).toBeGreaterThan(DEFAULT_TASK_CONTEXT_BYTES);
  expect(dictionary.entries).toHaveLength(inputs.length + declarationRefs.length);
});
