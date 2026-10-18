import { expect, it } from 'vitest';
import { mathDigest } from '../src/math/mathRuntimeIo';
import { compileTaskContext, frozenSourceContext, type TaskContextInput } from '../src/solver/contextCompiler';
import type { SolverProblem } from '../src/solver/problem';
import { taskVersion, type CooperativeTask } from '../src/solver/tasks';

const formal = 'namespace Original\ntheorem target (n : Nat) : n = n := by sorry\nend Original';
const problem = { projectRelative: 'generated/checkpoint', ownedFiles: ['Submission.lean'],
  declarations: { 'Submission.lean': [{ name: 'target', header: 'target (n : Nat) : n = n' }] },
  targets: [{ proofPath: 'Submission.lean', theoremName: 'Original.target', declarationHash: 'target-type' }],
  trustedFiles: {}, receiptDigest: 'checkpoint-problem', baseCommit: 'a'.repeat(40),
  contract: { formalStatement: formal, informalStatement: 'Every natural number equals itself.',
    assumptions: [], statementHash: 'statement', leanStatementHash: 'lean-statement' } } as unknown as SolverProblem;
const prerequisite: CooperativeTask = { id: 'prerequisite', kind: 'lemma', objective: 'Establish reflexivity.',
  proofPath: 'Submission.lean', theoremName: 'Original.reflexive', type: 'forall (n : Nat), n = n',
  dependsOn: [], revision: 0 };
const consumer: CooperativeTask = { id: 'consumer', kind: 'lemma', objective: 'Apply reflexivity in the consumer.',
  proofPath: 'Submission.lean', theoremName: 'Original.consumer',
  type: 'forall (n : Nat) (h : n = n), n = n', dependsOn: [prerequisite.id], revision: 0 };
const chinese = '\u5df2\u8bc1\u660e\u9012\u63a8\u4e0d\u53d8\u91cf\uff1b\u5c1a\u9700\u8fde\u63a5\u539f\u59cb\u76ee\u6807\u3002';
const tail = '\nNEXT_MATHEMATICAL_STEP: apply the monotone limit theorem and discharge its boundedness premise.\n' +
  '\u4e0b\u4e00\u6b65\uff1a\u5c06\u9012\u63a8\u754c\u4f20\u9012\u5230\u6781\u9650\uff0c\u95ed\u5408\u539f\u9898\u3002';
const checkpoint = ('For every n : Nat, maintain the invariant sum <= n * n.\n' + chinese + '\n').repeat(224) + tail;
const input = (): TaskContextInput => ({
  problem, instructions: 'Preserve the exact mathematical contracts and independently check proof claims.',
  taskText: 'Prove the original target.', checkpoint,
  frozenContexts: { 'Submission.lean': frozenSourceContext(problem, 'Submission.lean', formal) },
  cooperation: { tasks: [consumer, prerequisite].map(task => ({ task, status: 'pending', attempts: 0 })) },
  action: { kind: 'task', task: consumer,
    assignment: { taskId: consumer.id, taskDigest: taskVersion(consumer), workerId: 'solver', seedCommit: 'b'.repeat(40) } },
});
type Compiled = ReturnType<typeof compileTaskContext>;

function expectInterfacesAndBytes(context: Compiled, source: TaskContextInput) {
  expect(context.manifest.requiredTaskIds).toEqual([consumer.id, prerequisite.id]);
  expect(context.manifest.included).toContainEqual(expect.objectContaining({ id: 'task-interfaces', kind: 'interfaces', required: true }));
  expect(context.message).toContain(JSON.stringify(consumer.type));
  expect(context.message).toContain(JSON.stringify(prerequisite.type));
  expect(context.message).toContain(formal);
  expect(context.manifest.usedBytes).toBe(Buffer.byteLength(source.instructions) + Buffer.byteLength(context.message));
  expect(context.manifest.usedBytes).toBeLessThanOrEqual(context.manifest.maxBytes);
  expect(context.manifest.mandatoryBytes).toBeLessThanOrEqual(context.manifest.usedBytes);
  expect(context.manifest.optionalBytes).toBeLessThanOrEqual(context.manifest.maxOptionalBytes);
  expect(context.manifest.optionalBytes).toBe(context.manifest.included.filter(item => !item.required)
    .reduce((total, item) => total + item.bytes + 2, 0));
}

function expectCheckpointSource(context: Compiled) {
  expect(context.manifest.included).toContainEqual(expect.objectContaining({ id: 'checkpoint-source', kind: 'sources', required: true }));
  const source = context.message.split('\n').filter(line => line.startsWith('{')).map(line => JSON.parse(line))
    .find(value => value.path === 'RESEARCH.md');
  expect(source).toMatchObject({ path: 'RESEARCH.md', bytes: Buffer.byteLength(checkpoint), digest: mathDigest(checkpoint) });
  expect(context.message).toContain('worktree-root RESEARCH.md');
  expect(context.message).toContain('UTF-8');
  expect(context.message).not.toContain('\uFFFD');
}

it('retains a complete mixed-language mathematical checkpoint and its next step after the first 5000 bytes', () => {
  const source = input(), context = compileTaskContext(source);
  expect(Buffer.byteLength(checkpoint)).toBeGreaterThan(24 * 1024);
  expect(Buffer.byteLength(checkpoint)).toBeLessThan(32 * 1024);
  expect(context.message).toContain(checkpoint);
  expect(context.message.match(/NEXT_MATHEMATICAL_STEP/gu)).toHaveLength(1);
  expect(context.message).toContain(chinese);
  expect(context.message).toContain(tail);
  expect(context.manifest.included).toContainEqual(expect.objectContaining({ id: 'checkpoint', kind: 'checkpoint', required: false }));
  expect(context.manifest.omitted.some(item => item.id === 'checkpoint' || item.id === 'checkpoint:tail')).toBe(false);
  expectCheckpointSource(context);
  expectInterfacesAndBytes(context, source);
});

it.each([0, 3000])('omits an entire checkpoint when its optional allowance is %s, retaining its recoverable source', maxOptionalContextBytes => {
  const source = { ...input(), maxOptionalContextBytes }, context = compileTaskContext(source);
  expect(context.message).not.toContain('For every n : Nat, maintain the invariant');
  expect(context.message).not.toContain(tail);
  expect(context.manifest.included.some(item => item.id === 'checkpoint')).toBe(false);
  expect(context.manifest.omitted).toContainEqual({ id: 'checkpoint', kind: 'checkpoint', reason: 'optional-budget' });
  expect(context.manifest.omitted.some(item => item.id === 'checkpoint:tail')).toBe(false);
  expectCheckpointSource(context);
  expectInterfacesAndBytes(context, source);
});

it('retains the mandatory checkpoint source and all typed inputs when the total context allowance excludes its body', () => {
  const mandatory = compileTaskContext({ ...input(), maxOptionalContextBytes: 0 }).manifest.mandatoryBytes;
  const source = { ...input(), maxContextBytes: mandatory + 250 }, context = compileTaskContext(source);
  expect(context.message).not.toContain('For every n : Nat, maintain the invariant');
  expect(context.message).not.toContain(tail);
  expect(context.manifest.included.some(item => item.id === 'checkpoint')).toBe(false);
  expect(context.manifest.omitted).toContainEqual({ id: 'checkpoint', kind: 'checkpoint', reason: 'budget' });
  expectCheckpointSource(context);
  expectInterfacesAndBytes(context, source);
});

it('shows stable checkpoint observations without classifying prose as wasted work or imposing a cutoff', () => {
  const source = input();
  source.cooperation!.researchCheckpoints = { [consumer.id]: { taskDigest: taskVersion(consumer),
    inputDigest: 'input', outputDigest: 'output', count: 1, unchangedEvidenceCount: 12,
    candidateStatus: 'unclassified-draft' } };
  const context = compileTaskContext({ ...source, maxOptionalContextBytes: 0 });
  expect(context.manifest.included).toContainEqual(expect.objectContaining({ id: 'checkpoint-evidence', required: true }));
  expect(context.message).toContain('"savedCheckpointCountWithoutCandidateChange":12');
  expect(context.message).toContain('unclassified prose can contain useful mathematics');
  expect(context.message).toContain('neither accepts a theorem nor stops continued reasoning');
  source.cooperation!.researchCheckpoints[consumer.id].taskDigest = 'superseded';
  expect(compileTaskContext(source).manifest.included.some(section => section.id === 'checkpoint-evidence')).toBe(false);
});
