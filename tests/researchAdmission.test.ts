import { describe, expect, it } from 'vitest';
import { deliveryDetails, parseMathResponse, type DeliveryRecord } from '../src/solver/deliveries';
import { prepareResearchDelivery, ResearchAdmissionError, type ResearchAdmissionScope } from '../src/solver/researchAdmission';
import { bindMathematicalGap, type MathematicalGap } from '../src/solver/mathematicalGaps';
import { taskVersion, type CooperativeTask, type TaskRecord } from '../src/solver/tasks';

const fence = (kind: string, body: unknown) => '\x60\x60\x60' + kind + '\n' +
  (typeof body === 'string' ? body : JSON.stringify(body)) + '\n\x60\x60\x60';
const source: CooperativeTask = { id: 'research', kind: 'research', objective: 'Find a closed helper',
  dependsOn: [], revision: 0, groupId: 'route', sharing: 'group' };
const consumer: CooperativeTask = { id: 'goal', kind: 'goal', objective: 'Original theorem', theoremName: 'original',
  proofPath: 'Submission.lean', dependsOn: [source.id], revision: 0, groupId: 'route' };
const node = (task: CooperativeTask): TaskRecord => ({ task, status: 'pending', attempts: 0 });
const scope = (): ResearchAdmissionScope => ({ source, assignment: { taskId: source.id, taskDigest: taskVersion(source),
  workerId: 'researcher', seedCommit: 'a'.repeat(40) }, identity: { problemReceiptDigest: 'problem', environmentDigest: 'environment' },
  tasks: [node(source), node(consumer)], deliveries: [] });
const gap = (): MathematicalGap => ({ consumer: { taskId: consumer.id, taskDigest: taskVersion(consumer) },
  previousGap: 'No uniform bound', reduced: 'Established the degenerate case', remaining: 'Need the nondegenerate case',
  evidenceScope: 'Scratch probes only', reconsiderWhen: ['A uniform classification lemma is available'] });
const finding = { summary: 'The degenerate case is established.', conclusion: 'supporting' };
const admit = (value: unknown, current = scope()) => prepareResearchDelivery({ kind: 'event', value }, current);

describe('research response selection', () => {
  it('selects explicit math-result over an explanatory JSON graph and legacy result', () => {
    const notes = '# Method\n' + fence('json', { nodes: ['a', 'b'], links: [['a', 'b']] }) + '\n' +
      fence('math', { summary: 'Old sketch' }) + '\n' + fence('math-result', finding);
    expect(prepareResearchDelivery({ kind: 'notes', text: notes }, scope())).toMatchObject({ status: 'admitted', finding });
  });
  it('preserves Markdown with ordinary JSON instead of treating the graph as a result', () => {
    const text = '# Method\nA concrete argument.\n' + fence('json', { nodes: ['a'], edges: [], metadata: { summary: 'A graph explanation' } });
    expect(prepareResearchDelivery({ kind: 'notes', text }, scope())).toMatchObject({
      status: 'admitted', finding: { summary: text, conclusion: 'inconclusive' },
    });
  });
  it.each(['json', 'math', 'math-result', 'raw', 'markdown'])('keeps the supported %s format', kind => {
    const text = kind === 'raw' ? JSON.stringify(finding) : kind === 'markdown' ? finding.summary : fence(kind, finding);
    expect(prepareResearchDelivery({ kind: 'notes', text }, scope())).toMatchObject({ status: 'admitted', finding: { summary: finding.summary } });
  });
  it('rejects multiple explicit responses with actionable typed feedback', () => {
    expect(prepareResearchDelivery({ kind: 'notes', text: fence('math-result', finding) + '\n' + fence('math-result', finding) }, scope()))
      .toMatchObject({ status: 'rejected', code: 'math_math-result_requires_one_block', issues: [{ path: '$' }] });
  });
  it('retains ambiguity rejection for two legacy response candidates', () => {
    expect(() => parseMathResponse(fence('math', finding) + '\n' + fence('json', finding), 'math-result', {}, 'summary'))
      .toThrow('requires_one_block');
  });
  it('does not turn malformed explicit JSON or inherited plan control into prose', () => {
    for (const text of [fence('math-result', '{"summary":'), fence('math-plan', { tasks: [] }), '\x60\x60\x60math-result\n{'])
      expect(prepareResearchDelivery({ kind: 'notes', text }, scope()).status).toBe('rejected');
  });
  it('does not fall back to explanatory JSON when the explicit response lacks a summary', () => {
    const text = fence('json', finding) + '\n' + fence('math-result', { conclusion: 'inconclusive' });
    expect(prepareResearchDelivery({ kind: 'notes', text }, scope())).toMatchObject({
      status: 'rejected', code: 'math_research_delivery_invalid', issues: [{ path: 'summary' }],
    });
  });
  it('leaves other control parsers strict and keeps explicit bindings visible for host validation', () => {
    expect(parseMathResponse(fence('math', { commit: 'wrong', summary: 'Review' }), 'math-review', { commit: 'assigned' }).commit).toBe('wrong');
    expect(() => parseMathResponse(fence('math', finding) + '\n' + fence('json', finding), 'math-review')).toThrow('requires_one_block');
  });
});

describe('research delivery admission', () => {
  it('normalizes notes and event findings through the same frozen identity', () => {
    const current = scope();
    expect(prepareResearchDelivery({ kind: 'notes', text: JSON.stringify(finding) }, current))
      .toEqual(admit(finding, current));
    expect(admit(finding)).toMatchObject({ status: 'admitted', finding: { taskId: source.id, taskDigest: taskVersion(source) } });
  });
  it.each(['taskId', 'taskDigest'])('rejects an explicit conflicting %s instead of rebinding it', key => {
    expect(admit({ ...finding, [key]: 'wrong' })).toMatchObject({
      status: 'rejected', code: 'math_research_delivery_invalid', issues: [{ path: key }], recovery: 'correct-and-resubmit',
    });
  });
  it.each([null, [], 'text', { summary: '' }, { summary: ' ', conclusion: 'supporting' }, { ...finding, conclusion: 'proved' }])
    ('rejects invalid research finding %#', value => { expect(admit(value).status).toBe('rejected'); });
  it('keeps complete summaries and all supporting fields for artifact validation', () => {
    const value = { ...finding, summary: 'x'.repeat(64001), leanChecks: [{ status: 'inconclusive' }], extra: { argument: 'long proof sketch' } };
    const result = admit(value);
    expect(result).toMatchObject({ status: 'admitted', finding: value });
    if (result.status === 'admitted') expect(deliveryDetails(result.finding).summary).toHaveLength(3000);
  });
  it.each(['premises', 'remainingObligations'])('reports invalid %s field paths', field => {
    expect(admit({ ...finding, [field]: [42] })).toMatchObject({ status: 'rejected', code: 'math_delivery_invalid', issues: [{ path: field }] });
  });
  it('strictly validates gap fields and returns exact issue paths', () => {
    expect(admit({ ...finding, mathematicalGap: { ...gap(), remaining: '' } })).toMatchObject({
      status: 'rejected', code: 'math_delivery_invalid', issues: [{ path: 'mathematicalGap.remaining' }],
    });
    expect(admit({ ...finding, mathematicalGap: { ...gap(), futureFlag: true } }).status).toBe('rejected');
  });
  it('binds valid mathematical gaps without mutating the report', () => {
    const current = scope(), value = { ...finding, mathematicalGap: gap() }, original = structuredClone(value);
    expect(admit(value, current)).toMatchObject({ status: 'admitted', mathematicalGapScope: {
      ...current.identity, source, consumer, dependencies: [],
    } });
    expect(value).toEqual(original);
  });
  it('keeps consumer digest, group visibility and missing dependency rejection', () => {
    expect(admit({ ...finding, mathematicalGap: { ...gap(), consumer: { taskId: consumer.id, taskDigest: 'f'.repeat(64) } } }))
      .toMatchObject({ status: 'rejected', code: 'math_delivery_invalid:gap_consumer', issues: [{ path: 'mathematicalGap.consumer' }] });
    const hidden = { ...scope(), tasks: [node(source), node({ ...consumer, groupId: 'private', sharing: 'group' })] };
    expect(admit({ ...finding, mathematicalGap: { ...gap(), consumer: { taskId: consumer.id, taskDigest: taskVersion(hidden.tasks[1].task) } } }, hidden).status)
      .toBe('rejected');
    const missing = { ...scope(), source: { ...source, dependsOn: ['missing'] } };
    expect(admit({ ...finding, mathematicalGap: gap() }, missing)).toMatchObject({ status: 'rejected', code: 'math_delivery_invalid:gap_dependency' });
  });
  it('preserves field issues on errors consumed by the existing rejection code classifier', () => {
    const outcome = admit({ ...finding, mathematicalGap: { ...gap(), previousDeliveryId: 'missing' } });
    expect(outcome.status).toBe('rejected');
    if (outcome.status !== 'rejected') throw new Error('Expected admission rejection');
    const error = new ResearchAdmissionError(outcome);
    expect(error.message.split(/[\n:]/u, 1)[0]).toBe('math_delivery_invalid');
    expect(error.issues).toEqual(outcome.issues);
    expect(error.recovery).toBe('correct-and-resubmit');
  });
  it('does not infer immutable scope for an old previous delivery', () => {
    const current = scope();
    const deliveries = [{ id: 'old', producer: 'worker', kind: 'research', status: 'advisory', summary: 'Old gap',
      statement: '', premises: [], dependencies: [], remainingObligations: [], evidenceRefs: [], createdAt: 0,
      mathematicalGap: gap() } as DeliveryRecord];
    const withHistory = { ...current, deliveries };
    const report = { ...finding, mathematicalGap: { ...gap(), previousDeliveryId: 'old' } };
    expect(admit(report, withHistory)).toMatchObject({ status: 'rejected', code: 'math_delivery_invalid:gap_previous',
      issues: [{ path: 'mathematicalGap.previousDeliveryId' }] });
    deliveries[0].mathematicalGapScope = bindMathematicalGap(gap(), source, withHistory, current.identity);
    expect(admit(report, withHistory).status).toBe('admitted');
  });
});
