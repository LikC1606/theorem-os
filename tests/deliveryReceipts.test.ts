import { describe, expect, it } from 'vitest';
import { CooperativeResearch } from '../src/solver/cooperation';
import { deliveryReceiptFeedback, deliveryReceiptSchema, rejectedDeliveryReceipt, type DeliveryReceipt } from '../src/solver/deliveryReceipts';
import { assignmentDeliveryFile, taskVersion, type CooperativeAction, type CooperativeTask } from '../src/solver/tasks';

const task: CooperativeTask = { id: 'research', kind: 'research', objective: 'Resolve the exact gap', dependsOn: [], revision: 0 };
const action: Extract<CooperativeAction, { kind: 'task' }> = { kind: 'task', task, assignment: {
  taskId: task.id, taskDigest: taskVersion(task), workerId: 'writer', seedCommit: 'a'.repeat(40), assignmentId: 'dispatch',
} };
const reject = (submission: unknown, receipts: readonly DeliveryReceipt[] = []) => rejectedDeliveryReceipt({
  assignment: action.assignment, workerId: 'writer', environmentDigest: 'environment',
  submission: typeof submission === 'string' ? submission : JSON.stringify(submission), error: new Error('math_delivery_invalid'),
  now: receipts.length, receipts,
});

describe('delivery receipt correction chains', () => {
  it.each(['event', 'notes'] as const)('retains the explicit prior receipt on a rejected %s correction', kind => {
    const first = reject({ kind: 'research', finding: { summary: 'The initial rejected report' } });
    const finding = { summary: 'The incomplete correction', replacesReceipt: first.id };
    const submission = kind === 'event' ? JSON.stringify({ kind: 'research', finding }) :
      '```math-result\n' + JSON.stringify(finding) + '\n```';
    const second = reject(submission, [first]);
    expect(second.replacesReceipt).toBe(first.id);
    expect(deliveryReceiptSchema.parse(JSON.parse(JSON.stringify(second)))).toEqual(second);
    expect(first.status).toBe('needs-correction');
  });

  it.each(['workerId', 'assignmentKey', 'taskId', 'taskDigest', 'seedCommit', 'environmentDigest'] as const)(
    'does not link a receipt from another %s', field => {
      const first = { ...reject({ summary: 'Original rejection' }), [field]: 'other-scope' };
      const second = reject({ kind: 'research', finding: { summary: 'Correction', replacesReceipt: first.id } }, [first]);
      expect(second.replacesReceipt).toBeUndefined();
    });

  it('ignores unreadable correction references and superseded prior receipts', () => {
    const first = reject({ summary: 'Original rejection' });
    expect(reject('{"replacesReceipt":', [first]).replacesReceipt).toBeUndefined();
    expect(reject({ summary: 'Correction', replacesReceipt: first.id }, [{ ...first, status: 'superseded' }])
      .replacesReceipt).toBeUndefined();
  });

  it('resolves only a verified correction chain and leaves independent or foreign rejections pending', () => {
    const first = reject({ summary: 'Original rejection' });
    const second = reject({ kind: 'research', finding: { summary: 'Rejected correction', replacesReceipt: first.id } }, [first]);
    const independent = reject({ summary: 'Independent rejection' });
    const foreign = { ...reject({ summary: 'Foreign rejection' }), workerId: 'other-writer' };
    // A restored link outside the dispatch must never be followed by the resolver.
    first.replacesReceipt = foreign.id;
    const node = { task, feedback: deliveryReceiptFeedback(second) };
    const receipts = JSON.parse(JSON.stringify([first, second, independent, foreign])) as DeliveryReceipt[];
    const cooperative = Object.create(CooperativeResearch.prototype) as any;
    Object.assign(cooperative, { archive: { tasks: [node], deliveryReceipts: receipts },
      input: { state: { environmentDigest: 'environment' } } });
    cooperative.resolveDeliveryReceipts({ id: 'writer' }, action, second.id);
    expect(receipts.map(receipt => receipt.status)).toEqual(['recorded', 'recorded', 'needs-correction', 'needs-correction']);
    expect(node.feedback).toBe(deliveryReceiptFeedback(independent));
    expect(receipts[0].assignmentKey).toBe(assignmentDeliveryFile(action.assignment));
  });

  it('tells a gap correction to retain required fields and select only a scoped original goal', () => {
    const receipt = reject({ summary: 'Gap rejection' });
    receipt.issues = [{ path: 'mathematicalGap.previousDeliveryId', message: 'Invalid prior gap' }];
    const feedback = deliveryReceiptFeedback(receipt);
    expect(feedback).toContain('keeping required consumer, previousGap, reduced, remaining, evidenceScope and reconsiderWhen');
    expect(feedback).toContain('kind:"goal"');
    expect(feedback).toContain('mathematicalGaps[].deliveryId');
    expect(feedback).toContain('omit only previousDeliveryId');
  });
});
