import { z } from 'zod';
import { canonicalMathJson, mathDigest } from '../math/mathRuntimeIo';
import { assignmentDeliveryFile, type TaskAssignment } from './tasks';

export const deliveryReceiptSchema = z.object({
  id: z.string(), submissionDigest: z.string(), workerId: z.string(),
  assignmentKey: z.string(), taskId: z.string(), taskDigest: z.string(),
  seedCommit: z.string(), environmentDigest: z.string(), createdAt: z.number().int().nonnegative(),
  status: z.enum(['needs-correction', 'recorded', 'superseded']),
  code: z.string(), issues: z.array(z.object({ path: z.string(), message: z.string() })),
});
export type DeliveryReceipt = z.infer<typeof deliveryReceiptSchema>;

/** Protocol feedback is durable evidence about intake, never Lean acceptance. */
export function rejectedDeliveryReceipt(input: { assignment: TaskAssignment; workerId: string;
  environmentDigest: string; submission: string; error: Error; now: number }): DeliveryReceipt {
  const assignmentKey = assignmentDeliveryFile(input.assignment);
  const submissionDigest = mathDigest(input.submission);
  const details = input.error as Error & { issues?: readonly { path: string; message: string }[] };
  const code = input.error.message.split(/[\n:]/u, 1)[0];
  const issues = details.issues?.map(issue => ({ path: issue.path, message: issue.message })) ??
    [{ path: code === 'math_delivery_invalid_json' ? '$' : 'submission', message: input.error.message }];
  return { id: mathDigest(canonicalMathJson({ assignmentKey, submissionDigest, code, issues })),
    submissionDigest, workerId: input.workerId, assignmentKey,
    taskId: input.assignment.taskId, taskDigest: input.assignment.taskDigest,
    seedCommit: input.assignment.seedCommit, environmentDigest: input.environmentDigest,
    createdAt: input.now, status: 'needs-correction', code, issues };
}

export function deliveryReceiptFeedback(receipt: DeliveryReceipt): string {
  return 'Host delivery receipt (intake feedback, not proof acceptance):\n' + JSON.stringify(receipt) +
    '\nCorrect the indicated fields and append a new complete event to the same assignment delivery log; ' +
    'include replacesReceipt:' + JSON.stringify(receipt.id) + ' in the corrected finding to resolve this receipt. ' +
    'Do not repeat the rejected event or truncate the log. Read COOPERATION.json for current receipts.';
}
