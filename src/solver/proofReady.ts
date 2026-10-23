import { z } from 'zod';
import { canonicalMathJson, mathDigest } from '../math/mathRuntimeIo';
import { assignmentDeliveryFile, type TaskAssignment } from './tasks';

const commit = z.string().regex(/^[a-f0-9]{40,64}$/u);
const reference = z.object({ taskId: z.string(), taskDigest: z.string() }).strict();
/** Writer readiness and frozen checks are distinct; neither is original-goal acceptance. */
export const proofReadyRecordSchema = z.object({
  id: z.string(), submissionId: z.string(), assignmentKey: z.string(), workerId: z.string(),
  taskId: z.string(), taskDigest: z.string(), seedCommit: commit, problemReceiptDigest: z.string(),
  environmentDigest: z.string(), requestedAt: z.number().int().nonnegative(),
  frozenAt: z.number().int().nonnegative().optional(),
  status: z.enum(['awaiting-freeze', 'frozen', 'checked', 'failed', 'superseded']),
  snapshotCommit: commit.optional(), sourceDigest: z.string().optional(),
  evidence: z.enum(['conditional', 'unconditional']).optional(),
  conditions: z.array(reference).optional(), receiptIds: z.array(z.string()).optional(), reason: z.string().optional(),
}).strict().superRefine((value, context) => {
  if (['frozen', 'checked'].includes(value.status) && (!value.snapshotCommit || !value.sourceDigest))
    context.addIssue({ code: z.ZodIssueCode.custom, path: ['snapshotCommit'], message: 'A fixed snapshot is required.' });
  if (value.status === 'checked' && (!value.evidence || !value.receiptIds?.length))
    context.addIssue({ code: z.ZodIssueCode.custom, path: ['receiptIds'], message: 'Checked readiness requires Lean receipts.' });
  if (value.evidence === 'conditional' && !value.conditions?.length ||
      value.evidence === 'unconditional' && value.conditions?.length)
    context.addIssue({ code: z.ZodIssueCode.custom, path: ['conditions'], message: 'Evidence must match its frozen conditions.' });
});
export type ProofReadyRecord = z.infer<typeof proofReadyRecordSchema>;

export function proofReadyRecord(input: { assignment: TaskAssignment; workerId: string; submissionId: string;
  problemReceiptDigest: string; environmentDigest: string; now: number }): ProofReadyRecord {
  const assignmentKey = assignmentDeliveryFile(input.assignment);
  return { id: mathDigest(canonicalMathJson({ assignmentKey, submissionId: input.submissionId,
    problemReceiptDigest: input.problemReceiptDigest, environmentDigest: input.environmentDigest })),
    submissionId: input.submissionId, assignmentKey, workerId: input.workerId,
    taskId: input.assignment.taskId, taskDigest: input.assignment.taskDigest, seedCommit: input.assignment.seedCommit,
    problemReceiptDigest: input.problemReceiptDigest, environmentDigest: input.environmentDigest,
    requestedAt: input.now, status: 'awaiting-freeze' };
}
