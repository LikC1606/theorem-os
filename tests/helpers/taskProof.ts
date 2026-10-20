import type { TaskProof } from '../../src/solver/cooperativeProof';
import { markTaskAcceptance, taskVersion, type TaskRecord } from '../../src/solver/tasks';

type Options = { uses?: readonly TaskRecord[]; statementOnly?: boolean; accept?: boolean; receiptId?: string; result?: object;
  sourceCommit?: string; environmentDigest?: string; inputs?: { file: string; name?: string; digest: string }[];
  changes?: TaskProof['changes'] };

/**
 * Marks `item` integrated with a passed kernel-verified proof at commit 'canonical' (projection 'projection').
 * `uses` become task inputs and proof references (statement references when `statementOnly`); `accept` records
 * a fresh acceptance. Defaults: receipt `receipt-<id>`, source commit 'canonical', environment 'environment'.
 */
export function integratedProof(item: TaskRecord, options: Options = {}): TaskProof {
  const { uses = [], statementOnly = false, accept = true, receiptId = `receipt-${item.task.id}`, sourceCommit = 'canonical',
    environmentDigest = 'environment', inputs = [], changes = [] } = options;
  const used = () => uses.map(input => ({ file: input.task.proofPath!, name: input.task.theoremName! }));
  const proof = item.integratedCheck = { taskDigest: taskVersion(item.task), passed: true, commit: 'canonical',
    sourceDigest: 'source', seedCommit: 'seed', changes, verification: { status: 'kernel_verified', targetCommit: 'projection',
      results: [{ status: 'kernel_verified', targetCommit: 'projection', receiptId, ...options.result }] },
    references: { sourceCommit, environmentDigest, contextDigest: 'context', inputs,
      root: { file: item.task.proofPath!, name: item.task.theoremName! },
      tasks: uses.map(input => ({ taskId: input.task.id, taskDigest: taskVersion(input.task) })),
      statement: statementOnly ? used() : [], proof: statementOnly ? [] : used() } } as TaskProof;
  item.status = 'integrated';
  if (accept) markTaskAcceptance(proof);
  return proof;
}
