import type { ProofReferences } from './proofReferences';
import { taskVersion, type TaskRecord } from './tasks';

const sameName = (left: string, right: string): boolean => left === right ||
  (!left.includes('.') && right.endsWith('.' + left)) ||
  (!right.includes('.') && left.endsWith('.' + right));
const sameDeclaration = (left: { file: string; name: string }, right: { file: string; name: string }) =>
  left.file === right.file && sameName(left.name, right.name);

/** Task edges describe formal task interfaces; supporting declarations stay bound by source fingerprints. */
export function attributeTaskReferences(references: ProofReferences,
  tasks: readonly TaskRecord[]): NonNullable<ProofReferences['tasks']> {
  const uses = [...references.statement, ...references.proof].filter(reference => !sameDeclaration(reference, references.root));
  return tasks.filter(node => {
    const task = node.task;
    if (!['lemma', 'goal'].includes(task.kind) || !task.proofPath || !task.theoremName) return false;
    const target = { file: task.proofPath, name: task.theoremName };
    return !sameDeclaration(target, references.root) && uses.some(reference => sameDeclaration(reference, target));
  }).map(node => ({ taskId: node.task.id, taskDigest: taskVersion(node.task) }));
}
