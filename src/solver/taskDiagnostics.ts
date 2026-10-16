import { limitMathOutput } from '../math/mathProcess';
import { taskVersion, type TaskRecord } from './tasks';
import type { TaskProof } from './cooperativeProof';

/** A diagnostic describes one attempted version, never the task for all future versions. */
export type TaskDiagnostic = {
  message: string; taskDigest: string; environmentDigest?: string; commit?: string;
  sourceDigest?: string; contextDigest?: string; verificationStatus?: string; at: number; legacy?: boolean;
};

function archiveDiagnostic(node: TaskRecord) {
  const previous = node.diagnostic ?? (node.feedback ? {
    message: node.feedback, taskDigest: taskVersion(node.task), at: Date.now(), legacy: true,
  } : undefined);
  if (previous) node.diagnosticHistory = [...(node.diagnosticHistory ?? []), previous].slice(-8);
}

export function clearTaskDiagnostic(node: TaskRecord) {
  archiveDiagnostic(node);
  node.feedback = undefined; node.diagnostic = undefined;
}

export function setTaskDiagnostic(node: TaskRecord, message: string, environmentDigest: string,
  proof?: TaskProof, commit?: string) {
  archiveDiagnostic(node);
  const diagnostic: TaskDiagnostic = {
    message: limitMathOutput(message, 16_000, 'head'), taskDigest: taskVersion(node.task), environmentDigest,
    commit: commit ?? proof?.commit ?? node.assignment?.seedCommit, sourceDigest: proof?.sourceDigest,
    contextDigest: proof?.references?.contextDigest, verificationStatus: proof?.verification.status, at: Date.now(),
  };
  node.diagnostic = diagnostic; node.feedback = diagnostic.message;
}

/** Legacy checkpoints may contain a failure next to a later successful receipt. */
export function currentTaskFeedback(node: TaskRecord, environmentDigest?: string): string | undefined {
  const proof = node.integratedCheck ?? node.proof;
  if (['conditional', 'delivered', 'integrated'].includes(node.status) && proof?.passed &&
      proof.taskDigest === taskVersion(node.task)) return undefined;
  if (node.diagnostic && (node.diagnostic.taskDigest !== taskVersion(node.task) ||
      (environmentDigest && node.diagnostic.environmentDigest !== environmentDigest))) return undefined;
  return node.diagnostic?.message ?? node.feedback;
}
