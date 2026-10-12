import { git, type SolverProblem } from '../problem';
import type { ProofCheck } from './evidence';

export type ProofArtifact = Readonly<{ commit: string; sourceDigest: string }>;
export type IntegrationResult = Readonly<{
  candidate: ProofArtifact | null;
  dependenciesClosed: boolean;
  pendingVerification: SolverProblem['targets'];
}>;

/** The host adopts a complete checked proof; integration still requires independent host rechecking. */
export function integrateResearch(task: SolverProblem, artifacts: readonly ProofArtifact[], receipts: readonly ProofCheck[]): IntegrationResult {
  const candidate = artifacts.find(artifact => receipts.some(receipt => receipt.passed &&
    receipt.commit === artifact.commit && receipt.sourceDigest === artifact.sourceDigest));
  if (!candidate) return { candidate: null, dependenciesClosed: false, pendingVerification: task.targets };
  const currentHead = git(task.workspace, ['rev-parse', 'HEAD']);
  if (![task.baseCommit, candidate.commit].includes(currentHead) || git(task.workspace, ['status', '--porcelain', '--untracked-files=no']))
    throw new Error('math_main_workspace_changed');
  git(task.workspace, ['merge', '--ff-only', candidate.commit]);
  return { candidate, dependenciesClosed: true, pendingVerification: task.targets };
}
