import fs from 'node:fs';
import path from 'node:path';
import { checkManyFormalVerifications, type MathematicsVerifierBatchItem, type MathematicsVerifierBatchRequest,
  type MathematicsVerifierBatchResult, type MathematicsVerifierExecutionOptions } from '../../math/verifier';
import { canonicalMathJson, mathDigest } from '../../math/mathRuntimeIo';
import { commitSolverSources, git, type SolverProblem } from '../problem';
import { bindLeanPackages } from '../../math/leanDiagnostics';
import { hashMathFormalSourceDeclaration } from '../../math/leanSource';

export type ProofCheck = Readonly<{ commit: string; sourceDigest: string; passed: boolean; verification: MathematicsVerifierBatchResult }>;

const solverSourceDigest = (problem: SolverProblem, worktree: string) => mathDigest(canonicalMathJson(problem.ownedFiles
  .map(file => [file, mathDigest(fs.readFileSync(path.join(worktree, problem.projectRelative, file)))])));

/** Reuse binds a recorded check to the current files as well as its committed tree. */
export function solverProofIsCurrent(problem: SolverProblem, worktree: string, check: ProofCheck): boolean {
  return git(worktree, ['rev-parse', 'HEAD']) === check.commit &&
    !git(worktree, ['status', '--porcelain', '--', ...problem.ownedFiles.map(file => path.join(problem.projectRelative, file))]) &&
    solverSourceDigest(problem, worktree) === check.sourceDigest;
}

/** Match every receipt, in target order, to the exact committed proof request. */
export function proofReceiptsMatch(verification: MathematicsVerifierBatchResult, commit: string,
  items: readonly MathematicsVerifierBatchItem[]): boolean {
  return verification.status === 'kernel_verified' && verification.targetCommit === commit && verification.results.length === items.length &&
    verification.results.every((result, index) => result.status === 'kernel_verified' && result.targetCommit === commit &&
      result.proofPath === items[index]!.proofPath && result.theoremName === items[index]!.theoremName &&
      result.statementHash === items[index]!.statementHash && result.leanStatementHash === items[index]!.leanStatementHash &&
      result.claim === 'statement' && result.sourceDeclarationHash === items[index]!.expectedSourceDeclarationHash);
}

export async function checkProofEvidence(request: MathematicsVerifierBatchRequest & { targetCommit: string },
  options: MathematicsVerifierExecutionOptions): Promise<Pick<ProofCheck, 'passed' | 'verification'>> {
  const verification = await checkManyFormalVerifications({ ...request,
    batchTimeoutMs: request.timeoutMs === Infinity ? Infinity : request.batchTimeoutMs },
  { ...options, trustedLakePackagesRoots: (options.env?.DEEPSCIENTIST_MATH_TRUSTED_CACHE_ROOTS || '').split(path.delimiter).filter(Boolean) });
  return { verification, passed: proofReceiptsMatch(verification, request.targetCommit, request.items) };
}

/** Both single-worker and cooperative projections use the same saved declaration and package binding. */
export function checkProjectedDeclaration(problem: SolverProblem, checkout: string, sourceWorktree: string, commit: string,
  target: { proofPath: string; theoremName: string; digest: string; missingError: string },
  options: MathematicsVerifierExecutionOptions & { timeoutMs: number }) {
  return checkProjectedDeclarations(problem, checkout, sourceWorktree, commit, [target], options);
}

export function checkProjectedDeclarations(problem: SolverProblem, checkout: string, sourceWorktree: string, commit: string,
  targets: readonly { proofPath: string; theoremName: string; digest: string; missingError: string }[],
  options: MathematicsVerifierExecutionOptions & { timeoutMs: number }) {
  const projectRoot = path.join(checkout, problem.projectRelative);
  const items = targets.map(target => {
    const declarationHash = hashMathFormalSourceDeclaration(fs.readFileSync(path.join(projectRoot, target.proofPath), 'utf8'), target.theoremName);
    if (!declarationHash) throw new Error(target.missingError);
    return { proofPath: target.proofPath, theoremName: target.theoremName, expectedSourceDeclarationHash: declarationHash,
      statementHash: target.digest, leanStatementHash: target.digest, claim: 'statement' as const };
  });
  const packages = path.join(sourceWorktree, problem.projectRelative, '.lake', 'packages');
  if (fs.existsSync(packages)) bindLeanPackages(projectRoot, packages);
  const { timeoutMs, ...execution } = options;
  return checkProofEvidence({ projectRoot, targetCommit: commit, timeoutMs, items }, execution);
}

/** M2: exact-source Lean evidence. Reused rejections must come from this process and pinned environment. */
export async function checkSolverProof(problem: SolverProblem, worktree: string, env: NodeJS.ProcessEnv,
  signal?: AbortSignal, previous?: ProofCheck, timeoutMs = 180_000): Promise<ProofCheck> {
  signal?.throwIfAborted();
  const commit = commitSolverSources(problem, worktree);
  const projectRoot = path.join(worktree, problem.projectRelative);
  const sourceDigest = solverSourceDigest(problem, worktree);
  if (previous && !previous.passed && previous.commit === commit && previous.sourceDigest === sourceDigest &&
      previous.verification.targetCommit === commit && previous.verification.status === 'failed' &&
      previous.verification.results.every(result => !result.cleanupError) &&
      previous.verification.results.some(result => result.status === 'failed' &&
        /^.+\.lean:\d+:\d+:\s*error:/mu.test(`${result.stdoutPreview || ''}\n${result.stderrPreview || ''}`))) return previous;
  const evidence = await checkProofEvidence({ projectRoot, targetCommit: commit, timeoutMs,
    items: problem.targets.map(target => ({ proofPath: target.proofPath, theoremName: target.theoremName,
      expectedSourceDeclarationHash: target.declarationHash, statementHash: problem.contract.statementHash,
      leanStatementHash: problem.contract.leanStatementHash, claim: 'statement' as const })) },
  { env, signal, prepareLocalDependencies: problem.kind === 'lean-eval' });
  return { commit, sourceDigest, ...evidence };
}
