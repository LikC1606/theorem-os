import fs from 'node:fs';
import path from 'node:path';
import { checkManyFormalVerifications, type MathematicsVerifierBatchResult } from '../../math/verifier';
import { canonicalMathJson, mathDigest } from '../../math/mathRuntimeIo';
import { commitSolverSources, type SolverProblem } from '../problem';

export type ProofCheck = Readonly<{ commit: string; sourceDigest: string; passed: boolean; verification: MathematicsVerifierBatchResult }>;

/** M2: exact-source Lean evidence. Reused rejections must come from this process and pinned environment. */
export async function checkSolverProof(problem: SolverProblem, worktree: string, env: NodeJS.ProcessEnv,
  signal?: AbortSignal, previous?: ProofCheck, timeoutMs = 180_000): Promise<ProofCheck> {
  signal?.throwIfAborted();
  const commit = commitSolverSources(problem, worktree);
  const projectRoot = path.join(worktree, problem.projectRelative);
  const sourceDigest = mathDigest(canonicalMathJson(problem.ownedFiles.map(file => [file, mathDigest(fs.readFileSync(path.join(projectRoot, file)))])));
  if (previous && !previous.passed && previous.commit === commit && previous.sourceDigest === sourceDigest &&
      previous.verification.targetCommit === commit && previous.verification.status === 'failed' &&
      previous.verification.results.every(result => !result.cleanupError) &&
      previous.verification.results.some(result => result.status === 'failed' &&
        /^.+\.lean:\d+:\d+:\s*error:/mu.test(`${result.stdoutPreview || ''}\n${result.stderrPreview || ''}`))) return previous;
  const verification = await checkManyFormalVerifications({ projectRoot, targetCommit: commit, timeoutMs,
    batchTimeoutMs: timeoutMs === Infinity ? Infinity : undefined,
    items: problem.targets.map(target => ({ proofPath: target.proofPath, theoremName: target.theoremName,
      expectedSourceDeclarationHash: target.declarationHash, statementHash: problem.contract.statementHash,
      leanStatementHash: problem.contract.leanStatementHash, claim: 'statement' as const })) },
  { env, signal, prepareLocalDependencies: problem.kind === 'lean-eval',
    trustedLakePackagesRoots: (env.DEEPSCIENTIST_MATH_TRUSTED_CACHE_ROOTS || '').split(path.delimiter).filter(Boolean) });
  const passed = verification.status === 'kernel_verified' && verification.targetCommit === commit && verification.results.length === problem.targets.length &&
    verification.results.every((result, index) => result.status === 'kernel_verified' && result.targetCommit === commit &&
      result.proofPath === problem.targets[index]!.proofPath && result.theoremName === problem.targets[index]!.theoremName &&
      result.statementHash === problem.contract.statementHash && result.leanStatementHash === problem.contract.leanStatementHash &&
      result.claim === 'statement' && result.sourceDeclarationHash === problem.targets[index]!.declarationHash);
  return { commit, sourceDigest, passed, verification };
}
