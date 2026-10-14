import { MATH_PROOF_ENVIRONMENT_ENV } from '../math/mathProofEnvironment';
import { runMathematicsSandboxedCommand } from '../math/verifier';
import { runPersistedLeanEvalOfficialGate } from '../math/leanEvalBootstrap';
import { checkSolverProof, type ProofCheck } from './modules/evidence';
import { git, type SolverProblem } from './problem';

/** S3: final acceptance stays independent of replaceable research modules. */
export async function evaluateSolverProof(problem: SolverProblem, worktree: string, receipt: ProofCheck,
  env: NodeJS.ProcessEnv, signal: AbortSignal, options: { command?: string; timeoutMs: number }): Promise<Record<string, unknown>> {
  const currentHead = git(problem.workspace, ['rev-parse', 'HEAD']);
  if (![problem.baseCommit, receipt.commit].includes(currentHead) || git(problem.workspace, ['status', '--porcelain', '--untracked-files=no']))
    throw new Error('math_main_workspace_changed');
  git(problem.workspace, ['merge', '--ff-only', receipt.commit]);
  const finalCheck = await checkSolverProof(problem, problem.workspace, env, signal, undefined,
    options.timeoutMs === Infinity ? Infinity : undefined);
  if (!finalCheck.passed || finalCheck.commit !== receipt.commit || finalCheck.sourceDigest !== receipt.sourceDigest)
    throw new Error('math_integrated_proof_mismatch');
  if (options.command) {
    const result = await runMathematicsSandboxedCommand({ checkoutRoot: worktree, projectRelative: problem.projectRelative,
      command: '/bin/sh', args: ['-c', options.command], timeoutMs: options.timeoutMs, env, signal });
    return { status: result.timedOut || result.aborted || !result.started ? 'error' : result.exitCode === 0 ? 'passed' : 'failed',
      method: 'external-command', official: false, result };
  }
  if (problem.kind === 'lean-eval') {
    if (!problem.sourceRepository) throw new Error('math_official_source_missing');
    const { comparison } = await runPersistedLeanEvalOfficialGate({ activeProblemPath: problem.activeProblemPath,
      repositoryRoot: problem.sourceRepository, timeoutMs: options.timeoutMs,
      env: { ...env, [MATH_PROOF_ENVIRONMENT_ENV]: undefined }, signal });
    return { status: comparison.timedOut || comparison.aborted || comparison.cleanupError ? 'error' :
      comparison.status === 'official_verified' ? 'passed' : comparison.status === 'failed' ? 'failed' : 'error',
      method: 'official-comparator', official: true, comparison };
  }
  return { status: 'passed', method: 'host-lean-kernel-all-targets', official: false, verification: finalCheck };
}
