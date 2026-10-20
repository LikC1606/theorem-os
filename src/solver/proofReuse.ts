import fs from 'node:fs';
import path from 'node:path';
import { canonicalMathJson, mathDigest } from '../math/mathRuntimeIo';
import { resolveMathProofEnvironment } from '../math/mathProofEnvironment';
import { resolveMathematicsRuntimeEnvironment } from '../math/mathRuntimeEnvironment';
import { isMathFoundationalLeanAxiom } from '../math/contracts';
import type { MathematicsVerifierBatchResult } from '../math/verifier';

/** Mutable search paths cannot establish that the same Lean input was checked. */
export function proofReuseEnvironment(projectRoot: string, env: NodeJS.ProcessEnv): {
  env: NodeJS.ProcessEnv; digest?: string; reusable: boolean;
} {
  let runtime = env;
  try {
    runtime = resolveMathematicsRuntimeEnvironment(env);
    const sealed = resolveMathProofEnvironment(projectRoot, runtime);
    const packages = fs.lstatSync(path.join(projectRoot, '.lake', 'packages'), { throwIfNoEntry: false });
    if (runtime.LEAN_PATH?.trim() || runtime.LEAN_SYSROOT?.trim() ||
        !sealed && (packages || runtime.DEEPSCIENTIST_MATH_TRUSTED_CACHE_ROOTS?.trim()))
      return { env: runtime, reusable: false };
    const configuration = ['lean-toolchain', 'lakefile.toml', 'lakefile.lean', 'lake-manifest.json', '.lake/package-overrides.json']
      .map(file => {
        try { return [file, mathDigest(fs.readFileSync(path.join(projectRoot, file)))]; }
        catch (error) {
          if ((error as NodeJS.ErrnoException).code === 'ENOENT') return [file, null];
          throw error;
        }
      });
    return { env: runtime, reusable: true,
      digest: mathDigest(canonicalMathJson({ environment: runtime, packages: sealed?.identity ?? null, configuration })) };
  } catch {
    // Cache preparation cannot replace the verifier's own environment checks.
    return { env: runtime, reusable: false };
  }
}

export const proofVerificationDigest = (verification: MathematicsVerifierBatchResult): string =>
  mathDigest(canonicalMathJson(verification));

/** A batch can aggregate to failed while another target timed out or was blocked. */
export function hasDeterministicLeanFailure(verification: MathematicsVerifierBatchResult): boolean {
  return verification.status === 'failed' && verification.results.some(result => result.status === 'failed') &&
    verification.results.every(result => {
      const output = `${result.error || ''}\n${result.stdoutPreview || ''}\n${result.stderrPreview || ''}`;
      const sourceRejection = result.error === 'Proof source contains sorry or admit.' &&
          ((Number.isSafeInteger(result.sorryCount) && result.sorryCount > 0) ||
            (Number.isSafeInteger(result.admitCount) && result.admitCount > 0)) ||
        Boolean(result.axioms?.length && result.error === `Proof source declares explicit axioms: ${result.axioms.join(', ')}.`) ||
        Boolean(result.error?.startsWith('Theorem depends on non-foundational Lean axioms: ') &&
          result.axioms?.some(axiom => !isMathFoundationalLeanAxiom(axiom)));
      return result.targetCommit === verification.targetCommit && !result.cleanupError &&
        !/\b(?:timed?\s*out|timeout|deadline|abort(?:ed)?|interrupt(?:ed)?)\b/iu.test(output) &&
        (result.status === 'kernel_verified' || result.status === 'failed' &&
          (sourceRejection || (!result.error || /^Lean exited with status 1\.?$/u.test(result.error.trim())) &&
            /^.+\.lean:\d+:\d+:\s*error:/mu.test(output)));
    });
}
