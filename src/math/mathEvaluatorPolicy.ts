import { canonicalMathJson, mathDigest } from "./mathRuntimeIo";
import { projectMathematicsRuntimeEnvironment } from "./mathRuntimeEnvironment";

export type MathEvaluatorPolicyInput = Readonly<{
  command: string;
  timeoutMs: number;
  environment: Readonly<Record<string, string>>;
  protectedPaths: readonly string[];
  baseCommit: string;
  supervisorDigest: string;
}>;

/** Canonical evaluator identity shared by run, binding and recovery paths. */
export function mathEvaluatorPolicyDigest(input: MathEvaluatorPolicyInput): string {
  return mathDigest(
    canonicalMathJson({
      command: input.command,
      timeoutMs: input.timeoutMs,
      environment: projectMathematicsRuntimeEnvironment(input.environment),
      protectedPaths: input.protectedPaths.toSorted(),
      baseCommit: input.baseCommit,
      supervisorDigest: input.supervisorDigest,
    })
  );
}
