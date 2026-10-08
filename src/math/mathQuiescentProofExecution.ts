import fs from 'node:fs';
import path from 'node:path';
import { listProjectGitResearchTeamAssignments } from "../project-git/ProjectGitService";
import { resolveMathAssignmentContext } from "./mathAssignmentContext";
import { readMathLiteFeedback } from "./mathLiteFeedback";
import { collectMathCheckedProofSupport } from "./mathProofEfficiencyExecution";
import { assertMathCanonicalPath, readMathRunBinding, resolveMathRunProjectPaths } from "./mathRunBinding";
import { readLeanDependencyIdentity } from "./leanLspSession";
import { runMathWorkerProofAction } from "./mathWorkerProofSession";
import { canonicalMathJson, mathDigest } from "./mathRuntimeIo";
import type { MathRunInputs } from "./mathRunInputs";
import { MATHEMATICS_INTERACTION_PROFILE_ENV, MATHEMATICS_LITE_INTERACTION_PROFILE } from "./mathRuntimeEnvironment";

const attempted = new Map<string, string>();

/** A quiescent host may explore, but never takes over a remote Worker's source.
 * The selected branch remains subject to the Worker's ordinary checkout guards
 * and independent delivery verification. Pending transport replay never enters. */
export async function runMathQuiescentProofPreview(input: {
  projectRoot: string;
  teamId: string;
  assignmentId: string;
  runInputs: MathRunInputs;
  env: NodeJS.ProcessEnv;
  isQuiescent: () => boolean;
  hasPendingDispatch: () => boolean;
  deadlineAt: number;
  signal: AbortSignal;
}): Promise<{ status: 'skipped' | 'preview'; reason?: string; text?: string; sourceHash?: string; branchId?: string }> {
  const permitted = () => input.isQuiescent() && !input.hasPendingDispatch();
  if (!permitted()) return { status: 'skipped', reason: 'active_or_pending_transport' };
  if (input.env[MATHEMATICS_INTERACTION_PROFILE_ENV] !== MATHEMATICS_LITE_INTERACTION_PROFILE)
    return { status: 'skipped', reason: 'non_lite_run' };
  input.signal.throwIfAborted();
  if (Date.now() >= input.deadlineAt) return { status: 'skipped', reason: 'deadline' };
  const receipts = () =>
    listProjectGitResearchTeamAssignments({ workspace: input.projectRoot, teamId: input.teamId, strict: true });
  const receipt = receipts().find((item) => item.assignmentId === input.assignmentId);
  if (
    !receipt ||
    receipt.state !== 'accepted' ||
    receipt.delivery ||
    receipt.integration ||
    receipt.supersessionPending ||
    receipt.budgetCancellation
  )
    return { status: 'skipped', reason: 'inactive_assignment' };
  const context = resolveMathAssignmentContext({
    receipt,
    projectRoot: input.projectRoot,
    expectedTeamId: input.teamId,
    expectedSlotId: receipt.slotId,
    expectedAssignmentId: input.assignmentId,
    env: input.env,
  });
  if (context.protocol !== 'v2' || !context.routeRevisionsSupported || context.artifactPaths.length === 0)
    return { status: 'skipped', reason: 'unsupported_assignment' };
  const sources = [...new Set(context.artifactPaths)];
  if (sources.length !== 1) return { status: 'skipped', reason: 'multiple_source_files' };
  const binding = readMathRunBinding(input.runInputs);
  const workspaceRoot = receipt.preparedGit?.worktreePath;
  if (!workspaceRoot) return { status: 'skipped', reason: 'missing_worktree' };
  const paths = resolveMathRunProjectPaths(binding, input.projectRoot, workspaceRoot);
  if (receipt.preparedGit?.solverProjectRoot !== paths.solverProjectRoot)
    throw new Error('Quiescent proof project does not match its assignment binding.');
  const sourceFile = sources[0]!;
  const sourcePath = path.join(paths.solverProjectRoot, sourceFile);
  assertMathCanonicalPath(sourcePath);
  const sourceHash = mathDigest(fs.readFileSync(sourcePath));
  const projectRelative = path.relative(workspaceRoot, paths.solverProjectRoot).split(path.sep).join('/');
  const environment = readLeanDependencyIdentity({ workspaceRoot, projectRelative, sourceFile, env: input.env });
  if (environment.status !== 'known') return { status: 'skipped', reason: 'environment_unavailable' };
  const capability = {
    teamId: input.teamId,
    slotId: receipt.slotId,
    roleKind: 'worker',
    projectRoot: input.projectRoot,
  };
  const feedback = await readMathLiteFeedback({
    resolvedCapability: capability,
    signal: input.signal,
    runInputs: input.runInputs,
  });
  const key = mathDigest(
    canonicalMathJson({
      run: binding.runId,
      assignment: context.assignmentDigest,
      sourceFile,
      sourceHash,
      environment: environment.fingerprint,
      feedback: feedback.findings,
    })
  );
  if (attempted.has(key)) return { status: 'skipped', reason: 'unchanged_evidence' };
  const active = () => {
    if (!permitted()) return false;
    const current = receipts().find((item) => item.assignmentId === input.assignmentId);
    return (
      current &&
      canonicalMathJson(current) === canonicalMathJson(receipt) &&
      mathDigest(fs.readFileSync(sourcePath)) === sourceHash
    );
  };
  if (!active()) return { status: 'skipped', reason: 'changed_before_execution' };
  const remaining = input.deadlineAt - Date.now();
  if (remaining <= 0) return { status: 'skipped', reason: 'deadline' };
  const result = await runMathWorkerProofAction({
    workspaceRoot,
    projectRelative,
    sourceFile,
    statementHash: context.statementHash,
    contractSource: binding.problem?.formalStatement,
    routeFingerprint: context.initialRouteFingerprint,
    initialRouteFingerprint: context.initialRouteFingerprint,
    episodeId: receipt.assignmentId,
    problemId: context.problemId,
    historyProjectRoot: input.projectRoot,
    expectedSourceHash: sourceHash,
    action: 'search',
    searchMode: 'generic',
    applyBest: false,
    timeoutMs: remaining,
    signal: input.signal,
    env: input.env,
    validateActiveRoute: () => Boolean(active()),
    checkedProofBlocks: (view, execution) =>
      collectMathCheckedProofSupport({
        capability,
        environmentId: view.environmentFingerprint ?? '',
        proofSource: { file: sourceFile, sha256: view.sourceHash },
        runInputs: input.runInputs,
        env: input.env,
        signal: execution.signal ?? input.signal,
        deadlineAt: Math.min(input.deadlineAt, Date.now() + (execution.remainingTimeoutMs ?? remaining)),
      }),
  });
  input.signal.throwIfAborted();
  if (!active()) return { status: 'skipped', reason: 'changed_during_execution' };
  // Retry interrupted work; suppress only completed slices with identical evidence.
  if (
    !('executionDisposition' in result) ||
    !['aborted', 'timed_out', 'unavailable'].includes(String(result.executionDisposition))
  ) {
    attempted.set(key, result.status);
    if (attempted.size > 128) attempted.delete(attempted.keys().next().value!);
  }
  const candidate = 'candidate' in result ? result.candidate : undefined;
  const branchId = candidate?.branchId;
  const details = {
    sourceFile,
    sourceHash,
    environment: environment.fingerprint,
    status: result.status,
    applied: false,
    ...(candidate
      ? {
          candidate: {
            branchId,
            sourceHash: candidate.sourceHash,
            status: candidate.status,
            goals: candidate.goals,
            diagnostics: candidate.diagnostics.slice(0, 4000),
          },
        }
      : {}),
    ...('current' in result ? { currentGoals: result.current?.goals } : {}),
  };
  return {
    status: 'preview',
    sourceHash,
    ...(branchId ? { branchId } : {}),
    text: `Host local proof preview (no source was adopted): ${JSON.stringify(details)}\n${branchId ? 'Inspect the retained branch through lean_workspace branches/checkout, with the current source hash. Adopt only through the normal guarded checkout and verify/deliver the original target.' : 'The local slice did not produce a selected branch; continue from the actual remaining diagnostics.'}`,
  };
}
