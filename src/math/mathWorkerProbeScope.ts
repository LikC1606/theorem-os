import fs from 'node:fs';
import path from 'node:path';
import type { ProjectGitResearchTeamAssignmentReceipt } from "../project-git/index";
import type { MathRunBinding } from "../common/types/team/mathRuntimeContracts";
import { resolveMathRunProjectPaths } from "./mathRunBinding";

/**
 * A Worker's sources live in its own prepared worktree, not in the Team root.
 * The standalone lean_workspace probe resolved probeSourceFile against the Team
 * root, so every Worker probe failed with ENOENT (run 23). Select the calling
 * slot's accepted assignment and return the worktree plus its solver project.
 */
export function selectMathWorkerProbeScope(input: {
  receipts: readonly ProjectGitResearchTeamAssignmentReceipt[];
  slotId: string;
  assignmentId?: string;
  binding: Pick<MathRunBinding, 'workspace' | 'projectRoot'>;
  teamWorkspace: string;
}): Readonly<{ workspaceRoot: string; projectRelative: string }> | undefined {
  const active = input.receipts.filter(
    (receipt) =>
      receipt.state === 'accepted' &&
      receipt.slotId === input.slotId &&
      !receipt.budgetCancellation &&
      Boolean(receipt.preparedGit?.worktreePath) &&
      (input.assignmentId === undefined || receipt.assignmentId === input.assignmentId)
  );
  // Ambiguity is not resolved by guessing; the caller keeps its existing scope.
  if (active.length !== 1) return undefined;
  const receipt = active[0]!;
  const worktree = receipt.preparedGit!.worktreePath!;
  const paths = resolveMathRunProjectPaths(input.binding as MathRunBinding, input.teamWorkspace, worktree);
  if (receipt.preparedGit?.solverProjectRoot && receipt.preparedGit.solverProjectRoot !== paths.solverProjectRoot)
    throw new Error('Worker proof project does not match its worktree binding.');
  return Object.freeze({
    workspaceRoot: worktree,
    projectRelative: path.relative(worktree, paths.solverProjectRoot).split(path.sep).join('/'),
  });
}

/** True when a requested project root is the calling slot's own accepted worktree, or inside it. */
export function isMathWorkerOwnedRoot(input: {
  receipts: readonly ProjectGitResearchTeamAssignmentReceipt[];
  slotId: string;
  requestedRoot: string;
}): boolean {
  let requested: string;
  try {
    requested = fs.realpathSync(path.resolve(input.requestedRoot));
  } catch {
    return false;
  }
  return input.receipts.some((receipt) => {
    if (receipt.state !== 'accepted' || receipt.slotId !== input.slotId || !receipt.preparedGit?.worktreePath)
      return false;
    let worktree: string;
    try {
      worktree = fs.realpathSync(receipt.preparedGit.worktreePath);
    } catch {
      return false;
    }
    return requested === worktree || requested.startsWith(`${worktree}${path.sep}`);
  });
}
