import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import crypto from 'node:crypto';
import { execFileSync, spawnSync } from 'node:child_process';
import type { RuntimeMathAssignment } from "../common/types/team/mathRuntimeContracts";
import type { ProjectGitResearchTeamAssignmentReceipt } from "../project-git/ProjectGitService";
import type { ProjectGitMathSourceVerificationReceipt } from "../project-git/ProjectGitService";
import { createProjectGitCheckpoint } from "../project-git/ProjectGitService";
import { isMathFoundationalLeanAxiom } from "../common/types/team/mathematicsTeam";
import { assertMathCanonicalPath, isMathPathWithin } from "./mathRunBinding";
import {
  prepareMathProofImpactFinalCheck,
  recordMathProofImpactFinalCheck,
  readMathProofImpactEvents,
} from "./mathProofImpact";
import {
  certifyFormalVerifications,
  type MathematicsVerifierBatchRequest,
  type MathematicsVerifierBatchResult,
  type MathematicsVerifierExecutionOptions,
} from "./verifier";

export type MathV2PromotionPreflight = Readonly<{
  assignmentId: string;
  branch: string;
  worktreePath: string;
  baseCommit: string;
}>;

export type MathV2DraftPromotionFile = Readonly<{ pathRelative: string; contentSha256: string }>;

export type MathV2SourceVerificationItem = Readonly<{
  id: string;
  proofPath: string;
  contentSha256: string;
  theoremName: string;
  statementHash: string;
  leanStatementHash?: string;
  expectedSourceDeclarationHash: string;
  claim?: 'statement' | 'negation';
}>;

export type MathV2SourceVerificationRequest = Readonly<{
  worktreePath: string;
  projectRelative?: string;
  targetCommit: string;
  items: readonly MathV2SourceVerificationItem[];
  signal?: AbortSignal;
}>;

export type MathV2VerificationDisposition = 'verified' | 'candidate_rejected' | 'pending' | 'integrity_error';

export type MathV2SourceVerificationEvidence = Readonly<{
  schema: 'deepscientist.math.source-verification-evidence.v1';
  disposition: Exclude<MathV2VerificationDisposition, 'verified'>;
  targetCommit: string;
  checkedAt: number;
  itemIds: readonly string[];
  sourceHashes: readonly string[];
  diagnostics?: string;
}>;

export type MathV2SourceVerificationResult = Readonly<{
  verified: boolean;
  disposition: MathV2VerificationDisposition;
  diagnostics?: string;
  receipts?: ProjectGitMathSourceVerificationReceipt[];
  evidence?: MathV2SourceVerificationEvidence;
}>;

type MathV2Certifier = (
  request: MathematicsVerifierBatchRequest,
  options?: MathematicsVerifierExecutionOptions
) => Promise<MathematicsVerifierBatchResult>;

export type MathV2PromotionCommitRequest = Readonly<{
  worktreePath: string;
  includePaths: readonly string[];
  expectedFiles: readonly MathV2DraftPromotionFile[];
  assignmentId: string;
  branch: string;
  baseCommit: string;
}>;

const gitText = (root: string, args: readonly string[]): string =>
  execFileSync('git', ['-C', root, ...args], { encoding: 'utf8', maxBuffer: 8 * 1024 * 1024 }).trim();

export type MathPorcelainStatusEntry = Readonly<{
  indexStatus: string;
  worktreeStatus: string;
  pathRelative: string;
  originalPathRelative?: string;
}>;

/** Parse Git's NUL-delimited porcelain v1 output without trimming path bytes. */
export function parseMathPorcelainV1Z(value: Uint8Array): readonly MathPorcelainStatusEntry[] {
  const tokens: string[] = [];
  let start = 0;
  for (let index = 0; index <= value.length; index += 1) {
    if (index !== value.length && value[index] !== 0) continue;
    const bytes = value.slice(start, index);
    try {
      tokens.push(new TextDecoder('utf-8', { fatal: true }).decode(bytes));
    } catch {
      throw new Error('math_v2_verification_git_path_encoding');
    }
    start = index + 1;
  }
  const entries: MathPorcelainStatusEntry[] = [];
  for (let index = 0; index < tokens.length; index += 1) {
    const record = tokens[index]!;
    if (!record) continue;
    if (record.length < 3 || record[2] !== ' ') throw new Error('math_v2_verification_git_status_record');
    const indexStatus = record[0]!;
    const worktreeStatus = record[1]!;
    const pathRelative = record.slice(3);
    if (!pathRelative) throw new Error('math_v2_verification_git_status_path');
    if (indexStatus === 'R' || indexStatus === 'C' || worktreeStatus === 'R' || worktreeStatus === 'C') {
      const originalPathRelative = tokens[index + 1];
      if (!originalPathRelative) throw new Error('math_v2_verification_git_rename_record');
      index += 1;
      entries.push(Object.freeze({ indexStatus, worktreeStatus, pathRelative, originalPathRelative }));
    } else {
      entries.push(Object.freeze({ indexStatus, worktreeStatus, pathRelative }));
    }
  }
  return Object.freeze(entries);
}

/**
 * The worker proof session keeps its host-owned attempt and identity records in
 * the worktree. They are never part of a proof commit, but as untracked files
 * they made the already-committed replay path refuse, so every integrate of a
 * completed proof failed with "Checkpoint paths do not contain any Git changes"
 * (run 23). Only untracked records under this exact directory are tolerated.
 */
const HOST_WORKER_PROOF_RECORDS = '.deepscientist/math/worker-proof/';
export const isHostWorkerProofRecord = (entry: MathPorcelainStatusEntry): boolean =>
  entry.indexStatus === '?' &&
  entry.worktreeStatus === '?' &&
  !entry.originalPathRelative &&
  entry.pathRelative.startsWith(HOST_WORKER_PROOF_RECORDS) &&
  !entry.pathRelative.split('/').includes('..');

/**
 * lean_workspace creates this untracked science manifest in the Team root. The
 * post-merge canonical re-verification then refused the root as dirty, so a
 * verified proof would never reach solver_ready (found in the run 23d rehearsal).
 */
const HOST_SCIENCE_RUNTIME_MANIFEST = new Set(['.deepscientist/project.json', '.deepscientist/.gitignore']);
/**
 * Certification projects its Lean trace into the Team root. The verifier's own
 * status check already ignores these exact paths; post-merge re-verification
 * must agree, or a merged proof is refused as a dirty workspace (run 23/15).
 */
const HOST_TRACE_PROJECTION = 'mathematics/verification-trace.json';
const HOST_REPORT_TRACE = /^mathematics\/report-traces\/verification-[a-f0-9]{20}\.json$/u;
/** Untracked host-owned state that never belongs to a proof commit. */
export const isHostRuntimeRecord = (entry: MathPorcelainStatusEntry): boolean =>
  isHostWorkerProofRecord(entry) ||
  (entry.indexStatus === '?' &&
    entry.worktreeStatus === '?' &&
    !entry.originalPathRelative &&
    (HOST_SCIENCE_RUNTIME_MANIFEST.has(entry.pathRelative) ||
      entry.pathRelative === HOST_TRACE_PROJECTION ||
      HOST_REPORT_TRACE.test(entry.pathRelative)));

const gitPorcelainStatus = (root: string): readonly MathPorcelainStatusEntry[] =>
  parseMathPorcelainV1Z(
    execFileSync('git', ['-C', root, 'status', '--porcelain=v1', '-z', '--untracked-files=all'], {
      encoding: 'buffer',
      maxBuffer: 8 * 1024 * 1024,
    })
  );

const verificationEvidence = (
  disposition: Exclude<MathV2VerificationDisposition, 'verified'>,
  input: MathV2SourceVerificationRequest,
  targetCommit: string,
  diagnostics?: string,
  items: readonly MathV2SourceVerificationItem[] = input.items
): MathV2SourceVerificationEvidence =>
  Object.freeze({
    schema: 'deepscientist.math.source-verification-evidence.v1',
    disposition,
    targetCommit,
    checkedAt: Date.now(),
    itemIds: Object.freeze(items.map((item) => item.id)),
    sourceHashes: Object.freeze(items.map((item) => item.contentSha256)),
    ...(diagnostics ? { diagnostics } : {}),
  });

// Keep both ends of bounded verifier output: startup failures are often on stderr,
// while Lean reports elaboration errors on stdout. Diagnostics never confer identity.
const boundedDiagnostic = (value: string, limit: number): string => {
  if (value.length <= limit) return value;
  const marker = '\n...[truncated]...\n';
  const half = Math.floor((limit - marker.length) / 2);
  return `${value.slice(0, half)}${marker}${value.slice(-(limit - marker.length - half))}`;
};

const verificationDiagnostics = (
  summary: string,
  results: readonly MathematicsVerifierBatchResult['results'][number][]
): string => {
  const parts = [boundedDiagnostic(summary, 1024)];
  for (const result of results) {
    for (const [label, value] of [
      ['error', result.error],
      ['stderr', result.stderrPreview],
      ['stdout', result.stdoutPreview],
    ] as const) {
      if (value?.trim() && value !== summary) parts.push(`${label}: ${boundedDiagnostic(value.trim(), 2048)}`);
    }
    if (parts.join('\n').length >= 8192) break;
  }
  return boundedDiagnostic(parts.join('\n'), 8192);
};

const trustedCacheRoots = (projectRoot: string): string[] => {
  const packages = path.join(projectRoot, '.lake', 'packages');
  return fs.existsSync(packages) && fs.statSync(packages).isDirectory() ? [packages] : [];
};

/** Verify an exact source commit even after the canonical checkout has advanced. */
export async function verifyMathV2SourceCommit(
  input: MathV2SourceVerificationRequest,
  certify: MathV2Certifier = certifyFormalVerifications
): Promise<MathV2SourceVerificationResult> {
  const repositoryRoot = fs.realpathSync(gitText(input.worktreePath, ['rev-parse', '--show-toplevel']));
  const projectRoot = path.resolve(input.worktreePath, input.projectRelative ?? '');
  assertMathCanonicalPath(projectRoot);
  if (!isMathPathWithin(input.worktreePath, projectRoot) || !isMathPathWithin(repositoryRoot, projectRoot)) {
    throw new Error('math_v2_verification_project_root');
  }
  const relativeProjectRoot = path.relative(repositoryRoot, projectRoot);
  const projectItems = input.items.map((item) => {
    const sourcePath = path.resolve(input.worktreePath, item.proofPath);
    assertMathCanonicalPath(sourcePath);
    if (!isMathPathWithin(projectRoot, sourcePath)) throw new Error('math_v2_verification_project_root');
    return { ...item, proofPath: path.relative(projectRoot, sourcePath).split(path.sep).join('/') };
  });
  const targetCommit = gitText(repositoryRoot, [
    'rev-parse',
    '--verify',
    `${input.targetCommit}^{commit}`,
  ]).toLowerCase();
  if (targetCommit !== input.targetCommit.toLowerCase()) throw new Error('math_v2_verification_target_commit');
  const currentHead = gitText(input.worktreePath, ['rev-parse', 'HEAD']).toLowerCase();
  const dirtyEntries = gitPorcelainStatus(input.worktreePath);
  if (dirtyEntries.length) {
    const allowedNotes = new Set(
      input.items.map((item) => path.posix.join(path.posix.dirname(item.proofPath), 'RESEARCH.md'))
    );
    const dirtyPaths = dirtyEntries.flatMap((entry) =>
      [entry.pathRelative, entry.originalPathRelative]
        .filter((value): value is string => Boolean(value))
        .map((value) => value.replaceAll(path.sep, '/'))
    );
    const unexpected = dirtyEntries.filter((entry) => !isHostRuntimeRecord(entry));
    if (
      unexpected
        .flatMap((entry) => [entry.pathRelative, entry.originalPathRelative])
        .filter((value): value is string => Boolean(value))
        .some((entry) => !allowedNotes.has(entry.replaceAll(path.sep, '/')))
    ) {
      throw new Error(`math_v2_verification_dirty_workspace: ${dirtyPaths.join(', ')}`);
    }
  }
  const temporaryRoot =
    currentHead === targetCommit && dirtyEntries.length === 0
      ? undefined
      : fs.mkdtempSync(path.join(os.tmpdir(), 'math-v2-verify-'));
  const checkoutRoot = temporaryRoot ? path.join(temporaryRoot, 'checkout') : repositoryRoot;
  let added = false;
  let cleanupError: unknown;
  let operationError: { value: unknown } | undefined;
  let operationResult: MathV2SourceVerificationResult | undefined;
  try {
    operationResult = await (async (): Promise<MathV2SourceVerificationResult> => {
      if (temporaryRoot) {
        execFileSync('git', ['-C', repositoryRoot, 'worktree', 'add', '--detach', checkoutRoot, targetCommit], {
          stdio: 'pipe',
          maxBuffer: 8 * 1024 * 1024,
        });
        added = true;
      }
      const verificationProjectRoot = temporaryRoot ? path.join(checkoutRoot, relativeProjectRoot) : projectRoot;
      const impactChecks = projectItems.map((item) => {
        try {
          const context = prepareMathProofImpactFinalCheck({
            source: fs.readFileSync(path.join(verificationProjectRoot, item.proofPath), 'utf8'),
            theoremName: item.theoremName,
            statementHash: item.statementHash,
            expectedSourceDeclarationHash: item.expectedSourceDeclarationHash,
          });
          if (
            context &&
            readMathProofImpactEvents(context.scope.runRoot, context.scope.runId).events.some(
              (event) =>
                event.kind === 'final_checked' &&
                event.targetCommit === targetCommit &&
                event.targetId === context.targetId &&
                event.sourceHash === item.contentSha256
            )
          )
            return undefined;
          return context;
        } catch {
          return undefined;
        }
      });
      const impactCandidates = [...new Set(impactChecks.flatMap((context) => context?.candidates ?? []))].toSorted();
      const attributeDependencies = impactCandidates.length > 0 && impactCandidates.length <= 32;
      let batch: MathematicsVerifierBatchResult;
      try {
        batch = await certify(
          {
            projectRoot: verificationProjectRoot,
            targetCommit,
            items: projectItems.map(({ contentSha256: _contentSha256, ...item }) => item),
          },
          {
            signal: input.signal,
            trustedLakePackagesRoots: trustedCacheRoots(projectRoot),
          }
        );
      } catch (error) {
        const diagnostics = input.signal?.aborted
          ? 'Formal verification was cancelled before a complete result was available.'
          : `Formal verification did not complete: ${error instanceof Error ? error.message : String(error)}`;
        return {
          verified: false,
          disposition: 'pending',
          diagnostics,
          evidence: verificationEvidence('pending', input, targetCommit, diagnostics),
        };
      }
      const verifiedHead = gitText(verificationProjectRoot, ['rev-parse', 'HEAD']).toLowerCase();
      if (verifiedHead !== targetCommit) {
        const diagnostics = 'The verification workspace HEAD changed.';
        return {
          verified: false,
          disposition: 'integrity_error',
          diagnostics,
          evidence: verificationEvidence('integrity_error', input, targetCommit, diagnostics),
        };
      }
      if (batch.status === 'blocked' || batch.status === 'unavailable') {
        const diagnostics = verificationDiagnostics(`Formal verification ${batch.status}.`, batch.results);
        return {
          verified: false,
          disposition: 'pending',
          diagnostics,
          evidence: verificationEvidence('pending', input, targetCommit, diagnostics),
        };
      }
      if (batch.targetCommit.toLowerCase() !== targetCommit) {
        const diagnostics = 'Formal verification returned results for a different commit.';
        return {
          verified: false,
          disposition: 'integrity_error',
          diagnostics,
          evidence: verificationEvidence('integrity_error', input, targetCommit, diagnostics),
        };
      }
      const byId = new Map<string, (typeof batch.results)[number]>();
      for (const result of batch.results) {
        if (byId.has(result.checkId)) {
          const diagnostics = `Formal verification returned duplicate results for ${result.checkId}.`;
          return {
            verified: false,
            disposition: 'integrity_error',
            diagnostics,
            evidence: verificationEvidence('integrity_error', input, targetCommit, diagnostics),
          };
        }
        byId.set(result.checkId, result);
      }
      if (
        byId.size !== input.items.length ||
        [...byId.keys()].some((id) => !input.items.some((item) => item.id === id))
      ) {
        const diagnostics = 'Formal verification returned an unexpected result identity.';
        return {
          verified: false,
          disposition: 'integrity_error',
          diagnostics,
          evidence: verificationEvidence('integrity_error', input, targetCommit, diagnostics),
        };
      }
      const receipts: ProjectGitMathSourceVerificationReceipt[] = [];
      for (const item of input.items) {
        const verified = byId.get(item.id);
        if (!verified) {
          const diagnostics = `Formal verification returned no result for ${item.theoremName}.`;
          return {
            verified: false,
            disposition: 'pending',
            diagnostics,
            evidence: verificationEvidence('pending', input, targetCommit, diagnostics, [item]),
          };
        }
        const identityMatches =
          verified.targetCommit === targetCommit &&
          verified.proofPath === projectItems.find((candidate) => candidate.id === item.id)?.proofPath &&
          verified.proofHash === item.contentSha256 &&
          verified.theoremName === item.theoremName &&
          verified.statementHash === item.statementHash &&
          verified.leanStatementHash === item.leanStatementHash &&
          verified.claim === (item.claim ?? 'statement') &&
          verified.statementBinding === 'caller-bound-to-committed-declaration';
        if (verified.cleanupError) {
          const diagnostics = `Formal verification cleanup did not complete: ${verified.cleanupError}`;
          return {
            verified: false,
            disposition: 'pending',
            diagnostics,
            evidence: verificationEvidence('pending', input, targetCommit, diagnostics, [item]),
          };
        }
        if (
          verified.status === 'failed' &&
          verified.verifier === 'lean-kernel' &&
          identityMatches &&
          verified.sourceDeclarationHash === item.expectedSourceDeclarationHash &&
          !verified.cleanupError
        ) {
          const diagnostics = verificationDiagnostics(verified.error || `Lean rejected ${item.theoremName}.`, [
            verified,
          ]);
          return {
            verified: false,
            disposition: 'candidate_rejected',
            diagnostics,
            evidence: verificationEvidence('candidate_rejected', input, targetCommit, diagnostics, [item]),
          };
        }
        if (verified.status === 'blocked' || verified.status === 'unavailable') {
          const diagnostics = verificationDiagnostics(verified.error || `Formal verification ${verified.status}.`, [
            verified,
          ]);
          return {
            verified: false,
            disposition: 'pending',
            diagnostics,
            evidence: verificationEvidence('pending', input, targetCommit, diagnostics, [item]),
          };
        }
        if (
          verified.status !== 'kernel_verified' ||
          verified.verifier !== 'lean-kernel' ||
          !identityMatches ||
          verified.sourceDeclarationHash !== item.expectedSourceDeclarationHash ||
          verified.goalsRemaining !== 0 ||
          verified.sorryCount !== 0 ||
          verified.admitCount !== 0 ||
          verified.axioms.some((axiom) => !isMathFoundationalLeanAxiom(axiom))
        ) {
          const diagnostics =
            verified.error ||
            `Formal verification did not certify ${item.theoremName} at the requested source identity.`;
          return {
            verified: false,
            disposition: 'integrity_error',
            diagnostics,
            evidence: verificationEvidence('integrity_error', input, targetCommit, diagnostics, [item]),
          };
        }
        receipts.push({
          schema: 'deepscientist.math.source-verification.v1',
          receiptId: verified.receiptId,
          targetCommit: verified.targetCommit,
          sourcePath: item.proofPath,
          contentSha256: item.contentSha256,
          proofHash: verified.proofHash,
          theoremName: verified.theoremName,
          statementHash: verified.statementHash,
          ...(verified.leanStatementHash ? { leanStatementHash: verified.leanStatementHash } : {}),
          sourceDeclarationHash: verified.sourceDeclarationHash,
          verifier: 'lean-kernel',
          goalsRemaining: 0,
          sorryCount: 0,
          admitCount: 0,
          axioms: verified.axioms,
          checkedAt: verified.checkedAt,
        });
      }
      // Attribution needs a separately built Lake module. Its availability must
      // never change the already established original-proof acceptance result.
      if (attributeDependencies && !input.signal?.aborted) {
        try {
          const attributed = await certify(
            {
              projectRoot: verificationProjectRoot,
              targetCommit,
              timeoutMs: 30_000,
              batchTimeoutMs: 30_000,
              items: projectItems
                .filter((_, index) => impactChecks[index])
                .map(({ contentSha256: _contentSha256, ...item }) => item),
            },
            {
              signal: input.signal,
              trustedLakePackagesRoots: trustedCacheRoots(projectRoot),
              dependencyCandidates: impactCandidates,
              prepareLocalDependencies: true,
            }
          );
          for (const result of attributed.results) {
            const index = projectItems.findIndex((item) => item.id === result.checkId);
            const item = projectItems[index];
            const impact = impactChecks[index];
            if (
              !impact ||
              !item ||
              result.targetCommit !== targetCommit ||
              result.theoremName !== item.theoremName ||
              result.proofPath !== item.proofPath ||
              result.sourceDeclarationHash !== item.expectedSourceDeclarationHash ||
              result.axioms.some((axiom) => !isMathFoundationalLeanAxiom(axiom))
            )
              continue;
            recordMathProofImpactFinalCheck(impact, {
              ...result,
              ...(result.usedDeclarationDependencies
                ? {
                    usedDeclarationDependencies: result.usedDeclarationDependencies.filter((name) =>
                      impact.candidates.includes(name)
                    ),
                  }
                : {}),
            });
          }
        } catch {
          /* Failed optional attribution leaves dependency coverage unknown. */
        }
      }
      return { verified: true, disposition: 'verified', receipts };
    })();
  } catch (error) {
    operationError = { value: error };
  } finally {
    if (added) {
      try {
        execFileSync('git', ['-C', repositoryRoot, 'worktree', 'remove', '--force', checkoutRoot], {
          stdio: 'pipe',
          maxBuffer: 8 * 1024 * 1024,
        });
      } catch (error) {
        cleanupError = error;
      }
    }
    if (temporaryRoot) {
      try {
        fs.rmSync(temporaryRoot, { recursive: true, force: true });
      } catch (error) {
        cleanupError ??= error;
      }
    }
  }
  if (cleanupError) throw new Error('math_v2_verification_worktree_cleanup', { cause: cleanupError });
  if (operationError) throw operationError.value;
  if (!operationResult) throw new Error('math_v2_verification_missing_result');
  return operationResult;
}

/** Create the private source commit, or prove that the exact commit already exists after a crash. */
export function commitMathV2PromotionWorktree(
  input: MathV2PromotionCommitRequest
): Readonly<{ commit: string; replayed?: boolean }> {
  if (
    input.expectedFiles.length !== input.includePaths.length ||
    new Set(input.expectedFiles.map((file) => file.pathRelative)).size !== input.expectedFiles.length
  ) {
    throw new Error('math_v2_promotion_commit_identity');
  }
  for (const expected of input.expectedFiles) {
    if (!input.includePaths.includes(expected.pathRelative)) throw new Error('math_v2_promotion_commit_identity');
    const source = path.resolve(input.worktreePath, expected.pathRelative);
    if (!source.startsWith(`${path.resolve(input.worktreePath)}${path.sep}`) || !fs.statSync(source).isFile()) {
      throw new Error('math_v2_promotion_commit_identity');
    }
    if (crypto.createHash('sha256').update(fs.readFileSync(source)).digest('hex') !== expected.contentSha256) {
      throw new Error('math_v2_promotion_commit_identity');
    }
  }
  const checkpoint = createProjectGitCheckpoint({
    workspace: input.worktreePath,
    message: `Mathematics source ${input.assignmentId}`,
    includePaths: [...input.includePaths],
    stage: 'math-source',
  });
  if (checkpoint.ok && checkpoint.commit) return Object.freeze({ commit: checkpoint.commit });

  const branch = gitText(input.worktreePath, ['rev-parse', '--abbrev-ref', 'HEAD']);
  const head = gitText(input.worktreePath, ['rev-parse', 'HEAD']).toLowerCase();
  const allowedNotes = new Set(
    input.includePaths.map((file) => path.posix.join(path.posix.dirname(file), 'RESEARCH.md'))
  );
  const unsafeChanges = gitPorcelainStatus(input.worktreePath).some(
    (entry) =>
      (!allowedNotes.has(entry.pathRelative) && !isHostRuntimeRecord(entry)) ||
      (entry.indexStatus !== ' ' && entry.indexStatus !== '?') ||
      Boolean(entry.originalPathRelative)
  );
  const ancestor = spawnSync('git', ['-C', input.worktreePath, 'merge-base', '--is-ancestor', input.baseCommit, head]);
  if (branch !== input.branch || unsafeChanges || ancestor.status !== 0) {
    throw new Error(checkpoint.error || 'Unable to commit the v2 mathematics worktree.');
  }
  for (const expected of input.expectedFiles) {
    const blob = execFileSync('git', ['-C', input.worktreePath, 'show', `${head}:${expected.pathRelative}`], {
      maxBuffer: 8 * 1024 * 1024,
    });
    if (crypto.createHash('sha256').update(blob).digest('hex') !== expected.contentSha256) {
      throw new Error('math_v2_promotion_commit_identity');
    }
  }
  return Object.freeze({ commit: head, replayed: true });
}

export function prepareMathV2Promotion(
  receipt: ProjectGitResearchTeamAssignmentReceipt,
  assignment: RuntimeMathAssignment,
  projectRoot: string
): MathV2PromotionPreflight {
  if (receipt.schema !== 'deepscientist.research_team_assignment.v2' || receipt.state !== 'accepted')
    throw new Error('math_v2_promotion_receipt');
  if (receipt.assignmentId !== assignment.assignmentId || assignment.baseCommit.length < 40)
    throw new Error('math_v2_promotion_identity');
  const prepared = receipt.preparedGit;
  if (!prepared?.branch || !prepared.worktreePath || !prepared.baseCommit)
    throw new Error('math_v2_promotion_pending_worktree');
  if (prepared.baseCommit !== assignment.baseCommit) throw new Error('math_v2_promotion_base_commit');
  assertMathCanonicalPath(projectRoot);
  assertMathCanonicalPath(prepared.worktreePath);
  if (!fs.statSync(prepared.worktreePath).isDirectory()) throw new Error('math_v2_promotion_worktree');
  if (path.resolve(prepared.worktreePath) === path.resolve(projectRoot)) throw new Error('math_v2_promotion_worktree');
  return Object.freeze({
    assignmentId: assignment.assignmentId,
    branch: prepared.branch,
    worktreePath: prepared.worktreePath,
    baseCommit: prepared.baseCommit,
  });
}

/** Copy only the already staged, hash-identified files into the isolated Git worktree. */
export function promoteMathV2DraftToWorktree(
  plan: MathV2PromotionPreflight,
  assignment: RuntimeMathAssignment,
  files: readonly MathV2DraftPromotionFile[],
  workspace: string,
  projectRoot = workspace
): readonly string[] {
  assertMathCanonicalPath(plan.worktreePath);
  assertMathCanonicalPath(workspace);
  assertMathCanonicalPath(projectRoot);
  if (!isMathPathWithin(workspace, projectRoot)) throw new Error('math_v2_promotion_path');
  const sourceRoot = path.resolve(projectRoot, assignment.sourceRootRelative);
  if (!fs.statSync(plan.worktreePath).isDirectory()) throw new Error('math_v2_promotion_worktree');
  const prepared: Array<{ target: string; bytes: Buffer; relative: string }> = [];
  for (const file of files) {
    if (
      !file ||
      typeof file.pathRelative !== 'string' ||
      path.isAbsolute(file.pathRelative) ||
      file.pathRelative.includes('..')
    )
      throw new Error('math_v2_promotion_path');
    const source = path.resolve(assignment.draftRoot, file.pathRelative);
    const target = path.resolve(plan.worktreePath, path.relative(workspace, sourceRoot), file.pathRelative);
    assertMathCanonicalPath(source);
    if (!fs.statSync(source).isFile()) throw new Error('math_v2_promotion_source');
    if (!isMathPathWithin(plan.worktreePath, target)) throw new Error('math_v2_promotion_path');
    const bytes = fs.readFileSync(source);
    const digest = crypto.createHash('sha256').update(bytes).digest('hex');
    if (digest !== file.contentSha256) throw new Error('math_v2_promotion_hash');
    prepared.push({ target, bytes, relative: path.relative(plan.worktreePath, target).split(path.sep).join('/') });
  }
  const promoted: string[] = [];
  for (const entry of prepared) {
    fs.mkdirSync(path.dirname(entry.target), { recursive: true, mode: 0o700 });
    const temporary = `${entry.target}.${process.pid}.${Date.now()}.tmp`;
    fs.writeFileSync(temporary, entry.bytes, { mode: 0o600 });
    fs.renameSync(temporary, entry.target);
    promoted.push(entry.relative);
  }
  return Object.freeze(promoted);
}
