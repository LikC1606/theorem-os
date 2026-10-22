import fs from 'node:fs';
import path from 'node:path';
import { checkManyFormalVerifications, type MathematicsVerifierBatchItem, type MathematicsVerifierBatchRequest,
  type MathematicsVerifierBatchResult, type MathematicsVerifierExecutionOptions } from '../../math/verifier';
import { canonicalMathJson, mathDigest } from '../../math/mathRuntimeIo';
import { commitSolverSources, git, withSolverWorktree, type SolverProblem } from '../problem';
import { bindLeanPackages } from '../../math/leanDiagnostics';
import { hashMathFormalSourceDeclaration } from '../../math/leanSource';
import { hasDeterministicLeanFailure, proofReuseEnvironment, proofVerificationDigest } from '../proofReuse';

export type ProofCheck = Readonly<{ commit: string; sourceDigest: string; passed: boolean; verification: MathematicsVerifierBatchResult }>;

const checkedRejections = new WeakMap<ProofCheck, { inputDigest: string; verificationDigest: string }>();
const checkedProofs = new WeakMap<ProofCheck, string>();
const proofIdentity = (check: ProofCheck) => mathDigest(canonicalMathJson({
  commit: check.commit, sourceDigest: check.sourceDigest, passed: check.passed, verification: check.verification,
}));

/** Serialized or modified receipts cannot narrow a fixed candidate's required reviews. */
export const hasFreshSolverCheck = (check: ProofCheck): boolean =>
  check.passed && checkedProofs.get(check) === proofIdentity(check);

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

type AttributedProofCheck = Pick<ProofCheck, 'passed' | 'verification'> & { attributable: boolean };

/** Slice only a fully bound batch; receipt identities and their original metadata stay intact. */
export function attributeProofEvidence(verification: MathematicsVerifierBatchResult, commit: string,
  items: readonly MathematicsVerifierBatchItem[]): AttributedProofCheck[] {
  const matches = (index: number) => {
    const result = verification.results[index], item = items[index];
    return Boolean(result && item && result.targetCommit === commit && result.proofPath === item.proofPath &&
      result.theoremName === item.theoremName && result.statementHash === item.statementHash &&
      result.leanStatementHash === item.leanStatementHash && result.claim === 'statement' &&
      result.sourceDeclarationHash === item.expectedSourceDeclarationHash);
  };
  if (items.length > 1) {
    const status = verification.results.every(result => result.status === 'kernel_verified') ? 'kernel_verified' :
      verification.results.some(result => result.status === 'failed') ? 'failed' :
        verification.results.some(result => result.status === 'blocked') ? 'blocked' : 'unavailable';
    const distinct = (values: readonly string[]) => values.every(value => typeof value === 'string' && Boolean(value.trim())) &&
      new Set(values).size === values.length;
    if (verification.schema !== 'deepscientist.mathematics.verification-batch/v1' || verification.targetCommit !== commit ||
        typeof verification.sessionId !== 'string' || !verification.sessionId.trim() ||
        verification.status !== status || verification.results.length !== items.length ||
        !distinct(items.map(item => `${item.proofPath}\0${item.theoremName}`)) ||
        !distinct(verification.results.map(result => result.receiptId)) ||
        !distinct(verification.results.map(result => result.checkId)) ||
        verification.results.some((result, index) => !matches(index) || result.sessionId !== verification.sessionId ||
          result.checkId !== (items[index]!.id?.trim() || `check-${index + 1}`)))
      throw new Error('math_task_check_identity_changed');
  }
  // Infrastructure failures belong to the shared invocation, even when aggregateStatus reports failed.
  const interrupted = verification.results.some(result => result.cleanupError ||
    /\b(?:timed?\s*out|timeout|deadline|abort(?:ed)?|interrupt(?:ed)?)\b/iu.test(result.error ?? ''));
  const unavailable = verification.status === 'unavailable' || verification.results.some(result => result.status === 'unavailable');
  const blocked = interrupted || verification.status === 'blocked' || verification.results.some(result => result.status === 'blocked');
  return items.map((item, index) => {
    const result = verification.results[index];
    const view: MathematicsVerifierBatchResult = { ...verification,
      status: unavailable ? 'unavailable' : blocked ? 'blocked' : items.length > 1 ? result!.status : verification.status,
      results: result ? [result] : [] };
    const passed = proofReceiptsMatch(view, commit, [item]);
    return { verification: view, passed, attributable: verification.targetCommit === commit && matches(index) &&
      (passed || unavailable || blocked || hasDeterministicLeanFailure(view)) };
  });
}

export async function checkProofEvidence(request: MathematicsVerifierBatchRequest & { targetCommit: string },
  options: MathematicsVerifierExecutionOptions): Promise<Pick<ProofCheck, 'passed' | 'verification'>> {
  const verification = await checkManyFormalVerifications({ ...request,
    batchTimeoutMs: request.timeoutMs === Infinity ? Infinity : request.batchTimeoutMs },
  { ...options, trustedLakePackagesRoots: (options.env?.DEEPSCIENTIST_MATH_TRUSTED_CACHE_ROOTS || '').split(path.delimiter).filter(Boolean) });
  return { verification, passed: proofReceiptsMatch(verification, request.targetCommit, request.items) };
}

export async function checkProjectedDeclarations(problem: SolverProblem, checkout: string, sourceWorktree: string, commit: string,
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
  const evidence = await checkProofEvidence({ projectRoot, targetCommit: commit, timeoutMs, items }, execution);
  options.signal?.throwIfAborted();
  return { ...evidence, attributions: attributeProofEvidence(evidence.verification, commit, items) };
}

/** M2: exact-source Lean evidence. Reused rejections must come from this process and pinned environment. */
export async function checkSolverProof(problem: SolverProblem, worktree: string, env: NodeJS.ProcessEnv,
  signal?: AbortSignal, previous?: ProofCheck, timeoutMs = 180_000): Promise<ProofCheck> {
  signal?.throwIfAborted();
  const commit = commitSolverSources(problem, worktree);
  const projectRoot = path.join(worktree, problem.projectRelative);
  const sourceDigest = solverSourceDigest(problem, worktree);
  const environment = proofReuseEnvironment(projectRoot, env);
  const inputDigest = environment.reusable ? mathDigest(canonicalMathJson({
    tree: git(worktree, ['ls-tree', '-r', '-z', '--full-tree', 'HEAD']).split('\0')
      .filter(entry => entry && entry.slice(entry.indexOf('\t') + 1) !== 'RESEARCH.md'),
    problem: problem.receiptDigest, kind: problem.kind, project: problem.projectRelative,
    targets: problem.targets, statement: problem.contract.statementHash, leanStatement: problem.contract.leanStatementHash,
    sourceDigest, environment: environment.digest,
  })) : undefined;
  const provenance = previous && checkedRejections.get(previous);
  if (inputDigest && provenance?.inputDigest === inputDigest && previous && !previous.passed &&
      previous.sourceDigest === sourceDigest && provenance.verificationDigest === proofVerificationDigest(previous.verification)) {
    const reused = previous.commit === commit ? previous : { ...previous, commit };
    checkedRejections.set(reused, provenance);
    return reused;
  }
  const verify = (checkout: string) => checkProofEvidence({ projectRoot: path.join(checkout, problem.projectRelative), targetCommit: commit, timeoutMs,
    items: problem.targets.map(target => ({ proofPath: target.proofPath, theoremName: target.theoremName,
      expectedSourceDeclarationHash: target.declarationHash, statementHash: problem.contract.statementHash,
      leanStatementHash: problem.contract.leanStatementHash, claim: 'statement' as const })) },
  { env: environment.env, signal, prepareLocalDependencies: problem.kind === 'lean-eval', collectDeclarationReferences: true });
  // Advisory scratch and diagnostic logs stay in the worker. The strict verifier receives
  // only the fixed commit and the same pinned packages, without weakening its clean-tree gate.
  const evidence = git(worktree, ['status', '--porcelain=v1', '--untracked-files=all'])
    ? await withSolverWorktree(worktree, commit, async checkout => {
      const packages = path.join(projectRoot, '.lake', 'packages');
      if (fs.existsSync(packages)) bindLeanPackages(path.join(checkout, problem.projectRelative), packages);
      return verify(checkout);
    }) : await verify(worktree);
  const check = { commit, sourceDigest, ...evidence };
  if (check.passed) checkedProofs.set(check, proofIdentity(check));
  if (!check.passed && inputDigest && hasDeterministicLeanFailure(check.verification) &&
      proofReuseEnvironment(projectRoot, environment.env).digest === environment.digest)
    checkedRejections.set(check, { inputDigest, verificationDigest: proofVerificationDigest(check.verification) });
  return check;
}
