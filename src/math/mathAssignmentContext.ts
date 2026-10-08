import path from 'node:path';
import { execFileSync, spawnSync } from 'node:child_process';
import { z } from 'zod';
import type { MathFormalVerificationTarget } from "../common/types/team/mathRuntimeContracts";
import { decodeMathAssignmentJournal, normalizeRuntimeMathAssignment } from "./mathAssignmentJournal";
import { isMathPathWithin, mathAssignmentSourceRoot, readMathRunBinding } from "./mathRunBinding";
import { MATH_RUN_INPUTS_ENV, verifyMathRunInputs } from "./mathRunInputs";
import { canonicalMathJson, mathDigest } from "./mathRuntimeIo";

const v1Assignment = z
  .object({
    math: z.object({
      statementHash: z.string().regex(/^[a-f0-9]{64}$/u),
      routeFingerprint: z.string().trim().min(1).max(160),
      directAttempt: z.boolean().optional(),
      stage: z.string(),
      routeCards: z.array(z.unknown()).optional(),
      proofPlan: z.unknown().optional(),
      artifactPaths: z.array(z.string()).optional(),
      problemContract: z
        .object({
          problemId: z.string().trim().min(1).max(160),
          statementHash: z
            .string()
            .regex(/^[a-f0-9]{64}$/u)
            .optional(),
          leanStatementHash: z
            .string()
            .regex(/^[a-f0-9]{64}$/u)
            .optional(),
          formalStatement: z.string().min(1).optional(),
        })
        .passthrough()
        .optional(),
      researchContract: z
        .object({ problemId: z.string().trim().min(1).max(160) })
        .passthrough()
        .optional(),
    }),
  })
  .passthrough();

export type MathAssignmentReceiptContextInput = Readonly<{
  receipt: Readonly<{
    schema: string;
    teamId: string;
    slotId: string;
    assignmentId: string;
    state: string;
    assignment: unknown;
  }>;
  projectRoot: string;
  expectedTeamId?: string;
  expectedSlotId?: string;
  expectedAssignmentId?: string;
  env?: NodeJS.ProcessEnv;
}>;

export type MathAssignmentContext = Readonly<{
  protocol: 'v1' | 'v2';
  teamId: string;
  slotId: string;
  assignmentId: string;
  problemId: string;
  statementHash: string;
  leanStatementHash?: string;
  formalStatement?: string;
  initialRouteFingerprint: string;
  routeRevisionsSupported: boolean;
  assignmentDigest: string;
  verificationTargets: readonly MathFormalVerificationTarget[];
  artifactPaths: readonly string[];
  runId?: string;
  bindingDigest?: string;
  baseCommit?: string;
  sourceRootRelative?: string;
}>;

const fail = (code: string): never => {
  throw new Error(code);
};

function assertReceiptIdentity(
  record: ReturnType<typeof decodeMathAssignmentJournal>,
  input: MathAssignmentReceiptContextInput
): void {
  if (
    (input.expectedTeamId !== undefined && record.teamId !== input.expectedTeamId) ||
    (input.expectedSlotId !== undefined && record.slotId !== input.expectedSlotId) ||
    (input.expectedAssignmentId !== undefined && record.assignmentId !== input.expectedAssignmentId)
  )
    fail('math_assignment_context_identity_mismatch');
}

function frozenRunInputs(env: NodeJS.ProcessEnv) {
  const encoded = env[MATH_RUN_INPUTS_ENV];
  if (!encoded) fail('math_assignment_context_run_inputs_missing');
  try {
    return verifyMathRunInputs(JSON.parse(encoded));
  } catch {
    return fail('math_assignment_context_run_inputs_invalid');
  }
}

function assertAuthorizedExecutionBase(
  assignment: ReturnType<typeof normalizeRuntimeMathAssignment>,
  binding: ReturnType<typeof readMathRunBinding>,
  _projectRoot: string
): void {
  if (assignment.baseCommit === binding.baseCommit) return;
  // A different execution base is only valid for a host-created successor. The
  // predecessor edge is already part of the durable assignment request; the
  // Git checks below ensure it is a real descendant of the frozen C0.
  if (!assignment.request.predecessorAssignmentId) fail('math_assignment_context_binding_mismatch');
  try {
    // Both accepted entry points (outer W and binding.projectRoot P) must use
    // the same authenticated Git repository and the same P-relative target
    // coordinates. Never let the caller's spelling change the C0/C1 check.
    const repositoryRoot = binding.workspace;
    const resolved = execFileSync(
      'git',
      ['-C', repositoryRoot, 'rev-parse', '--verify', `${assignment.baseCommit}^{commit}`],
      { encoding: 'utf8' }
    )
      .trim()
      .toLowerCase();
    if (resolved !== assignment.baseCommit.toLowerCase()) fail('math_assignment_context_binding_mismatch');
    const ancestry = spawnSync(
      'git',
      ['-C', repositoryRoot, 'merge-base', '--is-ancestor', binding.baseCommit, assignment.baseCommit],
      { stdio: 'ignore' }
    );
    if (ancestry.status !== 0) fail('math_assignment_context_binding_mismatch');
    const repositoryTargetPath = (relativePath: string): string => {
      const absoluteTarget = path.resolve(binding.projectRoot, relativePath);
      if (!isMathPathWithin(binding.projectRoot, absoluteTarget)) fail('math_assignment_context_binding_mismatch');
      const repositoryRelative = path.relative(repositoryRoot, absoluteTarget).split(path.sep).join('/');
      if (!repositoryRelative || repositoryRelative.startsWith('../') || path.isAbsolute(repositoryRelative))
        fail('math_assignment_context_binding_mismatch');
      return repositoryRelative;
    };
    // Frozen target declarations cannot be rewritten between C0 and C1. Paths
    // absent at C0 are generated assignment sources and are checked by the
    // verification-target identity later in this function.
    for (const target of binding.problem?.verificationTargets ?? []) {
      const repositoryRelativeTarget = repositoryTargetPath(target.pathRelative);
      const existsAtBase = spawnSync(
        'git',
        ['-C', repositoryRoot, 'cat-file', '-e', `${binding.baseCommit}:${repositoryRelativeTarget}`],
        { stdio: 'ignore' }
      );
      if (existsAtBase.status !== 0) continue;
      const changed = spawnSync(
        'git',
        [
          '-C',
          repositoryRoot,
          'diff',
          '--quiet',
          binding.baseCommit,
          assignment.baseCommit,
          '--',
          repositoryRelativeTarget,
        ],
        { stdio: 'ignore' }
      );
      if (changed.status !== 0) fail('math_assignment_context_binding_mismatch');
    }
  } catch {
    fail('math_assignment_context_binding_mismatch');
  }
}

/** Resolve v1/v2 assignment identity without widening a v2 WAL record into the v1 shape. */
export function resolveMathAssignmentContext(input: MathAssignmentReceiptContextInput): MathAssignmentContext {
  let record: ReturnType<typeof decodeMathAssignmentJournal>;
  try {
    record = decodeMathAssignmentJournal(input.receipt);
  } catch {
    return fail('math_assignment_context_wal_invalid');
  }
  assertReceiptIdentity(record, input);
  const assignmentDigest = mathDigest(canonicalMathJson(record.assignment));
  if (record.version === 1) {
    const parsed = v1Assignment.safeParse(record.assignment);
    if (!parsed.success) fail('math_assignment_context_v1_invalid');
    const problemId = parsed.data.math.problemContract?.problemId ?? parsed.data.math.researchContract?.problemId;
    if (!problemId) fail('math_assignment_context_problem_missing');
    const statementHash = parsed.data.math.problemContract?.statementHash ?? parsed.data.math.statementHash;
    return Object.freeze({
      protocol: 'v1',
      teamId: record.teamId,
      slotId: record.slotId,
      assignmentId: record.assignmentId,
      problemId,
      statementHash,
      ...(parsed.data.math.problemContract?.leanStatementHash
        ? { leanStatementHash: parsed.data.math.problemContract.leanStatementHash }
        : {}),
      ...(parsed.data.math.problemContract?.formalStatement
        ? { formalStatement: parsed.data.math.problemContract.formalStatement }
        : {}),
      initialRouteFingerprint: parsed.data.math.routeFingerprint,
      routeRevisionsSupported:
        parsed.data.math.directAttempt === true &&
        parsed.data.math.stage === 'formalize' &&
        !parsed.data.math.routeCards?.length &&
        !parsed.data.math.proofPlan,
      assignmentDigest,
      verificationTargets: Object.freeze([]),
      artifactPaths: Object.freeze([...(parsed.data.math.artifactPaths ?? [])]),
    });
  }

  const assignment = normalizeRuntimeMathAssignment(record.assignment);
  const binding = readMathRunBinding(frozenRunInputs(input.env ?? process.env));
  const bindingDigest = mathDigest(canonicalMathJson(binding));
  const suppliedRoot = path.resolve(input.projectRoot);
  if (
    assignment.runId !== binding.runId ||
    assignment.bindingDigest !== bindingDigest ||
    record.slotId !== assignment.request.targetSlotId ||
    record.assignmentId !== assignment.assignmentId ||
    (suppliedRoot !== path.resolve(binding.workspace) && suppliedRoot !== path.resolve(binding.projectRoot)) ||
    assignment.sourceRootRelative !==
      path
        .relative(binding.projectRoot, mathAssignmentSourceRoot(binding, assignment.assignmentId))
        .split(path.sep)
        .join('/')
  )
    fail('math_assignment_context_binding_mismatch');
  assertAuthorizedExecutionBase(assignment, binding, input.projectRoot);
  if (!binding.problem) fail('math_assignment_context_problem_missing');
  const targets = assignment.request.verificationTargets ?? [];
  if (assignment.request.kind === 'formalize' && !targets.length)
    fail('math_assignment_context_verification_targets_missing');
  const boundTargets = binding.problem.verificationTargets ?? [];
  if (assignment.request.kind === 'formalize') {
    if (targets.length !== boundTargets.length) fail('math_assignment_context_verification_target_mismatch');
    const targetKey = (target: MathFormalVerificationTarget): string =>
      JSON.stringify({
        targetId: target.targetId,
        pathRelative: target.pathRelative,
        theoremName: target.theoremName,
        statementHash: target.statementHash,
        leanStatementHash: target.leanStatementHash ?? null,
        expectedSourceDeclarationHash: target.expectedSourceDeclarationHash,
        claim: target.claim ?? 'statement',
      });
    const boundKeys = new Set(boundTargets.map(targetKey));
    if (boundKeys.size !== targets.length || targets.some((target) => !boundKeys.has(targetKey(target))))
      fail('math_assignment_context_verification_target_mismatch');
  }
  if (
    targets.some(
      (target) =>
        target.statementHash !== binding.problem!.statementHash ||
        (binding.problem!.leanStatementHash !== undefined &&
          target.leanStatementHash !== binding.problem!.leanStatementHash)
    )
  )
    fail('math_assignment_context_verification_target_mismatch');
  const artifactPaths = targets.map((target) => path.posix.join(assignment.sourceRootRelative, target.pathRelative));
  return Object.freeze({
    protocol: 'v2',
    teamId: record.teamId,
    slotId: record.slotId,
    assignmentId: record.assignmentId,
    problemId: binding.problem.problemId,
    statementHash: binding.problem.statementHash,
    ...(binding.problem.leanStatementHash ? { leanStatementHash: binding.problem.leanStatementHash } : {}),
    ...(binding.problem.formalStatement ? { formalStatement: binding.problem.formalStatement } : {}),
    initialRouteFingerprint: binding.problem.initialRouteFingerprint,
    routeRevisionsSupported: assignment.request.kind === 'formalize',
    assignmentDigest,
    verificationTargets: Object.freeze(targets.map((target) => Object.freeze({ ...target }))),
    artifactPaths: Object.freeze(artifactPaths),
    runId: assignment.runId,
    bindingDigest: assignment.bindingDigest,
    baseCommit: assignment.baseCommit,
    sourceRootRelative: assignment.sourceRootRelative,
  });
}

/** Resolve common source spellings against the exact files owned by a v2 assignment. */
export function resolveMathAssignmentProofSource(
  context: MathAssignmentContext,
  sourceFile: string,
  projectRelative = ''
): string {
  if (context.protocol !== 'v2') return sourceFile;
  if (
    path.posix.isAbsolute(sourceFile) ||
    /^[A-Za-z]:/u.test(sourceFile) ||
    sourceFile.includes('\\') ||
    sourceFile.split('/').some((part) => !part || part === '.' || part === '..')
  )
    throw new Error('Proof session source path is invalid.');
  const candidates = new Set([sourceFile]);
  if (projectRelative && sourceFile.startsWith(`${projectRelative}/`))
    candidates.add(sourceFile.slice(projectRelative.length + 1));
  for (const candidate of candidates) {
    if (context.sourceRootRelative && context.verificationTargets.some((target) => target.pathRelative === candidate))
      candidates.add(path.posix.join(context.sourceRootRelative, candidate));
  }
  const owned = [...new Set(context.artifactPaths)].filter((file) => candidates.has(file));
  if (owned.length !== 1)
    throw new Error(
      `Proof session source is not owned by the active assignment. Authorized sources: ${[...new Set(context.artifactPaths)].join(', ')}`
    );
  return owned[0]!;
}

/** Map original-target aliases for probes while retaining private auxiliary files. */
export function resolveMathAssignmentProbeSource(
  context: MathAssignmentContext,
  sourceFile: string,
  projectRelative = ''
): string {
  if (context.protocol !== 'v2') return sourceFile;
  const relative =
    projectRelative && sourceFile.startsWith(`${projectRelative}/`)
      ? sourceFile.slice(projectRelative.length + 1)
      : sourceFile;
  if (
    context.artifactPaths.includes(relative) ||
    context.verificationTargets.some((target) => target.pathRelative === relative)
  )
    return resolveMathAssignmentProofSource(context, sourceFile, projectRelative);
  return sourceFile;
}

/** Overview may encounter unrelated legacy assignments; malformed v2 records still fail closed. */
export function tryResolveMathAssignmentContext(
  input: MathAssignmentReceiptContextInput
): MathAssignmentContext | undefined {
  try {
    return resolveMathAssignmentContext(input);
  } catch (error) {
    if (input.receipt.schema === 'deepscientist.research_team_assignment.v1') return undefined;
    throw error;
  }
}
