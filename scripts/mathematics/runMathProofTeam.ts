#!/usr/bin/env bun
import {
  prepareMathProofEnvironment,
  MATH_PROOF_ENVIRONMENT_ENV,
  resolveMathProofEnvironment,
} from "../../src/math/mathProofEnvironment";
import { resolveMathematicsLakePackagesCache } from "../../src/math/verifier";
import { verifyMathV2SourceCommit } from "../../src/math/mathIntegrationPromotion";
/**
 * Run a proof-only mathematics task through the standalone Mathematics Research
 * Team runtime.  This runner deliberately does not use the IOAI competition
 * bootstrap or its submission protocol. IMO2026 uses host-owned Lean-kernel
 * evaluation by default; an explicit external evaluator takes precedence.
 */

import { runMathQuiescentProofPreview } from "../../src/math/mathQuiescentProofExecution";
import {
  collectMathModelIsolationEvidence,
  cleanupMathModelIsolationProcesses,
  finalizeMathModelIsolationRun,
  registerMathModelIsolationRun,
  sealMathModelIsolationRun,
  type MathModelIsolationRun,
  verifyMathModelIsolationCore,
} from "../../src/math/mathModelIsolationEvidence";
import {
  createMathProofProgressMonitor,
  finalizeMathRunReceipt,
  mathRunCompletedProofGraceMs,
  mathRunExitCode,
  recoverMathRunReceiptCleanup,
  type MathCleanupOutcome,
} from "../../src/math/mathRunLifecycle";
import {
  compactMathProofImpactSummary,
  readMathProofImpactSummary,
} from "../../src/math/mathProofImpact";
import { readMathLiteFeedback } from "../../src/math/mathLiteFeedback";
import { selectMathematicsMethodHints } from "../../src/common/chat/team/mathematicsMethodHints";
import { randomUUID } from 'node:crypto';
import fs from 'node:fs';
import path from 'node:path';
import { spawn, spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import { z } from 'zod';
import { parse as parseToml } from 'smol-toml';
import { isDeepStrictEqual } from 'node:util';
import { createMathBudgetHostClient } from "../../src/math/mathBudgetHostClient";
import { buildMathematicsConversationExtra } from "../../src/common/chat/mathematics";
import {
  createHeadlessMathematicsTeamProfile,
  MATHEMATICS_WORKER_ASSIGNMENT_SCOPE,
} from "../../src/common/chat/team/modeProfiles";
import {
  mathematicsResearchPolicy,
  MATHEMATICS_RESEARCH_POLICY_ENV,
} from "../../src/common/chat/team/mathematicsResearchPolicy";
import { prepareResearchTeamRoleMcpServers } from "../../src/common/types/team/researchTeamMcp";
import {
  provisionResearchTeam,
  removeResearchTeamRuntimeResources,
  type ResearchTeamProvisioningDeps,
  type ProvisionResearchTeamResult,
} from "../../src/common/types/team/researchTeamProvisioning";
import type { ResearchTeamRoleContract } from "../../src/common/types/team/researchTeamContracts";
import {
  normalizeMathProblemContract,
  type MathProblemContract,
} from "../../src/common/types/team/mathematicsTeam";
import { LEAN_EVAL_BENCHMARK_COMMIT } from "../../src/math/leanEvalCatalogAdapter";
import {
  IMO2026_BOOTSTRAP_SCHEMA,
  theoremQualifiedNamesFromSource,
  verifyImo2026BootstrapReceipt,
  type Imo2026BootstrapReceipt,
} from "../../src/math/imo2026Adapter";
import {
  fromBackendTeam,
  fromBackendTeamRunAck,
  toBackendTeamCreate,
} from "../../src/common/adapter/teamMapper";
import type { ISessionMcpServer } from "../../src/common/config/storage";
import {
  BUILTIN_RESEARCH_TEAM_NAME,
  BUILTIN_SCIENCE_ARTIFACT_NAME,
  BUILTIN_RESEARCH_EVIDENCE_NAME,
  RESEARCH_TEAM_CAPABILITY_SCHEMA,
  RESEARCH_TEAM_CORE_BASE_URL_ENV,
} from "../../src/common/config/builtinMcpConstants";
import { PROJECT_WORKSPACE_ENV_KEYS } from "../../src/common/chat/projectWorkspace";
import {
  MATHEMATICS_INTERACTION_PROFILE_ENV,
  MATHEMATICS_SECOND_PROOF_OWNER_ENV,
  MATHEMATICS_LITE_INTERACTION_PROFILE,
  MATHEMATICS_PLANNING_POLICY_ENV,
  type MathematicsPlanningPolicy,
  resolveMathematicsRuntimeEnvironment,
  mathematicsRuntimeInstruction,
  projectMathematicsRuntimeEnvironment,
} from "../../src/math/mathRuntimeEnvironment";
import { readMathRetrievalCorpusEnvironment } from "../../src/math/mathRetrievalCorpus";
import {
  checkLeanToolchainReadiness,
  checkResolvedLeanToolchainReadiness,
  resolvePinnedLeanToolchainExecutable,
} from "../../src/math/leanToolchainReadiness";
import { hashMathFormalSourceDeclaration } from "../../src/math/verifier";
import {
  MathRunInputsIntegrityError,
  freezeMathRunInputs,
  verifyMathRunInputs,
  readMathRunEnvironmentProjection,
  MATH_RUN_INPUTS_ENV,
} from "../../src/math/mathRunInputs";
import { readMathematicsReceiptSecret } from "../../src/math/receiptAttestation";
import { normalizeRuntimeMathAssignment } from "../../src/math/mathAssignmentJournal";
import {
  listProjectGitResearchTeamAssignments,
  type ProjectGitResearchTeamAssignmentReceipt,
} from "../../src/project-git/ProjectGitService";
import {
  observeMathRun,
  type MathRunObservation,
} from "../../src/math/mathRunObservation";
import { ResearchTeamEventStream } from "../../src/team/coreTeamEvents";
import { ResearchTeamEventWaiter } from "../../src/team/coreTeamEventWaiter";
import {
  createMathDiagnostics,
  createMathTimingDiagnostics,
} from "../../src/math/mathDiagnostics";
import {
  discardLeanEvalTeamWorkspacesForTeam,
  prepareLeanEvalTeamWorkspace,
} from "../../src/math/leanEvalTeamWorkspace";
import {
  runMathEvaluation,
  resumeMathEvaluation,
  type MathEvaluationCandidate,
} from "../../src/math/mathEvaluator";
import {
  readMathPlanningContext,
  isMathPlanningSafetyError,
} from "../../src/math/mathPlanningContext";
import { mathEvaluatorPolicyDigest } from "../../src/math/mathEvaluatorPolicy";
import { preflightMathEvaluatorContainer } from "../../src/math/mathEvaluatorContainer";
import {
  canonicalMathJson,
  mathDigest,
  readMathJson,
  syncMathDirectory,
  writeMathJsonDurable,
} from "../../src/math/mathRuntimeIo";
import {
  mathBuildFile,
  readMathBuildManifest,
  verifyMathRuntimeProcess,
} from "../../src/math/mathBuildManifest";
import {
  assertMathCanonicalPath,
  normalizeMathRunBinding,
  readMathRunBinding,
  resolveMathGeneratedSourceRoot,
  verifyMathRunBindingArtifacts,
} from "../../src/math/mathRunBinding";
import { createResearchCoreTeamClient } from "../../src/team/coreTeamClient";
import {
  recoverMathOwnerlessAssignment,
  withMathOwnerlessRecoveryMcp,
} from "../../src/math/mathOwnerlessRecovery";
import type { ResearchTeamRuntimeRosterMember } from "../../src/common/types/team/researchTeamMcp";
import {
  deriveMathProofRunMetric,
  type MathProofSearchObservation,
} from "../../src/math/mathProofRunReport";

type JsonRecord = Record<string, unknown>;

/** Resolve the exact source selected by the durable solver-ready evidence. */
export function resolveMathEvaluationCandidate(
  input: Readonly<{
    workspace: string;
    teamId: string;
    assignmentId: string;
    binding: ReturnType<typeof normalizeMathRunBinding>;
    targetCommit: string;
  }>
): MathEvaluationCandidate {
  const receipt = listProjectGitResearchTeamAssignments({
    workspace: input.workspace,
    teamId: input.teamId,
    strict: true,
  }).find((candidate) => candidate.assignmentId === input.assignmentId);
  if (
    !receipt?.integration?.sourceVerificationReceipts?.length ||
    receipt.integration.mergedCommit !== input.targetCommit
  )
    throw new Error('math_evaluator_candidate_missing');
  const sourceReceipts = receipt.integration.sourceVerificationReceipts;
  const sourcePaths = new Set(sourceReceipts.map((value) => value.sourcePath));
  if (sourcePaths.size !== 1 || sourceReceipts.some((value) => value.targetCommit !== input.targetCommit))
    throw new Error('math_evaluator_candidate_integrity');
  const sourcePath = [...sourcePaths][0]!;
  if (
    path.isAbsolute(sourcePath) ||
    path.posix.normalize(sourcePath) !== sourcePath ||
    sourcePath.split('/').some((part) => ['.', '..', '.git', ''].includes(part))
  )
    throw new Error('math_evaluator_candidate_integrity');
  const hashes = new Set(sourceReceipts.map((value) => value.contentSha256));
  if (hashes.size !== 1) throw new Error('math_evaluator_candidate_integrity');
  const assignment = normalizeRuntimeMathAssignment(receipt.assignment);
  const expectedTargets = input.binding.problem?.verificationTargets ?? [];
  const targets = sourceReceipts.map((source) => {
    const target = expectedTargets.find((candidate) => {
      const expectedPath = path.posix.join(
        path.relative(input.workspace, input.binding.projectRoot).split(path.sep).join('/'),
        assignment.sourceRootRelative,
        candidate.pathRelative
      );
      return expectedPath === source.sourcePath && candidate.theoremName === source.theoremName;
    });
    if (
      !target ||
      source.sourceDeclarationHash !== target.expectedSourceDeclarationHash ||
      source.statementHash !== target.statementHash
    )
      throw new Error('math_evaluator_candidate_integrity');
    return {
      targetId: target.targetId,
      theoremName: source.theoremName,
      statementHash: source.statementHash,
      ...(source.leanStatementHash ? { leanStatementHash: source.leanStatementHash } : {}),
      sourceDeclarationHash: source.sourceDeclarationHash,
    };
  });
  if (
    targets.length !==
    expectedTargets.filter((target) => {
      const expectedPath = path.posix.join(
        path.relative(input.workspace, input.binding.projectRoot).split(path.sep).join('/'),
        assignment.sourceRootRelative,
        target.pathRelative
      );
      return expectedPath === sourcePath;
    }).length
  )
    throw new Error('math_evaluator_candidate_incomplete');
  return Object.freeze({ pathRelative: sourcePath, sha256: [...hashes][0]!, targets: Object.freeze(targets) });
}

/** Recheck every original declaration on the integrated commit, using the sealed Lean verifier. */
export async function runMathKernelEvaluation(
  input: Readonly<{
    workspace: string;
    commit: string;
    binding: Pick<ReturnType<typeof normalizeMathRunBinding>, 'projectRoot' | 'problem'>;
    candidate: MathEvaluationCandidate;
    signal?: AbortSignal;
  }>,
  verify: typeof verifyMathV2SourceCommit = verifyMathV2SourceCommit
) {
  const startedAt = Date.now();
  const expected = input.binding.problem?.verificationTargets ?? [];
  const seen = new Set<string>();
  if (!expected.length || input.candidate.targets.length !== expected.length)
    throw new Error('math_evaluator_candidate_incomplete');
  const items = input.candidate.targets.map((candidate) => {
    const target = expected.find((value) => value.targetId === candidate.targetId);
    if (
      !target ||
      seen.has(candidate.targetId) ||
      target.theoremName !== candidate.theoremName ||
      target.statementHash !== candidate.statementHash ||
      target.leanStatementHash !== candidate.leanStatementHash ||
      target.expectedSourceDeclarationHash !== candidate.sourceDeclarationHash ||
      (target.claim ?? 'statement') !== 'statement'
    )
      throw new Error('math_evaluator_candidate_integrity');
    seen.add(candidate.targetId);
    return {
      id: target.targetId,
      proofPath: input.candidate.pathRelative,
      contentSha256: input.candidate.sha256,
      theoremName: target.theoremName,
      statementHash: target.statementHash,
      leanStatementHash: target.leanStatementHash,
      expectedSourceDeclarationHash: target.expectedSourceDeclarationHash,
      claim: 'statement' as const,
    };
  });
  const verification = await verify({
    worktreePath: input.workspace,
    projectRelative: path.relative(input.workspace, input.binding.projectRoot),
    targetCommit: input.commit,
    items,
    signal: input.signal,
  });
  const status = verification.verified
    ? ('passed' as const)
    : verification.disposition === 'candidate_rejected'
      ? ('failed' as const)
      : ('error' as const);
  return {
    status,
    exitCode: status === 'passed' ? 0 : status === 'failed' ? 2 : 1,
    durationMs: Date.now() - startedAt,
    method: 'imo2026-host-lean-kernel-all-targets-v1',
    official: false,
    targetCommit: input.commit,
    checkedTargets: verification.verified ? items.length : 0,
    verification,
  };
}

type MathProofResumeState = {
  schema: 'deepscientist.math.proof-resume.v1';
  workspace: string;
  buildDigest: string;
  taskDigest: string;
  statementHash: string;
  benchmarkMethod: string;
  repetition?: number;
  researchPolicy: string | null;
  evaluationMode: string;
  teamId: string;
  teamRunId?: string;
  /** Digest binding the retained runtime resources to the cleanup journal. */
  resourceIdentityDigest?: string;
  runInputs: ReturnType<typeof verifyMathRunInputs>;
  baseCommit: string;
  mainlineAssignmentId: string;
  proofStartedAt: number;
  roster: readonly ResearchTeamRuntimeRosterMember[];
  conversations: Record<string, string>;
  assistantIds: string[];
  mcpServerIds: string[];
  continuationProgress: Record<string, MathContinuationProgress>;
  evaluationRoot?: string;
  evaluatorPolicyDigest?: string;
  /** Absolute path of the private wrapper used by this run. */
  runtimeLakeExecutable?: string;
  modelIsolationRun?: MathModelIsolationRun;
  runLimits?: Readonly<{ maxRunSeconds?: number; noProgressSeconds?: number }>;
  executionConfig?: Readonly<{
    benchmarkMethod: string;
    model: string;
    leadModel: string;
    workerModel: string;
    backend: string;
    leadThoughtLevel?: string;
    workerThoughtLevel?: string;
    planningPolicy?: MathematicsPlanningPolicy;
    roster: readonly Readonly<{ slotId: string; roleKind: string; laneId?: string }>[];
    pool: Readonly<{ agentLimit: number; reasoningConcurrency: number }>;
  }>;
};

export function readMathProofResumeState(file: string): MathProofResumeState {
  try {
    const parsed = readMathJson(file);
    if (!isRecord(parsed)) throw new Error();
    const state = parsed as unknown as MathProofResumeState;
    if (
      state.schema !== 'deepscientist.math.proof-resume.v1' ||
      typeof state.teamId !== 'string' ||
      !MATH_RESUME_ID_PATTERN.test(state.teamId.trim()) ||
      (state.teamRunId !== undefined &&
        (typeof state.teamRunId !== 'string' || !MATH_RESUME_ID_PATTERN.test(state.teamRunId.trim()))) ||
      typeof state.workspace !== 'string' ||
      !path.isAbsolute(state.workspace) ||
      !/^[a-f0-9]{64}$/u.test(state.buildDigest) ||
      !/^[a-f0-9]{64}$/u.test(state.taskDigest) ||
      !/^[a-f0-9]{64}$/u.test(state.statementHash) ||
      !Array.isArray(state.roster) ||
      !state.roster.length ||
      !state.conversations ||
      !Array.isArray(state.assistantIds) ||
      !Array.isArray(state.mcpServerIds) ||
      !state.mainlineAssignmentId ||
      !/^[a-f0-9]{40}(?:[a-f0-9]{24})?$/u.test(state.baseCommit) ||
      !Number.isFinite(state.proofStartedAt) ||
      !state.continuationProgress ||
      (state.resourceIdentityDigest !== undefined && !/^[a-f0-9]{64}$/u.test(state.resourceIdentityDigest)) ||
      (state.evaluationRoot !== undefined && !path.isAbsolute(state.evaluationRoot)) ||
      (state.evaluatorPolicyDigest !== undefined && !/^[a-f0-9]{64}$/u.test(state.evaluatorPolicyDigest))
    )
      throw new Error();
    if (!isRecord(state.conversations)) throw new Error();
    validateMathProofResumeRoster(state.roster);
    validateMathProofResumeConversations(state.roster, state.conversations);
    validateMathProofResumeResourceIds(state.assistantIds, 'assistantIds');
    validateMathProofResumeResourceIds(state.mcpServerIds, 'mcpServerIds');
    validateMathContinuationProgressRecord(state.continuationProgress);
    verifyMathRunInputs(state.runInputs);
    if (state.taskDigest !== state.runInputs.task.digest) throw new Error();
    if (
      state.runLimits !== undefined &&
      (!isRecord(state.runLimits) ||
        Object.entries(state.runLimits).some(
          ([key, value]) =>
            !['maxRunSeconds', 'noProgressSeconds'].includes(key) || !Number.isSafeInteger(value) || Number(value) < 1
        ))
    )
      throw new Error();
    if (state.runtimeLakeExecutable !== undefined && !path.isAbsolute(state.runtimeLakeExecutable)) throw new Error();
    if (state.executionConfig !== undefined) {
      if (
        typeof state.executionConfig !== 'object' ||
        !state.executionConfig.benchmarkMethod ||
        !state.executionConfig.model ||
        !state.executionConfig.leadModel ||
        !state.executionConfig.workerModel ||
        !state.executionConfig.backend ||
        (state.executionConfig.planningPolicy !== undefined &&
          !['current', 'failure-guided'].includes(state.executionConfig.planningPolicy)) ||
        !Array.isArray(state.executionConfig.roster) ||
        !state.executionConfig.pool ||
        !Number.isSafeInteger(state.executionConfig.pool.agentLimit) ||
        !Number.isSafeInteger(state.executionConfig.pool.reasoningConcurrency)
      )
        throw new Error();
    }
    return state;
  } catch {
    throw new Error('recovery_unavailable: invalid or missing retained run state');
  }
}

const MATH_RESUME_ID_PATTERN = /^[A-Za-z0-9][A-Za-z0-9._:-]{0,127}$/u;
const MATH_RESUME_DIGEST_PATTERN = /^[a-f0-9]{64}$/u;

function validateMathProofResumeResourceIds(value: unknown, field: string): readonly string[] {
  if (!Array.isArray(value)) throw new Error(`invalid retained ${field}`);
  const ids = value.map((item) => {
    if (typeof item !== 'string' || !MATH_RESUME_ID_PATTERN.test(item.trim()))
      throw new Error(`invalid retained ${field}`);
    return item.trim();
  });
  if (new Set(ids).size !== ids.length) throw new Error(`duplicate retained ${field}`);
  return Object.freeze(ids);
}

function validateMathProofResumeRoster(value: unknown): readonly ResearchTeamRuntimeRosterMember[] {
  if (!Array.isArray(value) || value.length === 0) throw new Error('invalid retained roster');
  const slots = new Set<string>();
  const roles = new Set<string>();
  let leadCount = 0;
  for (const item of value) {
    if (!isRecord(item)) throw new Error('invalid retained roster member');
    const slotId = item.slotId;
    const roleId = item.roleId;
    const roleKind = item.roleKind;
    const displayName = item.displayName;
    const laneId = item.laneId;
    if (
      typeof slotId !== 'string' ||
      !MATH_RESUME_ID_PATTERN.test(slotId.trim()) ||
      typeof roleId !== 'string' ||
      !MATH_RESUME_ID_PATTERN.test(roleId.trim()) ||
      (roleKind !== 'lead' && roleKind !== 'worker') ||
      (displayName !== undefined &&
        (typeof displayName !== 'string' || !displayName.trim() || displayName.length > 256)) ||
      (laneId !== undefined && (typeof laneId !== 'string' || !MATH_RESUME_ID_PATTERN.test(laneId.trim()))) ||
      (roleKind === 'lead' && laneId !== undefined)
    ) {
      throw new Error('invalid retained roster member');
    }
    const normalizedSlot = slotId.trim();
    const normalizedRole = roleId.trim();
    if (slots.has(normalizedSlot) || roles.has(normalizedRole)) throw new Error('duplicate retained roster identity');
    slots.add(normalizedSlot);
    roles.add(normalizedRole);
    if (roleKind === 'lead') leadCount += 1;
  }
  if (leadCount !== 1) throw new Error('retained roster must contain exactly one lead');
  return value as readonly ResearchTeamRuntimeRosterMember[];
}

function validateMathProofResumeConversations(
  roster: readonly ResearchTeamRuntimeRosterMember[],
  conversations: unknown
): void {
  if (!isRecord(conversations)) throw new Error('invalid retained conversations');
  const rosterSlots = new Set(roster.map((member) => member.slotId));
  const conversationSlots = Object.keys(conversations);
  if (conversationSlots.length !== rosterSlots.size || conversationSlots.some((slotId) => !rosterSlots.has(slotId)))
    throw new Error('retained conversations do not match roster');
  for (const slotId of conversationSlots) {
    const conversationId = conversations[slotId];
    if (typeof conversationId !== 'string' || !MATH_RESUME_ID_PATTERN.test(conversationId.trim()))
      throw new Error('invalid retained conversation identity');
  }
  const ids = conversationSlots.map((slotId) => String(conversations[slotId]).trim());
  if (new Set(ids).size !== ids.length) throw new Error('duplicate retained conversation identity');
}

function validateMathContinuationProgressRecord(value: unknown): void {
  if (!isRecord(value)) throw new Error('invalid retained continuation progress');
  for (const [key, item] of Object.entries(value)) {
    if (!key.trim() || key.length > 256 || !isRecord(item)) throw new Error('invalid retained continuation progress');
    const allowed = new Set([
      'fingerprint',
      'attempts',
      'appliedLeadReviewAttempt',
      'activityFingerprint',
      'evidenceFingerprint',
      'idempotencyKey',
      'messageFingerprint',
      'content',
      'planningContextDigest',
      'dispatchPending',
      'recoveryEpoch',
    ]);
    if (Object.keys(item).some((field) => !allowed.has(field)))
      throw new Error('invalid retained continuation progress');
    if (typeof item.fingerprint !== 'string' || !MATH_RESUME_DIGEST_PATTERN.test(item.fingerprint))
      throw new Error('invalid retained continuation fingerprint');
    if (!Number.isSafeInteger(item.attempts) || Number(item.attempts) < 0)
      throw new Error('invalid retained continuation attempts');
    for (const field of ['appliedLeadReviewAttempt'] as const) {
      if (item[field] !== undefined && (!Number.isSafeInteger(item[field]) || Number(item[field]) < 0))
        throw new Error('invalid retained continuation review attempt');
    }
    for (const field of ['activityFingerprint', 'evidenceFingerprint', 'planningContextDigest'] as const) {
      if (
        item[field] !== undefined &&
        (typeof item[field] !== 'string' || !MATH_RESUME_DIGEST_PATTERN.test(item[field]))
      )
        throw new Error('invalid retained continuation digest');
    }
    const transportFields = [
      'idempotencyKey',
      'messageFingerprint',
      'content',
      'dispatchPending',
      'recoveryEpoch',
    ] as const;
    const hasTransportState = transportFields.some((field) => item[field] !== undefined);
    if (hasTransportState) {
      if (
        typeof item.idempotencyKey !== 'string' ||
        !MATH_RESUME_ID_PATTERN.test(item.idempotencyKey) ||
        typeof item.messageFingerprint !== 'string' ||
        !MATH_RESUME_DIGEST_PATTERN.test(item.messageFingerprint) ||
        typeof item.dispatchPending !== 'boolean' ||
        typeof item.recoveryEpoch !== 'string' ||
        !item.recoveryEpoch.trim() ||
        (item.content !== undefined &&
          (typeof item.content !== 'string' ||
            !item.content.trim() ||
            mathDigest(canonicalMathJson(item.content)) !== item.messageFingerprint))
      ) {
        throw new Error('invalid retained continuation transport state');
      }
    }
  }
}

function mathProofResourceIdentityDigest(
  input: Readonly<{
    teamId: string;
    teamRunId?: string;
    assistantIds: readonly string[];
    mcpServerIds: readonly string[];
  }>
): string {
  return mathDigest(
    canonicalMathJson({
      teamId: input.teamId,
      teamRunId: input.teamRunId ?? null,
      assistantIds: [...input.assistantIds].sort(),
      mcpServerIds: [...input.mcpServerIds].sort(),
    })
  );
}

const retainedRunSnapshot = (
  teamId: string,
  value: unknown,
  fallback?: Readonly<{ teamRunId?: string; slotId?: string }>
) => {
  // A stopped Core session can legitimately retain the Team while exposing no
  // active run. Keep the provisioning contract satisfied with a durable
  // completed snapshot so the event waiter can reconcile and continue work.
  if (value == null) {
    const teamRunId = fallback?.teamRunId?.trim();
    const slotId = fallback?.slotId?.trim();
    if (!teamRunId || !slotId) return undefined;
    return {
      team_run_id: teamRunId,
      team_id: teamId,
      target_slot_id: slotId,
      target_role: 'lead' as const,
      accepted_slot_id: slotId,
      accepted_role: 'lead' as const,
      status: 'completed' as const,
    };
  }
  const run = asRecord(value, 'retained run');
  return fromBackendTeamRunAck(teamId, {
    ...run,
    accepted_slot_id: run.target_slot_id,
    accepted_role: run.target_role,
  });
};

const ACTIVE_SLOT_STATES = new Set(['queued', 'starting', 'running', 'paused']);
// Operational deadlock detection only. This does not bound model tokens or
// proof time once a Worker assignment has been accepted.
const LEAD_ASSIGNMENT_WATCHDOG_MS = 180_000;
// Core normally wakes the waiter through WebSocket events. Some follow-up
// turns finish without a terminal event, so keep a durable read path alive.
// This is a polling cadence, not a proof timeout or cancellation budget.
// Recovery must react quickly to a failed ownerless transport. This is only
// a status poll; dispatches remain idempotent and are still gated below.
const MATH_RECONCILIATION_POLL_MS = 5_000;
const MATH_OWNERLESS_RECOVERY_RETRY_MS = 5_000;
// Core persists a delivery just before projecting the mailbox wake. The Lead
// turn started by that wake can therefore predate `deliveredAt` by a few
// milliseconds; leave that fresh turn alone and let it process the delivery.
const LEAD_DELIVERY_START_RACE_MS = 250;

/**
 * Keep one model across the Lead and Worker roles.  Mathematics runs may use
 * the managed DeepSeek deployment or the explicitly configured Codex Sol
 * deployment; the Core process still owns the provider selected by CODEX_HOME.
 */
export function requireWestlakeDeepseekModels(
  models: Readonly<{ model: string; leadModel: string; workerModel: string }>
): void {
  const values = [models.model, models.leadModel, models.workerModel];
  const supported = new Set(['deepseek', 'gpt-5.6-sol', 'gpt-6-sol', 'gpt-6.1-sol', 'deepseek-flash', 'glm-flash']);
  if (values.some((value) => !supported.has(value)) || new Set(values).size !== 1) {
    throw new Error('math_model_must_be_supported_and_consistent');
  }
}

/** An explicitly selected provider source must match the isolated launch snapshot. */
export function requireMathCodexProviderSnapshot(env: NodeJS.ProcessEnv = process.env): void {
  const sourceHome = env.DEEPSCIENTIST_MATH_PROVIDER_SOURCE_HOME?.trim();
  if (!sourceHome) return;
  const runHome = env.CODEX_HOME?.trim();
  if (!runHome) throw new Error('math_provider_snapshot_home_missing');
  const read = (home: string) => {
    try {
      const config = parseToml(fs.readFileSync(path.join(home, 'config.toml'), 'utf8'));
      const id = config.model_provider;
      const providers = config.model_providers;
      if (typeof id !== 'string' || !isRecord(providers) || !isRecord(providers[id])) throw new Error();
      const provider = providers[id];
      const authPath = path.join(home, 'auth.json');
      const auth: unknown = fs.existsSync(authPath) ? JSON.parse(fs.readFileSync(authPath, 'utf8')) : null;
      if (auth !== null && !isRecord(auth)) throw new Error();
      return { id, provider, auth };
    } catch {
      // Parser diagnostics can contain credentials. Expose only a fixed code.
      throw new Error('math_provider_snapshot_invalid');
    }
  };
  const source = read(sourceHome);
  const isolated = read(runHome);
  if (source.id !== isolated.id || !isDeepStrictEqual(source.provider, isolated.provider))
    throw new Error('math_provider_snapshot_config_mismatch');
  if (!isDeepStrictEqual(source.auth, isolated.auth)) throw new Error('math_provider_snapshot_auth_mismatch');
}

/** Require an implementation-owned acknowledgment before provisioning any role. */
export async function requireMathRunInputsCapability(
  request: () => Promise<unknown>,
  requiredVersion: 1 | 2 = 1
): Promise<void> {
  let value: unknown;
  try {
    value = await request();
  } catch {
    throw new Error(
      'math_core_capability_unavailable: Cannot confirm Core frozen-input enforcement. Check Core connectivity/authentication and deploy a compatible Core before starting this run.'
    );
  }
  const capability = isRecord(value) ? value.math_run_inputs : undefined;
  const versions = isRecord(capability) ? capability.supported_versions : undefined;
  if (
    !Array.isArray(versions) ||
    !versions.every((version) => Number.isSafeInteger(version) && version > 0) ||
    !versions.includes(requiredVersion)
  ) {
    throw new Error(
      `math_core_capability_unsupported: Core must explicitly support math_run_inputs version ${requiredVersion}. Deploy a compatible Core on a supported platform; echoed run_inputs metadata is not sufficient.`
    );
  }
}

/** Return true only when Core exposes no outstanding work at run or slot level. */
export function isResearchTeamRunQuiescent(value: unknown): boolean {
  if (!value || typeof value !== 'object' || Array.isArray(value)) return false;
  const record = value as JsonRecord;
  if (isRecord(record.run) && !Object.prototype.hasOwnProperty.call(record, 'active_run')) {
    return isResearchTeamRunQuiescent(record.run);
  }
  // Core keeps the most recent completed run in `active_run` for durable
  // inspection. Its presence alone does not mean there is work to cancel;
  // only a non-terminal active run blocks cleanup.
  if (record.active_run !== undefined && record.active_run !== null) {
    if (!isRecord(record.active_run)) return false;
    const activeStatus = String(record.active_run.status || '').toLowerCase();
    if (!['completed', 'cancelled', 'canceled', 'failed', 'aborted'].includes(activeStatus)) return false;
  }
  const status = String(record.status || '').toLowerCase();
  if (['accepted', 'running', 'cancelling'].includes(status)) return false;
  const positiveCounters = [
    'active_child_count',
    'pending_wake_count',
    'starting_child_count',
    'queued_intent_count',
    'queued_foreground_count',
    'queued_background_count',
    'starting_batch_count',
    'running_batch_count',
    'active_enqueue_lease_count',
  ];
  if (positiveCounters.some((key) => record[key] !== undefined && record[key] !== 0)) return false;
  if (!Object.prototype.hasOwnProperty.call(record, 'slot_work') || !Array.isArray(record.slot_work)) return false;
  const slotWork = Array.isArray(record.slot_work) ? record.slot_work : [];
  return slotWork.every((item) => {
    if (!item || typeof item !== 'object' || Array.isArray(item)) return false;
    const slot = item as JsonRecord;
    if (ACTIVE_SLOT_STATES.has(String(slot.state || ''))) return false;
    if (!['idle', 'blocked'].includes(String(slot.state))) return false;
    if (
      ['queued_foreground_count', 'queued_background_count', 'pending_wake_count', 'starting_child_count'].some(
        (key) => slot[key] !== undefined && slot[key] !== 0
      )
    ) {
      return false;
    }
    if (slot.active_turn_id !== undefined && slot.active_turn_id !== null && String(slot.active_turn_id).trim()) {
      return false;
    }
    if (slot.team_run_id !== undefined && slot.team_run_id !== null && String(slot.team_run_id).trim()) return false;
    return true;
  });
}

export type MathContinuationProgress = Readonly<{
  fingerprint: string;
  attempts: number;
  /** Latest Lead review whose revised direction was applied to this Worker cycle. */
  appliedLeadReviewAttempt?: number;
  /** Shared research activity observed when this continuation was dispatched. */
  activityFingerprint?: string;
  /** Durable evidence observed when this continuation was dispatched. */
  evidenceFingerprint?: string;
  /** The transport key remains reusable until Core returns a definitive acknowledgment. */
  idempotencyKey?: string;
  messageFingerprint?: string;
  content?: string;
  planningContextDigest?: string;
  dispatchPending?: boolean;
  recoveryEpoch?: string;
}>;

const MATH_CONTINUATION_CONTEXT =
  'Continue from the current authorized source, the latest real Lean diagnostics and durable delivery evidence. RESEARCH.md is optional working memory and never establishes proof progress or completion.';

export function buildMathContinuationMessage(input: string): string {
  return `${input}\n${MATH_CONTINUATION_CONTEXT}`;
}

export type MathContinuationDispatch = Readonly<{
  content: string;
  messageFingerprint: string;
  idempotencyKey: string;
}>;

export function prepareMathTransportDispatch(
  baseKey: string,
  content: string,
  recoveryEpoch: string,
  previous?: Pick<
    MathContinuationProgress,
    'idempotencyKey' | 'messageFingerprint' | 'content' | 'dispatchPending' | 'recoveryEpoch'
  >
): MathContinuationDispatch {
  const epoch = recoveryEpoch.trim();
  if (!epoch) throw new Error('math_continuation_recovery_epoch_invalid');
  const normalizedContent = previous?.dispatchPending && previous.content ? previous.content : content.trim();
  if (!normalizedContent) throw new Error('math_continuation_message_empty');
  const messageFingerprint = mathDigest(canonicalMathJson(normalizedContent));
  if (previous?.dispatchPending) {
    if (!previous.idempotencyKey || !previous.messageFingerprint) {
      throw new Error('math_continuation_pending_identity_invalid');
    }
    if (messageFingerprint !== previous.messageFingerprint) {
      throw new Error(
        previous.content ? 'math_continuation_pending_content_invalid' : 'math_continuation_pending_content_unavailable'
      );
    }
  }
  const reusable =
    previous?.dispatchPending === true &&
    typeof previous.idempotencyKey === 'string' &&
    previous.idempotencyKey.length > 0;
  const idempotencyKey = reusable
    ? previous.idempotencyKey!
    : `math-recovery-${mathDigest(
        canonicalMathJson({
          recoveryEpoch: epoch,
          baseKey,
          messageFingerprint,
          previousDispatchKey: previous?.dispatchPending === false ? (previous.idempotencyKey ?? null) : null,
        })
      )}`;
  return Object.freeze({ content: normalizedContent, messageFingerprint, idempotencyKey });
}

/** An ambiguous send is retried as the same attempt after a runner restart. */
export function projectMathContinuationPlanningState(
  state: Readonly<Record<string, MathContinuationProgress>>
): Readonly<Record<string, MathContinuationProgress>> {
  return Object.freeze(
    Object.fromEntries(
      Object.entries(state).map(([key, value]) => [
        key,
        value.dispatchPending === true ? Object.freeze({ ...value, attempts: Math.max(0, value.attempts - 1) }) : value,
      ])
    )
  );
}

export function prepareMathContinuationDispatch(
  continuation: Pick<MathPendingAssignmentContinuation, 'idempotencyKey' | 'input'>,
  recoveryEpoch: string,
  previous?: MathContinuationProgress
): MathContinuationDispatch {
  return prepareMathTransportDispatch(
    continuation.idempotencyKey,
    buildMathContinuationMessage(continuation.input),
    recoveryEpoch,
    previous
  );
}

/** Retry one ambiguous transport acknowledgment with the exact same idempotent request. */
export async function recoverMathTransportAcknowledgement<T>(
  dispatch: () => Promise<T>,
  onInterrupted?: (error: unknown) => void,
  retryDelayMs = 250
): Promise<T> {
  try {
    return await dispatch();
  } catch (error) {
    const retryable =
      error instanceof TypeError ||
      (error instanceof Error &&
        (error.name === 'AbortError' || error.name === 'TimeoutError' || /^Core 5\d\d\b/u.test(error.message)));
    if (!retryable) throw error;
    onInterrupted?.(error);
    if (retryDelayMs > 0) await new Promise<void>((resolve) => setTimeout(resolve, retryDelayMs));
    return await dispatch();
  }
}

/** Bound recovery turns when the mathematical state has not changed. */
export const MAX_MATH_STALLED_RECOVERY_CONTINUATIONS = 3;

/**
 * Report how long an assignment has been running with no new host-checked
 * evidence, without deciding anything for the Lead.
 *
 * Run 23 attempt 14 had no such signal: the assignment stayed `accepted` for the
 * whole 90-minute wall, `distinctCheckedEvidenceCount` never left zero, and the
 * Lead received only "remains unresolved" for every review. Ending a run on this
 * clock would be wrong — across 23 observed runs, zero ever produced a single
 * checked evidence item, and the longest successful-work window without a
 * retained Worker commit was 2340s, so any threshold either kills ordinary runs
 * or never fires. The observation is therefore informational.
 */
function mathStallObservation(stallSeconds?: number): string {
  if (stallSeconds === undefined || !Number.isFinite(stallSeconds) || stallSeconds <= 0) return '';
  return ` No host-checked evidence has been recorded for this assignment in about ${Math.floor(stallSeconds)}s of run time; unintegrated Worker commits and file activity are not checked evidence.`;
}
/** Production recovery has no mathematical-attempt cap; transport/cancellation still govern exit. */
export const UNBOUNDED_MATH_STALLED_RECOVERY_CONTINUATIONS = Number.POSITIVE_INFINITY;

export function readMathContinuationProgress(file: string): Record<string, MathContinuationProgress> {
  if (!fs.existsSync(file)) return {};
  let parsed: unknown;
  try {
    parsed = readMathJson(file);
  } catch {
    throw new Error('math_continuation_state_invalid');
  }
  if (!parsed || typeof parsed !== 'object' || Array.isArray(parsed)) {
    throw new Error('math_continuation_state_invalid');
  }
  const progress = (parsed as JsonRecord).progress;
  if (!progress || typeof progress !== 'object' || Array.isArray(progress)) {
    throw new Error('math_continuation_state_invalid');
  }
  const restored: Record<string, MathContinuationProgress> = {};
  for (const [key, value] of Object.entries(progress)) {
    if (
      !value ||
      typeof value !== 'object' ||
      Array.isArray(value) ||
      typeof (value as JsonRecord).fingerprint !== 'string' ||
      !Number.isSafeInteger((value as JsonRecord).attempts) ||
      Number((value as JsonRecord).attempts) < 0
    ) {
      throw new Error('math_continuation_state_invalid');
    }
    const record = value as JsonRecord;
    if (
      record.appliedLeadReviewAttempt !== undefined &&
      (!Number.isSafeInteger(record.appliedLeadReviewAttempt) || Number(record.appliedLeadReviewAttempt) < 0)
    )
      throw new Error('math_continuation_state_invalid');
    const transportFields = [
      'idempotencyKey',
      'messageFingerprint',
      'content',
      'dispatchPending',
      'recoveryEpoch',
    ] as const;
    const hasTransportState = transportFields.some((field) => record[field] !== undefined);
    if (
      hasTransportState &&
      (typeof record.idempotencyKey !== 'string' ||
        !record.idempotencyKey.trim() ||
        typeof record.messageFingerprint !== 'string' ||
        !/^[a-f0-9]{64}$/u.test(record.messageFingerprint) ||
        typeof record.dispatchPending !== 'boolean' ||
        typeof record.recoveryEpoch !== 'string' ||
        !record.recoveryEpoch.trim() ||
        (record.planningContextDigest !== undefined &&
          (typeof record.planningContextDigest !== 'string' ||
            !/^[a-f0-9]{64}$/u.test(record.planningContextDigest))) ||
        (record.content !== undefined &&
          (typeof record.content !== 'string' ||
            !record.content.trim() ||
            mathDigest(canonicalMathJson(record.content)) !== record.messageFingerprint)))
    ) {
      throw new Error('math_continuation_state_invalid');
    }
    restored[key] = {
      fingerprint: String(record.fingerprint),
      attempts: Number(record.attempts),
      ...(record.appliedLeadReviewAttempt === undefined
        ? {}
        : { appliedLeadReviewAttempt: Number(record.appliedLeadReviewAttempt) }),
      ...(hasTransportState
        ? {
            idempotencyKey: String(record.idempotencyKey),
            messageFingerprint: String(record.messageFingerprint),
            ...(record.content === undefined ? {} : { content: String(record.content) }),
            ...(record.planningContextDigest === undefined
              ? {}
              : { planningContextDigest: String(record.planningContextDigest) }),
            dispatchPending: Boolean(record.dispatchPending),
            recoveryEpoch: String(record.recoveryEpoch),
          }
        : {}),
    };
  }
  return restored;
}

function canReplayMathContinuation(
  assignments: readonly ProjectGitResearchTeamAssignmentReceipt[],
  progressKey: string
): boolean {
  if (progressKey === 'lead:original-target') return true;
  const lead = progressKey.startsWith('lead:');
  const assignmentId = lead ? progressKey.slice('lead:'.length) : progressKey;
  const assignment = assignments.find((entry) => entry.assignmentId === assignmentId);
  return Boolean(
    assignment &&
    !assignment.supersessionPending &&
    !assignment.budgetCancellation &&
    assignment.state === 'accepted' &&
    !assignment.delivery &&
    !assignment.integration
  );
}

/** Delivery retires old Worker wakes and unresolved Lead reviews even when their ACK was lost. */
export function reconcileMathContinuationProgress(
  assignments: readonly ProjectGitResearchTeamAssignmentReceipt[],
  state: Readonly<Record<string, MathContinuationProgress>>
): Record<string, MathContinuationProgress> {
  return Object.fromEntries(
    Object.entries(state).filter(
      ([key, value]) => !value.dispatchPending || canReplayMathContinuation(assignments, key)
    )
  );
}

/**
 * Progress resets retry accounting. Each unchanged Worker recovery cycle
 * requires a newly acknowledged Lead review before the next cycle. Neither
 * the review count nor mathematical exploration has a whole-problem limit.
 */
export function planMathProgressContinuation(
  assignments: readonly ProjectGitResearchTeamAssignmentReceipt[],
  state: Readonly<Record<string, MathContinuationProgress>>,
  fingerprints: Readonly<Record<string, string>>,
  leadSlotId: string,
  recoveryReason?: string,
  maxStalledRecoveryContinuations = MAX_MATH_STALLED_RECOVERY_CONTINUATIONS,
  waitingOnResearch: Readonly<Record<string, readonly string[]>> = {},
  readySlotIds?: readonly string[],
  originalProofSlotId?: string,
  stallSeconds?: number
):
  | (MathPendingAssignmentContinuation & { progressKey: string; fingerprint: string; target: 'worker' | 'lead' })
  | undefined {
  if (
    maxStalledRecoveryContinuations !== Number.POSITIVE_INFINITY &&
    (!Number.isSafeInteger(maxStalledRecoveryContinuations) || maxStalledRecoveryContinuations < 0)
  ) {
    throw new Error('math_stalled_recovery_limit_invalid');
  }
  // A send with an uncertain acknowledgment is not a fresh scheduling
  // decision. Replay its retained message before observing newer evidence.
  for (const [progressKey, pending] of Object.entries(state)) {
    if (!pending.dispatchPending || !canReplayMathContinuation(assignments, progressKey)) continue;
    const target = progressKey.startsWith('lead:') ? 'lead' : 'worker';
    const assignmentId = target === 'lead' ? progressKey.slice('lead:'.length) : progressKey;
    const assignment = assignments.find((entry) => entry.assignmentId === assignmentId);
    if (!pending.content || !pending.idempotencyKey) throw new Error('math_continuation_pending_content_unavailable');
    return {
      assignmentId: progressKey === 'lead:original-target' ? progressKey : assignmentId,
      slotId: target === 'lead' ? leadSlotId : assignment!.slotId,
      attempt: pending.attempts + 1,
      progressKey,
      fingerprint: pending.fingerprint,
      target,
      idempotencyKey: pending.idempotencyKey,
      input: pending.content,
      ...(pending.appliedLeadReviewAttempt === undefined
        ? {}
        : { appliedLeadReviewAttempt: pending.appliedLeadReviewAttempt }),
    };
  }
  const dependencies = new Set(Object.values(waitingOnResearch).flat());
  const pendingAssignments = assignments.filter(
    (assignment) =>
      assignment.state === 'accepted' &&
      !assignment.delivery &&
      !assignment.integration &&
      !assignment.supersessionPending &&
      !assignment.budgetCancellation
  );
  const needsProofOwner =
    originalProofSlotId !== undefined &&
    !pendingAssignments.some((assignment) => assignment.slotId === originalProofSlotId) &&
    (!readySlotIds || readySlotIds.includes(originalProofSlotId));
  // Resume the research being awaited before waking its proof consumer. A
  // pending transport always replays first, even if new feedback arrived.
  const ordered = [...pendingAssignments].sort(
    (a, b) =>
      Number(Boolean(state[b.assignmentId]?.dispatchPending)) -
        Number(Boolean(state[a.assignmentId]?.dispatchPending)) ||
      Number(dependencies.has(b.assignmentId)) - Number(dependencies.has(a.assignmentId)) ||
      (state[a.assignmentId]?.attempts ?? 0) - (state[b.assignmentId]?.attempts ?? 0)
  );
  for (const assignment of recoveryReason || needsProofOwner ? [] : ordered) {
    if (
      assignment.state !== 'accepted' ||
      assignment.delivery ||
      assignment.supersessionPending ||
      assignment.budgetCancellation
    )
      continue;
    if (
      !state[assignment.assignmentId]?.dispatchPending &&
      waitingOnResearch[assignment.assignmentId]?.some((id) =>
        pendingAssignments.some((pending) => pending.assignmentId === id)
      )
    )
      continue;
    if (readySlotIds && !readySlotIds.includes(assignment.slotId)) continue;
    const fingerprint = fingerprints[assignment.assignmentId];
    if (!fingerprint) throw new Error('math_continuation_progress_missing');
    const previous = state[assignment.assignmentId];
    const attempts = previous?.fingerprint === fingerprint ? previous.attempts : 0;
    const key = `lead:${assignment.assignmentId}`;
    const previousLead = state[key];
    const reviews = previousLead?.fingerprint === fingerprint ? previousLead.attempts : 0;
    const reviewedCycle = maxStalledRecoveryContinuations === Number.POSITIVE_INFINITY;
    const appliedReview = previous?.fingerprint === fingerprint ? (previous.appliedLeadReviewAttempt ?? 0) : 0;
    const cycleAttempts = reviewedCycle && reviews > appliedReview ? 0 : attempts;
    const next = planMathPendingAssignmentContinuation(
      [assignment],
      new Map([[assignment.assignmentId, cycleAttempts]])
    );
    if (next)
      return {
        ...next,
        idempotencyKey: `math-cont-${mathDigest(canonicalMathJson({ key: next.idempotencyKey, fingerprint, ...(reviewedCycle ? { review: reviews } : {}) }))}`,
        progressKey: assignment.assignmentId,
        fingerprint,
        ...(reviewedCycle ? { appliedLeadReviewAttempt: reviews } : {}),
        target: 'worker',
      };
    if (readySlotIds && !readySlotIds.includes(leadSlotId)) continue;
    const attempt = reviews + 1;
    if (attempt > maxStalledRecoveryContinuations) return undefined;
    return {
      assignmentId: assignment.assignmentId,
      slotId: leadSlotId,
      attempt,
      progressKey: key,
      fingerprint,
      target: 'lead',
      idempotencyKey: `math-review-${mathDigest(canonicalMathJson({ assignmentId: assignment.assignmentId, fingerprint, attempt }))}`,
      input: `Assignment ${assignment.assignmentId} remains unresolved.${mathStallObservation(stallSeconds)} Review its retained worktree and real compiler evidence. Autonomously revise the argument or construct missing dependencies in the same assignment. Keep useful working notes in RESEARCH.md when needed. Continue the original target; an unresolved checkpoint is not terminal. Do not duplicate active assignments or fabricate proof receipts.`,
    };
  }
  if (
    readySlotIds &&
    (!readySlotIds.includes(leadSlotId) || (!recoveryReason && !needsProofOwner && pendingAssignments.length))
  )
    return undefined;
  const key = 'lead:original-target';
  const fingerprint = mathDigest(canonicalMathJson({ fingerprints, recoveryReason: recoveryReason ?? null }));
  const previousLead = state[key];
  const attempt = previousLead?.fingerprint === fingerprint ? previousLead.attempts + 1 : 1;
  // With no runnable owner, repeated reconciliation of identical evidence is
  // not a new planning event. Retain the run; new WAL/evidence wakes it again.
  if (
    maxStalledRecoveryContinuations === Number.POSITIVE_INFINITY &&
    previousLead?.fingerprint === fingerprint &&
    previousLead.attempts >= 1
  )
    return undefined;
  if (attempt > maxStalledRecoveryContinuations) return undefined;
  return {
    assignmentId: key,
    slotId: leadSlotId,
    attempt,
    progressKey: key,
    fingerprint,
    target: 'lead',
    idempotencyKey: `math-replan-${mathDigest(canonicalMathJson({ fingerprint, attempt }))}`,
    input: `The original target has no verified completion receipt. Recovery reason: ${recoveryReason ?? 'unfinished original target'}.${latestCompletedProofPendingIntegration(assignments) !== undefined ? ' A completed original-target proof delivery is waiting for integration: integrate it before any other action. If integrate returns a non-retryable error, report that exact error instead of reviewing the proof again.' : ''} Inspect current team assignments, retained source and real proof evidence. Reconcile stale or conflicting assignments using supported lifecycle tools, preserve worktrees, and autonomously continue the proof. Create or resume useful work and keep optional working notes in RESEARCH.md. Local progress or an unresolved report is nonterminal. Finish only with a valid original-target receipt. Respect workspace isolation and do not fabricate proof evidence.`,
  };
}

/** Returns true when quiescent recovery has exhausted its no-progress budget. */
export function isMathProgressContinuationExhausted(
  assignments: readonly ProjectGitResearchTeamAssignmentReceipt[],
  state: Readonly<Record<string, MathContinuationProgress>>,
  fingerprints: Readonly<Record<string, string>>,
  recoveryReason?: string,
  maxStalledRecoveryContinuations = MAX_MATH_STALLED_RECOVERY_CONTINUATIONS
): boolean {
  if (
    maxStalledRecoveryContinuations !== Number.POSITIVE_INFINITY &&
    (!Number.isSafeInteger(maxStalledRecoveryContinuations) || maxStalledRecoveryContinuations < 0)
  ) {
    throw new Error('math_stalled_recovery_limit_invalid');
  }
  for (const assignment of recoveryReason ? [] : assignments) {
    if (
      assignment.state !== 'accepted' ||
      assignment.delivery ||
      assignment.supersessionPending ||
      assignment.budgetCancellation
    )
      continue;
    const fingerprint = fingerprints[assignment.assignmentId];
    if (!fingerprint) throw new Error('math_continuation_progress_missing');
    const workerAttempts =
      state[assignment.assignmentId]?.fingerprint === fingerprint ? state[assignment.assignmentId].attempts : 0;
    if (workerAttempts < MAX_MATH_PENDING_ASSIGNMENT_CONTINUATIONS) return false;
    const key = `lead:${assignment.assignmentId}`;
    return state[key]?.fingerprint === fingerprint && state[key].attempts >= maxStalledRecoveryContinuations;
  }
  const key = 'lead:original-target';
  const fingerprint = mathDigest(canonicalMathJson({ fingerprints, recoveryReason: recoveryReason ?? null }));
  return state[key]?.fingerprint === fingerprint && state[key].attempts >= maxStalledRecoveryContinuations;
}

export const MAX_MATH_PENDING_ASSIGNMENT_CONTINUATIONS = 2;

const MATH_CONTINUATION_CHECKPOINT_MAX_CHARS = 768;
const MATH_CONTINUATION_CHECKPOINT_ID_PATTERN = /^[A-Za-z0-9][A-Za-z0-9._:-]{0,127}$/u;
const MATH_CONTINUATION_CHECKPOINT_HASH_PATTERN = /^[a-f0-9]{64}$/u;
const MATH_CONTINUATION_CHECKPOINT_OUTCOMES = new Set(['advanced', 'stalled', 'regressed', 'infra_failed']);
const MATH_CONTINUATION_CHECKPOINT_STAGES = new Set([
  'audit',
  'diversify',
  'select',
  'formalize',
  'local_gate',
  'review',
  'official_gate',
  'replan',
  'done',
]);
const MATH_CONTINUATION_CHECKPOINT_DIRECTIVES = new Set([
  'continue_node',
  'switch_node',
  'expand_node',
  'promote_helper',
  'port_upstream',
  're_decompose',
  'retry_infrastructure',
  'solver_complete',
]);
const MATH_CONTINUATION_CHECKPOINT_PROGRESS_KINDS = new Set([
  'kernel_progress',
  'foundation_progress',
  'goal_progress',
  'route_information',
  'research_information',
  'library_discovery',
  'infra_progress',
  'none',
]);

/**
 * Keep recovery prompts focused on the live Lean state.  Durable checkpoints
 * are host-owned scheduling hints, so only bounded identities and known enum
 * values belong in the model message; arbitrary diagnostic text stays behind
 * the assignment-bound tools where it can be read in full.
 */
function formatMathContinuationCheckpoint(
  checkpoint: NonNullable<ProjectGitResearchTeamAssignmentReceipt['mathProgress']>
): string {
  const fields: Record<string, string | number> = {};
  const addEnum = (key: string, value: unknown, allowed: ReadonlySet<string>): void => {
    if (typeof value === 'string' && allowed.has(value)) fields[key] = value;
  };
  addEnum('outcome', checkpoint.outcome, MATH_CONTINUATION_CHECKPOINT_OUTCOMES);
  addEnum('stage', checkpoint.nextStage, MATH_CONTINUATION_CHECKPOINT_STAGES);
  addEnum('directive', checkpoint.directive, MATH_CONTINUATION_CHECKPOINT_DIRECTIVES);
  addEnum('progressKind', checkpoint.progressKind, MATH_CONTINUATION_CHECKPOINT_PROGRESS_KINDS);
  if (Number.isSafeInteger(checkpoint.consecutiveStalls) && checkpoint.consecutiveStalls >= 0) {
    fields.stalls = checkpoint.consecutiveStalls;
  }
  if (typeof checkpoint.failureCategory === 'string' && /^[a-z][a-z0-9_]{0,63}$/u.test(checkpoint.failureCategory)) {
    fields.failureCategory = checkpoint.failureCategory;
  }
  if (
    typeof checkpoint.activePlanNodeId === 'string' &&
    MATH_CONTINUATION_CHECKPOINT_ID_PATTERN.test(checkpoint.activePlanNodeId)
  ) {
    fields.activePlanNodeId = checkpoint.activePlanNodeId;
  }
  if (
    typeof checkpoint.proofStateFingerprint === 'string' &&
    MATH_CONTINUATION_CHECKPOINT_HASH_PATTERN.test(checkpoint.proofStateFingerprint)
  ) {
    fields.proofState = checkpoint.proofStateFingerprint;
  }
  const encoded = JSON.stringify(fields);
  return encoded.length <= MATH_CONTINUATION_CHECKPOINT_MAX_CHARS
    ? encoded
    : JSON.stringify({
        outcome: fields.outcome,
        stage: fields.stage,
        directive: fields.directive,
        progressKind: fields.progressKind,
        stalls: fields.stalls,
      });
}

export type MathPendingAssignmentContinuation = Readonly<{
  assignmentId: string;
  slotId: string;
  attempt: number;
  idempotencyKey: string;
  input: string;
  appliedLeadReviewAttempt?: number;
}>;

/** Separate editable-source activity from host-checked proof evidence in recovery. */
export function collectMathContinuationEvidence(
  assignment: ProjectGitResearchTeamAssignmentReceipt,
  workerHead?: string
) {
  const worktree = assignment.preparedGit?.worktreePath;
  const sourceHashes: Record<string, string> = {};
  let sourceObservation: 'available' | 'unavailable' = 'unavailable';
  if (worktree) {
    const listed = spawnSync('git', ['ls-files', '-z', '--cached', '--others', '--exclude-standard', '--', '*.lean'], {
      cwd: worktree,
      encoding: 'utf8',
      maxBuffer: 8 * 1024 * 1024,
    });
    if (listed.status === 0) {
      sourceObservation = 'available';
      for (const relative of [...new Set(listed.stdout.split('\0').filter(Boolean))].sort()) {
        try {
          const root = fs.realpathSync(worktree);
          const file = fs.realpathSync(path.resolve(root, relative));
          if (!file.startsWith(`${root}${path.sep}`)) {
            sourceObservation = 'unavailable';
            continue;
          }
          sourceHashes[relative] = mathDigest(fs.readFileSync(file, 'utf8'));
        } catch {
          // A concurrent editor/delete must not abort the recovery loop.
          sourceObservation = 'unavailable';
        }
      }
    }
  }
  const integration = assignment.integration;
  const checkedSources = !integration?.reverificationRequired
    ? (integration?.sourceVerificationReceipts ?? [])
        .filter((receipt) => receipt.targetCommit === integration?.mergedCommit)
        .map((receipt) => ({
          sourcePath: receipt.sourcePath,
          contentSha256: receipt.contentSha256,
          theoremName: receipt.theoremName,
          statementHash: receipt.statementHash,
        }))
        .sort((a, b) => canonicalMathJson(a).localeCompare(canonicalMathJson(b)))
    : [];
  const proofEvidence = {
    checkedSources,
    statementHash: assignment.mathProgress?.statementHash ?? null,
    proofState: assignment.mathProgress?.proofStateFingerprint ?? null,
    progress: assignment.mathProgress?.progressFingerprint ?? null,
    node: assignment.mathProgress?.activePlanNodeId ?? null,
  };
  const evidence = {
    workerHead: workerHead ?? null,
    sourceObservation,
    sourceHashes,
    checkedSources,
    // Only observeMathRun's signed original-target validation can certify completion.
    originalObligationsRemaining: null as number | null,
    mathProgress: assignment.mathProgress ?? null,
  };
  return {
    assignmentId: assignment.assignmentId,
    worktree: worktree ?? null,
    evidence,
    activityFingerprint: mathDigest(canonicalMathJson(evidence)),
    fingerprint: mathDigest(canonicalMathJson(proofEvidence)),
  };
}

/** Observe authorized research without confusing unread notifications with proof readiness. */
export async function collectMathRecoveryContext(
  assignments: readonly ProjectGitResearchTeamAssignmentReceipt[],
  snapshots: readonly ReturnType<typeof collectMathContinuationEvidence>[],
  input: {
    projectRoot: string;
    teamId: string;
    runInputs: Parameters<typeof readMathLiteFeedback>[0]['runInputs'];
    signal: AbortSignal;
  }
) {
  const fingerprints: Record<string, string> = {};
  const waitingOnResearch: Record<string, readonly string[]> = {};
  const researchProducers: Record<string, readonly string[]> = {};
  for (const snapshot of snapshots) {
    input.signal.throwIfAborted();
    const receipt = assignments.find((item) => item.assignmentId === snapshot.assignmentId)!;
    let researchRevision: string | null = null;
    if (
      receipt.schema === 'deepscientist.research_team_assignment.v2' &&
      receipt.state === 'accepted' &&
      !receipt.delivery &&
      !receipt.integration &&
      !receipt.supersessionPending &&
      !receipt.budgetCancellation &&
      normalizeRuntimeMathAssignment(receipt.assignment).request.kind === 'formalize'
    ) {
      // The feedback reader validates lineage, grants and the current WAL.
      // No unseen report is marked read merely because the host is scheduling.
      const feedback = await readMathLiteFeedback({
        resolvedCapability: {
          projectRoot: input.projectRoot,
          teamId: input.teamId,
          slotId: receipt.slotId,
          roleKind: 'worker',
        },
        runInputs: input.runInputs,
        signal: input.signal,
        consume: false,
        automatic: true,
        onEvidenceRevision: (revision) => {
          researchRevision = revision;
        },
      });
      // Only an explicit wait validated against the frozen source, producer
      // identity and evidence baseline may suspend this proof consumer.
      researchProducers[receipt.assignmentId] = feedback.outstanding_research_assignment_ids;
      waitingOnResearch[receipt.assignmentId] = [
        ...new Set(feedback.waiting_on_research_assignment_ids ?? []),
      ].toSorted();
    }
    // Editable source activity authorizes another attempt, never acceptance.
    fingerprints[snapshot.assignmentId] = mathDigest(
      canonicalMathJson({
        proof: snapshot.fingerprint,
        activity: snapshot.activityFingerprint,
        researchRevision,
        waitingOnResearch: waitingOnResearch[snapshot.assignmentId] ?? [],
        lifecycle: {
          state: receipt.state,
          delivery: receipt.delivery ? { id: receipt.delivery.deliveryId, result: receipt.delivery.result } : null,
          integration: receipt.integration
            ? {
                mode: receipt.integration.executionMode,
                commit: receipt.integration.mergedCommit ?? null,
                reverificationRequired: receipt.integration.reverificationRequired ?? false,
                verification: receipt.integration.verification
                  ? {
                      disposition: receipt.integration.verification.disposition,
                      targetCommit: receipt.integration.verification.targetCommit,
                      itemIds: receipt.integration.verification.itemIds,
                      sourceHashes: receipt.integration.verification.sourceHashes,
                      diagnostics: receipt.integration.verification.diagnostics ?? null,
                    }
                  : null,
                solverReady: Boolean(receipt.integration.solverReadyReceipt),
              }
            : null,
          supersession: receipt.supersessionPending ? { winner: receipt.supersessionPending.winnerAssignmentId } : null,
          cancelled: receipt.budgetCancellation?.status ?? null,
        },
      })
    );
  }
  return { fingerprints, waitingOnResearch, researchProducers };
}

/** Shared reconciliation gate: only unfinished live work may schedule recovery. */
export function shouldContinueMathRunObservation(
  observation: Pick<MathRunObservation, 'state' | 'pendingAssignmentQuiescent'>,
  hasRecoverableSlot = false
): boolean {
  return (
    (observation.state === 'waiting' || observation.state === 'incomplete') &&
    (observation.state === 'incomplete' || observation.pendingAssignmentQuiescent || hasRecoverableSlot)
  );
}

export function shouldResolveMathRunObservation(
  observation: Pick<MathRunObservation, 'state' | 'quiescent' | 'assignmentCounts'> &
    Partial<Pick<MathRunObservation, 'pendingAssignmentQuiescent'>>,
  continuationScheduled = false,
  recoveryExhausted = false,
  recoveryBlocked = false
): boolean {
  if (observation.state === 'waiting' || continuationScheduled) return false;
  if (observation.state === 'incomplete') {
    if (recoveryBlocked) return false;
    // A live/pending assignment remains resumable. Once there is no pending
    // work and the selected recovery policy is exhausted, the host may close
    // this incomplete observation; this is not a proof success.
    if (
      (observation.assignmentCounts.pending > 0 &&
        !(recoveryExhausted && observation.pendingAssignmentQuiescent === true)) ||
      !recoveryExhausted
    )
      return false;
  }
  if (observation.state === 'runtime_error' || observation.state === 'solver_ready') return true;
  return (
    observation.assignmentCounts.pending === 0 ||
    observation.quiescent ||
    (recoveryExhausted && observation.pendingAssignmentQuiescent === true)
  );
}

/**
 * Runner-observable efficiency figures for comparing runs without a
 * transcript dig (run 23e needed a separate analysis to find where time went).
 * Diagnostic only; never evidence.
 */
export function summarizeMathRunEfficiency(input: {
  assignments: readonly ProjectGitResearchTeamAssignmentReceipt[];
  turnsBySlot: ReadonlyMap<string, number>;
  startedAt: number;
}) {
  const since = (value: string | undefined) => {
    const at = value ? Date.parse(value) : Number.NaN;
    return Number.isFinite(at) ? Math.max(0, at - input.startedAt) : null;
  };
  const kinds = { formalize: 0, research: 0, other: 0 };
  const deliveries = { completed: 0, blocked: 0, other: 0 };
  let integrated = 0;
  let firstDeliveryMs: number | null = null;
  let firstResearchDeliveryMs: number | null = null;
  let firstFormalizeDeliveryMs: number | null = null;
  let firstCompletedProofMs: number | null = null;
  for (const item of input.assignments) {
    let kind: 'formalize' | 'research' | 'other' = 'other';
    try {
      const requested = normalizeRuntimeMathAssignment(item.assignment).request.kind;
      kind = requested === 'formalize' || requested === 'research' ? requested : 'other';
    } catch {
      kind = 'other';
    }
    kinds[kind] += 1;
    if (item.integration) integrated += 1;
    if (!item.delivery) continue;
    const status = (item.delivery.result as { delivery?: { status?: unknown } } | undefined)?.delivery?.status;
    deliveries[status === 'completed' ? 'completed' : status === 'blocked' ? 'blocked' : 'other'] += 1;
    const at = since(item.delivery.deliveredAt);
    if (at !== null) {
      firstDeliveryMs = Math.min(firstDeliveryMs ?? at, at);
      if (kind === 'research') firstResearchDeliveryMs = Math.min(firstResearchDeliveryMs ?? at, at);
    }
    if (kind === 'formalize' && at !== null) {
      firstFormalizeDeliveryMs = Math.min(firstFormalizeDeliveryMs ?? at, at);
      if (status === 'completed') firstCompletedProofMs = Math.min(firstCompletedProofMs ?? at, at);
    }
  }
  return {
    semantics: 'runner-observed counts and times from run start; diagnostic only',
    assignments: kinds,
    deliveries,
    integrated,
    first_delivery_ms: firstDeliveryMs,
    first_research_delivery_ms: firstResearchDeliveryMs,
    first_formalize_delivery_ms: firstFormalizeDeliveryMs,
    first_completed_proof_ms: firstCompletedProofMs,
    turns_by_slot: Object.fromEntries([...input.turnsBySlot].toSorted(([a], [b]) => a.localeCompare(b))),
  };
}

/** Latest delivery time of a completed original-target proof the Lead has not integrated yet. */
export function latestCompletedProofPendingIntegration(
  assignments: readonly ProjectGitResearchTeamAssignmentReceipt[]
): number | undefined {
  let latest: number | undefined;
  for (const item of assignments) {
    if (!item.delivery || item.integration || item.state === 'superseded') continue;
    const result = item.delivery.result as { delivery?: { status?: unknown } } | undefined;
    if (result?.delivery?.status !== 'completed') continue;
    try {
      if (normalizeRuntimeMathAssignment(item.assignment).request.kind !== 'formalize') continue;
    } catch {
      continue;
    }
    const at = Date.parse(item.delivery.deliveredAt);
    if (Number.isFinite(at)) latest = Math.max(latest ?? at, at);
  }
  return latest;
}

/** Continue an accepted assignment whose Worker turn ended before delivery. */
export function planMathPendingAssignmentContinuation(
  assignments: readonly ProjectGitResearchTeamAssignmentReceipt[],
  attempts: ReadonlyMap<string, number>,
  maxAttempts = MAX_MATH_PENDING_ASSIGNMENT_CONTINUATIONS
): MathPendingAssignmentContinuation | undefined {
  if (!Number.isSafeInteger(maxAttempts) || maxAttempts < 0) {
    throw new Error('math_pending_assignment_continuation_limit_invalid');
  }
  const pending = assignments.find(
    (assignment) =>
      assignment.state === 'accepted' &&
      !assignment.delivery &&
      !assignment.supersessionPending &&
      !assignment.budgetCancellation
  );
  if (!pending) return undefined;
  const completedAttempts = attempts.get(pending.assignmentId) ?? 0;
  if (!Number.isSafeInteger(completedAttempts) || completedAttempts < 0) {
    throw new Error('math_pending_assignment_continuation_state_invalid');
  }
  if (completedAttempts >= maxAttempts) return undefined;
  const attempt = completedAttempts + 1;
  const idempotencyKey = `math-cont-${mathDigest(
    canonicalMathJson({
      teamId: pending.teamId,
      slotId: pending.slotId,
      assignmentId: pending.assignmentId,
      attempt,
    })
  )}`;
  // A continuation can run after the previous model turn was interrupted or
  // after the Lead was restarted.  Keep the durable scheduler checkpoint in
  // the message so the Worker resumes from the known semantic bottleneck
  // instead of spending its first turn rediscovering an already rejected
  // route.  Only bounded, host-derived fields are included; source text and
  // diagnostics remain available through the assignment-bound tools.
  const checkpoint = pending.mathProgress;
  const checkpointSummary = checkpoint
    ? `Durable checkpoint (host metadata; treat as recovery memory): ${formatMathContinuationCheckpoint(checkpoint)}.`
    : 'No durable semantic checkpoint is available; inspect the current source and assignment-bound Lean diagnostics before choosing a route.';
  // Runtime v2 records carry the authenticated scope; legacy assignments keep
  // their existing proof recovery. Never infer scope from a slot name or notes.
  const research =
    isRecord(pending.assignment) &&
    pending.assignment.schema === 'deepscientist.math.assignment.v2' &&
    normalizeRuntimeMathAssignment(pending.assignment).request.kind === 'research';
  const roleInstructions = research
    ? [
        'Continue only the assigned research question and its acceptance criteria, using the retained findings and authorized evidence.',
        'Keep the original proof files read-only; use only your own private draft and scoped source probe for auxiliary checks.',
        'Inspect the supplied failure evidence before repeating a search or claim. Test the exact missing inference, hypotheses or boundary case and preserve useful findings in RESEARCH.md.',
        'Use research_team share for an actionable finding, then deliver the research report when the assigned question is answered or its precise remaining gap is established. State the evidence, uncertainty and next proof obligation; the proof owner independently checks the result.',
      ]
    : [
        checkpointSummary,
        'Independently review the current proof state. A missing library API alone does not establish impossibility.',
        'Choose the next step from the current argument and Lean feedback: construct a missing dependency or revise an unsuccessful approach. Preserve compiling progress and avoid redundant helper checkpoints.',
        'If research_team already returned helper_checkpointed for the current HEAD, do not deliver that HEAD again; use the retained helper and continue the next proof dependency now.',
        'Keep ordinary helper checkpoints inside this assignment and its existing worktree. They are not terminal deliveries.',
        'Do not call research_team describe. Choose a useful next action: inspect definitions, test an uncertain premise, revise the argument, edit the proof, or check the actual candidate with lean_workspace probe using {action:"probe"}. The runtime binds the current assignment and target source; for targets in multiple files, supply proofSession.sourceFile.',
        'Deliver the complete original theorem when ready. A mathematical gap is shared, not delivered: preserve compiling work, share the precise question once per commit, then continue independent obligations or end the turn without deliver if none remain. Use blocked delivery only for an infrastructure failure that prevents useful work, with the actual diagnostic.',
      ];
  return Object.freeze({
    assignmentId: pending.assignmentId,
    slotId: pending.slotId,
    attempt,
    idempotencyKey,
    input: [
      `Continue the same pending assignment ${pending.assignmentId} in this conversation and its existing assigned worktree.`,
      'The assignment is still active because the preceding turn ended without an accepted delivery.',
      ...roleInstructions,
    ].join(' '),
  });
}

let pendingProofEnvironmentCleanup: (() => Promise<void>) | undefined;
let pendingStartupCleanup: ((removeTeam: boolean) => Promise<void>) | undefined;
let pendingEventCleanup: (() => void) | undefined;

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..', '..');
const HEADLESS_DISABLED_SKILLS = [
  'aionui-config',
  'cron',
  'officecli',
  'skill-creator',
  'deepscientist-team',
  'deepscientist-mathematics',
] as const;

const quoteShellArgument = (value: string): string => `'${value.replaceAll("'", `'"'"'`)}'`;

const stableLeanEvalBranchSegment = (value: string): string => {
  const normalized = value
    .trim()
    .toLowerCase()
    .replace(/[^a-z0-9]+/gu, '-')
    .replace(/^-+|-+$/gu, '')
    .slice(0, 36);
  if (!normalized) throw new Error('Lean-Eval assignment cannot form a stable branch segment');
  return normalized;
};

/** Build one fixed, narrow Mathlib query from the rarest qualified name in the target declaration. */
export function buildMathlibPremiseQuery(formalStatement: string, mathlibSourcePath: string): string {
  const declarationStart = formalStatement.search(/\b(?:theorem|lemma|example)\b/u);
  const declaration = declarationStart >= 0 ? formalStatement.slice(declarationStart) : formalStatement;
  const qualifiedNames = [
    ...new Set(
      [...declaration.matchAll(/\b[A-Z][A-Za-z0-9_']*(?:\.[A-Za-z][A-Za-z0-9_']*)+\b/gu)].map((match) => match[0])
    ),
  ].sort((left, right) => {
    const depth = right.split('.').length - left.split('.').length;
    return depth || right.length - left.length || left.localeCompare(right);
  });
  const targetName =
    qualifiedNames[0] ?? declaration.match(/\b(?:theorem|lemma|example)\s+([A-Za-z_][A-Za-z0-9_']*)/u)?.[1];
  if (!targetName) throw new Error('math_target_has_no_premise_name');
  const pattern = targetName.replace(/[.*+?^${}()|[\]\\]/gu, '\\$&');
  return [
    'rg',
    '--line-number',
    '--max-count',
    '40',
    '--glob',
    quoteShellArgument('*.lean'),
    '--',
    quoteShellArgument(pattern),
    quoteShellArgument(mathlibSourcePath),
  ].join(' ');
}

/** New launches have one planning behavior; legacy policy values are read only from old records. */
export function buildMathWorkerObjective(_formalStatement: string, _solverProjectRelativePath?: string): string {
  return 'Own the original theorem, not the first proof route; preserve useful checked work. In RESEARCH.md retain the mechanism, exact hypotheses, missing implication and evidence that could revive earlier work. A residual goal belongs to its chosen inference, not automatically to the original theorem. At a mathematical obstacle, trace burdens from a helper, representation or candidate family and seek a concrete alternative connection. For a missing construction, identify the object type and required relations, justify a candidate form, substitute it and refine unmet conditions. Distinguish sufficient choices from necessary conditions; a failed candidate family does not refute the target. Let actual remaining obligations shape the claim and task; exploration may discover the interface first. Test uncertain uses with explicit parameters in authorized private drafts, never added original premises. Simple local repairs need no planning ceremony. When no usable route is known, use definitions, targeted examples or a better representation. Do not always select the hardest, easiest or weakest lemma. After a failed check, compare the exact goal and diagnostic with the previous attempt; if they are unchanged, do not repeat the same search or tactic. Change one concrete premise, representation, theorem interface or research question so the next check can distinguish progress from repetition. Before a substantial retry, inspect applicable earlier evidence; reuse old work only with new facts or a targeted revision. Failure to prove is not refutation. Read a relevant worked example only when useful; align objects, operations, essential assumptions and return to the goal. Distinguish direct theorem reuse from mechanism transfer; never invent stronger structure. Query the intended transformation using local definitions, relations and namespaces through lean_workspace searchMode=premises and premiseQuery with the live goal (applyBest=false checks without adoption). Inspect full local declarations, including section assumptions and #check @ or #print as needed, then instantiate in this context. Let applicable results revise the connection and delegate only remaining gaps; preserve specified witnesses and formulas. Use lean_workspace with {"action":"probe"} for ordinary assignment-bound candidate checks; read its diagnostic, feedback and cited artifacts first. Continue the same authorized assignment until the original target is verified or an exact blocker requires handoff.';
}

/** Reject retired launch controls; old policy parsing stays in the historical input reader. */
export function resolveMathPlanningPolicyForRun(explicit: string | undefined, retained?: string): void {
  if (explicit !== undefined)
    throw new Error('--planning-policy is deprecated; remove it. New tasks use unified planning.');
  if (retained !== undefined)
    throw new Error('recovery_unavailable: legacy planning configuration requires its original fixed build entrypoint');
}

export function buildMathLiteVerificationTargets(contract: MathProblemContract) {
  const theoremNames = theoremQualifiedNamesFromSource(contract.formalStatement);
  if (!theoremNames.length) throw new Error('math_lite_verification_target_name_unavailable');
  return Object.freeze(
    theoremNames.map((theoremName) => {
      const expectedSourceDeclarationHash = hashMathFormalSourceDeclaration(contract.formalStatement, theoremName);
      if (!expectedSourceDeclarationHash) throw new Error('math_lite_verification_target_hash_unavailable');
      return Object.freeze({
        targetId: `target-${mathDigest(canonicalMathJson({ theoremName, statementHash: contract.statementHash })).slice(0, 24)}`,
        pathRelative: 'Submission.lean',
        theoremName,
        statementHash: contract.statementHash,
        leanStatementHash: contract.leanStatementHash,
        expectedSourceDeclarationHash,
        claim: 'statement' as const,
      });
    })
  );
}

export type MathStartIntent = Readonly<{ kind: 'formalize'; targetSlotId: string }>;

/** Resolve the proof owner from the authenticated runtime roster. */
export function resolveMathStartIntent(
  roster: readonly Pick<ResearchTeamRuntimeRosterMember, 'slotId' | 'roleKind' | 'laneId'>[]
): MathStartIntent {
  const target = roster.find((member) => member.roleKind === 'worker' && member.laneId === 'lean-engineering');
  if (!target) throw new Error('math_formalize_slot_unavailable');
  return Object.freeze({ kind: 'formalize', targetSlotId: target.slotId });
}

export function buildMathProofTeamLaunchContext(
  input: Readonly<{
    task: string;
    taskFile: string;
    legacyContractFile: string;
    baseCommit: string;
    solverProjectRelativePath: string;
    formalStatement: string;
    officialVerificationCommand?: string;
    mathlibSourcePath?: string;
    lakeExecutable?: string;
    environmentInstruction: string;
    runBindingRef?: string;
    assignmentId?: string;
    benchmarkMethod?: 'deepscientist_team' | 'single_worker';
    secondProofOwner?: boolean;
    /** False when the run froze no retrieval corpus, so premise search cannot answer. */
    premiseSearchAvailable?: boolean;
  }>
) {
  if (!input.task.trim()) throw new TypeError('Public task is empty');
  if (!/^[0-9a-f]{40}(?:[0-9a-f]{24})?$/u.test(input.baseCommit)) {
    throw new TypeError('Invalid base commit');
  }
  const solverProjectRelativePath = path.normalize(input.solverProjectRelativePath.trim());
  const assignmentId = input.assignmentId?.trim() || 'lean-eval-mainline-v1';
  if (!/^[A-Za-z0-9_.-]{1,128}$/u.test(assignmentId)) throw new TypeError('Invalid assignment id');
  const mathlibSourcePath = (
    input.mathlibSourcePath?.trim() || `${solverProjectRelativePath}/.lake/packages/mathlib/Mathlib`
  ).replaceAll('\\', '/');
  const lakeExecutable = input.lakeExecutable?.trim() || 'lake';
  if (!lakeExecutable) throw new TypeError('Invalid lake executable');
  const officialVerificationCommand =
    input.officialVerificationCommand?.trim() || `${lakeExecutable} env lean Submission.lean`;
  if (
    !solverProjectRelativePath ||
    solverProjectRelativePath === '.' ||
    solverProjectRelativePath === '..' ||
    solverProjectRelativePath.startsWith(`..${path.sep}`) ||
    path.isAbsolute(solverProjectRelativePath)
  ) {
    throw new TypeError('Invalid solver project path');
  }
  const profile = createHeadlessMathematicsTeamProfile(undefined, {
    mathematicsRouteDiscovery: input.benchmarkMethod === 'single_worker' ? false : true,
    benchmarkMethod: input.benchmarkMethod,
    secondProofOwner: input.secondProofOwner === true,
  });
  const workerObjective = buildMathWorkerObjective(input.formalStatement, solverProjectRelativePath);
  // Run 23 attempt 14: the second proof owner spent a turn on searchMode=premises
  // and got an unavailable-corpus reply, because this run freezes no retrieval corpus.
  const premiseSearchAvailable = input.premiseSearchAvailable !== false;
  const firstDispatch = 'dispatch exactly one Lean Engineer as the persistent owner of the complete original theorem, starting from the next concrete source obligation. In the same dispatch call, when the decisive mathematical step is uncertain, also give one Researcher a bounded investigation of that step so research runs in parallel with formalization. For a necessary helper with known inputs and a stable consumer interface, assign checked auxiliary Lean code instead of a broad report. Use a second available Researcher in this same call when another independent necessary helper has ready inputs; do not wait for the proof owner to block or finish another bound. Leave slots idle when no distinct useful task is ready';
  const secondOwnerRule =
    input.secondProofOwner === true
      ? 'This Team has a second Lean Engineer. You may give it at most one assignment on the complete original theorem through a structurally different decomposition from the primary Lean Engineer; name the differing mechanism in its task. Never give both the same route. The first host-verified integration wins and the other attempt is superseded automatically; integrate a completed proof before anything else.'
      : undefined;
  // Run 23 attempt 7 never used the second Lean Engineer: the single-owner
  // prohibitions below still applied and outweighed secondOwnerRule. With a
  // second owner they exclude only further competing proofs.
  const competingProofRule =
    input.secondProofOwner === true
      ? 'competing full proofs beyond the one second-owner assignment'
      : 'competing full proofs';
  const extraOwnerRule =
    input.secondProofOwner === true
      ? 'Do not create a proof owner beyond the two Lean Engineers or redispatch a running assignment.'
      : 'Do not create a second proof owner or redispatch a running assignment.';
  const leadContext = [
    'You are the Mathematics Lead. Dispatch the runtime-selected Worker immediately, before developing a private proof. Organize distinct useful research from the public goal and Worker evidence.',
    `To start useful work, use the injected research_team MCP tool and ${firstDispatch}. The assignment task must include the exact public target as supplied, original hypotheses, expected artifact, acceptance criteria and the first decisive check; when the formal statement is not present in the public task, say so and direct the Worker to the runtime-supplied contract instead of guessing. A "next obligation" is a starting point, never a smaller replacement theorem. Use describe when the roster or tool contract is unknown; use the actual roster slot id and an ordinary task string. After the initial dispatch, end this turn promptly so the Worker can receive a full context window; do not continue a long private mathematical search before yielding. The same applies to every later turn: take the one coordination action the new evidence requires, then yield. Deep mathematical investigation belongs to a Researcher assignment, not to a private Lead turn. Do not poll status to wait: deliveries, shares and feedback wake you, so call status only when a decision needs the current roster (run 23e spent 37 status calls waiting).`,
    selectMathematicsMethodHints(input.task),
    ...(secondOwnerRule ? [secondOwnerRule] : []),
    'On deliveries or stalled assignments, inspect real evidence and choose whether to continue, request independent research, revise the argument or integrate. Treat helper checkpoints as nonterminal.',
    `For each auxiliary dispatch, supply the actual object types, original hypotheses and required relation. A construction task derives a justified candidate form and refines unmet conditions; a route review receives the actual connection and its extra premise, then seeks a checked replacement rather than assuming that premise mandatory. For old work, supply the established result, missing relation and new evidence, asking only whether that evidence repairs the gap. Separate structural transfer from library support when useful. After a checked library call, remove discharged work and delegate only residual gaps; do not fill idle slots with duplicate or placeholder work. When a Researcher delivers and the gap it studied is still open, give it the next distinct question about that gap instead of leaving it idle. A proof owner that reported a mathematical blocker has ended its assignment but not the run: its worktree, checked lemmas and RESEARCH.md persist, so a later assignment on the same slot resumes that exact work and can start from the recorded gap instead of the original seed. Prefer such a resumption over leaving the slot idle. Use ordinary tasks, not placeholders, ${competingProofRule} or cyclic waits.`,
    'Choose helper production or independent scrutiny from the actual gap. For a stable required claim, give a Researcher its exact Lean declaration, original hypotheses, intended consumer call and authorized evidence, and request checked auxiliary code. For an uncertain conjecture, request its cheapest decisive test and a checked replacement when needed. Identify independent necessary helpers across all original targets early; do not wait for serial target completion. Do not redo proved lemmas or duplicate the full proof. The proof owner continues independent obligations and receives frozen findings at a safe tool boundary. Reports remain provisional.',
    `On a nonterminal share, use the attached feedback first and inspect the exact conjecture and frozen evidence before broad searches. Dispatch independent research only when its result can change a concrete proof decision, while the existing Lean Worker continues independent necessary work. After new evidence, choose one concrete next action or retain the state and yield. ${extraOwnerRule} If no independent obligation exists, waiting is correct.`,
    'Treat shared findings as provisional mathematical evidence. A counterexample refutes only the stated conjecture under its exact assumptions, not automatically the original theorem. Preserve compiling lemmas when revising the missing argument. Repeated identical source, diagnostics, or searches are not new progress; choose a different concrete inference or request investigation, without imposing time, token, or attempt cutoffs.',
    'When a Researcher report arrives, compare its exact assumptions with the current source. Use the host-routed share and feedback references without restating the whole report; the active proof owner can check a sufficient result before other research ends. If feedback already reaches the owner and no dispatch, correction or integration decision is needed, yield without another status call or summary message. Do not skip an unresolved challenge to that result. Only actual terminal blocked work uses a legal successor. Reports are provisional and do not complete the original target.',
    'Use ordinary RESEARCH.md notes for mathematical memory when useful. The runner handles transport recovery and independent evaluation; notes and delivery prose do not establish completion.',
    'Keep a short record in RESEARCH.md of refuted surrogate claims, their counterexamples, and the original hypothesis each surrogate omitted. Before dispatching a new abstraction, identify how it uses that missing hypothesis; renaming the same unproved implication is not a distinct route. Research completed means a report is available, not that its claims passed Lean. Keep ordinary helper/API repairs in the same proof assignment and use shares for progress; do not request a blocked delivery after each helper.',
    'Track the current mathematical gap and applicable history in ordinary prose. Give research tasks the actual target, hypotheses and intended use. Choose production, a short conditional use or structure exploration by the uncertain mechanism; do not copy schematic claim names instead of the actual mathematics. Stable interfaces allow upstream proof and explicit-parameter downstream work to overlap. When an interface changes, check an adapter before rewriting a valid consumer; cyclic assumptions establish neither claim. Do not create route approval or a structured research registry.',
  ].join('\n');
  return Object.freeze({
    profile,
    workerObjective,
    initialMessage: [
      `Public task:\n${input.task}`,
      `Frozen task file: ${input.taskFile}.${input.runBindingRef ? ` Run binding (v2): ${input.runBindingRef}.` : ''} Runtime problem receipt: ${input.legacyContractFile}. Canonical dispatch base commit: ${input.baseCommit}.`,
      `The authorized solver project is ${solverProjectRelativePath} inside the assigned worktree; all proof edits belong there and nowhere else.`,
      'Runtime-owned files are read-only: do not edit, move, copy, regenerate, or reinterpret active-problem.json, the run binding, the frozen task, or any other receipt/input file. Edit only the authorized Submission.lean in the assigned solver project; use the injected project/worktree identity as authoritative.',
      `Understand the goal and autonomously begin useful formalization. Read the live roster; the runtime supplies assignment, project, worktree, statement, verification, and source identities. If rejected, repair only target_slot_id or task.`,
    ].join('\n'),
    roleContext: (role: ResearchTeamRoleContract): string =>
      role.kind === 'lead'
        ? `${leadContext}\n\n${role.prompt}`
        : role.laneId === 'lean-engineering'
          ? [
              role.prompt,
              `Frozen public task and run instructions:\n${input.task}`,
              MATHEMATICS_WORKER_ASSIGNMENT_SCOPE,
              'The following Lean proof-owner instructions apply only when the current assignment.kind is "formalize". For "research", follow the scoped research instructions above and deliver its report.',
              'For a formalize assignment, you are the Lean Engineer. Own the complete theorem through bounded proof obligations; edit only authorized solver files in git.worktreePath and retain compiling commits.',
              workerObjective,
              'Continue from Lean feedback; never stop because a library query misses.',
              `The process starts at the assigned Git worktree root (the runtime-selected cwd). The solver project is ${solverProjectRelativePath}; enter that relative directory once. The assignment's sourceRootRelative is relative to this Lean project, not the Git root. Edit and check Submission.lean under that assigned source directory, and deliver it using files relative to the assigned source directory; the project-root Submission.lean is only the original seed. Inspect the public Challenge.lean, authorized solver sources, local diffs and installed library definitions as needed. Keep searches inside these authorized roots. Do not read README.md, reference answers, prior submissions, other runs or evaluator-private material.`,
              'Runtime-owned active-problem.json, run-binding, frozen task, receipt, and input files are read-only. Never edit, move, copy, or regenerate them; the injected project/worktree identity is authoritative. Only Submission.lean and ordinary working notes in the assigned worktree are solver-owned.',
              `Read the public goal and existing solver files before editing. The installed Mathlib source is ${mathlibSourcePath}. For ordinary candidate checkpoints, call the assignment-bound lean_workspace probe with {action:"probe"}; the runtime selects the current assignment and private target source and returns the frozen diagnostic and linked evidence. For targets in multiple files, supply proofSession.sourceFile. Use terminal lake env lean for focused experiments, environment diagnosis, or when MCP is unavailable, and do not repeat a terminal compile already represented by the same host-frozen result. The independent official verification command remains ${quoteShellArgument(officialVerificationCommand)}. Do not install packages, source environment files or replace the pinned toolchain.`,
              'Keep share and delivery summaries to the established result, the exact open gap and the next action; do not restate the proof. Keep RESEARCH.md short: the current route, the exact blocker, refuted claims with their counterexample, and names of checked lemmas. Replace stale sections instead of appending, so every restart reads a small file.',
              'Independently choose the route and next useful action. For a nontrivial argument, keep a short ordinary working account of the current route, exact missing implication, relevant failures and purpose of the next action; simple local repairs need no planning note. A decisive example, exact lookup or representation change may precede a source edit. Use the pinned Lean check for candidate status; terminal experiments are separate from host-frozen Lean diagnostics.',
              'If the checked-out candidate is already complete and has authorized provenance, verify it and deliver it unchanged through the normal host checks. Preserve any assisted-source attribution; an existing proof does not establish autonomous discovery.',
              'Search for the intended transformation using definitions, relations and namespaces. Batch independent source searches and reads for the next proof step in one terminal call, and stop once the relevant declarations are known. Read full local types and section assumptions; instantiate on original hypotheses. Confirm new library names from installed source first. When a type needs #check @ or #print, batch the queries with the next meaningful candidate checkpoint so one Mathlib import checks both; use a separate scratch compile only when the unresolved type prevents that proof step. Separate no match, missing corpus scope and unavailable corpus; preserve integrity errors. A failed call excludes that use, not every related theorem. If no result applies, inspect definitions, construct dependencies or revise the connection. A search miss is not evidence that the theorem is impossible.',
              ...(premiseSearchAvailable
                ? []
                : [
                    'This run has no frozen retrieval corpus: lean_workspace search cannot return premise candidates. Read the installed Mathlib source directly with ordinary file tools and inspect full local declarations with #check @ or #print. Do not spend turns calling searchMode=premises; an unavailable-corpus reply is not a search miss and carries no mathematical information.',
                  ]),
              'Preserve existing helpers. For independent helper verification, identify the new declarations and explain how they advance the main proof. Avoid redundant helper restatements solely to create checkpoints.',
              'Implement a coherent group of independent helpers or localized repairs supported by the current diagnostics, then check the changed candidate in one assignment-bound probe. Batch independent type queries into that check. Keep a separate decisive check when an uncertain interface would invalidate downstream work; do not blindly expand an unchecked dependent argument. A routine local repair needs no share, planning note or Lead decision.',
              'Keep ordinary helper checkpoints inside this assignment, its proof session, and its assigned worktree; retain the same Worker and continue to the next dependency.',
              'Do not call deliver for an ordinary helper checkpoint. Older helper_checkpointed responses remain resumable, but do not create a new one in this flow.',
              'The delivered original-target proof must contain no sorry, admit, added axioms, unsafe, or native_decide. While the target remains unfinished, retain and compile checked helper declarations without claiming target verification; do not restore the seed or delete helpers merely to remove an unfinished target placeholder. Commit compiling improvements.',
              'Ordinary Lean type, name and tactic errors stay in this assignment: repair the first diagnostic and continue. When a decisive unproved conjecture needs investigation, commit your compiling progress first and then use research_team action="share" once for that commit with result={summary:"exact assumptions, conjecture, evidence and missing inference",files:["Submission.lean","RESEARCH.md"]}; include only existing files. This freezes a progress snapshot without ending your assignment. Continue independent base lemmas, exact library interfaces, or a conditional bridge while the Researcher tests the conjecture. Never assume the conjecture true or include it as an axiom. A search miss alone does not justify giving up.',
              'Keep RESEARCH.md in the assigned source directory next to Submission.lean; the worktree-root copy is excluded from git and cannot be shared or delivered. After sharing a blocker, keep in RESEARCH.md the exact missing lemma and useful work that does not depend on it. Work on those independent obligations without assuming the missing lemma. Use feedback attached to the latest Lean checkpoint first. Call research_team action="read_feedback" only when findings are missing or a prior response may have been lost. Read cited proof source using action="read_artifact" with the exact artifact_ref and returned nextOffsetBytes until the relevant declarations and dependencies are complete; artifact fields on read_feedback do not read that source. Do not reread unchanged findings or poll unchanged source. If no useful independent work remains and research is outstanding, preserve the checkpoint and end this conversational turn without deliver; the assignment and worktree persist for feedback or recovery. Never cancel a slow turn to obtain feedback.',
              'Share only at a commit, at most once per commit, and only a precise unresolved inference whose answer can change the next proof action; research traffic is not progress. Numerical checks are leads, not proof. Continue independent obligations while research runs. When feedback arrives, compare its assumptions with the current source and state which mathematical change follows before checking it; retain compatible checked work.',
              'Once the complete original theorem passes the pinned Lean check, avoid cosmetic edits for non-failing style warnings. Review the exact candidate and retain its successful check; an unchanged source and environment do not need another local compile merely because git commit ran. If bytes or dependencies change, recheck before delivery. Batch final diff, placeholder inspection and commit where possible, then deliver promptly. Host integration and independent final verification must still run.',
              'Before expanding an uncertain argument, check its decisive inference against exact Lean types and hypotheses using the assignment-bound Lean checkpoint. Use sourceProbe for a concrete tactic experiment at a known committed source span. Trace an unmet premise to the original problem or the chosen connection; ask for a concrete local alternative when evidence warrants it, preserving independent work. For existence goals, a loose sufficient bound may suffice, but compare its actual obligations rather than equating weakness with ease. A successful API lookup alone is not verification of the lemma.',
              'A checked conditional lemma is reusable partial work, not a proof of the original theorem or its premise. Keep its unresolved premise explicit. With a stable interface, downstream work may overlap its proof: share a substantial independent helper obligation as soon as its exact statement, original hypotheses and consumer call are known, rather than waiting until it is the sole blocker. Continue the consumer with an explicit parameter or other independent obligations. With an uncertain interface, test only the decisive connection and feed actual obligations back before expanding. If the premise changes, check an adapter to retain the old consumer or repair only its affected use. Final adoption must supply a real proof from original assumptions. An open premise alone does not refute a route or require a new assignment. Use a concrete counterexample, incompatible hypothesis, or failed inference to revise the route; preserve checked lemmas and continue in the same proof worktree.',
              'Before any blocked delivery, edit and compile at least one real attempt at each independent lemma you recorded in RESEARCH.md; a blocked delivery whose source is still the unchanged seed is premature. A failed tool call is not a mathematical blocker. If no useful independent work remains and no research response is outstanding, commit your progress, use research_team action="share" once for that commit with the precise question and missing step, then end this conversational turn without deliver: the Lead is woken, the assignment and worktree persist, and the runtime continues this same assignment. deliver ends the assignment and its context (run 23 attempts 10 and 12 lost their proof state this way), so use result={status:"blocked",...} only when Lean or a required execution service cannot run or authorized files cannot be written, with the actual tool diagnostic. A provisional shared finding does not certify the original target; validate it against the exact hypotheses and current source before using it.',
              'Check mathematical domains before committing a proof step: a PositiveReal (or any subtype with a strict positivity field) cannot be instantiated with 0, and an impossible local hypothesis such as 0 < 0 is a proof-construction error, not a useful contradiction. Read the exact live goal and theorem types, then repair the first Lean diagnostic with a valid witness or a different route. Do not repeat an unchanged API probe after it has already returned the same declarations; edit the proof or state the concrete blocker.',
              'When the complete original theorem is ready, use research_team with action="deliver" and result={status:"completed",files:["Submission.lean"],summary:"brief verified result"}. Delivery fields belong inside result, not at the top level. A mathematical gap is shared, not delivered; never present partial evidence as completion.',
              'Before a substantial retry, inspect the supplied relevant failure evidence. Separate an implementation error, missing premise, exact counterexample, failed connection, and unresolved attempt. Failure to prove is not a refutation. For a revised claim, check whether an earlier counterexample still satisfies its assumptions and whether added premises follow from the original theorem. Choose one useful next action and state how its result affects the current argument. Runtime or authentication failures require runtime handling, not a new conjecture.',
            ].join('\n')
          : [
              role.prompt,
              `Frozen public task and run instructions:\n${input.task}`,
              MATHEMATICS_WORKER_ASSIGNMENT_SCOPE,
              'The following research specialization applies when the current assignment.kind is "research".',
              'For a mathematical handoff, distinguish local files from immutable evidence. Read supplied math-artifact:// references through research_team read_artifact, copying the exact reference from assignment inputs; never pass a filename or invent an artifact reference. Read authorized local public task files using ordinary file tools inside your assigned worktree. If no artifact inputs were supplied, begin with the frozen public task and authorized local files. Keep the original proof files read-only; check auxiliary declarations only in your own private draft with the scoped source probe. Return a concise ordinary-text summary of the exact question, supporting evidence, remaining unknowns and next proof obligation; no proof receipt is needed for a research report.',
              'Read the current question and supplied failure evidence. For construction, state the object type and target relations, justify a candidate form and substitute it; use residual conditions to refine it and distinguish sufficient choices from necessity. A candidate-family failure does not refute the target. For a route-added premise, trace its introduction and return a checked local connection, revised claim or exact obstruction; criticism alone is no replacement. Read a relevant worked example on demand. Align source objects, operations, assumptions and return to the goal; distinguish applicable theorem reuse from mechanism transfer. For stronger source structure, seek a general local version or rebuild only a justified step; never invent an instance. Query the intended transformation only in authorized local library files with available tools, or request frozen findings via Lead. Inspect full types (#check @ or #print as needed), then try the actual call in private sourceProbe and return its conditions, residual goals or mismatch. Do not duplicate a peer lookup or reprove available support. Use research_team action="share" early, without files when unnecessary. Keep RESEARCH.md; respect cancellation and identity failures and deliver normally.',
              'Follow the assigned purpose. For helper production, prove the exact required declaration in your private auxiliary source and check its intended consumer call; do not replace production with a survey or broad finite audit. For scrutiny, test the exact conjecture with a decisive counterexample or boundary case, then supply a checked correction when needed. Share a sufficient checked helper and its frozen source immediately, before polishing RESEARCH.md, running additional illustrative tests or writing the final report. Include dependencies and the intended call; the owner independently checks adoption.',
              "Before starting, list the declarations already proved in the proof owner's latest shared snapshot and do not re-prove or restate them; work only on the exact missing step you were given. Report a lemma the proof owner can call, with its exact statement, rather than a survey.",
              'Distinguish producing a claim from consuming it. A producer tests its decisive mechanism; a consumer uses the exact claim as an explicit parameter in its authorized private draft with current public definitions. Read sourceProbe before/after and other diagnostics; share actual goals with variables, hypotheses and instances so the producer can revise missing premises or quantifiers. A concrete lemma shares its exact declaration and intended call with actual proof for frozen readback. Exploration may first find structure. Conditional work proves neither its premise nor original target; a successful local probe is not whole-file success. Re-share changed interfaces; check adapters before discarding valid downstream work.',
              'Explain how the finding changes the next proof action and which earlier work remains usable. For a corrected claim, check that added assumptions are available from the original theorem and that the claim still serves its purpose. Distinguish checked evidence, a proposed argument and an open gap; the Lean Worker must independently check the result.',
              'Before calling an argument complete, spell out its hardest witness construction or decreasing measure and check empty/singleton cases, zero exponents, strict inequalities, and attainment assumptions when applicable. Distinguish checked steps from conjectural bridges in ordinary prose. Preserve counterexamples and the hypothesis they show is necessary in RESEARCH.md; do not revisit a refuted abstraction without a specific stronger premise from the original statement.',
            ].join('\n'),
    skillIds: Object.freeze([] as string[]),
    disabledSkillIds: HEADLESS_DISABLED_SKILLS,
  });
}

export function resolveMathThoughtLevel(value?: string): string | undefined {
  const level = value?.trim();
  return !level || level === 'provider-default' ? undefined : level;
}

type MathExecutionModels = Pick<
  NonNullable<MathProofResumeState['executionConfig']>,
  'model' | 'leadModel' | 'workerModel' | 'leadThoughtLevel' | 'workerThoughtLevel'
>;

export function resolveMathExecutionModels(
  flags: ReadonlyMap<string, string>,
  retained?: MathExecutionModels
): MathExecutionModels {
  const model = flags.get('model')?.trim() || retained?.model || 'gpt-6.1-sol';
  const effort = (flag: string, previous?: string): string | undefined =>
    flags.has(flag) ? resolveMathThoughtLevel(flags.get(flag)) : retained ? previous : 'xhigh';
  return {
    model,
    leadModel: flags.get('lead-model')?.trim() || retained?.leadModel || model,
    workerModel: flags.get('worker-model')?.trim() || retained?.workerModel || model,
    leadThoughtLevel: effort('lead-thought-level', retained?.leadThoughtLevel),
    workerThoughtLevel: effort('worker-thought-level', retained?.workerThoughtLevel),
  };
}

function parseFlags(argv: readonly string[]): Map<string, string> {
  const flags = new Map<string, string>();
  for (let index = 0; index < argv.length; index += 1) {
    const key = argv[index];
    if (!key?.startsWith('--')) continue;
    if (
      key === '--help' ||
      key === '--startup-only' ||
      key === '--no-token-limit' ||
      key === '--route-discovery' ||
      key === '--second-proof-owner'
    ) {
      flags.set(key.slice(2), 'true');
      continue;
    }
    const value = argv[index + 1];
    if (key === '--upgrade-runtime' && (!value || value.startsWith('--'))) {
      flags.set('upgrade-runtime', 'true');
      continue;
    }
    if (!value || value.startsWith('--')) throw new Error(`${key} requires a value`);
    if (key === '--upgrade-runtime' && value !== 'true' && value !== 'false') {
      throw new Error('--upgrade-runtime expects true or false');
    }
    flags.set(key.slice(2), value);
    index += 1;
  }
  return flags;
}

function required(flags: Map<string, string>, key: string): string {
  const value = flags.get(key)?.trim();
  if (!value) throw new Error(`--${key} is required`);
  return value;
}

/** Runtime state and receipts must live below a host-owned private directory. */
function ensureMathProofPrivateParent(file: string, create = true, requirePrivate = true): void {
  if (!path.isAbsolute(file) || path.resolve(file) !== file) throw new Error('math_output_path_invalid');
  const parent = path.dirname(file);
  if (create) fs.mkdirSync(parent, { recursive: true, mode: 0o700 });
  assertMathCanonicalPath(parent);
  const stat = fs.lstatSync(parent);
  if (
    !stat.isDirectory() ||
    (requirePrivate && (stat.mode & 0o077) !== 0) ||
    (process.getuid && stat.uid !== process.getuid())
  )
    throw new Error('math_output_directory_not_private');
}

function assertMathProofPrivateArtifact(
  file: string,
  createParent = true,
  requirePrivateParent = true,
  requirePrivateArtifact = true
): void {
  ensureMathProofPrivateParent(file, createParent, requirePrivateParent);
  const stat = fs.lstatSync(file, { throwIfNoEntry: false });
  if (!stat) return;
  if (
    stat.isSymbolicLink() ||
    !stat.isFile() ||
    stat.nlink !== 1 ||
    (requirePrivateArtifact && (stat.mode & 0o077) !== 0) ||
    (process.getuid && stat.uid !== process.getuid()) ||
    fs.realpathSync(file) !== file
  )
    throw new Error('math_output_artifact_not_private');
}

export function materializePinnedLakeExecutable(source: string, runtimeRoot: string): string {
  const canonicalSource = fs.realpathSync(source);
  const sourceStat = fs.lstatSync(canonicalSource);
  if (sourceStat.isSymbolicLink() || !sourceStat.isFile()) throw new Error('math_run_binding_lake_invalid');
  fs.mkdirSync(runtimeRoot, { recursive: true, mode: 0o700 });
  const destination = path.join(runtimeRoot, 'lake');
  const toolchainRoot = path.dirname(path.dirname(canonicalSource));
  const libraryRoot = path.join(toolchainRoot, 'lib');
  const wrapper = [
    '#!/bin/sh',
    `export PATH=${quoteShellArgument(path.dirname(canonicalSource))}:/usr/bin:/bin:"${'${PATH:-}'}"`,
    `if [ -n "${'${LD_LIBRARY_PATH:-}'}" ]; then export LD_LIBRARY_PATH=${quoteShellArgument(libraryRoot)}:"$LD_LIBRARY_PATH"; else export LD_LIBRARY_PATH=${quoteShellArgument(libraryRoot)}; fi`,
    `exec ${quoteShellArgument(canonicalSource)} "$@"`,
    '',
  ].join('\n');
  const descriptor = fs.openSync(destination, 'wx', 0o500);
  try {
    fs.writeFileSync(descriptor, wrapper, 'utf8');
    fs.fchmodSync(descriptor, 0o500);
    fs.fsyncSync(descriptor);
  } finally {
    fs.closeSync(descriptor);
  }
  // The run binding requires a private, non-writable single-link executable.
  return fs.realpathSync(destination);
}

function validatePinnedLakeExecutable(file: string): string {
  const resolved = path.resolve(file);
  if (resolved !== file || !fs.existsSync(resolved)) throw new Error('recovery_unavailable: lake wrapper missing');
  const stat = fs.lstatSync(resolved);
  if (
    stat.isSymbolicLink() ||
    !stat.isFile() ||
    stat.nlink !== 1 ||
    (stat.mode & 0o111) === 0 ||
    (stat.mode & 0o222) !== 0 ||
    fs.realpathSync(resolved) !== resolved
  ) {
    throw new Error('recovery_unavailable: lake wrapper integrity');
  }
  return resolved;
}

function asRecord(value: unknown, label: string): JsonRecord {
  if (!value || typeof value !== 'object' || Array.isArray(value)) throw new Error(`${label} is not an object`);
  return value as JsonRecord;
}

function isRecord(value: unknown): value is JsonRecord {
  return Boolean(value && typeof value === 'object' && !Array.isArray(value));
}

/**
 * Project durable, host-owned proof-search state into benchmark telemetry.
 * Model messages, Markdown notes and the legacy research workflow are
 * deliberately ignored. Missing measurements remain unavailable.
 */
function readMathProofSearchObservations(
  input: Readonly<{
    workspace: string;
    teamId: string;
  }>
): readonly MathProofSearchObservation[] {
  const receipts = listProjectGitResearchTeamAssignments({
    workspace: input.workspace,
    teamId: input.teamId,
    strict: true,
  }).toSorted((left, right) => {
    const time = left.updatedAt.localeCompare(right.updatedAt);
    return time || left.assignmentId.localeCompare(right.assignmentId);
  });
  const observations: MathProofSearchObservation[] = [];
  for (const receipt of receipts) {
    const assignment = isRecord(receipt.assignment) ? receipt.assignment : undefined;
    const assignmentMath = assignment && isRecord(assignment.math) ? assignment.math : undefined;
    const progress = receipt.mathProgress;
    const routeFingerprint =
      progress?.routeFingerprint ??
      (typeof assignmentMath?.routeFingerprint === 'string' ? assignmentMath.routeFingerprint : undefined);
    const proofStateFingerprint = progress?.proofStateFingerprint;
    const compilerFromProgress = progress?.routePerformance
      ?.map((record) => record.totalLeanCalls)
      .filter((value): value is number => Number.isSafeInteger(value) && value >= 0);
    const compilerCalls =
      compilerFromProgress && compilerFromProgress.length ? Math.max(...compilerFromProgress) : undefined;
    if (routeFingerprint === undefined && proofStateFingerprint === undefined && compilerCalls === undefined) continue;
    observations.push({
      ...(routeFingerprint ? { routeFingerprint } : {}),
      ...(proofStateFingerprint ? { proofStateFingerprint } : {}),
      ...(compilerCalls !== undefined ? { compilerCalls } : {}),
    });
  }
  return observations;
}

function unwrap(value: unknown): unknown {
  const record = value && typeof value === 'object' && !Array.isArray(value) ? (value as JsonRecord) : undefined;
  if (record?.success === false) throw new Error(String(record.error || record.message || 'Core request failed'));
  return record && Object.prototype.hasOwnProperty.call(record, 'data') ? record.data : value;
}

function normalizeRunnerRunState(value: unknown): JsonRecord {
  const record = asRecord(value, 'run state');
  return isRecord(record.run) && !Object.prototype.hasOwnProperty.call(record, 'active_run')
    ? (record.run as JsonRecord)
    : record;
}

/** Read Core slot activity across current and legacy run-state wire shapes. */
function runnerSlotWork(runState: JsonRecord): readonly unknown[] {
  const activeRun = isRecord(runState.active_run) ? runState.active_run : undefined;
  const sources = [
    Array.isArray(runState.slot_work) ? runState.slot_work : undefined,
    Array.isArray(runState.slots) ? runState.slots : undefined,
    activeRun && Array.isArray(activeRun.slot_work) ? activeRun.slot_work : undefined,
  ].filter((source): source is unknown[] => Array.isArray(source));
  if (sources.length === 0) return [];

  // Core may expose a complete top-level snapshot while active_run.slot_work
  // only contains the currently targeted slot. Merge by slot_id so recovery
  // gates can observe every role and still use the freshest active snapshot.
  const merged: unknown[] = [];
  const indexBySlotId = new Map<string, number>();
  for (const source of sources) {
    for (const value of source) {
      const slotId = isRecord(value) && typeof value.slot_id === 'string' ? value.slot_id : undefined;
      if (slotId === undefined) {
        merged.push(value);
        continue;
      }
      const existingIndex = indexBySlotId.get(slotId);
      if (existingIndex === undefined) {
        indexBySlotId.set(slotId, merged.length);
        merged.push(value);
      } else {
        merged[existingIndex] = value;
      }
    }
  }
  return merged;
}

/** Independent idle slots may resume while other Workers continue. Both
 * projections must agree that this target has no writer or queued work. */
export function mathReadyContinuationSlots(runState: JsonRecord, successorSlotId?: string): readonly string[] {
  if (mathRuntimeRecoveryBlocked(runState)) return [];
  const run = isRecord(runState.active_run) ? runState.active_run : undefined;
  // A global enqueue/starting lease can still be assigning an unprojected slot.
  if (
    run &&
    ['queued_intent_count', 'starting_batch_count', 'active_enqueue_lease_count'].some(
      (key) => typeof run[key] !== 'number' || run[key] !== 0
    )
  )
    return [];
  const projections = [runState.slot_work, run?.slot_work].filter(Array.isArray) as unknown[][];
  const slots = projections.flat();
  const ids = [
    ...new Set(
      slots
        .filter(isRecord)
        .map((slot) => slot.slot_id)
        .filter((id): id is string => typeof id === 'string')
    ),
  ];
  return ids.filter((id) =>
    slots
      .filter((slot) => isRecord(slot) && slot.slot_id === id)
      .every((slot) => {
        if (!isRecord(slot)) return false;
        return (
          slot.state === 'idle' &&
          slot.queued_foreground_count === 0 &&
          (id === successorSlotId ||
            (slot.queued_background_count === 0 &&
              (slot.pending_wake_count === undefined || slot.pending_wake_count === 0))) &&
          !slot.active_turn_id &&
          !slot.team_run_id &&
          !slot.blocked_reason &&
          !slot.runtime_health
        );
      })
  );
}

/** Return the run identity represented by the freshest Core snapshot. */
function runnerActiveRunId(runState: JsonRecord): string | undefined {
  const activeRun = isRecord(runState.active_run) ? runState.active_run : undefined;
  const value = activeRun?.team_run_id ?? runState.team_run_id;
  const runId = typeof value === 'string' ? value.trim() : '';
  return runId || undefined;
}

/** A slot-level projection is authoritative for whether an assignment is queued. */
function runnerSlotHasWork(runState: JsonRecord, slotId: string): boolean {
  return runnerSlotWork(runState).some((value) => {
    if (!isRecord(value) || value.slot_id !== slotId) return false;
    const state = typeof value.state === 'string' ? value.state : '';
    return (
      ['queued', 'starting', 'running', 'paused'].includes(state) ||
      (typeof value.queued_foreground_count === 'number' && value.queued_foreground_count > 0) ||
      (typeof value.queued_background_count === 'number' && value.queued_background_count > 0) ||
      (typeof value.pending_wake_count === 'number' && value.pending_wake_count > 0) ||
      (typeof value.active_turn_id === 'string' && value.active_turn_id.trim().length > 0) ||
      (typeof value.team_run_id === 'string' && value.team_run_id.trim().length > 0)
    );
  });
}

/** A terminal or stopped snapshot cannot authorize an automatic runtime wake. */
function mathRuntimeRecoveryBlocked(runState: JsonRecord): boolean {
  const run = isRecord(runState.active_run) ? runState.active_run : runState;
  const status = String(run.status ?? '').toLowerCase();
  return (
    runState.session_generation === null ||
    ['failed', 'cancelled', 'canceled', 'cancelling', 'aborted'].includes(status) ||
    runnerSlotWork(runState).some(
      (slot) =>
        isRecord(slot) && ['runtime_failed', 'session_stopped', 'removing'].includes(String(slot.blocked_reason))
    )
  );
}

/**
 * Find durable assignments whose Worker is only blocked because its runtime
 * was never attached. A completed Core run cannot wake these slots by itself,
 * so the runner must repair the runtime before replaying the assignment.
 */
export function findRuntimeStartingMathAssignments(
  runState: unknown,
  assignments: readonly Pick<
    ProjectGitResearchTeamAssignmentReceipt,
    'state' | 'delivery' | 'slotId' | 'teamRunId' | 'supersessionPending' | 'budgetCancellation'
  >[]
): readonly string[] {
  if (!isRecord(runState) || mathRuntimeRecoveryBlocked(runState)) return [];
  const startingSlots = new Set(
    runnerSlotWork(runState)
      .filter(
        (value): value is JsonRecord =>
          isRecord(value) && value.state === 'blocked' && value.blocked_reason === 'runtime_starting'
      )
      .map((value) => String(value.slot_id || '').trim())
      .filter(Boolean)
  );
  return Object.freeze(
    [
      ...new Set(
        assignments
          .filter(
            (assignment) =>
              (assignment.state === 'prepared' || assignment.state === 'accepted') &&
              !assignment.delivery &&
              !assignment.supersessionPending &&
              !assignment.budgetCancellation &&
              !isStaleMathAssignmentSnapshot(assignment, runState) &&
              startingSlots.has(assignment.slotId)
          )
          .map((assignment) => assignment.slotId)
      ),
    ].sort()
  );
}

/** Deliveries still awaiting Lead handling; terminal receipts are historical evidence. */
export function pendingMathLeadDeliveries(
  assignments: readonly ProjectGitResearchTeamAssignmentReceipt[],
  leadSlotId: string
): readonly ProjectGitResearchTeamAssignmentReceipt[] {
  return Object.freeze(
    assignments
      .filter(
        (assignment) =>
          assignment.slotId !== leadSlotId &&
          assignment.state === 'accepted' &&
          assignment.delivery !== undefined &&
          !assignment.supersessionPending &&
          !assignment.budgetCancellation
      )
      .toSorted((left, right) => {
        const leftAt = Date.parse(left.delivery!.deliveredAt);
        const rightAt = Date.parse(right.delivery!.deliveredAt);
        return leftAt - rightAt || left.assignmentId.localeCompare(right.assignmentId);
      })
  );
}

/**
 * A WAL receipt from a previous Core run must be reviewed by the Lead when its
 * Worker has no corresponding current-run intent. Replaying it directly to a
 * Worker would violate the run identity and can duplicate an old attempt.
 */
export function isStaleMathAssignmentSnapshot(
  assignment: Pick<ProjectGitResearchTeamAssignmentReceipt, 'state' | 'delivery' | 'teamRunId' | 'slotId'>,
  runState: JsonRecord
): boolean {
  if (assignment.state !== 'accepted' || assignment.delivery) return false;
  const receiptRunId = assignment.teamRunId?.trim();
  const currentRunId = runnerActiveRunId(runState);
  return Boolean(
    receiptRunId && currentRunId && receiptRunId !== currentRunId && !runnerSlotHasWork(runState, assignment.slotId)
  );
}

export function classifyMathRuntimeError(error: unknown): string {
  if (error instanceof MathRunInputsIntegrityError) return 'math_run_inputs_integrity_failed';
  return error instanceof Error && /^[a-z_]+$/u.test(error.message) ? error.message : 'math_runtime_error';
}

/**
 * A delivery may be persisted before the Worker turn has fully unwound. Only
 * cancel that still-running turn when it started before the delivery was
 * recorded; a turn started afterwards belongs to a later assignment even if
 * the Worker slot has been reused.
 */
export function isWorkerDeliveryTurnStale(
  delivery: ProjectGitResearchTeamAssignmentReceipt['delivery'] | undefined,
  slot: unknown
): boolean {
  if (!delivery || !isRecord(slot)) return false;
  const deliveredAtMs = Date.parse(delivery.deliveredAt);
  const startedAtMs = slot.active_turn_started_at_ms;
  return (
    Number.isFinite(deliveredAtMs) &&
    typeof startedAtMs === 'number' &&
    Number.isFinite(startedAtMs) &&
    startedAtMs < deliveredAtMs
  );
}

/**
 * A Lead can remain inside a long-lived wait call after Core has queued a
 * Worker delivery for its mailbox. If the Lead turn predates that delivery,
 * cancelling it lets the normal mailbox wake start a fresh Lead turn. The
 * delivery timestamp is the authoritative boundary. Missing timestamps or a
 * slow bit alone do not establish a stale turn.
 */
export function shouldRecoverStalledLeadTurn(
  runState: JsonRecord,
  leadSlot: unknown,
  hasPendingDelivery: boolean,
  pendingDeliveryAtMs?: number
): boolean {
  if (!hasPendingDelivery || !isRecord(leadSlot) || leadSlot.state !== 'running') return false;
  if (typeof leadSlot.active_turn_id !== 'string' || !leadSlot.active_turn_id.trim()) return false;
  const startedAtMs = leadSlot.active_turn_started_at_ms;
  const hasTurnStart = typeof startedAtMs === 'number' && Number.isFinite(startedAtMs);
  const hasDeliveryTime = typeof pendingDeliveryAtMs === 'number' && Number.isFinite(pendingDeliveryAtMs);
  if (hasDeliveryTime) {
    if (!hasTurnStart || pendingDeliveryAtMs - startedAtMs <= LEAD_DELIVERY_START_RACE_MS) return false;
  } else {
    return false;
  }
  const activeRun = isRecord(runState.active_run) ? runState.active_run : runState;
  const queuedIntentCount = activeRun.queued_intent_count;
  const queuedForegroundCount = leadSlot.queued_foreground_count;
  const queuedBackgroundCount = leadSlot.queued_background_count;
  return [queuedIntentCount, queuedForegroundCount, queuedBackgroundCount].some(
    (value) => typeof value === 'number' && Number.isSafeInteger(value) && value > 0
  );
}

/** A new pending owner always protects its turn from an older delivery. */
export function shouldCancelMathDeliveredWorkerTurn(
  delivery: Parameters<typeof isWorkerDeliveryTurnStale>[0],
  slot: unknown,
  hasPendingSlotAssignment: boolean
): boolean {
  if (hasPendingSlotAssignment || !isRecord(slot) || slot.state !== 'running') return false;
  if (typeof slot.active_turn_id !== 'string' || !slot.active_turn_id.trim()) return false;
  if (typeof slot.active_turn_started_at_ms !== 'number' || !Number.isFinite(slot.active_turn_started_at_ms))
    return false;
  if (!delivery || !Number.isFinite(Date.parse(delivery.deliveredAt))) return false;
  // Only an explicitly delivered episode with no subsequent owner may end.
  return true;
}

/** Integration does not give a sealed Worker episode permission to start another turn. */
export function selectMathDeliveredWorkerTurn(
  assignments: readonly ProjectGitResearchTeamAssignmentReceipt[],
  slot: unknown,
  leadSlotId: string
): ProjectGitResearchTeamAssignmentReceipt | undefined {
  if (!isRecord(slot) || slot.slot_id === leadSlotId) return undefined;
  const slotAssignments = assignments.filter((assignment) => assignment.slotId === slot.slot_id);
  const hasPendingOwner = slotAssignments.some(
    (assignment) =>
      ['prepared', 'accepted'].includes(assignment.state) &&
      !assignment.delivery &&
      !assignment.integration &&
      !assignment.supersessionPending &&
      !assignment.budgetCancellation
  );
  if (hasPendingOwner) return undefined;
  return slotAssignments
    .filter((assignment) => shouldCancelMathDeliveredWorkerTurn(assignment.delivery, slot, false))
    .toSorted((left, right) => Date.parse(right.delivery!.deliveredAt) - Date.parse(left.delivery!.deliveredAt))[0];
}

/**
 * Decide whether a durable Worker delivery needs an explicit Lead wake.
 * Keeping this predicate separate from the polling loop makes the idle-slot
 * race auditable and prevents a wake from being emitted for a terminal run,
 * an already active Lead turn, or a delivery set already handed to Core.
 */
export function shouldQueueLeadDeliveryWake(
  input: Readonly<{
    hasPendingDelivery: boolean;
    deliveryKey: string;
    leadConversationId?: string;
    leadSlot: unknown;
    leadTurnId?: string;
    activeRunStatus: string;
    alreadyQueued: boolean;
  }>
): boolean {
  if (!input.hasPendingDelivery || !input.deliveryKey.trim()) return false;
  if (!input.leadConversationId?.trim() || input.activeRunStatus.toLowerCase() !== 'running') return false;
  if (input.alreadyQueued || input.leadTurnId?.trim()) return false;
  if (!isRecord(input.leadSlot) || input.leadSlot.state !== 'idle') return false;
  return true;
}

/**
 * Elapsed time is not evidence that a live Lead turn is stuck. A slow model
 * response can still be doing useful research, so recovery must come from a
 * terminal transport error or durable Team state rather than a clock.
 */
export function shouldRecoverUnassignedLeadTurn(
  _runState: JsonRecord,
  _leadSlot: unknown,
  _hasWorkerAssignment: boolean,
  _nowMs = Date.now(),
  _thresholdMs = 180_000
): boolean {
  return false;
}

/**
 * Core's `active_turn_slow` bit is observability metadata. It must not cancel
 * an active Strategy turn; transport failures are recovered through the
 * structured retry path and completed turns through durable assignment state.
 */
export function shouldRecoverStalledStrategyTurn(
  _runState: JsonRecord,
  _leadSlot: unknown,
  _strategySlot: unknown,
  _assignment: Pick<ProjectGitResearchTeamAssignmentReceipt, 'state' | 'delivery' | 'slotId'>
): boolean {
  return false;
}

/**
 * A Lean turn may spend a long time alternating between model, editor and
 * compiler calls without closing a goal. Only an explicitly configured
 * no-progress budget authorizes time-based cancellation; Core's slow marker
 * and missing checked evidence do not establish that a live turn is stuck.
 */
export function shouldRecoverStalledLeanTurn(
  runState: JsonRecord,
  _leadSlot: unknown,
  leanSlot: unknown,
  assignment: Pick<ProjectGitResearchTeamAssignmentReceipt, 'state' | 'delivery' | 'slotId'>,
  nowMs = Date.now(),
  thresholdMs = LEAD_ASSIGNMENT_WATCHDOG_MS,
  lastCheckedEvidenceAtMs?: number,
  enforceNoProgressBudget = false
): boolean {
  if (
    !enforceNoProgressBudget ||
    assignment.state !== 'accepted' ||
    assignment.delivery ||
    !isRecord(leanSlot) ||
    leanSlot.state !== 'running' ||
    typeof leanSlot.active_turn_id !== 'string' ||
    !leanSlot.active_turn_id.trim()
  )
    return false;
  const startedAtMs = leanSlot.active_turn_started_at_ms;
  if (
    typeof startedAtMs !== 'number' ||
    !Number.isFinite(startedAtMs) ||
    !Number.isFinite(nowMs) ||
    !Number.isFinite(thresholdMs) ||
    thresholdMs < 0 ||
    (lastCheckedEvidenceAtMs !== undefined && !Number.isFinite(lastCheckedEvidenceAtMs))
  )
    return false;
  const inactivityStartedAtMs = Math.max(
    startedAtMs,
    lastCheckedEvidenceAtMs === undefined ? startedAtMs : lastCheckedEvidenceAtMs
  );
  if (nowMs - inactivityStartedAtMs < thresholdMs) return false;
  const activeRun = isRecord(runState.active_run) ? runState.active_run : runState;
  return ['accepted', 'running'].includes(String(activeRun.status ?? '').toLowerCase());
}

function readGitHead(workspace: string): Promise<string | undefined> {
  return new Promise((resolve) => {
    const child = spawn('git', ['rev-parse', '--verify', 'HEAD'], {
      cwd: workspace,
      stdio: ['ignore', 'pipe', 'ignore'],
    });
    let stdout = '';
    let settled = false;
    const finish = (value: string | undefined): void => {
      if (settled) return;
      settled = true;
      clearTimeout(timer);
      resolve(value);
    };
    const timer = setTimeout(() => {
      child.kill('SIGTERM');
      finish(undefined);
    }, 10_000);
    child.stdout.on('data', (chunk) => {
      stdout = `${stdout}${chunk}`.slice(-256);
    });
    child.once('error', () => finish(undefined));
    child.once('close', (code) => finish(code === 0 ? stdout.trim().toLowerCase() || undefined : undefined));
  });
}

/**
 * Commits a Worker retained in its own worktree before any delivery. The
 * team workspace HEAD cannot show them, so without this a long proof turn
 * that commits helpers looks identical to an idle one. Diagnostic only.
 */
export async function readMathWorkerCommitIds(
  workspace: string,
  assignments: readonly ProjectGitResearchTeamAssignmentReceipt[]
): Promise<string[]> {
  const root = fs.realpathSync(workspace);
  const ids = new Set<string>();
  for (const assignment of assignments) {
    if (assignment.state !== 'accepted' || assignment.delivery || assignment.integration) continue;
    const git = assignment.preparedGit;
    const base = (git?.progressBaseCommit ?? git?.baseCommit)?.trim().toLowerCase();
    if (!git?.worktreePath || !base || !/^[0-9a-f]{40,64}$/u.test(base)) continue;
    let worktree: string;
    try {
      worktree = fs.realpathSync(git.worktreePath);
    } catch {
      continue;
    }
    if (path.relative(root, worktree).startsWith('..')) continue;
    const listed = await new Promise<string>((resolve) => {
      const child = spawn('git', ['rev-list', '--max-count=64', `${base}..HEAD`], {
        cwd: worktree,
        stdio: ['ignore', 'pipe', 'ignore'],
      });
      let stdout = '';
      const timer = setTimeout(() => child.kill('SIGTERM'), 10_000);
      child.stdout.on('data', (chunk) => {
        stdout = `${stdout}${chunk}`.slice(0, 64 * 65);
      });
      child.once('error', () => resolve(''));
      child.once('close', (code) => {
        clearTimeout(timer);
        resolve(code === 0 ? stdout : '');
      });
    });
    for (const id of listed.split(/\s+/u)) if (/^[0-9a-f]{40,64}$/u.test(id)) ids.add(id);
  }
  return [...ids].sort();
}

function runGit(workspace: string, args: readonly string[]): void {
  const result = spawnSync('git', args, { cwd: workspace, encoding: 'utf8' });
  if (result.status !== 0) {
    throw new Error(`git ${args.join(' ')} failed: ${(result.stderr || result.stdout || '').trim()}`);
  }
}

/**
 * The bootstrap solver view is deliberately not a Git worktree: the verifier
 * worktree must retain the benchmark and private reference material.  Give
 * the Team a small local repository containing only the public solver view so
 * artifact commits never expose the verifier checkout.
 */
export function ensureIsolatedGitWorkspace(workspace: string, projectRoot: string): void {
  const gitPath = path.join(workspace, '.git');
  if (fs.existsSync(gitPath)) {
    const marker = fs.lstatSync(gitPath);
    if (!marker.isDirectory() && !marker.isFile()) throw new Error('solver workspace has an invalid .git marker');
    const branch = spawnSync('git', ['symbolic-ref', '--quiet', 'HEAD'], { cwd: workspace, encoding: 'utf8' });
    if (branch.error || (branch.status !== 0 && branch.status !== 1))
      throw new Error('solver workspace Git branch is unavailable');
    // Integration requires an attached Lead branch. Preserve the baseline and
    // any working proof when a fresh solver checkout starts at detached HEAD.
    if (branch.status === 1) runGit(workspace, ['switch', '-c', `deepscientist/math-mainline-${randomUUID()}`]);
    return;
  }
  if (path.resolve(projectRoot) === path.resolve(workspace)) {
    throw new Error('solver workspace must contain a generated public project');
  }
  if (fs.existsSync(path.join(projectRoot, 'Solution.lean'))) {
    throw new Error('solver workspace contains forbidden Solution.lean');
  }
  runGit(workspace, ['init', '--quiet']);
  runGit(workspace, ['config', 'user.email', 'deepscientist@localhost']);
  runGit(workspace, ['config', 'user.name', 'DeepScientist']);
  runGit(workspace, ['add', '--', 'generated']);
  runGit(workspace, ['commit', '--quiet', '-m', 'Lean-Eval public solver baseline']);
}

/** Receipt identity is known at launch; semantic checks must be performed by the Team. */
export function readMathProofTeamContract(activeProblem: unknown): MathProblemContract {
  const receipt = asRecord(activeProblem, 'active problem');
  if (receipt.schema === IMO2026_BOOTSTRAP_SCHEMA) {
    verifyImo2026BootstrapReceipt(receipt as unknown as Imo2026BootstrapReceipt);
    const contract = normalizeMathProblemContract(
      asRecord(receipt.contract, 'active IMO2026 problem contract') as unknown as MathProblemContract
    );
    if (receipt.problemId !== contract.problemId) throw new Error('Active problem contract identity mismatch');
    return contract;
  }
  if (
    receipt.schema !== 'deepscientist.mathematics.lean-eval-bootstrap-receipt.v1' ||
    receipt.benchmarkCommit !== LEAN_EVAL_BENCHMARK_COMMIT
  ) {
    throw new Error('A pinned Lean-Eval bootstrap receipt is required');
  }
  const contract = normalizeMathProblemContract(
    asRecord(receipt.contract, 'active problem contract') as unknown as MathProblemContract
  );
  if (receipt.problemId !== contract.problemId) throw new Error('Active problem contract identity mismatch');
  return contract;
}

/** Reject mismatched workspaces and unusable Lean before Git or Core mutations. */
export function preflightMathProofTeamWorkspace(workspacePath: string, activeProblem: unknown, env: NodeJS.ProcessEnv) {
  readMathProofTeamContract(activeProblem);
  const receipt = activeProblem as JsonRecord;
  const receiptWorkspace = receipt.workspaceRoot;
  const receiptProjectRoot = receipt.projectRoot;
  if (
    typeof receiptWorkspace !== 'string' ||
    typeof receiptProjectRoot !== 'string' ||
    !path.isAbsolute(receiptWorkspace) ||
    !path.isAbsolute(receiptProjectRoot)
  ) {
    throw new Error('Lean-Eval receipt workspace paths must be absolute');
  }
  const workspace = fs.realpathSync(workspacePath);
  if (!fs.statSync(workspace).isDirectory() || fs.realpathSync(receiptWorkspace) !== workspace) {
    throw new Error('Lean-Eval receipt workspace does not match --workspace');
  }
  const projectRoot = fs.realpathSync(receiptProjectRoot);
  const relativeProject = path.relative(path.resolve(receiptWorkspace), path.resolve(receiptProjectRoot));
  if (
    !relativeProject ||
    relativeProject === '..' ||
    relativeProject.startsWith(`..${path.sep}`) ||
    path.isAbsolute(relativeProject) ||
    projectRoot !== path.resolve(workspace, relativeProject) ||
    !fs.statSync(projectRoot).isDirectory()
  ) {
    throw new Error('Lean-Eval receipt projectRoot must be a non-symlink project inside --workspace');
  }
  const toolchainReadiness = checkResolvedLeanToolchainReadiness({ projectRoot, env, timeoutMs: 180_000 });
  if (toolchainReadiness.status !== 'ready') {
    // Probe output can contain environment values. Keep the startup error static.
    throw new Error(
      `Lean toolchain preflight ${toolchainReadiness.status}: check lean-toolchain and the pinned lake/lean environment before starting a Team`
    );
  }
  // Version discovery does not load dependency oleans. Reject an unprepared
  // Mathlib cache before creating Git state or spending any model calls.
  let requiresMathlib = receipt.schema === IMO2026_BOOTSTRAP_SCHEMA;
  const manifest = path.join(projectRoot, 'lake-manifest.json');
  if (fs.existsSync(manifest)) {
    try {
      const value: unknown = JSON.parse(fs.readFileSync(manifest, 'utf8'));
      if (!isRecord(value) || !Array.isArray(value.packages)) throw new Error();
      requiresMathlib ||= value.packages.some((entry: unknown) => isRecord(entry) && entry.name === 'mathlib');
    } catch {
      throw new Error('math_dependency_manifest_invalid: restore the pinned lake-manifest.json before starting a Team');
    }
  }
  if (requiresMathlib) {
    // `import Mathlib` is an intentionally broad aggregate import. On the
    // network-backed runner cache it walks thousands of `.olean` files and
    // can exceed the startup budget even when the pinned cache is complete.
    // Manifest binding above already verifies package identities; these
    // representative artifacts provide a bounded, side-effect-free cache
    // check without invoking Lake or touching Git state.
    const packagesRoot = resolveMathematicsLakePackagesCache(projectRoot, env);
    const requiredArtifacts = packagesRoot
      ? [
          path.join(packagesRoot, 'mathlib', '.lake', 'build', 'lib', 'lean', 'Mathlib.olean'),
          path.join(packagesRoot, 'mathlib', '.lake', 'build', 'lib', 'lean', 'Mathlib', 'Tactic.olean'),
          path.join(packagesRoot, 'batteries', '.lake', 'build', 'lib', 'lean', 'Batteries.olean'),
        ]
      : [];
    const ready = requiredArtifacts.length > 0 && requiredArtifacts.every((file) => {
      try {
        const stat = fs.statSync(file);
        return stat.isFile() && stat.size > 0;
      } catch {
        return false;
      }
    });
    if (!ready)
      throw new Error(
        'math_dependency_preflight_unavailable: prepare the pinned toolchain and manifest-compatible compiled Mathlib cache before starting a Team'
      );
  }
  return Object.freeze({ workspace, projectRoot, toolchainReadiness });
}

async function main(): Promise<void> {
  const flags = parseFlags(process.argv.slice(2));
  if (flags.has('planning-policy'))
    throw new Error('--planning-policy is deprecated; remove it. New tasks use the unified default planning behavior.');
  if (flags.has('check-provider-only')) {
    if (!process.env.DEEPSCIENTIST_MATH_PROVIDER_SOURCE_HOME?.trim())
      throw new Error('math_provider_snapshot_source_missing');
    requireMathCodexProviderSnapshot();
    console.log('math_provider_snapshot_matches_source');
    process.exit(0);
  }
  if (flags.has('help')) {
    console.log(
      'Usage: bun scripts/mathematics/runMathProofTeam.ts --runtime-url URL --build-manifest FILE --workspace GIT_WORKTREE --task-file FILE --output FILE --receipt-file ACTIVE_PROBLEM_JSON [--evaluator-command CMD --evaluator-cgroup-root DIR] [--model MODEL] [--lead-model MODEL] [--worker-model MODEL] [--lead-thought-level LEVEL] [--worker-thought-level LEVEL] [--timeout-seconds N] [--max-run-seconds N] [--no-progress-seconds N] [--evaluator-timeout-seconds N] [--mcp-root DIR] [--startup-only] [--no-token-limit] [--check-provider-only 1] [--cleanup-team-run-file FILE]\nNew-run defaults: all roles use gpt-6.1-sol with xhigh reasoning.\nEvaluation recovery: bun scripts/mathematics/runMathProofTeam.ts --build-manifest FILE --resume-evaluation-request FILE [--mcp-root DIR]'
    );
    // Imported desktop services may open storage/MCP handles before the flag
    // is parsed. Help is terminal, so do not leave those handles alive.
    process.exit(0);
  }
  if (flags.has('resume-evaluation-request')) {
    const mcpRoot = fs.realpathSync(flags.get('mcp-root') || path.join(ROOT, 'out', 'main'));
    readMathBuildManifest(fs.realpathSync(required(flags, 'build-manifest')), ROOT, mcpRoot);
    const controller = new AbortController();
    const abort = (): void => controller.abort();
    process.once('SIGINT', abort);
    process.once('SIGTERM', abort);
    try {
      const result = await resumeMathEvaluation({
        requestFile: path.resolve(required(flags, 'resume-evaluation-request')),
        supervisor: path.join(mcpRoot, 'math-evaluator-supervisor.js'),
        flockExecutable: '/usr/bin/flock',
        signal: controller.signal,
      });
      process.stdout.write(`${JSON.stringify({ evaluation: result })}\n`);
      process.exit(result.status === 'passed' ? 0 : result.status === 'failed' ? 2 : 1);
    } finally {
      process.removeListener('SIGINT', abort);
      process.removeListener('SIGTERM', abort);
    }
  }
  const coreUrl = new URL(flags.get('runtime-url') || required(flags, 'core-url')).origin;
  if (!['127.0.0.1', '[::1]', 'localhost'].includes(new URL(coreUrl).hostname))
    throw new Error('math_core_must_be_local');
  const cleanupManifest = flags.get('cleanup-team-run-file')?.trim();
  if (cleanupManifest) {
    const cleanupManifestPath = path.resolve(cleanupManifest);
    // Cleanup manifests may be handed off from a shared sticky temporary
    // directory. Keep canonical, owner and single-link checks here; normal
    // run output still requires a private parent and owner-only artifacts.
    assertMathProofPrivateArtifact(cleanupManifestPath, false, false, false);
    await cleanupMathProofTeamRun(coreUrl, cleanupManifestPath);
    process.exit(0);
  }
  requireMathCodexProviderSnapshot();
  let runtimeEnv = resolveMathematicsRuntimeEnvironment();
  const policyValue = flags.get('research-policy') ?? runtimeEnv[MATHEMATICS_RESEARCH_POLICY_ENV];
  const researchPolicy = policyValue === undefined ? undefined : mathematicsResearchPolicy(policyValue);
  if (researchPolicy) {
    throw new Error(`interaction_profile_incompatible: ${researchPolicy.id} requires its legacy research-policy build`);
  }
  if (flags.has('route-discovery')) {
    throw new Error('interaction_profile_incompatible: --route-discovery requires its legacy research workflow build');
  }
  runtimeEnv = {
    ...runtimeEnv,
    [MATHEMATICS_INTERACTION_PROFILE_ENV]: MATHEMATICS_LITE_INTERACTION_PROFILE,
    // Frozen with the run inputs so dispatch and supersession read the same choice.
    ...(flags.has('second-proof-owner') ? { [MATHEMATICS_SECOND_PROOF_OWNER_ENV]: 'true' } : {}),
  };
  const noTokenLimit = flags.has('no-token-limit');
  const upgradeRuntime = flags.get('upgrade-runtime') === 'true';
  const benchmarkMethodFlag = flags.get('benchmark-method');
  if (benchmarkMethodFlag !== undefined && !['deepscientist_team', 'single_worker'].includes(benchmarkMethodFlag))
    throw new Error('Unsupported benchmark method');
  const budgetAccounting = noTokenLimit
    ? {
        mode: 'unlimited',
        basis: 'no_cumulative_admission_control',
        totalTokenLimit: null as number | null,
        tokenLimitEnforced: false,
        strictTokenGuarantee: false,
      }
    : undefined;
  const workspace = fs.realpathSync(required(flags, 'workspace'));
  const sourceTaskFile = fs.realpathSync(required(flags, 'task-file'));
  const output = path.resolve(required(flags, 'output'));
  ensureMathProofPrivateParent(output);
  const progressFile = `${output}.progress.ndjson`;
  const progress = createMathDiagnostics(progressFile);
  progress('startup_preflight_started');
  const retainedRunStateFile = flags.has('resume-run-state')
    ? path.resolve(required(flags, 'resume-run-state'))
    : undefined;
  if (retainedRunStateFile) assertMathProofPrivateArtifact(retainedRunStateFile);
  const resume: MathProofResumeState | undefined = flags.has('resume-run-state')
    ? readMathProofResumeState(retainedRunStateFile!)
    : undefined;
  resolveMathPlanningPolicyForRun(undefined, resume?.executionConfig?.planningPolicy);
  if (!resume && runtimeEnv[MATHEMATICS_PLANNING_POLICY_ENV] !== undefined)
    console.warn('Deprecated DEEPSCIENTIST_MATH_PLANNING_POLICY ignored for new mathematics runs.');
  const { [MATHEMATICS_PLANNING_POLICY_ENV]: _retiredPlanningSelector, ...newRunEnvironment } = runtimeEnv;
  runtimeEnv = newRunEnvironment;
  const benchmarkMethod =
    benchmarkMethodFlag ?? resume?.executionConfig?.benchmarkMethod ?? resume?.benchmarkMethod ?? 'deepscientist_team';
  if (!['deepscientist_team', 'single_worker'].includes(benchmarkMethod))
    throw new Error('Unsupported benchmark method');
  const repetition = Number(flags.get('replicate') ?? flags.get('repetition') ?? String(resume?.repetition ?? 1));
  if (!Number.isSafeInteger(repetition) || repetition < 1) throw new Error('invalid --replicate');
  const runStateFile = path.resolve(
    flags.get('run-state-file') || flags.get('resume-run-state') || `${output}.run-state.json`
  );
  assertMathProofPrivateArtifact(runStateFile);
  if (!resume && fs.existsSync(runStateFile)) throw new Error('Retained run state exists; use --resume-run-state');
  const mainlineAssignmentId = resume?.mainlineAssignmentId ?? `lean-eval-mainline-${mathDigest(output).slice(0, 16)}`;
  const cleanupManifestPath = `${output}.cleanup.json`;
  assertMathProofPrivateArtifact(cleanupManifestPath);
  if (resume && !fs.existsSync(cleanupManifestPath)) {
    throw new Error('recovery_unavailable: cleanup manifest is missing');
  }
  const receiptFile = fs.realpathSync(flags.get('receipt-file') || path.join(workspace, 'active-problem.json'));
  const mcpRoot = fs.realpathSync(flags.get('mcp-root') || path.join(ROOT, 'out', 'main'));
  const buildManifestRef = fs.realpathSync(required(flags, 'build-manifest'));
  const buildManifest = readMathBuildManifest(buildManifestRef, ROOT, mcpRoot);
  if (resume && !resume.executionConfig) throw new Error('recovery_unavailable: retained execution config is missing');
  const retainedConfig = resume?.executionConfig;
  const { model, leadModel, workerModel, leadThoughtLevel, workerThoughtLevel } = resolveMathExecutionModels(
    flags,
    retainedConfig
  );
  if (
    resume &&
    ((flags.has('model') && model !== retainedConfig!.model) ||
      (flags.has('lead-model') && leadModel !== retainedConfig!.leadModel) ||
      (flags.has('worker-model') && workerModel !== retainedConfig!.workerModel) ||
      (benchmarkMethodFlag !== undefined && benchmarkMethod !== retainedConfig!.benchmarkMethod) ||
      (flags.has('lead-thought-level') && leadThoughtLevel !== retainedConfig!.leadThoughtLevel) ||
      (flags.has('worker-thought-level') && workerThoughtLevel !== retainedConfig!.workerThoughtLevel))
  ) {
    throw new Error('recovery_unavailable: retained execution config differs');
  }
  requireWestlakeDeepseekModels({ model, leadModel, workerModel });
  const timeoutSeconds = flags.has('timeout-seconds') ? Number(flags.get('timeout-seconds')) : undefined;
  const optionalLimit = (flag: string, retained?: number): number | undefined => {
    const value = flags.has(flag) ? Number(flags.get(flag)) : retained;
    if (value !== undefined && (!Number.isSafeInteger(value) || value < 1 || value > 2_147_483))
      throw new Error(`invalid --${flag}`);
    if (resume && flags.has(flag) && value !== retained) throw new Error('recovery_unavailable: run limits differ');
    return value;
  };
  const runLimits = {
    maxRunSeconds: optionalLimit('max-run-seconds', resume?.runLimits?.maxRunSeconds),
    noProgressSeconds: optionalLimit('no-progress-seconds', resume?.runLimits?.noProgressSeconds),
  };
  const evaluatorTimeoutSeconds = Number(flags.get('evaluator-timeout-seconds') || '1800');
  const evaluatorCommand = flags.get('evaluator-command')?.trim();
  const evaluatorCgroupRoot = evaluatorCommand ? required(flags, 'evaluator-cgroup-root') : undefined;
  const evaluatorSupervisor = evaluatorCommand
    ? fs.realpathSync(path.join(mcpRoot, 'math-evaluator-supervisor.js'))
    : undefined;
  const startupOnly = flags.has('startup-only');
  if (timeoutSeconds !== undefined && (!Number.isSafeInteger(timeoutSeconds) || timeoutSeconds < 60))
    throw new Error('invalid --timeout-seconds');
  if (!Number.isSafeInteger(evaluatorTimeoutSeconds) || evaluatorTimeoutSeconds < 1)
    throw new Error('invalid --evaluator-timeout-seconds');
  if (evaluatorCgroupRoot) await preflightMathEvaluatorContainer(evaluatorCgroupRoot);
  if (fs.existsSync(output)) throw new Error(`output already exists: ${output}`);
  if (fs.existsSync(cleanupManifestPath)) {
    if (!resume) {
      throw new Error(`cleanup manifest already exists; run --cleanup-team-run-file ${cleanupManifestPath} first`);
    }
    // A runner can die after provisioning but before it writes a final receipt.
    // Recovery must keep the same Team and journal instead of treating the
    // durable cleanup manifest as an unrecoverable duplicate run.
    try {
      const retainedCleanup = asRecord(readMathJson(cleanupManifestPath), 'cleanup manifest');
      if (retainedCleanup.schema !== 'deepscientist.mathematics.proof-team-cleanup.v1')
        throw new Error('invalid cleanup manifest schema');
      if (new URL(String(retainedCleanup.core_url ?? '')).origin !== new URL(coreUrl).origin)
        throw new Error('cleanup manifest core_url differs from recovery Core');
      if (String(retainedCleanup.team_id ?? '').trim() !== resume.teamId)
        throw new Error('cleanup manifest team differs from retained run');
      const retainedCleanupTeamRunId =
        retainedCleanup.team_run_id === null || retainedCleanup.team_run_id === undefined
          ? undefined
          : stableRunnerResourceId(retainedCleanup.team_run_id, 'team_run_id');
      const retainedCleanupAssistantIds = stableRunnerResourceIds(retainedCleanup.assistant_ids, 'assistant_ids');
      const retainedCleanupMcpServerIds = stableRunnerResourceIds(retainedCleanup.mcp_server_ids, 'mcp_server_ids');
      if ((resume.teamRunId ?? undefined) !== retainedCleanupTeamRunId)
        throw new Error('cleanup manifest team run differs from retained run');
      if (
        canonicalMathJson([...resume.assistantIds].sort()) !==
          canonicalMathJson([...retainedCleanupAssistantIds].sort()) ||
        canonicalMathJson([...resume.mcpServerIds].sort()) !==
          canonicalMathJson([...retainedCleanupMcpServerIds].sort())
      )
        throw new Error('cleanup manifest resources differ from retained run');
      const retainedResourceIdentityDigest =
        retainedCleanup.resource_identity_digest === null || retainedCleanup.resource_identity_digest === undefined
          ? undefined
          : String(retainedCleanup.resource_identity_digest);
      const expectedResourceIdentityDigest = mathProofResourceIdentityDigest({
        teamId: resume.teamId,
        teamRunId: retainedCleanupTeamRunId,
        assistantIds: retainedCleanupAssistantIds,
        mcpServerIds: retainedCleanupMcpServerIds,
      });
      if (
        retainedResourceIdentityDigest !== undefined &&
        retainedResourceIdentityDigest !== expectedResourceIdentityDigest
      )
        throw new Error('cleanup manifest resource identity digest is invalid');
      if (
        resume.resourceIdentityDigest !== undefined &&
        resume.resourceIdentityDigest !== expectedResourceIdentityDigest
      )
        throw new Error('retained run resource identity digest is invalid');
    } catch (error) {
      throw new Error(
        `recovery_unavailable: cleanup manifest mismatch (${error instanceof Error ? error.message : String(error)})`
      );
    }
  }
  const gitPath = path.join(workspace, '.git');
  if (fs.existsSync(gitPath)) {
    const gitMarker = fs.lstatSync(gitPath);
    if (!gitMarker.isDirectory() && !gitMarker.isFile()) throw new Error('--workspace must be a Git worktree');
  }
  const task = new TextDecoder('utf-8', { fatal: true }).decode(fs.readFileSync(sourceTaskFile)).trim();
  if (!task) throw new Error('--task-file is empty');
  const activeProblemPath = receiptFile;
  const activeProblemValue = JSON.parse(fs.readFileSync(activeProblemPath, 'utf8')) as JsonRecord;
  const problemContract = readMathProofTeamContract(activeProblemValue);
  const evaluationMode = flags.get('evaluation-mode') ?? 'official';
  if (
    !['official', 'benchmark'].includes(evaluationMode) ||
    evaluationMode !== (activeProblemValue.evaluationMode ?? 'official')
  )
    throw new Error('Evaluation mode does not match the retained bootstrap receipt');
  const frozenTask = task;
  const buildDigest = mathDigest(fs.readFileSync(buildManifestRef));
  if (
    resume &&
    (resume.workspace !== workspace ||
      resume.buildDigest !== buildDigest ||
      resume.runInputs.task.digest !== mathDigest(frozenTask) ||
      resume.statementHash !== problemContract.statementHash ||
      resume.benchmarkMethod !== benchmarkMethod ||
      (resume.repetition ?? 1) !== repetition ||
      resume.evaluationMode !== evaluationMode ||
      resume.researchPolicy !== null)
  )
    throw new Error('recovery_unavailable: retained run identity differs');
  if (resume) {
    const retainedEnvironment = readMathRunEnvironmentProjection(resume.runInputs) as Record<string, string>;
    if (retainedEnvironment[MATHEMATICS_INTERACTION_PROFILE_ENV] !== MATHEMATICS_LITE_INTERACTION_PROFILE) {
      throw new Error('recovery_unavailable: interaction profile incompatible with math-lite-v1');
    }
  }
  const { projectRoot: receiptProjectRoot, toolchainReadiness } = preflightMathProofTeamWorkspace(
    workspace,
    activeProblemValue,
    runtimeEnv
  );
  if (!resume) ensureIsolatedGitWorkspace(workspace, receiptProjectRoot);
  const baseCommit = resume?.baseCommit ?? (await readGitHead(workspace));
  if (!baseCommit) throw new Error('workspace HEAD is unavailable for the bound math contract');
  const lakeSource =
    resolvePinnedLeanToolchainExecutable({ projectRoot: receiptProjectRoot, executable: 'lake', env: runtimeEnv }) ??
    toolchainReadiness.lakePath;
  if (!lakeSource || !toolchainReadiness.toolchain) throw new Error('math_run_binding_lean_identity_unavailable');
  const lakeExecutable = resume?.runtimeLakeExecutable
    ? validatePinnedLakeExecutable(resume.runtimeLakeExecutable)
    : materializePinnedLakeExecutable(lakeSource, `${output}.runtime/toolchain`);
  const sourceBinding = resolveMathGeneratedSourceRoot({
    projectRoot: receiptProjectRoot,
    lakeExecutable,
    environment: runtimeEnv,
  });
  const toolManifestRef = runtimeEnv.DEEPSCIENTIST_LEAN_EVAL_TOOL_MANIFEST?.trim();
  if (!toolManifestRef || !path.isAbsolute(toolManifestRef))
    throw new Error('math_run_binding_tool_manifest_unavailable');
  const toolManifest = mathBuildFile(fs.realpathSync(toolManifestRef));
  const lakeExecutableDigest = mathBuildFile(lakeExecutable).sha256;
  const buildManifestDigest = mathDigest(fs.readFileSync(buildManifestRef));
  const scienceArtifactBundle = buildManifest.bundles.find(
    (entry) => path.basename(entry.path) === 'builtin-mcp-science-artifact.js'
  );
  if (!scienceArtifactBundle) throw new Error('math_run_binding_artifact_implementation_unavailable');
  const retrievalImplementation = {
    path: scienceArtifactBundle.path,
    sha256: scienceArtifactBundle.sha256,
    bytes: scienceArtifactBundle.bytes,
  };
  const projectRelative = path.relative(workspace, receiptProjectRoot);
  const evaluatorProtectedPaths = ['lean-toolchain', 'lakefile.lean', 'lakefile.toml', 'lake-manifest.json'].map(
    (file) => path.join(projectRelative, file)
  );
  // Reported once the diagnostics stream exists below.
  let preparedProofEnvironmentStats: Readonly<Record<string, number>> | undefined;
  if (!resume) {
    const { [MATH_PROOF_ENVIRONMENT_ENV]: _previousProofEnvironment, ...newEnvironment } = runtimeEnv;
    runtimeEnv = newEnvironment;
    const packages = resolveMathematicsLakePackagesCache(receiptProjectRoot, runtimeEnv);
    if (packages) {
      const prepared = await prepareMathProofEnvironment(receiptProjectRoot, packages, {
        env: runtimeEnv,
        cacheRoot: flags.get('proof-environment-cache-dir'),
        onProgress: (phase, details) => progress('proof_environment_preparing', { phase, ...details }),
      });
      pendingProofEnvironmentCleanup = prepared.dispose;
      runtimeEnv = { ...runtimeEnv, [MATH_PROOF_ENVIRONMENT_ENV]: prepared.environmentValue };
      preparedProofEnvironmentStats = prepared.stats;
    }
  } else {
    // Retained identities must still point at their original sealed environment.
    // Never silently rebuild from a mutable cache during resume.
    const retained = readMathRunEnvironmentProjection(resume.runInputs) as Record<string, string>;
    const { [MATH_PROOF_ENVIRONMENT_ENV]: _ambientProofEnvironment, ...withoutAmbient } = runtimeEnv;
    runtimeEnv = {
      ...withoutAmbient,
      ...(retained[MATH_PROOF_ENVIRONMENT_ENV] === undefined
        ? {}
        : {
            [MATH_PROOF_ENVIRONMENT_ENV]: retained[MATH_PROOF_ENVIRONMENT_ENV],
          }),
    };
    resolveMathProofEnvironment(receiptProjectRoot, runtimeEnv);
  }
  // A retained run must keep its original evaluator policy. Older runs without
  // one can be certified separately without rewriting their frozen inputs.
  const kernelEvaluator =
    !evaluatorCommand &&
    activeProblemValue.schema === IMO2026_BOOTSTRAP_SCHEMA &&
    (!resume || Boolean(resume.evaluatorPolicyDigest));
  const evaluatorPolicyDigestValue =
    evaluatorCommand || kernelEvaluator
      ? mathEvaluatorPolicyDigest({
          command: evaluatorCommand ?? 'deepscientist:imo2026-kernel-evaluator:v1',
          timeoutMs: evaluatorCommand ? evaluatorTimeoutSeconds * 1000 : 0,
          environment: projectMathematicsRuntimeEnvironment(runtimeEnv),
          protectedPaths: evaluatorProtectedPaths,
          baseCommit,
          supervisorDigest: evaluatorCommand ? mathDigest(fs.readFileSync(evaluatorSupervisor!)) : buildManifestDigest,
        })
      : undefined;
  const evaluationRoot = resume?.evaluationRoot ?? `${output}.evaluations`;
  if (resume && resume.evaluatorPolicyDigest !== evaluatorPolicyDigestValue) {
    throw new Error('recovery_unavailable: evaluator policy differs from retained run');
  }
  if (resume && resume.evaluationRoot && path.resolve(resume.evaluationRoot) !== path.resolve(evaluationRoot)) {
    throw new Error('recovery_unavailable: evaluator root differs from retained run');
  }
  const frozen = resume
    ? {
        inputs: resume.runInputs,
        environment: {
          ...(readMathRunEnvironmentProjection(resume.runInputs) as NodeJS.ProcessEnv),
          [MATH_RUN_INPUTS_ENV]: JSON.stringify(resume.runInputs),
        },
      }
    : freezeMathRunInputs({
        parentDirectory: path.dirname(output),
        workspace,
        task: frozenTask,
        environment: runtimeEnv,
        retrievalImplementation,
        retrievalProjectRoot: receiptProjectRoot,
        createBinding: (inputs) => {
          const environment = JSON.parse(fs.readFileSync(inputs.environment.path, 'utf8')) as Record<string, string>;
          const runId = mathDigest(inputs.root);
          return normalizeMathRunBinding({
            schema: 'deepscientist.math.run-binding.v2',
            runId,
            taskFile: inputs.task.path,
            taskHash: inputs.task.digest,
            workspace,
            projectRoot: receiptProjectRoot,
            baseCommit,
            allowedWriteRoots: [receiptProjectRoot],
            environmentFile: inputs.environment.path,
            environmentDigest: mathDigest(canonicalMathJson(environment)),
            leanToolchain: toolchainReadiness.toolchain,
            lakeExecutableDigest,
            toolManifestDigest: toolManifest.sha256,
            leanSourceRoots: sourceBinding.leanSourceRoots,
            generatedSourceRoot: sourceBinding.generatedSourceRoot,
            artifactStoreRoot: path.join(`${output}.runtime`, 'runs', runId, 'artifacts'),
            artifactStorePolicyDigest: mathDigest(
              canonicalMathJson({
                schema: 'deepscientist.math.artifact-store-policy.v1',
                implementationDigest: scienceArtifactBundle.sha256,
                manifestSchema: 'deepscientist.math.artifacts.v1',
                objectIdentity: 'sha256',
                storage: 'run_scoped_copy',
              })
            ),
            buildManifestRef,
            buildManifestDigest,
            evaluatorConfigured: Boolean(evaluatorPolicyDigestValue),
            ...(evaluatorPolicyDigestValue ? { evaluatorPolicyDigest: evaluatorPolicyDigestValue } : {}),
            problem: {
              problemId: problemContract.problemId,
              statementHash: problemContract.statementHash,
              leanStatementHash: problemContract.leanStatementHash,
              formalStatement: problemContract.formalStatement,
              initialRouteFingerprint:
                typeof activeProblemValue.routeFingerprint === 'string' && activeProblemValue.routeFingerprint.trim()
                  ? activeProblemValue.routeFingerprint.trim()
                  : `${problemContract.problemId.replace(/_/gu, '-')}-mainline-direct-v1`,
              verificationTargets: buildMathLiteVerificationTargets(problemContract),
            },
          });
        },
      });
  const runBinding = readMathRunBinding(frozen.inputs);
  const frozenPlanningEnvironment = readMathRunEnvironmentProjection(frozen.inputs) as Record<string, string>;
  if (frozenPlanningEnvironment[MATHEMATICS_PLANNING_POLICY_ENV] !== undefined)
    throw new Error('recovery_unavailable: legacy planning snapshot requires its original fixed build entrypoint');
  verifyMathRunBindingArtifacts(frozen.inputs, { lakeExecutable, toolManifestRef });
  // The V2 research-team artifact registry creates the run-scoped store lazily
  // from this parent. Create the canonical parent before the first dispatch so
  // its lock acquisition cannot fail with ENOENT in a fresh experiment.
  const artifactRunRoot = path.dirname(runBinding.artifactStoreRoot);
  assertMathCanonicalPath(artifactRunRoot);
  fs.mkdirSync(artifactRunRoot, { recursive: true, mode: 0o700 });
  if ((fs.statSync(artifactRunRoot).mode & 0o777) !== 0o700) {
    throw new Error('math_artifact_run_root_permissions');
  }
  runtimeEnv = { ...runtimeEnv, ...frozen.environment };
  const runtimeBinding = readMathRunBinding(frozen.inputs);
  if (
    runtimeBinding.evaluatorConfigured !== Boolean(evaluatorPolicyDigestValue) ||
    runtimeBinding.evaluatorPolicyDigest !== evaluatorPolicyDigestValue
  ) {
    throw new Error('math_evaluator_policy_binding_mismatch');
  }
  const taskFile = frozen.inputs.task.path;

  if (preparedProofEnvironmentStats) progress('proof_environment_prepared', preparedProofEnvironmentStats);
  const timing = createMathTimingDiagnostics(progress);
  const proofClockStartedAt = resume?.proofStartedAt ?? Date.now();
  const proofProgressFile = `${output}.proof-progress.json`;
  const proofProgress = createMathProofProgressMonitor({
    runId: runBinding.runId,
    startedAt: proofClockStartedAt,
    ...(resume && fs.existsSync(proofProgressFile) ? { retained: readMathJson(proofProgressFile) } : {}),
  });
  let runLimitReason: string | undefined;
  let proofWallTimer: ReturnType<typeof setTimeout> | undefined;
  let wallGraceReported = false;
  const turnsBySlot = new Map<string, number>();
  let lastProgressDigest: string | undefined;
  let cleanupOutcome: MathCleanupOutcome = {
    status: 'retained',
    reason: 'solver_not_evaluated',
    resourcesRemoved: false,
    manifestRetained: true,
  };
  const manifestAssistantIds: string[] = [...(resume?.assistantIds ?? [])];
  const manifestMcpServerIds: string[] = [...(resume?.mcpServerIds ?? [])];
  let manifestTeamId: string | undefined = resume?.teamId;
  let manifestTeamRunId: string | undefined = resume?.teamRunId;
  let retainedRuntime: Pick<MathProofResumeState, 'roster' | 'conversations'> | undefined = resume
    ? { roster: resume.roster, conversations: resume.conversations }
    : undefined;
  let modelIsolationRun: MathModelIsolationRun | undefined = resume?.modelIsolationRun;
  let manifestCreated = Boolean(resume && fs.existsSync(cleanupManifestPath));
  let lifecycleState = 'prepared';
  const writeCleanupManifest = (): void => {
    fs.mkdirSync(path.dirname(cleanupManifestPath), { recursive: true });
    const value = {
      schema: 'deepscientist.mathematics.proof-team-cleanup.v1',
      core_url: coreUrl,
      team_id: manifestTeamId ?? null,
      team_run_id: manifestTeamRunId ?? null,
      assistant_ids: [...new Set(manifestAssistantIds)],
      mcp_server_ids: [...new Set(manifestMcpServerIds)],
      resource_identity_digest: manifestTeamId
        ? mathProofResourceIdentityDigest({
            teamId: manifestTeamId,
            teamRunId: manifestTeamRunId,
            assistantIds: [...new Set(manifestAssistantIds)],
            mcpServerIds: [...new Set(manifestMcpServerIds)],
          })
        : null,
      run_inputs: frozen.inputs,
      lifecycle_state: lifecycleState,
      budget_accounting: budgetAccounting,
      cleanup: cleanupOutcome,
      result_ref: output,
      created_at: new Date().toISOString(),
    };
    if (!manifestCreated) {
      const fd = fs.openSync(cleanupManifestPath, 'wx', 0o600);
      try {
        fs.writeFileSync(fd, canonicalMathJson(value));
        fs.fsyncSync(fd);
      } finally {
        fs.closeSync(fd);
      }
      syncMathDirectory(path.dirname(cleanupManifestPath));
      manifestCreated = true;
    } else {
      writeMathJsonDurable(cleanupManifestPath, value);
    }
    if (retainedRuntime && manifestTeamId)
      writeMathJsonDurable(runStateFile, {
        schema: 'deepscientist.math.proof-resume.v1',
        workspace,
        buildDigest,
        taskDigest: frozen.inputs.task.digest,
        statementHash: problemContract.statementHash,
        benchmarkMethod,
        repetition,
        evaluationMode,
        researchPolicy: null,
        teamId: manifestTeamId,
        teamRunId: manifestTeamRunId,
        resourceIdentityDigest: manifestTeamId
          ? mathProofResourceIdentityDigest({
              teamId: manifestTeamId,
              teamRunId: manifestTeamRunId,
              assistantIds: [...new Set(manifestAssistantIds)],
              mcpServerIds: [...new Set(manifestMcpServerIds)],
            })
          : undefined,
        runInputs: frozen.inputs,
        baseCommit,
        mainlineAssignmentId,
        proofStartedAt: proofStartedAt ?? Date.now(),
        ...retainedRuntime,
        assistantIds: [...new Set(manifestAssistantIds)],
        mcpServerIds: [...new Set(manifestMcpServerIds)],
        continuationProgress,
        evaluationRoot,
        runtimeLakeExecutable: lakeExecutable,
        ...(modelIsolationRun ? { modelIsolationRun } : {}),
        runLimits,
        executionConfig: {
          benchmarkMethod,
          model,
          leadModel,
          workerModel,
          backend: 'codex',
          ...(leadThoughtLevel ? { leadThoughtLevel } : {}),
          ...(workerThoughtLevel ? { workerThoughtLevel } : {}),
          roster: retainedRuntime.roster.map((member) => ({
            slotId: member.slotId,
            roleKind: member.roleKind,
            ...(member.laneId ? { laneId: member.laneId } : {}),
          })),
          pool: {
            agentLimit: retainedRuntime.roster.filter((member) => member.roleKind !== 'lead').length,
            reasoningConcurrency: profile.pool.reasoningConcurrency,
          },
        },
        ...(evaluatorPolicyDigestValue ? { evaluatorPolicyDigest: evaluatorPolicyDigestValue } : {}),
      });
  };
  // Establish a recovery journal before provisioning creates any external
  // resources. Every subsequent resource creation updates it atomically.
  if (!resume) writeCleanupManifest();
  const mathEnvInstruction = mathematicsRuntimeInstruction(runtimeEnv.DEEPSCIENTIST_MATH_ENV_FILE);
  const mathTransportEnv = frozen.environment;
  progress('runner_started', {
    coreUrl,
    workspace,
    receiptFile,
    taskFile,
    sourceTaskFile,
    evaluatorConfigured: Boolean(evaluatorPolicyDigestValue),
    leanToolchainReadiness: toolchainReadiness,
  });

  const request = async (pathname: string, init: RequestInit = {}, timeoutMs = 120_000): Promise<unknown> => {
    const method = init.method || 'GET';
    const transportRetry = method === 'GET';
    let lastError: unknown;
    for (let attempt = 0; attempt < (transportRetry ? 3 : 1); attempt += 1) {
      try {
        const { response, body } = await timing.measure('transport', async () => {
          const response = await fetch(`${coreUrl}${pathname}`, {
            ...init,
            headers: { 'content-type': 'application/json', ...init.headers },
            signal: init.signal ?? AbortSignal.timeout(timeoutMs),
          });
          return { response, body: await response.text() };
        });
        if ((response.status === 429 || response.status >= 500) && transportRetry && attempt < 2) {
          await response.body?.cancel().catch(() => {});
          await new Promise<void>((resolve) => setTimeout(resolve, attempt === 0 ? 250 : 1_000));
          continue;
        }
        let value: unknown;
        try {
          value = body ? JSON.parse(body) : null;
        } catch {
          throw new Error(`Core ${response.status} returned non-JSON for ${pathname}`);
        }
        if (!response.ok)
          throw new Error(`Core ${response.status} for ${pathname}: ${JSON.stringify(value).slice(0, 500)}`);
        progress('request', { method, pathname, status: response.status });
        return unwrap(value);
      } catch (error) {
        lastError = error;
        const retryableTransport =
          error instanceof TypeError ||
          (error instanceof Error && (error.name === 'AbortError' || error.name === 'TimeoutError'));
        if (!transportRetry || !retryableTransport || attempt >= 2) throw error;
        await new Promise<void>((resolve) => setTimeout(resolve, attempt === 0 ? 250 : 1_000));
      }
    }
    throw lastError instanceof Error ? lastError : new Error(`Core request failed for ${pathname}`);
  };

  let capabilities: unknown;
  const mathRunInputsVersion = 2;
  await requireMathRunInputsCapability(async () => {
    capabilities = await request('/api/conversations/runtime-capabilities', {}, 10_000);
    return capabilities;
  }, mathRunInputsVersion);
  verifyMathRuntimeProcess(buildManifest, capabilities);
  const modelIsolationPolicyFile = flags.get('model-isolation-policy');
  const modelIsolation = modelIsolationPolicyFile
    ? verifyMathModelIsolationCore({
        policyFile: fs.realpathSync(modelIsolationPolicyFile),
        coreCapabilities: capabilities,
        launcher: path.join(mcpRoot, 'math-model-isolation.js'),
        workspace,
        models: [model, leadModel, workerModel],
      })
    : undefined;
  progress('core_math_capability_confirmed', { mathRunInputsVersion });

  const requiredBundles: Record<string, string> = {
    [BUILTIN_RESEARCH_TEAM_NAME]: 'builtin-mcp-research-team.js',
    [BUILTIN_SCIENCE_ARTIFACT_NAME]: 'builtin-mcp-science-artifact.js',
    [BUILTIN_RESEARCH_EVIDENCE_NAME]: 'builtin-mcp-research-evidence.js',
  };
  // Fail before Team provisioning when the Core endpoint or its MCP registry
  // is unavailable. Later model/session requests retain their longer timeout;
  // this readiness check must not consume the proof-run budget.
  const sourceByName = new Map<string, ISessionMcpServer>();
  // Always use a fresh, domain-neutral orchestration bundle. The role
  // capability environment makes it expose research_team only.
  for (const [name, bundle] of Object.entries(requiredBundles)) {
    const script = path.join(mcpRoot, bundle);
    if (!fs.existsSync(script)) throw new Error(`missing MCP bundle: ${script}`);
    sourceByName.set(name, {
      id: `math-proof-source-${name}`,
      name,
      transport: { type: 'stdio', command: 'node', args: [script], env: mathTransportEnv },
    });
  }
  const selectServers = (names: readonly string[], roleId: string): ISessionMcpServer[] =>
    names.map((name) => {
      const server = sourceByName.get(name);
      if (!server) throw new Error(`role ${roleId} requires unavailable MCP ${name}`);
      return server;
    });

  const launchContext = buildMathProofTeamLaunchContext({
    task,
    taskFile,
    legacyContractFile: activeProblemPath,
    baseCommit,
    solverProjectRelativePath: path.relative(workspace, receiptProjectRoot),
    formalStatement: problemContract.formalStatement,
    officialVerificationCommand: problemContract.officialVerificationCommand,
    assignmentId: mainlineAssignmentId,
    mathlibSourcePath: (() => {
      const cacheRoot = runtimeEnv.DEEPSCIENTIST_MATH_TRUSTED_CACHE_ROOTS?.split(path.delimiter).find(Boolean);
      return cacheRoot ? path.join(cacheRoot, 'mathlib', 'Mathlib') : undefined;
    })(),
    lakeExecutable,
    environmentInstruction: mathEnvInstruction,
    runBindingRef: frozen.inputs.binding!.path,
    benchmarkMethod: benchmarkMethod as 'deepscientist_team' | 'single_worker',
    secondProofOwner: runtimeEnv[MATHEMATICS_SECOND_PROOF_OWNER_ENV] === 'true',
    premiseSearchAvailable: Boolean(readMathRetrievalCorpusEnvironment(runtimeEnv)),
  });
  const { profile, initialMessage, workerObjective } = launchContext;
  const modeExtra: JsonRecord = {
    // Bind mathematical conversations to the generated solver project. The
    // outer workspace remains the run container, but project-bound MCP tools
    // must resolve the same root as the Lean assignment and artifact store.
    workspace: receiptProjectRoot,
    custom_workspace: true,
    backend: 'codex',
    assistant_locale: 'zh-CN',
    headless_proof_search: true,
    headless_proof_mainline: false,
    mode_stack: { schema: 'deepscientist.mode_stack.v1', primary: 'science', overlays: ['mathematical-research'] },
    mathematical_research: buildMathematicsConversationExtra(receiptProjectRoot),
    mathematics_runtime: {
      run_inputs: frozen.inputs,
      envFile: runtimeEnv.DEEPSCIENTIST_MATH_ENV_FILE,
      instruction: mathematicsRuntimeInstruction(runtimeEnv.DEEPSCIENTIST_MATH_ENV_FILE),
    },
    science: { report: { enabled: false } },
  };
  const coreRuntimeClient = createResearchCoreTeamClient({ baseUrl: coreUrl, requestTimeoutMs: 60_000 });
  const requiredSkills = (): readonly string[] => launchContext.skillIds;
  const withMathEnv = (server: ISessionMcpServer): ISessionMcpServer =>
    server.transport.type !== 'stdio'
      ? server
      : {
          ...server,
          transport: {
            ...server.transport,
            env: {
              ...server.transport.env,
              ...mathTransportEnv,
              AIONUI_BASE_URL: coreUrl,
              ...(server.name === BUILTIN_RESEARCH_TEAM_NAME ? { [RESEARCH_TEAM_CORE_BASE_URL_ENV]: coreUrl } : {}),
              [PROJECT_WORKSPACE_ENV_KEYS.projectRoot]: receiptProjectRoot,
            },
          },
        };
  let sessionReady: (() => void) | undefined;
  let eventStream: ResearchTeamEventStream | undefined;
  let eventWaiter: ResearchTeamEventWaiter<MathRunObservation> | undefined;
  let runtimeEventWake: (() => void) | undefined;
  let waitTimeoutController: AbortController | undefined;
  let waitTimeoutTimer: ReturnType<typeof setTimeout> | undefined;
  let proofStartedAt: number | undefined = proofClockStartedAt;
  let lastRunState: JsonRecord = {};
  let directDispatchRuntime:
    | Readonly<{
        teamId: string;
        lead: ResearchTeamRuntimeRosterMember;
        startIntent: MathStartIntent;
        roster: readonly ResearchTeamRuntimeRosterMember[];
      }>
    | undefined;

  const refreshWaitTimeout = (): void => {
    if (timeoutSeconds === undefined) return;
    waitTimeoutController ??= new AbortController();
    if (waitTimeoutTimer) clearTimeout(waitTimeoutTimer);
    waitTimeoutTimer = setTimeout(() => {
      waitTimeoutController?.abort(new Error('math_run_wait_interrupted'));
    }, timeoutSeconds * 1000);
  };
  const clearWaitTimeout = (): void => {
    if (waitTimeoutTimer) clearTimeout(waitTimeoutTimer);
    waitTimeoutTimer = undefined;
  };
  const continuationStateFile = `${output}.continuation.json`;
  let continuationProgress = readMathContinuationProgress(continuationStateFile);
  // This value is process-local. A resumed process must enqueue a fresh message
  // rather than replaying one that an earlier process may already have consumed.
  const recoveryEpoch = `runner-${randomUUID()}`;
  let ownerlessRecoveryAttempt:
    | { fingerprint: string; retryAt: number; outcome?: Awaited<ReturnType<typeof recoverMathOwnerlessAssignment>> }
    | undefined;
  const deps: ResearchTeamProvisioningDeps = {
    updateConversation: ({ id, updates, merge_extra }) =>
      request(`/api/conversations/${encodeURIComponent(id)}`, {
        method: 'PATCH',
        body: JSON.stringify({ ...updates, merge_extra }),
      }),
    listAssistants: async () => (await request('/api/assistants')) as never,
    createAssistant: async (params) => {
      const assistant = (await request('/api/assistants', {
        method: 'POST',
        body: JSON.stringify(params),
      })) as { id?: unknown };
      if (typeof assistant.id === 'string' && assistant.id.trim()) manifestAssistantIds.push(assistant.id.trim());
      writeCleanupManifest();
      return assistant as never;
    },
    writeAssistantRule: (params) =>
      request('/api/skills/assistant-rule/write', { method: 'POST', body: JSON.stringify(params) }),
    removeAssistant: ({ id }) => request(`/api/assistants/${encodeURIComponent(id)}`, { method: 'DELETE' }),
    createMcpServer: async (params) => {
      const server = (await request('/api/mcp/servers', {
        method: 'POST',
        body: JSON.stringify(params),
      })) as { id?: unknown };
      if (typeof server.id === 'string' && server.id.trim()) manifestMcpServerIds.push(server.id.trim());
      writeCleanupManifest();
      return server as never;
    },
    toggleMcpServer: async ({ id }) =>
      (await request(`/api/mcp/servers/${encodeURIComponent(id)}/toggle`, { method: 'POST' })) as never,
    updateMcpServer: ({ id, data }) =>
      request(`/api/mcp/servers/${encodeURIComponent(id)}`, { method: 'PUT', body: JSON.stringify(data) }),
    removeMcpServer: ({ id }) => request(`/api/mcp/servers/${encodeURIComponent(id)}`, { method: 'DELETE' }),
    createTeam: async (params) => {
      const team = fromBackendTeam(
        await request(
          '/api/teams',
          {
            method: 'POST',
            body: JSON.stringify(toBackendTeamCreate(params)),
          },
          600_000
        )
      );
      manifestTeamId = team.id;
      writeCleanupManifest();
      return team;
    },
    removeTeam: ({ id }) => request(`/api/teams/${encodeURIComponent(id)}`, { method: 'DELETE' }),
    setSessionMode: ({ team_id, session_mode }) =>
      request(`/api/teams/${encodeURIComponent(team_id)}/session-mode`, {
        method: 'POST',
        body: JSON.stringify({ mode: session_mode }),
      }),
    ensureSession: ({ team_id }) => request(`/api/teams/${encodeURIComponent(team_id)}/session`, { method: 'POST' }, 600_000),
    // Fresh headless math runs start the Lead before warming every Worker.
    // The delivery gate wakes a Worker on demand when Core reports
    // runtime_starting; resumed runs still restore all retained runtimes below.
    ...(resume
      ? {
          ensureAgentRuntime: ({ team_id, slot_id }: { team_id: string; slot_id: string }) =>
            coreRuntimeClient.ensureAgentRuntime!(team_id, slot_id),
        }
      : {}),
    waitForMcpToolsReady: ({ registerSessionReady, onSlotReady, slotIds }) =>
      new Promise<void>((resolve, reject) => {
        sessionReady = () => {
          void (async () => {
            try {
              // Session creation is not proof that every role received its MCP
              // catalog. Re-read each authoritative conversation and every
              // bound server before releasing the first model turn; otherwise
              // the Lead can dispatch into a Worker that is still unusable.
              const team = fromBackendTeam(
                await request(`/api/teams/${encodeURIComponent(manifestTeamId!)}`, {}, 15_000)
              );
              const agents = team.agents;
              const catalog = await request('/api/mcp/servers', {}, 15_000);
              const catalogIds = new Set(
                (Array.isArray(catalog) ? catalog : [])
                  .filter((server): server is JsonRecord => isRecord(server))
                  .map((server) => String(server.id || '').trim())
                  .filter(Boolean)
              );
              await Promise.all(
                slotIds.map(async (slotId) => {
                  const agent = agents.find(
                    (candidate) =>
                      candidate &&
                      typeof candidate === 'object' &&
                      !Array.isArray(candidate) &&
                      (candidate as JsonRecord).slot_id === slotId
                  ) as JsonRecord | undefined;
                  const conversationId = agent?.conversation_id;
                  if (typeof conversationId !== 'string' || !conversationId.trim()) {
                    throw new Error(`Research Team slot ${slotId} conversation is unavailable after session startup`);
                  }
                  const conversation = asRecord(
                    await request(`/api/conversations/${encodeURIComponent(conversationId)}`, {}, 15_000),
                    `Research Team slot ${slotId} conversation`
                  );
                  const extra = conversation.extra;
                  const mcpIds =
                    extra && typeof extra === 'object' && !Array.isArray(extra)
                      ? (extra as JsonRecord).mcp_server_ids
                      : undefined;
                  if (
                    !Array.isArray(mcpIds) ||
                    !mcpIds.length ||
                    mcpIds.some((id) => typeof id !== 'string' || !id.trim())
                  ) {
                    throw new Error(`Research Team slot ${slotId} MCP catalog is unavailable after session startup`);
                  }
                  if (mcpIds.some((id) => !catalogIds.has(String(id).trim()))) {
                    throw new Error(`Research Team slot ${slotId} MCP server is missing from the Core catalog`);
                  }
                  onSlotReady?.(slotId);
                })
              );
              resolve();
            } catch (error) {
              reject(error);
            }
          })();
        };
        registerSessionReady?.(() => sessionReady?.());
      }),
    sendMessage: async ({ team_id, input, files }) => {
      verifyMathRunInputs(frozen.inputs);
      if (files?.length || input !== initialMessage) throw new Error('math_direct_dispatch_input_invalid');
      const dispatchRuntime = directDispatchRuntime;
      if (!dispatchRuntime || dispatchRuntime.teamId !== team_id) {
        throw new Error('math_direct_dispatch_runtime_unavailable');
      }
      // Recovery must restore the proof owner even when startup selected a
      // preliminary Researcher task instead of the formalization lane.
      const originalProofSlotId = resolveMathStartIntent(dispatchRuntime.roster).targetSlotId;
      const url = new URL('/ws', coreUrl);
      url.protocol = url.protocol === 'https:' ? 'wss:' : 'ws:';
      eventStream = new ResearchTeamEventStream({ teamId: team_id, createSocket: () => new WebSocket(url) });
      if (runLimits.maxRunSeconds !== undefined) {
        waitTimeoutController ??= new AbortController();
        const scheduleWallLimit = (): void => {
          let remaining = runLimits.maxRunSeconds! * 1000 - (Date.now() - proofClockStartedAt);
          if (remaining <= 0) {
            // The same bounded window as limitReason: a completed original-target
            // proof waiting for integration keeps the run alive until it ends.
            let pendingSince: number | undefined;
            try {
              pendingSince = latestCompletedProofPendingIntegration(
                listProjectGitResearchTeamAssignments({ workspace, teamId: team_id, strict: true })
              );
            } catch {
              pendingSince = undefined;
            }
            const graceEnd =
              pendingSince === undefined ? 0 : pendingSince + mathRunCompletedProofGraceMs(runLimits.maxRunSeconds!);
            if (graceEnd <= Date.now()) {
              runLimitReason = 'math_run_wall_limit';
              waitTimeoutController?.abort();
              return;
            }
            remaining = graceEnd - Date.now();
          }
          // Node timers overflow beyond a signed 32-bit millisecond delay.
          proofWallTimer = setTimeout(scheduleWallLimit, Math.min(remaining, 2_147_483_647));
        };
        scheduleWallLimit();
      }
      eventWaiter = new ResearchTeamEventWaiter({
        stream: eventStream,
        startupOnly,
        ...(timeoutSeconds !== undefined
          ? {
              signal: (refreshWaitTimeout(), waitTimeoutController!.signal),
              heartbeatMs: Math.min(30_000, Math.max(5_000, Math.floor((timeoutSeconds * 1000) / 4))),
            }
          : {}),
        ...(runLimits.maxRunSeconds !== undefined ? { signal: waitTimeoutController!.signal } : {}),
        pollIntervalMs: MATH_RECONCILIATION_POLL_MS,
        observe: (event) => {
          if (event.name === 'team.childTurnCompleted' && typeof event.data.slot_id === 'string')
            turnsBySlot.set(event.data.slot_id, (turnsBySlot.get(event.data.slot_id) ?? 0) + 1);
          progress(event.name, {
            teamRunId: event.data.team_run_id,
            slotId: event.data.slot_id,
            turnId: event.data.turn_id,
          });
          runtimeEventWake?.();
        },
        reconcile: async () => {
          waitTimeoutController?.signal.throwIfAborted();
          lastRunState = normalizeRunnerRunState(
            await request(`/api/teams/${encodeURIComponent(team_id)}/run-state`, {}, 15_000)
          );
          timing.observeSlots(lastRunState.slot_work);
          const assignments = listProjectGitResearchTeamAssignments({ workspace, teamId: team_id, strict: true });
          const reconciledProgress = reconcileMathContinuationProgress(assignments, continuationProgress);
          if (Object.keys(reconciledProgress).length !== Object.keys(continuationProgress).length) {
            continuationProgress = reconciledProgress;
            writeMathJsonDurable(continuationStateFile, { teamId: team_id, progress: continuationProgress });
          }
          const head = await readGitHead(workspace);
          if (!head) throw new Error('math_workspace_head_unavailable');
          // A retained Worker receipt belongs to the run that actually
          // accepted it. Reconciliation must not rewrite that identity to the
          // latest run: the latest run may be a Lead control turn. A Worker
          // receipt is rebound only after a real Worker-target transport ack.
          let observation = observeMathRun({
            teamId: team_id,
            statementHash: problemContract.statementHash,
            core: lastRunState,
            assignments,
            workspaceHead: head,
            receiptSecret: readMathematicsReceiptSecret(),
          });
          // An explicit timeout is an inactivity budget, not a total proof wall
          // clock. Any valid Core snapshot proves the runtime is still alive.
          refreshWaitTimeout();
          const checkedEvidenceIds = assignments.flatMap((assignment) => {
            const integration = assignment.integration;
            const checked = !integration?.reverificationRequired
              ? (integration?.sourceVerificationReceipts ?? [])
                  .filter((item) => item.targetCommit === integration?.mergedCommit)
                  .map((item) =>
                    mathDigest(
                      canonicalMathJson([item.sourcePath, item.contentSha256, item.theoremName, item.statementHash])
                    )
                  )
              : [];
            const checkpoint = assignment.mathProgress;
            if (
              checkpoint?.outcome === 'advanced' &&
              checkpoint.proofStateFingerprint &&
              ['kernel_progress', 'goal_progress', 'foundation_progress'].includes(checkpoint.progressKind ?? '')
            )
              checked.push(mathDigest(canonicalMathJson([checkpoint.statementHash, checkpoint.proofStateFingerprint])));
            return checked;
          });
          const workerCommitIds = await readMathWorkerCommitIds(workspace, assignments);
          proofProgress.observe({
            checkedEvidenceIds,
            workerCommitIds,
            activityFingerprint: mathDigest(
              canonicalMathJson([
                head,
                workerCommitIds,
                assignments.map((item) => [
                  item.assignmentId,
                  item.mathProgress?.proofStateFingerprint ?? null,
                  item.state,
                ]),
              ])
            ),
            pendingProofAssignments: assignments.filter(
              (item) =>
                ['prepared', 'accepted'].includes(item.state) &&
                normalizeRuntimeMathAssignment(item.assignment).request.kind === 'formalize'
            ).length,
            solverReady: Boolean(observation.solverReady),
          });
          const progressState = proofProgress.state();
          const progressDigest = mathDigest(canonicalMathJson(progressState));
          if (progressDigest !== lastProgressDigest) {
            writeMathJsonDurable(proofProgressFile, progressState);
            lastProgressDigest = progressDigest;
          }
          progress('proof_progress_observed', proofProgress.snapshot());
          if (observation.state !== 'solver_ready' && observation.state !== 'runtime_error') {
            const reviewPendingSince = assignments
              .filter((item) => item.delivery && !item.integration && item.state !== 'superseded')
              .map((item) => Date.parse(item.delivery!.deliveredAt))
              .filter(Number.isFinite)
              .reduce<number | undefined>((latest, at) => Math.max(latest ?? at, at), undefined);
            const completedProofPendingSince = latestCompletedProofPendingIntegration(assignments);
            runLimitReason ??= proofProgress.limitReason(runLimits, observation.quiescent, {
              reviewPendingSince,
              completedProofPendingSince,
            });
            if (
              !runLimitReason &&
              completedProofPendingSince !== undefined &&
              runLimits.maxRunSeconds !== undefined &&
              Date.now() - proofClockStartedAt >= runLimits.maxRunSeconds * 1000 &&
              !wallGraceReported
            ) {
              wallGraceReported = true;
              progress('run_wall_limit_deferred_for_completed_proof', {});
            }
            if (runLimitReason) return { ...observation, state: 'incomplete', reason: runLimitReason };
          }
          let continuationScheduled = false;
          let recoveryExhausted = false;
          let ownerlessRecoveryBlocked = false;
          const hasActiveProofOwner = assignments.some(
            (item) =>
              item.slotId === originalProofSlotId &&
              item.state === 'accepted' &&
              !item.delivery &&
              !item.integration &&
              !item.supersessionPending &&
              !item.budgetCancellation
          );
          // Background notices do not retain a sealed predecessor's writer
          // authority. Actual successor authorization remains with the handler.
          const readySlotIds = mathReadyContinuationSlots(
            lastRunState,
            hasActiveProofOwner ? undefined : originalProofSlotId
          );
          const hasIdleOwner = assignments.some(
            (item) =>
              item.state === 'accepted' && !item.delivery && !item.integration && readySlotIds.includes(item.slotId)
          );
          const hasRecoverableProofSlot =
            !hasActiveProofOwner &&
            readySlotIds.includes(originalProofSlotId) &&
            readySlotIds.includes(dispatchRuntime.lead.slotId);
          const pendingTransport = Object.values(continuationProgress).some((entry) => entry.dispatchPending);
          if (
            shouldContinueMathRunObservation(
              observation,
              hasIdleOwner || hasRecoverableProofSlot || pendingTransport
            )
          ) {
            const staleAssignments = assignments.filter((assignment) =>
              isStaleMathAssignmentSnapshot(assignment, lastRunState)
            );
            const recoveryReason =
              observation.reason ?? (staleAssignments.length ? 'math_assignment_run_stale' : undefined);
            const snapshots = await Promise.all(
              assignments.map(async (assignment) => {
                const worktree = assignment.preparedGit?.worktreePath;
                const workerHead = worktree ? await readGitHead(worktree) : undefined;
                return collectMathContinuationEvidence(assignment, workerHead);
              })
            );
            const recoverySignal = waitTimeoutController?.signal ?? new AbortController().signal;
            const recoveryContext = await collectMathRecoveryContext(assignments, snapshots, {
              projectRoot: runBinding.workspace,
              teamId: team_id,
              runInputs: frozen.inputs,
              signal: recoverySignal,
            }).catch((error: unknown) => {
              recoverySignal.throwIfAborted();
              if (isMathPlanningSafetyError(error)) throw error;
              progress('recovery_feedback_unavailable', {
                reason: error instanceof Error ? error.message : String(error),
              });
              return {
                fingerprints: Object.fromEntries(
                  snapshots.map((snapshot) => [
                    snapshot.assignmentId,
                    mathDigest(canonicalMathJson([snapshot.fingerprint, snapshot.activityFingerprint])),
                  ])
                ),
                waitingOnResearch: {} as Record<string, readonly string[]>,
                researchProducers: {} as Record<string, readonly string[]>,
              };
            });
            const { fingerprints, waitingOnResearch, researchProducers } = recoveryContext;
            const planningProgress = projectMathContinuationPlanningState(continuationProgress);
            recoveryExhausted =
              (observation.quiescent || observation.pendingAssignmentQuiescent) &&
              isMathProgressContinuationExhausted(
                assignments,
                planningProgress,
                fingerprints,
                recoveryReason,
                UNBOUNDED_MATH_STALLED_RECOVERY_CONTINUATIONS
              );
            let continuation =
              readySlotIds.length || pendingTransport
                ? planMathProgressContinuation(
                    assignments,
                    planningProgress,
                    fingerprints,
                    dispatchRuntime.lead.slotId,
                    recoveryReason,
                    UNBOUNDED_MATH_STALLED_RECOVERY_CONTINUATIONS,
                    waitingOnResearch,
                    readySlotIds,
                    originalProofSlotId,
                    Math.max(0, Date.now() - (proofProgress.snapshot().lastCheckedEvidenceAt ?? proofClockStartedAt)) /
                      1000
                  )
                : undefined;
            // If a completed Lead review did not create a proof owner, execute
            // only the normal handler's existing lifecycle action. No source or
            // identity is manufactured here, and a live/queued Lead is never raced.
            let ownerlessRecovery: Awaited<ReturnType<typeof recoverMathOwnerlessAssignment>> | undefined;
            const ownerlessReview = planningProgress['lead:original-target'];
            if (!continuation && !pendingTransport && hasRecoverableProofSlot && ownerlessReview?.attempts) {
              const fingerprint = mathDigest(
                canonicalMathJson({ fingerprints, recoveryReason: recoveryReason ?? null })
              );
              if (
                !ownerlessRecoveryAttempt ||
                ownerlessRecoveryAttempt.fingerprint !== fingerprint ||
                Date.now() >= ownerlessRecoveryAttempt.retryAt
              ) {
                ownerlessRecoveryAttempt = { fingerprint, retryAt: Date.now() + MATH_OWNERLESS_RECOVERY_RETRY_MS };
                const conversationId = retainedRuntime?.conversations[dispatchRuntime.lead.slotId];
                ownerlessRecovery = await (async () => {
                  if (!conversationId) throw new Error('math_ownerless_recovery_conversation_unavailable');
                  return withMathOwnerlessRecoveryMcp(
                    {
                      readCore: (pathname, signal) => request(pathname, { signal }, 15_000),
                      conversationId,
                      teamId: team_id,
                      leadSlotId: dispatchRuntime.lead.slotId,
                      projectRoot: runBinding.workspace,
                      environment: runtimeEnv,
                      frozenEnvironment: frozen.environment,
                      signal: recoverySignal,
                    },
                    (call) =>
                      recoverMathOwnerlessAssignment({
                        call,
                        assignments,
                        targetSlotId: originalProofSlotId,
                        // The complete objective is already in the bound Worker
                        // context. Lite task becomes a bounded WAL objective; do
                        // not copy the much longer role instructions into it.
                        workerObjective:
                          'Continue the unchanged original theorem from the frozen task and retained authorized source. Inspect real Lean evidence, preserve every original target, and use the normal delivery and independent verification path.',
                        signal: recoverySignal,
                      })
                  );
                })().catch((error: unknown) => {
                  recoverySignal.throwIfAborted();
                  if (isMathPlanningSafetyError(error)) throw error;
                  return {
                    status: 'blocked' as const,
                    reason:
                      error instanceof Error && /^math_[a-z_]+$/u.test(error.message)
                        ? error.message
                        : 'math_ownerless_recovery_unavailable',
                    producerAssignmentIds: [],
                  };
                });
                ownerlessRecoveryAttempt.outcome = ownerlessRecovery;
                progress('ownerless_lifecycle_recovery', ownerlessRecovery);
              } else ownerlessRecovery = ownerlessRecoveryAttempt.outcome;
            }
            if (!continuation && ownerlessRecovery && ownerlessRecovery.status !== 'dispatched') {
              // An unavailable proof successor must not starve independent
              // retained research. The legal ownership repair remains pending.
              continuation = planMathProgressContinuation(
                assignments,
                planningProgress,
                fingerprints,
                dispatchRuntime.lead.slotId,
                recoveryReason,
                UNBOUNDED_MATH_STALLED_RECOVERY_CONTINUATIONS,
                waitingOnResearch,
                readySlotIds,
                undefined,
                Math.max(0, Date.now() - (proofProgress.snapshot().lastCheckedEvidenceAt ?? proofClockStartedAt)) / 1000
              );
            }
            ownerlessRecoveryBlocked =
              ownerlessRecovery?.status === 'blocked' &&
              observation.pendingAssignmentQuiescent &&
              continuation === undefined;
            writeMathJsonDurable(`${output}.proof-recovery.json`, {
              schema: 'deepscientist.math.proof-recovery.v1',
              teamId: team_id,
              problemId: problemContract.problemId,
              runInputsDigest: mathDigest(canonicalMathJson(frozen.inputs)),
              snapshots,
              waitingOnResearch,
              researchProducers,
              ...(ownerlessRecovery ? { ownerlessRecovery } : {}),
              continuation: continuation
                ? { target: continuation.target, assignmentId: continuation.assignmentId }
                : { target: null, reason: ownerlessRecovery?.reason ?? 'awaiting_slot_or_lifecycle' },
            });
            if (ownerlessRecovery?.status === 'dispatched') return undefined;
            if (continuation) {
              continuationScheduled = true;
              const previousProgress = continuationProgress[continuation.progressKey];
              const replayingPending = previousProgress?.dispatchPending === true;
              let planningContextDigest: string | undefined;
              let continuationInput = continuation.input;
              if (!recoveryReason && !replayingPending) {
                continuationInput +=
                  '\n\nPlanning checkpoint: identify the exact current mathematical gap, what earlier evidence actually established, and one next action whose outcome would change the argument. Reuse checked local library support, preserve exact formula obligations and investigate only the residual gap; inspect full declarations before transferring a mechanism or retrying a call. Do not treat an unproved attempt, search miss, or runtime fault as a refutation.';
                const formalizeReceipts = assignments.filter(
                  (assignment) =>
                    assignment.schema === 'deepscientist.research_team_assignment.v2' &&
                    normalizeRuntimeMathAssignment(assignment.assignment).request.kind === 'formalize'
                );
                const activeFormalizers = formalizeReceipts.filter(
                  (assignment) => assignment.state === 'accepted' && !assignment.delivery && !assignment.integration
                );
                const planningReceipt =
                  formalizeReceipts.find((assignment) => assignment.assignmentId === continuation.assignmentId) ??
                  (continuation.target === 'lead' && activeFormalizers.length === 1 ? activeFormalizers[0] : undefined);
                if (planningReceipt) {
                  const planningSignal = waitTimeoutController?.signal ?? new AbortController().signal;
                  const localPreviewPromise = runMathQuiescentProofPreview({
                    projectRoot: runBinding.workspace,
                    teamId: team_id,
                    assignmentId: planningReceipt.assignmentId,
                    runInputs: frozen.inputs,
                    env: runtimeEnv,
                    isQuiescent: () => isResearchTeamRunQuiescent(lastRunState),
                    hasPendingDispatch: () =>
                      Object.values(continuationProgress).some((item) => item.dispatchPending === true),
                    signal: planningSignal,
                    deadlineAt: Date.now() + 30_000,
                  }).catch((error: unknown): undefined => {
                    planningSignal.throwIfAborted();
                    if (isMathPlanningSafetyError(error)) throw error;
                    progress('local_proof_preview_unavailable', {
                      assignmentId: planningReceipt.assignmentId,
                      reason: error instanceof Error ? error.message : String(error),
                    });
                    return undefined;
                  });
                  const planningContextPromise = readMathPlanningContext({
                    resolvedCapability: {
                      teamId: team_id,
                      slotId: planningReceipt.slotId,
                      roleKind: 'worker',
                      projectRoot: runBinding.workspace,
                    },
                    signal: planningSignal,
                    runInputs: frozen.inputs,
                  }).catch((error: unknown): undefined => {
                    planningSignal.throwIfAborted();
                    if (isMathPlanningSafetyError(error)) throw error;
                    progress('planning_context_unavailable', {
                      assignmentId: planningReceipt.assignmentId,
                      historyCoverage: 'unavailable',
                    });
                    return undefined;
                  });
                  const [previewResult, contextResult] = await Promise.allSettled([
                    localPreviewPromise,
                    planningContextPromise,
                  ]);
                  if (previewResult.status === 'rejected') throw previewResult.reason;
                  if (contextResult.status === 'rejected') throw contextResult.reason;
                  const localPreview = previewResult.value;
                  const context = contextResult.value;
                  if (localPreview?.text) continuationInput += `\n\n${localPreview.text}`;
                  if (localPreview)
                    progress('local_proof_preview', { assignmentId: planningReceipt.assignmentId, ...localPreview });
                  if (context) {
                    planningContextDigest = context.contextDigest;
                    if (context.historyCoverage === 'partial') {
                      continuationInput +=
                        previousProgress?.planningContextDigest === context.contextDigest
                          ? `\nRelevant failure evidence is unchanged: ${context.evidenceRefs.join(', ')}`
                          : `\n${context.text}`;
                    }
                    progress('planning_context_prepared', {
                      assignmentId: planningReceipt.assignmentId,
                      contextDigest: context.contextDigest,
                      historyCoverage: context.historyCoverage,
                      evidenceCount: context.evidenceRefs.length,
                    });
                  }
                }
              }
              waitTimeoutController?.signal.throwIfAborted();
              const transport = prepareMathContinuationDispatch(
                { ...continuation, input: continuationInput },
                recoveryEpoch,
                previousProgress
              );
              const dispatchAttempt = replayingPending ? previousProgress.attempts : continuation.attempt;
              continuationProgress[continuation.progressKey] = {
                fingerprint: replayingPending ? previousProgress.fingerprint : continuation.fingerprint,
                attempts: dispatchAttempt,
                ...(continuation.appliedLeadReviewAttempt === undefined
                  ? {}
                  : { appliedLeadReviewAttempt: continuation.appliedLeadReviewAttempt }),
                idempotencyKey: transport.idempotencyKey,
                messageFingerprint: transport.messageFingerprint,
                content: transport.content,
                ...(replayingPending
                  ? previousProgress.planningContextDigest
                    ? { planningContextDigest: previousProgress.planningContextDigest }
                    : {}
                  : planningContextDigest
                    ? { planningContextDigest }
                    : {}),
                dispatchPending: true,
                recoveryEpoch: replayingPending ? (previousProgress.recoveryEpoch ?? recoveryEpoch) : recoveryEpoch,
              };
              writeMathJsonDurable(continuationStateFile, { teamId: team_id, progress: continuationProgress });
              const backoffMs =
                Math.min(
                  dispatchAttempt +
                    (continuation.appliedLeadReviewAttempt ?? 0) * MAX_MATH_PENDING_ASSIGNMENT_CONTINUATIONS,
                  15
                ) * 2_000;
              progress('assignment_continuation_scheduled', {
                assignmentId: continuation.assignmentId,
                slotId: continuation.slotId,
                attempt: dispatchAttempt,
                backoffMs,
              });
              await new Promise<void>((resolve) => setTimeout(resolve, backoffMs));
              waitTimeoutController?.signal.throwIfAborted();
              verifyMathRunInputs(frozen.inputs);
              const latestState = normalizeRunnerRunState(
                await request(`/api/teams/${encodeURIComponent(team_id)}/run-state`, {}, 15_000)
              );
              const recoveryBlocked = mathRuntimeRecoveryBlocked(latestState);
              const latestAssignments = listProjectGitResearchTeamAssignments({
                workspace,
                teamId: team_id,
                strict: true,
              });
              const continuationRetired = !canReplayMathContinuation(latestAssignments, continuation.progressKey);
              if (
                recoveryBlocked ||
                continuationRetired ||
                (!replayingPending && !mathReadyContinuationSlots(latestState).includes(continuation.slotId))
              ) {
                // We have not sent anything: undo this reservation rather than
                // labeling it an uncertain transport and enqueueing a duplicate.
                if (!replayingPending) {
                  if (previousProgress) continuationProgress[continuation.progressKey] = previousProgress;
                  else delete continuationProgress[continuation.progressKey];
                }
                continuationProgress = reconcileMathContinuationProgress(latestAssignments, continuationProgress);
                writeMathJsonDurable(continuationStateFile, { teamId: team_id, progress: continuationProgress });
                return undefined;
              }
              const sendContinuation = () => {
                waitTimeoutController?.signal.throwIfAborted();
                return request(
                  `/api/teams/${encodeURIComponent(team_id)}/agents/${encodeURIComponent(continuation.slotId)}/messages`,
                  {
                    method: 'POST',
                    body: JSON.stringify({
                      content: transport.content,
                      idempotency_key: transport.idempotencyKey,
                    }),
                  }
                );
              };
              const acknowledgement = fromBackendTeamRunAck(
                team_id,
                await recoverMathTransportAcknowledgement(sendContinuation, (error) =>
                  progress('assignment_continuation_ack_interrupted', {
                    assignmentId: continuation.assignmentId,
                    slotId: continuation.slotId,
                    idempotencyKey: transport.idempotencyKey,
                    error: error instanceof Error ? error.message : String(error),
                  })
                ),
                continuation.slotId
              );
              if (
                acknowledgement.accepted_slot_id !== continuation.slotId ||
                !['accepted', 'queued', 'blocked_runtime_starting'].includes(acknowledgement.enqueue_status ?? '')
              ) {
                continuationProgress[continuation.progressKey] = {
                  ...continuationProgress[continuation.progressKey]!,
                  dispatchPending: false,
                };
                writeMathJsonDurable(continuationStateFile, { teamId: team_id, progress: continuationProgress });
                throw new Error('math_pending_assignment_continuation_not_persisted');
              }
              continuationProgress[continuation.progressKey] = {
                ...continuationProgress[continuation.progressKey]!,
                dispatchPending: false,
              };
              writeMathJsonDurable(continuationStateFile, { teamId: team_id, progress: continuationProgress });
              manifestTeamRunId = acknowledgement.team_run_id;
              writeCleanupManifest();
              progress('assignment_continuation_queued', {
                assignmentId: continuation.assignmentId,
                slotId: continuation.slotId,
                attempt: dispatchAttempt,
                teamRunId: acknowledgement.team_run_id,
                enqueueStatus: acknowledgement.enqueue_status,
              });
              return undefined;
            }
          }
          if (observation.teamRunId && manifestTeamRunId !== observation.teamRunId) {
            manifestTeamRunId = observation.teamRunId;
            writeCleanupManifest();
          }
          progress('runtime_reconciled', { state: observation.state, assignmentCounts: observation.assignmentCounts });
          return shouldResolveMathRunObservation(
            observation,
            continuationScheduled,
            recoveryExhausted,
            ownerlessRecoveryBlocked
          ) ||
            (startupOnly && observation.workerDispatched)
            ? observation
            : undefined;
        },
      });
      pendingEventCleanup = () => {
        eventWaiter?.close();
        eventStream?.close();
      };
      eventStream.subscribeInvalidation((event) => {
        timing.invalidate();
        progress('stream_invalidated', { ...event });
      });
      if (runLimitReason) {
        // Finish provisioning so the normal limit receipt and cleanup can run.
        // There is no new dispatch acknowledgement when the deadline expired.
        return retainedRunSnapshot(team_id, lastRunState.active_run);
      }
      await eventStream.start();
      if (runLimitReason) return retainedRunSnapshot(team_id, lastRunState.active_run);
      waitTimeoutController?.signal.throwIfAborted();
      progress('event_subscription_ready');
      lifecycleState = 'running';
      writeCleanupManifest();
      proofStartedAt ??= Date.now();
      if (resume) {
        const retainedRun = isRecord(lastRunState.active_run) ? lastRunState.active_run : undefined;
        const retainedStatus = String(retainedRun?.status || '').toLowerCase();
        // A runner can die after provisioning the Team but before Core creates
        // the first run. There is no active run to reattach in that state;
        // recover by issuing the idempotent Lead dispatch below.
        const canResumeAfterTerminalFailure =
          !retainedRun || ['failed', 'cancelled', 'canceled', 'aborted'].includes(retainedStatus);
        if (!canResumeAfterTerminalFailure) {
          progress('research_run_reattached', { teamId: team_id, runInputsRoot: frozen.inputs.root });
          return retainedRunSnapshot(team_id, lastRunState.active_run, {
            teamRunId: resume.teamRunId,
            slotId: dispatchRuntime.lead.slotId,
          });
        }
        progress('research_run_recovery_dispatch', {
          teamId: team_id,
          previousTeamRunId: String(retainedRun?.team_run_id || resume.teamRunId || ''),
          previousStatus: retainedStatus,
          slotId: dispatchRuntime.lead.slotId,
        });
        const recoveryMessage = `${initialMessage}\n\nRecovery context: the previous Team run ended with status "${retainedStatus}" before producing a valid result. Continue from the retained workspace, current source and real Lean evidence. Inspect prior failed attempts, choose the next productive proof step, and continue useful proof work toward independent verification of the original target. A precise mathematical or infrastructure blocker may use the existing blocked handoff; independent research may start from a nonterminal share.`;
        const recoveryDispatch = prepareMathTransportDispatch(
          `math-lead-recovery-${mainlineAssignmentId}`,
          recoveryMessage,
          recoveryEpoch
        );
        const acknowledgement = await createResearchCoreTeamClient({ baseUrl: coreUrl }).dispatch(
          team_id,
          dispatchRuntime.lead.slotId,
          recoveryMessage,
          undefined,
          recoveryDispatch.idempotencyKey,
          undefined
        );
        if (
          !acknowledgement.team_run_id ||
          !['accepted', 'queued', 'blocked_runtime_starting'].includes(acknowledgement.enqueue_status ?? '')
        ) {
          throw new Error('math_recovery_lead_dispatch_not_accepted');
        }
        manifestTeamRunId = acknowledgement.team_run_id;
        writeCleanupManifest();
        progress('autonomous_lead_recovery_started', {
          teamRunId: acknowledgement.team_run_id,
          previousTeamRunId: String(retainedRun?.team_run_id || resume.teamRunId || ''),
          slotId: dispatchRuntime.lead.slotId,
        });
        return acknowledgement;
      }
      const initialDispatch = prepareMathTransportDispatch(
        `math-lead-${mainlineAssignmentId}`,
        initialMessage,
        recoveryEpoch
      );
      const acknowledgement = await createResearchCoreTeamClient({ baseUrl: coreUrl }).dispatch(
        team_id,
        dispatchRuntime.lead.slotId,
        [
          initialMessage,
          `Runtime-selected start intent: ${dispatchRuntime.startIntent.kind}. In the first assignment use target_slot_id=${dispatchRuntime.startIntent.targetSlotId}. This slot was resolved from the authenticated runtime roster; do not substitute another slot. Frozen main task reference: ${mainlineAssignmentId}.`,
          ...(dispatchRuntime.startIntent.kind === 'formalize'
            ? [
                `Use this minimal valid research_team input to start the proof owner now: ${JSON.stringify({
                  action: 'dispatch',
                  assignments: [
                    {
                      target_slot_id: dispatchRuntime.startIntent.targetSlotId,
                      kind: 'formalize',
                      task: 'Own the complete original target in the frozen public task and runtime contract. Read the authorized source, prove all required declarations under the original hypotheses, check the candidate, and deliver the fully verified artifact. Begin with the next concrete source obligation.',
                    },
                  ],
                })}. Add a distinct Researcher in the same call when useful; omit optional fields unless the declared schema requires them.`,
              ]
            : []),
        ].join('\n'),
        undefined,
        initialDispatch.idempotencyKey,
        workspace
      );
      if (
        !acknowledgement.team_run_id ||
        !['accepted', 'queued', 'blocked_runtime_starting'].includes(acknowledgement.enqueue_status ?? '')
      ) {
        throw new Error('math_lead_dispatch_not_accepted');
      }
      manifestTeamRunId = acknowledgement.team_run_id;
      progress('autonomous_lead_started', {
        teamRunId: acknowledgement.team_run_id,
        slotId: dispatchRuntime.lead.slotId,
      });
      return acknowledgement;
    },
  };

  const restoreTeam = async (): Promise<ProvisionResearchTeamResult> => {
    let phase = 'team';
    try {
      if (!resume) throw new Error();
      const team = fromBackendTeam(await request(`/api/teams/${encodeURIComponent(resume.teamId)}`, {}, 15_000));
      if (team.id !== resume.teamId) throw new Error();
      const retained = resume.executionConfig;
      if (!retained || retained.backend !== 'codex' || retained.benchmarkMethod !== benchmarkMethod) throw new Error();
      const expectedRoster = new Map(retained.roster.map((member) => [member.slotId, member]));
      if (expectedRoster.size !== resume.roster.length || team.agents.length !== resume.roster.length)
        throw new Error();
      for (const member of resume.roster) {
        const expected = expectedRoster.get(member.slotId);
        const agent = team.agents.find((item) => item.slot_id === member.slotId);
        if (
          !expected ||
          !agent ||
          (agent.model && agent.model !== (expected.roleKind === 'lead' ? leadModel : workerModel))
        )
          throw new Error();
      }
      phase = 'conversations';
      for (const member of resume.roster) {
        const conversationId = resume.conversations[member.slotId];
        const agent = team.agents.find((item) => item.slot_id === member.slotId);
        if (!conversationId || agent?.conversation_id !== conversationId) throw new Error();
        const conversation = asRecord(
          await request(`/api/conversations/${encodeURIComponent(conversationId)}`, {}, 15_000),
          'retained conversation'
        );
        const extra = asRecord(conversation.extra, 'retained extra');
        const runtime = asRecord(extra.mathematics_runtime, 'retained mathematics runtime');
        if (canonicalMathJson(verifyMathRunInputs(runtime.run_inputs)) !== canonicalMathJson(frozen.inputs))
          throw new Error();
      }
      phase = 'run_state';
      lastRunState = normalizeRunnerRunState(
        await request(`/api/teams/${encodeURIComponent(team.id)}/run-state`, {}, 15_000)
      );
      if (upgradeRuntime || modelIsolation) {
        phase = 'runtime_upgrade';
        await request(`/api/teams/${encodeURIComponent(team.id)}/session`, { method: 'DELETE' }, 120_000);
        progress('team_runtime_session_restarted', {
          teamId: team.id,
          previousBuildDigest: resume.buildDigest,
          buildDigest,
        });
      }
      if (modelIsolation && modelIsolationPolicyFile) {
        if (!resume.modelIsolationRun) throw new Error('math_isolation_resume_binding_missing');
        modelIsolationRun = registerMathModelIsolationRun({
          policyFile: fs.realpathSync(modelIsolationPolicyFile),
          expectedDigest: modelIsolation.digest,
          workspace,
          conversationIds: Object.values(resume.conversations),
          runId: runBinding.runId,
          retained: resume.modelIsolationRun,
        });
        writeCleanupManifest();
      }
      const lead = resume.roster.find((member) => member.roleKind === 'lead');
      if (!lead) throw new Error();
      phase = 'assignments';
      listProjectGitResearchTeamAssignments({ workspace, teamId: team.id, strict: true });
      directDispatchRuntime = {
        teamId: team.id,
        lead,
        startIntent: resolveMathStartIntent(resume.roster),
        roster: resume.roster,
      };
      phase = 'worker_runtime_wakeup';
      await Promise.all(
        resume.roster.map(async (member) => {
          await coreRuntimeClient.ensureAgentRuntime?.(team.id, member.slotId);
          progress(member.roleKind === 'lead' ? 'lead_runtime_woken' : 'worker_runtime_woken', {
            slotId: member.slotId,
            roleId: member.roleId,
          });
        })
      );
      phase = 'event_subscription';
      const run = await deps.sendMessage({ team_id: team.id, input: initialMessage });
      return {
        team,
        run,
        leaderConversationId: resume.conversations[lead.slotId]!,
        runtimeResources: {
          assistantIds: resume.assistantIds,
          mcpServersByRole: [resume.mcpServerIds.map((id) => ({ id, name: id, sourceName: id }))],
        },
      };
    } catch {
      pendingEventCleanup?.();
      throw new Error(`recovery_unavailable: ${phase}`);
    }
  };
  const provisioned = resume
    ? await restoreTeam()
    : await provisionResearchTeam(
        {
          profile,
          // IMO2026 bootstraps a Git repository at the outer workspace and
          // places the solver project below generated/<problem>. The Team
          // Git capability must bind to that repository root; MCP transports
          // remain explicitly scoped to receiptProjectRoot above.
          projectRoot: workspace,
          userId: 'system_default_user',
          teamName: `Mathematics Proof ${path.basename(workspace)}`,
          backend: 'codex',
          model,
          leadModel,
          workerModel,
          leadThoughtLevel,
          workerThoughtLevel,
          sessionMode: 'agent-full-access',
          // This runner always creates a fresh Core Team. There is no prior
          // session to reset, so avoid the generic stop-session round trip.
          stopSessionBeforeEnsure: false,
          initialMessage,
          modeConversationExtra: modeExtra,
          // The first Lead dispatch uses the outer Git workspace. Bind it
          // before warmup so that dispatch can reuse the prepared ACP session.
          leaderConversationExtra: { workspace },
          requiredMcpServers: (role) => getRequiredMcpNames(role),
          requiredSkillIds: requiredSkills,
          disabledBuiltinSkillIds: launchContext.disabledSkillIds,
          onLaunchProgress: (event) => progress('team_launch_progress', { ...event }),
          onRuntimeReady: async ({ team, agents, roster }) => {
            const lead = roster.find((member) => member.roleKind === 'lead');
            if (!lead) throw new Error('math_lead_unavailable');
            const startIntent = resolveMathStartIntent(roster);
            progress('math_start_intent_resolved', { state: startIntent.kind, slotId: startIntent.targetSlotId });
            directDispatchRuntime = Object.freeze({ teamId: team.id, lead, startIntent, roster });
            retainedRuntime = {
              roster,
              conversations: Object.fromEntries(agents.map((agent) => [agent.slot_id, agent.conversation_id])),
            };
            if (modelIsolation && modelIsolationPolicyFile) {
              modelIsolationRun = registerMathModelIsolationRun({
                policyFile: fs.realpathSync(modelIsolationPolicyFile),
                expectedDigest: modelIsolation.digest,
                workspace,
                conversationIds: Object.values(retainedRuntime.conversations),
                runId: runBinding.runId,
              });
            }
            writeCleanupManifest();
          },
          buildConversationParams: (role, initialPromptSha256) => {
            const names = getRequiredMcpNames(role);
            const roleServers = prepareResearchTeamRoleMcpServers(
              selectServers(names, role.id),
              profile,
              role,
              receiptProjectRoot
            ).map(withMathEnv);
            const roleSkills = requiredSkills();
            const rolePrompt = launchContext.roleContext(role);
            progress('math_role_context_prepared', {
              roleId: role.id,
              roleKind: role.kind,
              ...(role.laneId ? { laneId: role.laneId } : {}),
              taskSha256: mathDigest(task),
              contextSha256: mathDigest(rolePrompt),
              taskOccurrences: rolePrompt.split(task).length - 1,
              initialMessageSha256: mathDigest(initialMessage),
            });
            return {
              name: role.displayName,
              extra: {
                ...modeExtra,
                enabled_skills: [...roleSkills],
                preset_enabled_skills: [...roleSkills],
                exclude_builtin_skills: [...launchContext.disabledSkillIds],
                exclude_auto_inject_skills: [...launchContext.disabledSkillIds],
                selected_mcp_server_ids: [],
                selected_session_mcp_servers: roleServers,
                mcp_server_ids: [],
                mcp_servers: roleServers.map((server) => server.name),
                mcp_statuses: roleServers.map((server) => ({ id: server.id, name: server.name, status: 'loaded' })),
                session_mcp_servers: roleServers,
                extra_skill_paths: roleSkills.map((skillId) => path.join(ROOT, 'resources', 'skills', skillId)),
                research_team_profile_id: profile.id,
                research_team_workflow_id: profile.workflowId,
                research_team_role_id: role.id,
                research_team_role_kind: role.kind,
                research_team_initial_prompt_sha256: initialPromptSha256,
                ...(role.laneId ? { research_team_lane_id: role.laneId } : {}),
                preset_context: rolePrompt,
                preset_rules: '',
              },
            };
          },
        },
        deps
      );
  const teamId = provisioned.team.id;
  let teamRunId = provisioned.run?.team_run_id;
  manifestTeamId = teamId;
  manifestTeamRunId = teamRunId;
  manifestAssistantIds.push(...provisioned.runtimeResources.assistantIds);
  manifestMcpServerIds.push(
    ...provisioned.runtimeResources.mcpServersByRole.flatMap((servers) => servers.map((server) => server.id))
  );
  // A failed journal update must leave resources available for explicit recovery.
  writeCleanupManifest();
  let cancelled = false;
  let removed = false;
  // Cleanup may be entered from the signal handler while final receipt
  // publication (or isolation finalization) is already stopping the Team.
  // Serialize those calls and remember an escalation from stop-only to full
  // resource removal so concurrent callers cannot race DELETE/revoke calls.
  let startupCleanupTask: Promise<void> | undefined;
  let startupCleanupRemoveTeam = false;
  let workerDeliveryGateBusy = false;
  let workerDeliveryGateTask: Promise<boolean | void> | undefined;
  const waitForWorkerDeliveryGate = async (): Promise<void> => {
    // The gate task is assigned immediately after its async body is created;
    // yield once if cleanup observes the tiny assignment window.
    while (workerDeliveryGateBusy) {
      const task = workerDeliveryGateTask;
      if (task) {
        await task.catch(() => {});
      } else {
        await Promise.resolve();
      }
    }
  };
  // A headless Team may be provisioned before its first run id exists. Treat
  // that state as non-quiescent until Core proves there is no active run.
  let runQuiescent = false;
  const performStartupCleanup = async (removeTeam: boolean): Promise<void> => {
    if (removed) return;
    // A delivery gate may have already started a Core request when cleanup is
    // triggered by a signal or by final receipt publication. Wait for that
    // request before cancelling or deleting the Team.
    await waitForWorkerDeliveryGate();
    cleanupOutcome = {
      status: 'pending',
      reason: removeTeam ? 'remove_resources' : 'stop_runtime',
      resourcesRemoved: false,
      manifestRetained: true,
    };
    const retainCleanup = (reason: string, status: 'failed' | 'deferred' = 'deferred'): void => {
      cleanupOutcome = { status, reason, resourcesRemoved: false, manifestRetained: true };
      writeCleanupManifest();
    };
    if (!removed) {
      try {
        // Always refresh the authoritative snapshot. The retained run ID can
        // belong to the proof turn while Core has advanced to a later control
        // run by the time cleanup starts.
        const snapshot = normalizeRunnerRunState(
          await request(`/api/teams/${encodeURIComponent(teamId)}/run-state`, {}, 15_000)
        );
        lastRunState = snapshot;
        const discovered = runnerActiveRunId(snapshot);
        if (discovered) {
          teamRunId = discovered;
          manifestTeamRunId = discovered;
          writeCleanupManifest();
        }
        runQuiescent = isResearchTeamRunQuiescent(snapshot);
        // A busy snapshot without an identity is unsafe to cancel: the
        // retained ID may now refer to an unrelated control run.
        if (!runQuiescent && !discovered) {
          progress('cleanup_run_id_unavailable', { teamId });
          retainCleanup('active_run_id_unavailable');
          return;
        }
      } catch (error) {
        progress('cleanup_state_read_failed', { error: String(error) });
        retainCleanup('state_read_failed', 'failed');
        return;
      }
    }
    if (teamRunId && !runQuiescent) {
      if (!cancelled) {
        try {
          await request(`/api/teams/${encodeURIComponent(teamId)}/runs/${encodeURIComponent(teamRunId)}/cancel`, {
            method: 'POST',
            body: JSON.stringify({
              reason: startupOnly ? 'startup-only verification completed' : 'proof runner cleanup requested',
            }),
          });
          cancelled = true;
        } catch (error) {
          progress('team_cancel_failed', { error: String(error) });
        }
      }
      for (let attempt = 0; attempt < 20; attempt += 1) {
        try {
          lastRunState = normalizeRunnerRunState(
            await request(`/api/teams/${encodeURIComponent(teamId)}/run-state`, {}, 15_000)
          );
          if (isResearchTeamRunQuiescent(lastRunState)) {
            runQuiescent = true;
            break;
          }
        } catch (error) {
          progress('cleanup_state_read_failed', { error: String(error) });
          break;
        }
        await new Promise<void>((resolve) => setTimeout(resolve, 500));
      }
    }
    if (removeTeam && !removed && runQuiescent) {
      let teamDeleted = false;
      try {
        await request(`/api/teams/${encodeURIComponent(teamId)}`, { method: 'DELETE' });
        teamDeleted = true;
      } catch (error) {
        const message = String(error);
        // A prior cleanup may already have removed the Team. In that case it
        // is safe to continue with the dependent runtime resources.
        teamDeleted = /Core 404\b/u.test(message);
        progress('team_delete_failed', { error: message, already_absent: teamDeleted });
      }
      if (!teamDeleted) {
        progress('runtime_resources_cleanup_deferred', { teamId, teamRunId });
        retainCleanup('team_delete_failed', 'failed');
        return;
      }
      try {
        const cleanupWarnings = await removeResearchTeamRuntimeResources(provisioned.runtimeResources, deps);
        if (cleanupWarnings.length) {
          progress('runtime_resources_cleanup_failed', { errors: cleanupWarnings });
          retainCleanup('runtime_resources_cleanup_failed', 'failed');
          return;
        }
        const discardedLeanEvalAssignments = discardLeanEvalTeamWorkspacesForTeam({
          projectRoot: receiptProjectRoot,
          teamId,
        });
        if (discardedLeanEvalAssignments.length) {
          progress('lean_eval_team_workspaces_discarded', {
            teamId,
            assignmentIds: discardedLeanEvalAssignments,
          });
        }
        removed = true;
        try {
          writeMathJsonDurable(`${cleanupManifestPath}.completed`, {
            ...asRecord(readMathJson(cleanupManifestPath), 'cleanup manifest'),
            cleanup: {
              status: 'completed',
              reason: 'resources_removed',
              resourcesRemoved: true,
              manifestRetained: false,
            },
          });
          fs.unlinkSync(cleanupManifestPath);
          syncMathDirectory(path.dirname(cleanupManifestPath));
        } catch {
          progress('cleanup_manifest_remove_failed', { cleanupManifestPath });
          cleanupOutcome = {
            status: 'failed',
            reason: 'manifest_remove_failed',
            resourcesRemoved: true,
            manifestRetained: true,
          };
          return;
        }
        cleanupOutcome = {
          status: 'completed',
          reason: 'resources_removed',
          resourcesRemoved: true,
          manifestRetained: false,
        };
      } catch (error) {
        progress('runtime_resources_cleanup_failed', { error: String(error) });
        retainCleanup('runtime_resources_cleanup_failed', 'failed');
      }
    } else if (removeTeam && !runQuiescent) {
      progress('cleanup_deferred_active_run', { teamId, teamRunId });
      retainCleanup('active_run_not_quiescent');
    } else if (!removeTeam) {
      if (runQuiescent) {
        cleanupOutcome = {
          status: 'stopped',
          reason: 'runtime_quiescent_resources_retained',
          resourcesRemoved: false,
          manifestRetained: true,
        };
        writeCleanupManifest();
      } else retainCleanup('active_run_not_quiescent');
    }
  };
  pendingStartupCleanup = (removeTeam: boolean): Promise<void> => {
    startupCleanupRemoveTeam ||= removeTeam;
    if (startupCleanupTask) return startupCleanupTask;
    startupCleanupTask = (async () => {
      // A stop-only request can be upgraded while its state read/cancel poll is
      // in flight. Run the stronger request after the current pass completes.
      while (!removed) {
        const requestedRemoveTeam = startupCleanupRemoveTeam;
        startupCleanupRemoveTeam = false;
        await performStartupCleanup(requestedRemoveTeam);
        if (!startupCleanupRemoveTeam) break;
      }
    })().finally(() => {
      startupCleanupTask = undefined;
    });
    return startupCleanupTask;
  };
  let signalExit: Promise<void> | undefined;
  const evaluationAbort = new AbortController();
  let activeEvaluation: ReturnType<typeof runMathEvaluation> | ReturnType<typeof runMathKernelEvaluation> | undefined;
  const handleTerminationSignal = (signal: NodeJS.Signals): void => {
    if (signalExit) return;
    signalExit = (async () => {
      progress('runner_signal', { signal });
      evaluationAbort.abort();
      try {
        lifecycleState = 'interrupted';
        writeCleanupManifest();
        pendingEventCleanup?.();
      } finally {
        // Explicit stop waits for the supervisor and its process tree; parent crashes do not cancel it.
        try {
          await activeEvaluation?.catch((error: unknown) => {
            if (!(error instanceof Error) || error.message !== 'math_evaluator_interrupted') throw error;
          });
        } finally {
          await pendingStartupCleanup?.(false);
        }
      }
      await pendingProofEnvironmentCleanup?.();
      process.exit(signal === 'SIGINT' ? 130 : 143);
    })().catch((error) => {
      console.error(`cleanup after ${signal} failed`, error instanceof Error ? error.stack || error.message : error);
      process.exit(1);
    });
  };
  process.once('SIGINT', handleTerminationSignal);
  process.once('SIGTERM', handleTerminationSignal);
  progress('team_provisioned', {
    teamId,
    teamRunId,
    roleCount: profile.roles.length,
    agentLimit: profile.pool.agentLimit,
    reasoningConcurrency: profile.pool.reasoningConcurrency,
  });

  if (!eventWaiter || proofStartedAt === undefined) throw new Error('math_event_wait_not_initialized');
  // A Worker delivery ends that Worker episode. Keep the Lead alive so it can
  // inspect and integrate the delivery; cancelling a Lead after an elapsed-time
  // threshold strands accepted evidence and causes duplicate retries.
  const workerDeliveryGateTurns = new Set<string>();
  const stalledAssignmentTurns = new Set<string>();
  const leadDeliveryGateTurns = new Set<string>();
  const leadDeliveryWakeDeliveries = new Set<string>();
  const runtimeStartingRecoveries = new Set<string>();
  let workerDeliveryGateWatchdog: ReturnType<typeof setTimeout> | undefined;
  const runWorkerDeliveryGate = (): void => {
    if (
      workerDeliveryGateBusy ||
      !runtimeEventWake ||
      runLimitReason ||
      !retainedRuntime ||
      !directDispatchRuntime ||
      !manifestTeamId
    )
      return;
    workerDeliveryGateBusy = true;
    const task = (async () => {
      const assignments = listProjectGitResearchTeamAssignments({ workspace, teamId, strict: true });
      const runState = normalizeRunnerRunState(
        await request(`/api/teams/${encodeURIComponent(teamId)}/run-state`, {}, 15_000)
      );
      if (!runtimeEventWake || runLimitReason || mathRuntimeRecoveryBlocked(runState)) return;
      const proofSnapshot = proofProgress.snapshot();
      const noProgressBudgetMs =
        runLimits.noProgressSeconds === undefined ? LEAD_ASSIGNMENT_WATCHDOG_MS : runLimits.noProgressSeconds * 1000;
      const enforceNoProgressBudget = runLimits.noProgressSeconds !== undefined;
      const lastCheckedEvidenceAtMs = proofSnapshot.lastCheckedEvidenceAt ?? proofClockStartedAt;
      const slots = runnerSlotWork(runState);
      const leadSlot = slots.find((value) => isRecord(value) && value.slot_id === directDispatchRuntime.lead.slotId);
      const pendingLeadDeliveries = pendingMathLeadDeliveries(assignments, directDispatchRuntime.lead.slotId);
      const hasPendingLeadDelivery = pendingLeadDeliveries.length > 0;
      const pendingLeadDeliveryAtMs = pendingLeadDeliveries
        .map((assignment) => Date.parse(assignment.delivery!.deliveredAt))
        .filter((value) => Number.isFinite(value))
        .sort((left, right) => left - right)[0];
      const leadTurnId =
        isRecord(leadSlot) && typeof leadSlot.active_turn_id === 'string' ? leadSlot.active_turn_id : undefined;
      const leadConversationId = retainedRuntime.conversations[directDispatchRuntime.lead.slotId];
      const activeRunStatus = String(
        (isRecord(runState.active_run) ? runState.active_run.status : runState.status) || ''
      ).toLowerCase();
      const runtimeStartingSlots = findRuntimeStartingMathAssignments(runState, assignments);
      const runtimeRunId = runnerActiveRunId(runState) ?? 'session';
      const runtimeRecoveryKeys = new Set(runtimeStartingSlots.map((slotId) => `${runtimeRunId}:${slotId}`));
      for (const retained of runtimeStartingRecoveries) {
        if (!runtimeRecoveryKeys.has(retained)) runtimeStartingRecoveries.delete(retained);
      }
      for (const slotId of runtimeStartingSlots) {
        const recoveryKey = `${runtimeRunId}:${slotId}`;
        if (runtimeStartingRecoveries.has(recoveryKey)) continue;
        runtimeStartingRecoveries.add(recoveryKey);
        try {
          await coreRuntimeClient.ensureAgentRuntime?.(teamId, slotId);
          progress('worker_runtime_starting_recovered', { slotId, teamRunId: runtimeRunId });
        } catch (error) {
          runtimeStartingRecoveries.delete(recoveryKey);
          progress('worker_runtime_starting_recovery_failed', {
            slotId,
            teamRunId: runtimeRunId,
            error: error instanceof Error ? error.message : String(error),
          });
        }
        return;
      }
      // Honor an explicit no-progress budget. With no budget, keep active
      // formalization turns alive; completed turns and transport failures use
      // the normal continuation path without discarding ongoing compiler work.
      for (const assignment of assignments) {
        if (
          assignment.state !== 'accepted' ||
          assignment.delivery ||
          assignment.integration ||
          assignment.supersessionPending ||
          assignment.budgetCancellation
        )
          continue;
        let kind: string;
        try {
          kind = normalizeRuntimeMathAssignment(assignment.assignment).request.kind;
        } catch {
          continue;
        }
        if (kind !== 'formalize') continue;
        const slot = slots.find((value) => isRecord(value) && value.slot_id === assignment.slotId);
        const turnId = isRecord(slot) && typeof slot.active_turn_id === 'string' ? slot.active_turn_id : undefined;
        const conversationId = retainedRuntime.conversations[assignment.slotId];
        if (
          !turnId ||
          !conversationId ||
          !shouldRecoverStalledLeanTurn(
            runState,
            leadSlot,
            slot,
            assignment,
            Date.now(),
            noProgressBudgetMs,
            lastCheckedEvidenceAtMs,
            enforceNoProgressBudget
          ) ||
          stalledAssignmentTurns.has(turnId)
        )
          continue;
        stalledAssignmentTurns.add(turnId);
        try {
          await request(`/api/conversations/${encodeURIComponent(conversationId)}/cancel`, {
            method: 'POST',
            body: JSON.stringify({ turn_id: turnId }),
          });
          progress('stalled_assignment_turn_cancelled', {
            assignmentId: assignment.assignmentId,
            slotId: assignment.slotId,
            turnId,
            activeTurnStartedAtMs: isRecord(slot) ? slot.active_turn_started_at_ms : undefined,
          });
        } catch (error) {
          stalledAssignmentTurns.delete(turnId);
          progress('stalled_assignment_turn_cancel_failed', {
            assignmentId: assignment.assignmentId,
            slotId: assignment.slotId,
            turnId,
            error: error instanceof Error ? error.message : String(error),
          });
        }
        return;
      }
      // Core normally wakes the Lead when a Worker delivery is projected. If
      // that wake races with cancellation, the durable delivery can remain
      // pending while the Lead slot is idle. Requeue one explicit Lead wake so
      // the accepted evidence is reviewed instead of remaining orphaned.
      const wakeDeliveryKey = pendingLeadDeliveries.map((assignment) => assignment.delivery!.deliveryId).join('|');
      if (
        shouldQueueLeadDeliveryWake({
          hasPendingDelivery: hasPendingLeadDelivery,
          deliveryKey: wakeDeliveryKey,
          leadConversationId,
          leadSlot,
          leadTurnId,
          activeRunStatus,
          alreadyQueued: leadDeliveryWakeDeliveries.has(wakeDeliveryKey),
        })
      ) {
        leadDeliveryWakeDeliveries.add(wakeDeliveryKey);
        const wakeMessage = [
          'Runtime delivery wake: durable Worker evidence is pending while the Lead slot is idle.',
          'Resume this Team turn and inspect the newest Worker delivery before dispatching any duplicate assignment.',
          'Call research_team(action="status") first, then acknowledge and integrate the delivery or choose the next concrete route action.',
          'An advisory finding or blocked boundary is progress; continue the original theorem autonomously.',
        ].join(' ');
        try {
          const dispatch = prepareMathTransportDispatch(
            `math-lead-delivery-wake-${mathDigest(wakeDeliveryKey)}`,
            wakeMessage,
            recoveryEpoch
          );
          const acknowledgement = asRecord(
            await request(
              `/api/teams/${encodeURIComponent(teamId)}/agents/${encodeURIComponent(directDispatchRuntime.lead.slotId)}/messages`,
              {
                method: 'POST',
                body: JSON.stringify({
                  content: dispatch.content,
                  idempotency_key: dispatch.idempotencyKey,
                }),
              }
            ),
            'lead delivery wake acknowledgment'
          );
          if (
            !['accepted', 'queued', 'blocked_runtime_starting'].includes(String(acknowledgement.enqueue_status || ''))
          ) {
            throw new Error('math_lead_delivery_wake_not_accepted');
          }
          progress('lead_delivery_wake_queued', {
            deliveryIds: pendingLeadDeliveries.map((assignment) => assignment.delivery!.deliveryId),
            enqueueStatus: acknowledgement.enqueue_status,
            teamRunId: acknowledgement.team_run_id,
          });
        } catch (error) {
          leadDeliveryWakeDeliveries.delete(wakeDeliveryKey);
          progress('lead_delivery_wake_queue_failed', {
            deliveryIds: pendingLeadDeliveries.map((assignment) => assignment.delivery!.deliveryId),
            error: error instanceof Error ? error.message : String(error),
          });
        }
        return;
      }
      if (
        leadTurnId &&
        leadConversationId &&
        shouldRecoverStalledLeadTurn(runState, leadSlot, hasPendingLeadDelivery, pendingLeadDeliveryAtMs) &&
        !leadDeliveryGateTurns.has(leadTurnId)
      ) {
        leadDeliveryGateTurns.add(leadTurnId);
        await request(`/api/conversations/${encodeURIComponent(leadConversationId)}/cancel`, {
          method: 'POST',
          body: JSON.stringify({ turn_id: leadTurnId }),
        });
        progress('lead_delivery_turn_cancelled', {
          turnId: leadTurnId,
          activeTurnStartedAtMs: isRecord(leadSlot) ? leadSlot.active_turn_started_at_ms : undefined,
          pendingDeliveryAtMs: pendingLeadDeliveryAtMs,
          queuedIntentCount: isRecord(runState.active_run) ? runState.active_run.queued_intent_count : undefined,
        });
        return;
      }
      for (const slot of slots) {
        const assignment = selectMathDeliveredWorkerTurn(assignments, slot, directDispatchRuntime.lead.slotId);
        if (!assignment?.delivery || !isRecord(slot)) continue;
        const delivery = assignment.delivery;
        const turnId = typeof slot.active_turn_id === 'string' ? slot.active_turn_id : undefined;
        const conversationId = retainedRuntime.conversations[assignment.slotId];
        if (!turnId || !conversationId) continue;

        const deliveryTurnStale = isWorkerDeliveryTurnStale(delivery, slot);
        const orphanedPostDeliveryTurn = !deliveryTurnStale;
        if (workerDeliveryGateTurns.has(turnId)) continue;
        await request(`/api/conversations/${encodeURIComponent(conversationId)}/cancel`, {
          method: 'POST',
          body: JSON.stringify({ turn_id: turnId }),
        });
        // Retry failed cancellation and catch each later orphaned turn, even
        // after the Lead has integrated the same durable delivery.
        workerDeliveryGateTurns.add(turnId);
        progress('worker_delivery_turn_cancelled', {
          assignmentId: assignment.assignmentId,
          deliveryId: delivery.deliveryId,
          slotId: assignment.slotId,
          turnId,
          activeTurnStartedAtMs: slot.active_turn_started_at_ms,
          deliveredAt: delivery.deliveredAt,
          orphanedPostDeliveryTurn,
        });
        break;
      }
    })()
      .catch((error) => progress('worker_delivery_gate_failed', { error: String(error) }))
      .finally(() => {
        workerDeliveryGateBusy = false;
        if (workerDeliveryGateTask === task) workerDeliveryGateTask = undefined;
        // A single delayed recovery check covers a turn that emits no durable
        // Core event while it is thinking. This is a watchdog, not a snapshot
        // polling loop: normal progress is still driven by WebSocket events.
        if (runtimeEventWake && !workerDeliveryGateWatchdog) {
          workerDeliveryGateWatchdog = setTimeout(
            () => {
              workerDeliveryGateWatchdog = undefined;
              runtimeEventWake?.();
            },
            runLimits.noProgressSeconds === undefined ? LEAD_ASSIGNMENT_WATCHDOG_MS : MATH_RECONCILIATION_POLL_MS
          );
        }
      });
    workerDeliveryGateTask = task;
    void task;
  };
  const scheduleRuntimeWatchdog = (): void => {
    if (workerDeliveryGateWatchdog || !runtimeEventWake) return;
    workerDeliveryGateWatchdog = setTimeout(
      () => {
        workerDeliveryGateWatchdog = undefined;
        runtimeEventWake?.();
      },
      runLimits.noProgressSeconds === undefined ? LEAD_ASSIGNMENT_WATCHDOG_MS : MATH_RECONCILIATION_POLL_MS
    );
  };
  runtimeEventWake = () => {
    if (workerDeliveryGateBusy) return;
    if (workerDeliveryGateWatchdog) {
      clearTimeout(workerDeliveryGateWatchdog);
      workerDeliveryGateWatchdog = undefined;
    }
    queueMicrotask(runWorkerDeliveryGate);
    scheduleRuntimeWatchdog();
  };
  runtimeEventWake();
  let observation: MathRunObservation | undefined;
  let runtimeError: string | undefined;
  try {
    observation = await eventWaiter.wait();
    if (observation.state === 'runtime_error') runtimeError = observation.reason ?? 'math_runtime_error';
  } catch (error) {
    // Persist a bounded operational outcome, never reinterpret IO failure as an unsolved theorem.
    if (runLimitReason) progress('run_limit_reached', { reason: runLimitReason });
    else {
      runtimeError = classifyMathRuntimeError(error);
      progress('runtime_failed', { reason: runtimeError });
    }
  } finally {
    runtimeEventWake = undefined;
    if (workerDeliveryGateWatchdog) clearTimeout(workerDeliveryGateWatchdog);
    workerDeliveryGateWatchdog = undefined;
    // The gate can still be in a Core request when the waiter is interrupted.
    // Let it settle before cleanup can cancel/delete the Team, otherwise a
    // stale delivery wake or turn cancellation may race resource removal.
    await waitForWorkerDeliveryGate();
    pendingEventCleanup?.();
    pendingEventCleanup = undefined;
    clearWaitTimeout();
    if (proofWallTimer) clearTimeout(proofWallTimer);
  }
  if (signalExit) return signalExit;
  // Usage is a host observation. Query it once after the proof/evaluator
  // boundary and only publish a total when every bound role exposes provider
  // token totals; partial or context-window telemetry remains unavailable.
  let observedRunTokens: number | undefined;
  if (directDispatchRuntime && coreRuntimeClient.readAgentUsage) {
    try {
      const usages = await Promise.all(
        directDispatchRuntime.roster.map((member) =>
          coreRuntimeClient.readAgentUsage!(teamId, member.slotId).catch((): undefined => undefined)
        )
      );
      if (
        usages.length > 0 &&
        usages.every((usage) => usage?.measurement === 'token_totals' && Number.isSafeInteger(usage.totalTokens))
      ) {
        observedRunTokens = usages.reduce((sum, usage) => sum + (usage?.totalTokens ?? 0), 0);
        progress('run_token_usage_observed', { totalTokens: observedRunTokens });
      } else {
        progress('run_token_usage_unavailable', {});
      }
    } catch {
      progress('run_token_usage_unavailable', {});
    }
  }
  teamRunId = observation?.teamRunId ?? manifestTeamRunId ?? teamRunId;
  runQuiescent = observation?.quiescent ?? false;
  let modelIsolationEvidence: ReturnType<typeof collectMathModelIsolationEvidence> | undefined;
  if (modelIsolation && modelIsolationPolicyFile) {
    try {
      if (!modelIsolationRun) throw new Error('math_isolation_run_binding_missing');
      sealMathModelIsolationRun({ policyFile: fs.realpathSync(modelIsolationPolicyFile), binding: modelIsolationRun });
      await pendingStartupCleanup?.(false);
      // A quiescent run can retain live ACP processes. Stop the actual session
      // before verifying a candidate or accepting final isolation evidence.
      await request(`/api/teams/${encodeURIComponent(teamId)}/session`, { method: 'DELETE' }, 120_000);
      // Core acknowledges session deletion before its ACP supervisors finish
      // exiting. Reap the receipt-bound process trees before issuing a
      // termination certificate; PID and kernel start-time checks keep this
      // cleanup safe across PID reuse.
      await cleanupMathModelIsolationProcesses({
        policyFile: fs.realpathSync(modelIsolationPolicyFile),
        binding: modelIsolationRun,
        timeoutMs: 10_000,
      });
      modelIsolationEvidence = await finalizeMathModelIsolationRun({
        policyFile: fs.realpathSync(modelIsolationPolicyFile),
        binding: modelIsolationRun,
        allowUnstartedConversations: true,
        // Core tears down ACP sessions asynchronously after the Team session
        // DELETE returns. Give bwrap/relay descendants enough time to exit
        // before treating delayed process observation as an isolation failure.
        timeoutMs: 60_000,
      });
      progress('model_isolation_terminated', { instanceCount: modelIsolationEvidence.receipts.length });
    } catch (error) {
      runtimeError = 'math_model_isolation_evidence_invalid';
      progress('model_isolation_finalization_failed', {
        reason:
          error instanceof Error && /^math_isolation_[a-z_]+$/u.test(error.message)
            ? error.message
            : 'math_isolation_finalization_unavailable',
      });
    }
  }
  const workspaceHead = await readGitHead(workspace);
  const solverReadyReceipt = observation?.solverReady;
  const solutionCommit = solverReadyReceipt?.targetCommit;
  const completionSignalValid = Boolean(
    !runtimeError && !runLimitReason && solutionCommit && solutionCommit === workspaceHead
  );
  let runOutcome = runtimeError
    ? 'runtime_error'
    : runLimitReason
      ? 'limit_reached'
      : startupOnly
        ? 'startup_verified'
        : completionSignalValid
          ? 'solver_ready'
          : 'incomplete';
  let evaluator: JsonRecord = { status: 'not_configured' };
  const proofDurationMs = Date.now() - proofStartedAt;
  if (evaluatorCommand || kernelEvaluator) {
    if (!completionSignalValid || !solverReadyReceipt) {
      evaluator = { status: 'skipped', reason: runtimeError ?? 'solver_ready_receipt_missing' };
    } else {
      verifyMathRunInputs(frozen.inputs);
      progress('evaluator_started', { solutionCommit });
      try {
        const evaluationCandidate = resolveMathEvaluationCandidate({
          workspace,
          teamId,
          assignmentId: solverReadyReceipt.assignmentId,
          binding: runBinding,
          targetCommit: solverReadyReceipt.targetCommit,
        });
        if (kernelEvaluator) {
          activeEvaluation = timing.measure('final_evaluator', () =>
            runMathKernelEvaluation({
              workspace,
              commit: solverReadyReceipt.targetCommit,
              binding: runBinding,
              candidate: evaluationCandidate,
              signal: evaluationAbort.signal,
            })
          );
          const result = await activeEvaluation;
          const verificationReceiptFile = `${output}.kernel-evaluation.json`;
          writeMathJsonDurable(verificationReceiptFile, result);
          const { verification, ...summary } = result;
          evaluator = {
            ...summary,
            verificationReceiptFile,
            verificationReceiptDigest: mathDigest(fs.readFileSync(verificationReceiptFile)),
            ...(verification.diagnostics ? { reason: verification.diagnostics } : {}),
          };
        } else {
          activeEvaluation = timing.measure('final_evaluator', () =>
            runMathEvaluation({
              signal: evaluationAbort.signal,
              runId: runBinding.runId,
              receiptId: solverReadyReceipt.receiptId,
              workspace,
              commit: solverReadyReceipt.targetCommit,
              runInputs: frozen.inputs,
              root: evaluationRoot,
              cgroupRoot: evaluatorCgroupRoot!,
              supervisor: evaluatorSupervisor!,
              command: evaluatorCommand!,
              timeoutMs: evaluatorTimeoutSeconds * 1000,
              environment: runtimeEnv,
              baseCommit,
              flockExecutable: '/usr/bin/flock',
              protectedPaths: evaluatorProtectedPaths,
              candidate: evaluationCandidate,
              ...(fs.existsSync(path.join(receiptProjectRoot, '.lake', 'packages'))
                ? {
                    lakePackages: {
                      projectRelative: path.relative(workspace, receiptProjectRoot),
                      path: path.join(receiptProjectRoot, '.lake', 'packages'),
                    },
                  }
                : {}),
            })
          );
          evaluator = await activeEvaluation;
        }
        if (evaluator.status === 'error' || evaluator.status === 'timeout') {
          runtimeError = `math_evaluator_${evaluator.status}`;
          runOutcome = 'runtime_error';
        } else if (evaluator.status === 'interrupted') {
          runtimeError = 'math_evaluator_interrupted';
          runOutcome = 'runtime_error';
        }
      } catch {
        runtimeError = 'math_evaluator_runtime_error';
        runOutcome = 'runtime_error';
        evaluator = { status: 'error', reason: runtimeError };
      }
      progress('evaluator_finished', { status: evaluator.status, durationMs: evaluator.durationMs });
    }
  }
  if (signalExit) return signalExit;
  const receiptStatus = runtimeError
    ? 'runtime_error'
    : runLimitReason
      ? 'limit_reached'
      : evaluator.status === 'passed'
        ? 'evaluated_passed'
        : evaluator.status === 'failed'
          ? 'evaluated_failed'
          : 'incomplete';
  const searchObservations = readMathProofSearchObservations({
    workspace,
    teamId,
  });
  const benchmarkMetrics = deriveMathProofRunMetric({
    runId: mathDigest(canonicalMathJson(frozen.inputs)),
    runIdentity: mathDigest(canonicalMathJson(frozen.inputs)),
    problemId: problemContract.problemId,
    benchmarkMethod,
    repetition,
    receipt: {
      status: receiptStatus,
      solver_ready_receipt_valid: Boolean(solverReadyReceipt),
      completion_signal_valid: completionSignalValid,
      startup_only: startupOnly,
      ...(runtimeError ? { error_code: runtimeError } : {}),
      durations_ms: { proof: proofDurationMs, evaluator: evaluator.durationMs ?? 0 },
      evaluator,
    },
    totalTokens: observedRunTokens,
    tokenUsageSource: observedRunTokens === undefined ? undefined : 'provider',
    verifierStatus: runtimeError
      ? 'unavailable'
      : solverReadyReceipt
        ? completionSignalValid
          ? 'passed'
          : 'failed'
        : 'missing',
    searchObservations,
  });
  const receipt = {
    schema: 'deepscientist.mathematics.proof-team-run.v2',
    status: receiptStatus,
    ...(runtimeError ? { error_code: runtimeError } : {}),
    ...(runLimitReason ? { limit_reason: runLimitReason } : {}),
    team_id: teamId,
    team_run_id: teamRunId,
    run_id: runBinding.runId,
    run_inputs_digest: mathDigest(canonicalMathJson(frozen.inputs)),
    run_binding_ref: frozen.inputs.binding!.path,
    run_binding_digest: frozen.inputs.binding!.digest,
    build_manifest_ref: buildManifestRef,
    build_manifest_digest: mathDigest(fs.readFileSync(buildManifestRef)),
    budget_accounting: budgetAccounting,
    model,
    lead_model: leadModel,
    worker_model: workerModel,
    thought_levels: {
      lead: leadThoughtLevel ?? 'provider-default',
      worker: workerThoughtLevel ?? 'provider-default',
    },
    durations_ms: { proof: proofDurationMs, evaluator: evaluator.durationMs ?? 0 },
    timing_diagnostics: timing.snapshot(),
    model_isolation: modelIsolationEvidence ?? null,
    proof_progress: proofProgress.snapshot(),
    efficiency: (() => {
      try {
        return summarizeMathRunEfficiency({
          assignments: teamId ? listProjectGitResearchTeamAssignments({ workspace, teamId, strict: true }) : [],
          turnsBySlot,
          startedAt: proofClockStartedAt,
        });
      } catch {
        return null;
      }
    })(),
    proof_impact: compactMathProofImpactSummary(
      readMathProofImpactSummary(artifactRunRoot, runBinding.runId, { targetCommit: workspaceHead })
    ),
    run_limits: runLimits,
    assignment_counts: observation?.assignmentCounts ?? null,
    incomplete_reason: observation?.state === 'incomplete' ? (observation.reason ?? null) : null,
    solver_ready: Boolean(solverReadyReceipt),
    solver_ready_receipt_valid: Boolean(solverReadyReceipt),
    solver_ready_receipt_id: solverReadyReceipt?.receiptId ?? null,
    solution_commit: solutionCommit ?? null,
    completion_evidence: solverReadyReceipt ? 'runtime_receipt' : 'missing',
    completion_signal_valid: completionSignalValid,
    startup_only: startupOnly,
    run_outcome: runOutcome,
    evaluator,
    benchmark_metrics: benchmarkMetrics,
    completed_at: new Date().toISOString(),
  };
  fs.mkdirSync(path.dirname(output), { recursive: true });
  const receiptJson = canonicalMathJson(receipt);
  if (Buffer.byteLength(receiptJson) >= 32768 - 1024) throw new Error('math_final_receipt_too_large');
  lifecycleState = runOutcome;
  const removeResources = shouldRemoveMathProofTeamResources({
    startupOnly,
    runtimeError,
    runQuiescent,
    completionSignalValid,
    evaluatorStatus: typeof evaluator.status === 'string' ? evaluator.status : undefined,
  });
  cleanupOutcome = {
    status: startupOnly || runLimitReason || removeResources ? 'pending' : 'retained',
    reason: removeResources ? 'remove_resources' : 'preserve_recovery_resources',
    resourcesRemoved: false,
    manifestRetained: true,
  };
  const finalized = await finalizeMathRunReceipt({
    output,
    receipt,
    pending: cleanupOutcome,
    cleanup: async () => {
      writeCleanupManifest();
      if (startupOnly || runLimitReason) await pendingStartupCleanup?.(false);
      if (removeResources) await pendingStartupCleanup?.(true);
      await pendingProofEnvironmentCleanup?.();
      return cleanupOutcome;
    },
  });
  const exitCode = mathRunExitCode({
    runtimeError,
    limitReached: runLimitReason,
    startupOnly,
    completionSignalValid,
    evaluatorStatus: evaluator.status,
    cleanup: finalized.cleanup,
  });
  progress('runner_finished', {
    teamId,
    teamRunId,
    status: receipt.status,
    evaluatorStatus: evaluator.status,
    cleanupStatus: finalized.cleanup.status,
    exitCode,
  });
  process.stdout.write(
    `${JSON.stringify({
      status: receipt.status,
      run_outcome: runOutcome,
      team_id: teamId,
      output,
      solution_commit: solutionCommit ?? null,
      evaluator_status: evaluator.status,
      cleanup: finalized.cleanup,
      exit_code: exitCode,
    })}\n`
  );
  process.exit(exitCode);
}

async function cleanupMathProofTeamRun(coreUrl: string, manifestPath: string): Promise<void> {
  const completedPath = `${manifestPath}.completed`;
  const sourcePath = fs.existsSync(completedPath) ? completedPath : manifestPath;
  const raw = readMathJson(sourcePath) as JsonRecord;
  if (sourcePath === completedPath && fs.existsSync(manifestPath)) {
    const { cleanup: _completedCleanup, ...completedIdentity } = raw;
    const { cleanup: _pendingCleanup, ...pendingIdentity } = asRecord(readMathJson(manifestPath), 'cleanup manifest');
    if (canonicalMathJson(completedIdentity) !== canonicalMathJson(pendingIdentity))
      throw new Error('math_cleanup_journal_changed');
  }
  if (raw.schema !== 'deepscientist.mathematics.proof-team-cleanup.v1') {
    throw new Error('invalid mathematics proof cleanup manifest schema');
  }
  const manifestCoreUrl = String(raw.core_url ?? '').trim();
  if (!manifestCoreUrl) throw new Error('cleanup manifest is missing core_url');
  if (new URL(manifestCoreUrl).origin !== new URL(coreUrl).origin) {
    throw new Error('cleanup manifest core_url does not match --core-url');
  }
  const teamId =
    raw.team_id === null || raw.team_id === undefined ? undefined : stableRunnerResourceId(raw.team_id, 'team_id');
  const teamRunId =
    raw.team_run_id === null || raw.team_run_id === undefined
      ? undefined
      : stableRunnerResourceId(raw.team_run_id, 'team_run_id');
  const assistantIds = stableRunnerResourceIds(raw.assistant_ids, 'assistant_ids');
  const mcpServerIds = stableRunnerResourceIds(raw.mcp_server_ids, 'mcp_server_ids');
  if (raw.resource_identity_digest !== undefined && raw.resource_identity_digest !== null) {
    if (
      typeof raw.resource_identity_digest !== 'string' ||
      !MATH_RESUME_DIGEST_PATTERN.test(raw.resource_identity_digest) ||
      !teamId ||
      raw.resource_identity_digest !==
        mathProofResourceIdentityDigest({
          teamId,
          teamRunId,
          assistantIds,
          mcpServerIds,
        })
    ) {
      throw new Error('invalid cleanup manifest resource identity digest');
    }
  }
  const runInputs = verifyMathRunInputs(raw.run_inputs);
  const runBinding = readMathRunBinding(runInputs);
  const finalizeCleanup = (): void => {
    if (raw.result_ref !== undefined) {
      if (typeof raw.result_ref !== 'string' || !path.isAbsolute(raw.result_ref))
        throw new Error('math_cleanup_receipt_path_invalid');
      recoverMathRunReceiptCleanup({
        output: raw.result_ref,
        identity: {
          run_id: runBinding.runId,
          team_id: teamId ?? null,
          run_inputs_digest: mathDigest(canonicalMathJson(runInputs)),
          run_binding_ref: runInputs.binding!.path,
          run_binding_digest: runInputs.binding!.digest,
        },
      });
    }
    if (fs.existsSync(manifestPath)) fs.unlinkSync(manifestPath);
    syncMathDirectory(path.dirname(manifestPath));
  };
  if (sourcePath === completedPath) {
    if (!isRecord(raw.cleanup) || raw.cleanup.status !== 'completed') throw new Error('math_cleanup_journal_invalid');
    finalizeCleanup();
    return;
  }
  const failures: string[] = [];
  if (raw.budget_conversation_ids !== undefined) {
    const ids = stableRunnerResourceIds(raw.budget_conversation_ids, 'budget_conversation_ids');
    if (ids.length) {
      const client = createMathBudgetHostClient({
        baseUrl: coreUrl,
        hostSecret: process.env.DEEPSCIENTIST_MATH_BUDGET_HOST_SECRET ?? '',
      });
      const results = await Promise.allSettled(ids.map((id) => client.revoke(id)));
      if (results.some((result) => result.status === 'rejected')) throw new Error('math_budget_team_cleanup_failed');
    }
  }
  const remove = async (pathname: string): Promise<boolean> => {
    try {
      const response = await fetch(`${coreUrl}${pathname}`, {
        method: 'DELETE',
        headers: { 'content-type': 'application/json' },
        signal: AbortSignal.timeout(30_000),
      });
      if (response.ok || response.status === 404) return true;
      failures.push(`Core ${response.status} for ${pathname}`);
      return false;
    } catch (error) {
      failures.push(`${pathname}: ${error instanceof Error ? error.message : String(error)}`);
      return false;
    }
  };
  const post = async (pathname: string, body: JsonRecord): Promise<boolean> => {
    try {
      const response = await fetch(`${coreUrl}${pathname}`, {
        method: 'POST',
        headers: { 'content-type': 'application/json' },
        body: JSON.stringify(body),
        signal: AbortSignal.timeout(30_000),
      });
      if (response.ok || response.status === 404) return true;
      failures.push(`Core ${response.status} for ${pathname}`);
      return false;
    } catch (error) {
      failures.push(`${pathname}: ${error instanceof Error ? error.message : String(error)}`);
      return false;
    }
  };
  const readRunStateSnapshot = async (): Promise<{ quiescent: boolean; teamRunId?: string } | undefined> => {
    if (!teamId) return { quiescent: true };
    try {
      const response = await fetch(`${coreUrl}/api/teams/${encodeURIComponent(teamId)}/run-state`, {
        method: 'GET',
        headers: { 'content-type': 'application/json' },
        signal: AbortSignal.timeout(30_000),
      });
      if (response.status === 404) return { quiescent: true };
      if (!response.ok) {
        failures.push(`Core ${response.status} for team run state`);
        return undefined;
      }
      const payload = (await response.json()) as JsonRecord;
      if (payload.success === false) {
        failures.push('Core rejected team run state cleanup read');
        return undefined;
      }
      const data =
        payload.data && typeof payload.data === 'object' && !Array.isArray(payload.data)
          ? (payload.data as JsonRecord)
          : payload;
      const run = isRecord(data.run) && !Object.prototype.hasOwnProperty.call(data, 'active_run') ? data.run : data;
      if (!Object.prototype.hasOwnProperty.call(run, 'active_run') || !Array.isArray(run.slot_work)) {
        failures.push('Core returned an incomplete team run state cleanup snapshot');
        return undefined;
      }
      // Quiescence is a property of the complete durable snapshot. Checking
      // only active_run incorrectly treats a busy top-level slot_work array as
      // stopped when Core has no active_run projection.
      const activeRun =
        run.active_run && typeof run.active_run === 'object' && !Array.isArray(run.active_run)
          ? (run.active_run as JsonRecord)
          : undefined;
      const quiescent = isResearchTeamRunQuiescent(run);
      return {
        quiescent,
        ...(!quiescent
          ? {
              teamRunId: String(
                (activeRun?.team_run_id ?? run.team_run_id ?? runnerActiveRunId(run) ?? '').toString()
              ).trim(),
            }
          : {}),
      };
    } catch (error) {
      failures.push(`team run state: ${error instanceof Error ? error.message : String(error)}`);
      return undefined;
    }
  };
  if (teamId) {
    const sessionStopped = await remove(`/api/teams/${encodeURIComponent(teamId)}/session`);
    if (!sessionStopped) throw new Error(`MATHEMATICS_RUNTIME_CLEANUP_FAILED:session:${failures.length}`);
    const initialState = await readRunStateSnapshot();
    if (!initialState) throw new Error(`MATHEMATICS_RUNTIME_CLEANUP_FAILED:state:${failures.length}`);
    const activeRunId = selectMathCleanupRunId(teamRunId, initialState);
    if (!initialState.quiescent && !activeRunId) {
      failures.push('active Team run has no team_run_id');
      throw new Error(`MATHEMATICS_RUNTIME_CLEANUP_FAILED:run_id:${failures.length}`);
    }
    if (activeRunId && !initialState.quiescent) {
      const cancelled = await post(
        `/api/teams/${encodeURIComponent(teamId)}/runs/${encodeURIComponent(activeRunId)}/cancel`,
        { reason: 'durable mathematics proof runner cleanup' }
      );
      if (!cancelled) throw new Error(`MATHEMATICS_RUNTIME_CLEANUP_FAILED:cancel:${failures.length}`);
    }
    let quiescent = false;
    for (let attempt = 0; attempt < 20; attempt += 1) {
      const observed = await readRunStateSnapshot();
      if (observed?.quiescent === true) {
        quiescent = true;
        break;
      }
      if (!observed) break;
      await new Promise<void>((resolve) => setTimeout(resolve, 500));
    }
    if (!quiescent) throw new Error(`MATHEMATICS_RUNTIME_CLEANUP_FAILED:active_run:${failures.length}`);
  }
  if (teamId) {
    const teamRemoved = await remove(`/api/teams/${encodeURIComponent(teamId)}`);
    if (!teamRemoved) throw new Error(`MATHEMATICS_RUNTIME_CLEANUP_FAILED:team:${failures.length}`);
  }
  await Promise.all([
    ...assistantIds.map((id) => remove(`/api/assistants/${encodeURIComponent(id)}`)),
    ...mcpServerIds.map((id) => remove(`/api/mcp/servers/${encodeURIComponent(id)}`)),
  ]);
  if (failures.length) throw new Error(`MATHEMATICS_RUNTIME_CLEANUP_FAILED:${failures.length}`);
  if (teamId) {
    discardLeanEvalTeamWorkspacesForTeam({ projectRoot: runBinding.projectRoot, teamId });
  }
  // Keep a durable completion journal across a crash before receipt finalization.
  const completed = {
    ...raw,
    cleanup: { status: 'completed', reason: 'resources_removed', resourcesRemoved: true, manifestRetained: false },
  };
  if (fs.existsSync(completedPath) && canonicalMathJson(readMathJson(completedPath)) !== canonicalMathJson(completed))
    throw new Error('math_cleanup_journal_changed');
  writeMathJsonDurable(completedPath, completed);
  finalizeCleanup();
}

export function selectMathCleanupRunId(
  retainedTeamRunId: string | undefined,
  snapshot: Readonly<{ quiescent: boolean; teamRunId?: string }>
): string | undefined {
  if (snapshot.quiescent) return undefined;
  // Never cancel a retained ID when the authoritative snapshot is busy but
  // does not identify its active run. It may refer to an unrelated run.
  void retainedTeamRunId;
  return snapshot.teamRunId?.trim() || undefined;
}

/**
 * Enter cleanup after an authenticated solver completion. Cleanup must itself
 * cancel residual work and confirm quiescence before deleting resources.
 * Startup checks, runtime failures and incomplete runs retain their manifest.
 */
export function shouldRemoveMathProofTeamResources(
  input: Readonly<{
    startupOnly: boolean;
    runtimeError?: string;
    runQuiescent: boolean;
    completionSignalValid: boolean;
    evaluatorStatus?: string;
  }>
): boolean {
  return (
    input.startupOnly === false &&
    !input.runtimeError &&
    input.completionSignalValid === true &&
    input.evaluatorStatus === 'passed'
  );
}

function stableRunnerResourceId(value: unknown, field: string): string {
  const normalized = String(value ?? '').trim();
  if (!/^[A-Za-z0-9][A-Za-z0-9._:-]{0,127}$/u.test(normalized)) {
    throw new Error(`invalid cleanup manifest ${field}`);
  }
  return normalized;
}

function stableRunnerResourceIds(value: unknown, field: string): readonly string[] {
  if (!Array.isArray(value)) throw new Error(`invalid cleanup manifest ${field}`);
  const ids = value.map((item) => stableRunnerResourceId(item, field));
  if (new Set(ids).size !== ids.length) throw new Error(`duplicate cleanup manifest ${field}`);
  return Object.freeze(ids);
}

function getRequiredMcpNames(role: ResearchTeamRoleContract): readonly string[] {
  // Keep this local to the proof runner so an accidental IOAI mode change
  // cannot add a challenge acquisition adapter or a second coordinator.
  void role;
  return [
    BUILTIN_RESEARCH_TEAM_NAME,
    BUILTIN_SCIENCE_ARTIFACT_NAME,
    ...(role.allowedTools.some((tool) => tool.toolName === 'research_evidence')
      ? [BUILTIN_RESEARCH_EVIDENCE_NAME]
      : []),
  ];
}

if (process.argv[1] && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  main().catch(async (error) => {
    pendingEventCleanup?.();
    try {
      try {
        await pendingStartupCleanup?.(false);
      } finally {
        await pendingProofEnvironmentCleanup?.();
      }
    } catch {
      console.error('math_runner_cleanup_incomplete');
    }
    console.error(error instanceof Error ? error.stack || error.message : String(error));
    process.exit(1);
  });
}
