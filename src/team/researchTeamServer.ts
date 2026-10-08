import { contractMathNamedProofDispatch } from "../math/mathProofEfficiencyExecution";
import { recordMathProofImpact } from "../math/mathProofImpact";
/**
 * @license
 * Copyright 2026 DeepScientist (deepscientist.cc)
 * SPDX-License-Identifier: Apache-2.0
 */

import { selectMathematicsMethodHints } from "../common/chat/team/mathematicsMethodHints";
import { MATHEMATICS_WORKED_EXAMPLES } from "../common/chat/team/mathematicsWorkedExamples";
import {
  publishMathLiteBlockerBoundary,
  readMathLiteBlockerLineage,
} from "../math/mathLiteBlockerContext";
import { McpServer, type ToolCallback } from '@modelcontextprotocol/sdk/server/mcp.js';
import { StdioServerTransport } from '@modelcontextprotocol/sdk/server/stdio.js';
import type { Transport } from '@modelcontextprotocol/sdk/shared/transport.js';
import fs from 'node:fs';
import path from 'node:path';
import { execFileSync } from 'node:child_process';
import { z } from 'zod';
import {
  readMathLiteFeedback,
  readMathLiteBlockedEvidenceRevision,
  recordMathLiteBlockedEvidence,
  readMathLiteFeedbackArtifact,
  recordMathLiteFeedbackUse,
  mathLiteFeedbackCursor,
  acknowledgeMathLiteResearchWait,
  mathLiteProofContextArtifactId,
  mathLiteInitialProofContextArtifactId,
  readLatestMathLiteProgress,
} from "../math/mathLiteFeedback";
import { installMathMcpShutdown } from "../math/mathMcpShutdown";
import { RESEARCH_TEAM_CORE_BASE_URL_ENV } from "../common/config/builtinMcpConstants";
import type { ResearchTeamMcpAction } from "../common/types/team/researchTeamMcp";
import { TEAM_WAIT_LEVELS } from "../common/types/team/teamWaitPolicy";
import {
  createResearchCoreTeamClient,
  isResearchSlotReadyForSuccessor,
  type ResearchCoreTeamClient,
} from "./coreTeamClient";
import { runResearchTeamTool } from "./researchTeamTool";
import { ResearchTeamOrchestrationError } from "./orchestrator";
import { resolveTeamAgentSlotId } from "../common/types/team/teamAgentIds";
import { isTeamRunAckPersisted } from "../common/types/team/teamTypes";
import { projectRuntimeMathAssignmentToExecutionView } from "../math/mathAssignmentExecutionAdapter";
import {
  isMathLiteRunEnvironment,
  MATH_RUN_INPUTS_ENV,
  verifyMathRunInputs,
  verifyMathRunInputsEnvironment,
} from "../math/mathRunInputs";
import {
  assertMathCanonicalPath,
  isMathPathWithin,
  readMathRunBinding,
  resolveMathRunProjectPaths,
} from "../math/mathRunBinding";
import { MathArtifactStore, MathArtifactError } from "../math/mathArtifactStore";
import { isMathPlanningSafetyError } from "../math/mathPlanningContext";
import { MathIntegrationJournal } from "../math/mathIntegrationJournal";
import {
  hasMathV2BlockedDelivery,
  selectMathV2IntegrationDelivery,
} from "../math/mathIntegrationSelector";
import { MathAssignmentRegistry } from "../math/mathAssignmentRegistry";
import {
  buildMathAssignmentResearchGraph,
  mathAssignmentResearchQuestionId,
  mathAssignmentResearchEvidenceVersion,
} from "../math/mathAssignmentResearchGraph";
import { normalizeRuntimeMathAssignment } from "../math/mathAssignmentJournal";
import {
  mathArtifactReadShape,
  mathLiteDeliveryIntentSchema,
  mathLiteProgressIntentSchema,
  mathLiteProgressSnapshotSchema,
  mathResearchQuestionSchema,
  normalizeMathProgressSummary,
  mathSourceArtifactSchema,
  normalizeMathLiteDeliveryIntent,
} from "../math/mathPublicWire";
import {
  mathLiteDeliveryArtifactId,
  freezeMathLiteDeliveryFileSet,
  readMathLiteSealedSet,
  prepareMathLiteWorkerDelivery,
  writeMathLiteSealedSet,
  type MathLiteSealedSet,
} from "../math/mathWorkerDeliveryAdapter";
import { recoverMathV2SourceStages, stageMathV2Sources } from "../math/mathSourceStaging";
import type { MathSourceArtifact, MathResearchQuestion } from "../common/types/team/mathRuntimeContracts";
import {
  readMathJson,
  canonicalMathJson,
  mathDigest,
  withMathRuntimeLease,
  writeMathJsonDurable,
} from "../math/mathRuntimeIo";
import { createMathematicsMcpValidator, withMathematicsMcpValidation } from "./mathematicsMcpValidation";
import {
  certifyFormalVerifications,
  commitMathV2PromotionWorktree,
  verifyMathV2SourceCommit,
  createLeanEvalStructuredSearchProvider,
  readLeanEvalStructuredSearchConfig,
  runLeanEvalCounterexampleProbe,
  runImo2026HostFastCheck,
  runMathematicsRoutePreflight,
  checkLeanToolchainReadiness,
  verifyMathematicsHelperNode,
} from "../math/index";
import { runLeanEvalTeamSession } from "../math/leanEvalTeamSession";
import {
  discardLeanEvalTeamWorkspace,
  hasLeanEvalTeamWorkspace,
  integrateLeanEvalTeamWorkspace,
  prepareLeanEvalTeamWorkspace,
} from "../math/leanEvalTeamWorkspace";
import {
  discardProjectGitAgentWorktree,
  integrateProjectGitAgentBranch,
  listProjectGitResearchTeamAssignments,
  recordProjectGitResearchTeamAssignment,
  createProjectGitResearchTeamDeliveryId,
  recordProjectGitResearchTeamBudgetCancellation,
  recordProjectGitResearchTeamDelivery,
  recordProjectGitResearchTeamSupersessionPending,
  readProjectGitResearchTeamAssignment,
  completeProjectGitResearchTeamAssignment,
  supersedeProjectGitResearchTeamAssignment,
  prepareProjectGitAgentWorktree,
  isProjectGitCommitAncestor,
  resolveProjectGitCommit,
  type ProjectGitIntegrateAgentBranchRequest,
  type ProjectGitDiscardAgentWorktreeRequest,
} from "../project-git/index";
import {
  readBoundResearchTeamToolCapability,
  readResearchTeamRoleCapability,
  resolveResearchTeamRuntimeCapability,
} from "./toolCapability";

// Matches the public mathAssignmentShape inputs limit.
const MATH_ASSIGNMENT_INPUT_LIMIT = 16;

const RESEARCH_TEAM_SERVER_NAME = 'DeepScientist Research Team';

const compactStringList = (maxItems: number) =>
  z.preprocess((value) => (typeof value === 'string' ? [value] : value), z.array(z.string()).max(maxItems));

/**
 * Leads often copy both selectors from a delivery notice. A delivery id ends
 * with its assignment id, so the pair is unambiguous when they agree; rejecting
 * it only cost an integrate retry (run 23).
 */
export function isConsistentDeliverySelectorPair(value: {
  result?: unknown;
  delivery_id?: string;
  assignment_id?: string;
}): boolean {
  return (
    value.result === undefined &&
    typeof value.delivery_id === 'string' &&
    typeof value.assignment_id === 'string' &&
    value.assignment_id.trim() !== '' &&
    value.delivery_id.split(':').at(-1) === value.assignment_id.trim()
  );
}

function stableLeanEvalBranchSegment(value: string): string {
  const normalized = value
    .trim()
    .toLowerCase()
    .replace(/[^a-z0-9]+/gu, '-')
    .replace(/^-+|-+$/gu, '')
    .slice(0, 36);
  if (!normalized) throw new Error('Lean-Eval assignment cannot form a stable branch segment');
  return normalized;
}

function createResearchTeamProjectGitDriver() {
  const defaultDriver = {
    prepareAgentWorktree: prepareProjectGitAgentWorktree,
    resolveCommit: resolveProjectGitCommit,
    isCommitAncestor: isProjectGitCommitAncestor,
    discardAgentWorktree: discardProjectGitAgentWorktree,
    integrateAgentBranch: integrateProjectGitAgentBranch,
    recordResearchTeamAssignment: recordProjectGitResearchTeamAssignment,
    recordResearchTeamDelivery: recordProjectGitResearchTeamDelivery,
    recordResearchTeamBudgetCancellation: recordProjectGitResearchTeamBudgetCancellation,
    recordResearchTeamSupersessionPending: recordProjectGitResearchTeamSupersessionPending,
    readResearchTeamAssignment: readProjectGitResearchTeamAssignment,
    listResearchTeamAssignments: listProjectGitResearchTeamAssignments,
    completeResearchTeamAssignment: completeProjectGitResearchTeamAssignment,
    supersedeResearchTeamAssignment: supersedeProjectGitResearchTeamAssignment,
  };
  return Object.freeze({
    ...defaultDriver,
    integrateAgentBranch: (request: ProjectGitIntegrateAgentBranchRequest) => {
      if (request.assignmentId && hasLeanEvalTeamWorkspace(request.workspace, request.assignmentId)) {
        const isolated = integrateLeanEvalTeamWorkspace({
          projectRoot: request.workspace,
          assignmentId: request.assignmentId,
          branch: request.branch,
          ...(request.expectedHead ? { expectedHead: request.expectedHead } : {}),
          ...(request.summary ? { summary: request.summary } : {}),
        });
        return isolated.ok
          ? {
              ok: true,
              branch: isolated.branch,
              mergedCommit: isolated.mergedCommit,
              alreadyIntegrated: isolated.alreadyIntegrated,
            }
          : { ok: false, error: isolated.error };
      }
      return defaultDriver.integrateAgentBranch(request);
    },
    discardAgentWorktree: (request: ProjectGitDiscardAgentWorktreeRequest) => {
      if (request.assignmentId && hasLeanEvalTeamWorkspace(request.workspace, request.assignmentId)) {
        discardLeanEvalTeamWorkspace({ projectRoot: request.workspace, assignmentId: request.assignmentId });
        return { ok: true, discarded: true };
      }
      return defaultDriver.discardAgentWorktree(request);
    },
  });
}

async function main(): Promise<void> {
  const researchTeamRoleCapability = readResearchTeamRoleCapability();
  if (!researchTeamRoleCapability) {
    throw new Error('Dedicated Research Team MCP requires a bound Research Team role capability');
  }
  const leanEvalStructuredSearchConfig = readLeanEvalStructuredSearchConfig();
  const leanEvalStructuredSearchProvider = leanEvalStructuredSearchConfig
    ? createLeanEvalStructuredSearchProvider(leanEvalStructuredSearchConfig)
    : undefined;
  let researchTeamCapability = readBoundResearchTeamToolCapability();
  let researchTeamCapabilityKey = researchTeamCapabilityCacheKey(researchTeamCapability);
  let researchTeamCapabilityResolution: Promise<NonNullable<typeof researchTeamCapability> | undefined> | undefined;
  let researchTeamCapabilityResolutionKey: string | undefined;
  let researchTeamClient: ResearchCoreTeamClient | undefined;
  let researchTeamClientBaseUrl: string | undefined;
  let mathArtifactStore: MathArtifactStore | undefined;
  let mathArtifactStoreInitialization: Promise<MathArtifactStore> | undefined;
  let mathIntegrationJournal: MathIntegrationJournal | undefined;
  let mathAssignmentRegistry: MathAssignmentRegistry | undefined;
  const ensureMathArtifactStore = async (expectedProjectRoot: string): Promise<MathArtifactStore> => {
    if (mathArtifactStore) return mathArtifactStore;
    if (!mathArtifactStoreInitialization) {
      mathArtifactStoreInitialization = (async () => {
        const encoded = process.env[MATH_RUN_INPUTS_ENV];
        if (!encoded) throw new Error('Mathematics run binding is unavailable.');
        const inputs = verifyMathRunInputs(JSON.parse(encoded));
        const binding = readMathRunBinding(inputs);
        resolveMathRunProjectPaths(binding, expectedProjectRoot);
        const store = new MathArtifactStore({
          runRoot: path.dirname(binding.artifactStoreRoot),
          runId: binding.runId,
          flockExecutable: '/usr/bin/flock',
        });
        await store.initialize();
        await store.recover();
        mathArtifactStore = store;
        return store;
      })().catch((error) => {
        mathArtifactStoreInitialization = undefined;
        throw error;
      });
    }
    return mathArtifactStoreInitialization;
  };
  const getMathIntegrationJournal = (): MathIntegrationJournal => {
    if (mathIntegrationJournal) return mathIntegrationJournal;
    const encoded = process.env[MATH_RUN_INPUTS_ENV];
    if (!encoded) throw new Error('Mathematics run binding is unavailable.');
    const inputs = verifyMathRunInputs(JSON.parse(encoded));
    const binding = readMathRunBinding(inputs);
    if (!researchTeamCapability) throw new Error('Mathematics Team capability is unavailable.');
    resolveMathRunProjectPaths(binding, researchTeamCapability.projectRoot);
    mathIntegrationJournal = new MathIntegrationJournal({
      runRoot: path.dirname(binding.artifactStoreRoot),
      flockExecutable: '/usr/bin/flock',
      resolveCanonicalHead: () => resolveProjectGitCommit({ workspace: binding.workspace, reference: 'HEAD' }),
      isCanonicalHeadAtOrAfter: (mergedCommit) =>
        isProjectGitCommitAncestor({ workspace: binding.workspace, ancestor: mergedCommit, descendant: 'HEAD' }),
    });
    return mathIntegrationJournal;
  };
  const getMathAssignmentRegistry = (): MathAssignmentRegistry => {
    if (mathAssignmentRegistry) return mathAssignmentRegistry;
    const encoded = process.env[MATH_RUN_INPUTS_ENV];
    if (!encoded || !researchTeamCapability) throw new Error('Mathematics run binding is unavailable.');
    const binding = readMathRunBinding(verifyMathRunInputs(JSON.parse(encoded)));
    resolveMathRunProjectPaths(binding, researchTeamCapability.projectRoot);
    const projectGit = createResearchTeamProjectGitDriver();
    const ensureStore = async (): Promise<MathArtifactStore> => {
      if (mathArtifactStore) return mathArtifactStore;
      if (!mathArtifactStoreInitialization) {
        mathArtifactStoreInitialization = (async () => {
          const store = new MathArtifactStore({
            runRoot: path.dirname(binding.artifactStoreRoot),
            runId: binding.runId,
            flockExecutable: '/usr/bin/flock',
          });
          await store.initialize();
          await store.recover();
          mathArtifactStore = store;
          return store;
        })().catch((error) => {
          mathArtifactStoreInitialization = undefined;
          throw error;
        });
      }
      return mathArtifactStoreInitialization;
    };
    mathAssignmentRegistry = new MathAssignmentRegistry({
      binding,
      teamId: researchTeamCapability.teamId,
      workerIds: new Set(
        researchTeamCapability.roster.filter((member) => member.roleKind === 'worker').map((member) => member.slotId)
      ),
      flockExecutable: '/usr/bin/flock',
      assertBinding: () => verifyMathRunInputsEnvironment(process.env),
      ports: {
        readAssignments: () =>
          projectGit.listResearchTeamAssignments?.({
            workspace: binding.workspace,
            teamId: researchTeamCapability!.teamId,
            strict: true,
          }) ?? [],
        recordAssignment: (request) => projectGit.recordResearchTeamAssignment!(request),
        currentCommit: () => resolveProjectGitCommit({ workspace: binding.workspace, reference: 'HEAD' }),
        isCommitAncestor: (ancestor, descendant) =>
          isProjectGitCommitAncestor({ workspace: binding.workspace, ancestor, descendant }),
        assertReadPath: (relativePath, commit) => {
          const absolute = path.resolve(binding.projectRoot, relativePath);
          assertMathCanonicalPath(absolute);
          if (!isMathPathWithin(binding.projectRoot, absolute)) throw new Error('math_read_path_outside_project');
          const repositoryPath = path.relative(binding.workspace, absolute).split(path.sep).join('/');
          execFileSync('git', ['-C', binding.workspace, 'cat-file', '-e', `${commit}:${repositoryPath}`], {
            stdio: 'ignore',
          });
        },
        assertWritePath: (relativePath) => assertMathCanonicalPath(path.resolve(binding.projectRoot, relativePath)),
        grantArtifacts: async (artifactId) => (await ensureStore()).grantedClosure(artifactId, { role: 'lead' }),
        predecessorEnded: async (receipt) => {
          if (
            !researchTeamClient ||
            (receipt.state !== 'integrated' &&
              receipt.state !== 'superseded' &&
              receipt.integration?.verification?.disposition !== 'candidate_rejected' &&
              !hasMathV2BlockedDelivery(receipt))
          )
            return false;
          // A sealed result or failed proof check ends the candidate, not the
          // Worker turn. Verify the old execution ended before reserving a repair.
          const state = await researchTeamClient.readRunState(researchTeamCapability!.teamId, undefined, true);
          return isResearchSlotReadyForSuccessor(state, researchTeamCapability!.teamId, receipt.slotId);
        },
        supersedeAssignment: ({ receipt, winnerAssignmentId, reason }) => {
          projectGit.supersedeResearchTeamAssignment!({
            workspace: binding.workspace,
            teamId: researchTeamCapability!.teamId,
            slotId: receipt.slotId,
            assignmentId: receipt.assignmentId,
            supersession: { winnerAssignmentId, reason },
          });
        },
      },
    });
    return mathAssignmentRegistry;
  };
  const server = new McpServer({ name: RESEARCH_TEAM_SERVER_NAME, version: '0.1.0' });
  let transport: Transport = new StdioServerTransport();

  const mathematicsRole = researchTeamRoleCapability.profileId === 'mathematics-research-team';
  const mathematicsLiteRole = mathematicsRole && isMathLiteRunEnvironment(process.env);
  const legacyDispatchItemSchema = z
    .object({
      target_slot_id: z.string().describe('Short idle Worker agent_id from the capability roster, for example A002.'),
      assignment: z
        .record(z.string(), z.unknown())
        .optional()
        .describe('Advanced compatibility path: complete deepscientist.research-team.assignment.v1 contract.'),
      task: z
        .union([z.string(), z.record(z.string(), z.unknown())])
        .optional()
        .describe(
          'Preferred path: one atomic task string or structured task object. The runtime fills identity, lane, projectRoot, and defaults.'
        ),
      base_commit: z
        .string()
        .optional()
        .describe('Preferred path: exact full Git base commit used to create the isolated Worker worktree.'),
      role_template_id: z
        .string()
        .optional()
        .describe(
          'Optional assignment specialization; the Worker keeps its system-preconfigured role and authority.'
        ),
      role_kind: z.literal('generic').optional(),
      role_label: z.string().optional(),
      role_instructions: z.string().max(4000).optional(),
      execution_mode: z.enum(['advisory', 'artifact']).optional(),
      math: z.record(z.string(), z.unknown()).optional(),
      math_assignment: z.record(z.string(), z.unknown()).optional(),
      acceptance_criteria: compactStringList(20).optional(),
      failure_criteria: compactStringList(20).optional(),
      expected_artifacts: compactStringList(50).optional(),
      budget: z
        .object({
          maxMinutes: z.number().int().positive().optional(),
          maxAttempts: z.number().int().positive().optional(),
        })
        .strict()
        .optional(),
      idempotency_key: z.string().describe('Stable key reused only for retries of this exact assignment.'),
    })
    .strict()
    .refine(
      (value) =>
        value.math_assignment
          ? !value.assignment && !value.task
          : Boolean(value.assignment) !==
            (typeof value.task === 'string' ? Boolean(value.task.trim()) : Boolean(value.task)),
      {
        message: 'Provide exactly one of assignment or task.',
      }
    )
    .refine(
      (value) => Boolean(value.math_assignment) || Boolean(value.assignment) || Boolean(value.base_commit?.trim()),
      {
        message: 'The preferred task path requires base_commit.',
      }
    );
  const liteDispatchIntentShape = {
    research_question: mathResearchQuestionSchema
      .optional()
      .describe(
        'Research only: exact statement, assumptions and targetConnection. The host assigns a stable question ID and prevents duplicate work on the same frozen evidence. Reuse the same question when retrying.'
      ),
    kind: z
      .enum(['research', 'formalize'])
      .optional()
      .describe(
        'Task type independent of Worker slot. Set research for a bounded investigation, including on a Lean Worker. Formalize requires a Lean Worker. Omission preserves the slot default.'
      ),
    consumer_assignment_ids: z
      .array(z.string().min(1).max(128))
      .min(1)
      .max(16)
      .refine((ids) => new Set(ids).size === ids.length, 'duplicate')
      .optional()
      .describe(
        'Research only: exact active or blocked proof assignment IDs from status. Freeze their authorized context and return findings only to these consumers and their continuations. Omit for legacy automatic owner context or early research.'
      ),
  };
  const liteDispatchItemSchema = z
    .object({
      target_slot_id: z.string().min(1).max(128),
      task: z.string().trim().min(1).max(4000),
      ...liteDispatchIntentShape,
    })
    .strict();
  const dispatchItemSchema = mathematicsLiteRole ? liteDispatchItemSchema : legacyDispatchItemSchema;
  const deliveryItemSchema = z
    .object({
      target_slot_id: z.string().describe('Short Worker agent_id that produced this result, for example A002.'),
      result: z
        .record(z.string(), z.unknown())
        .optional()
        .describe('Compatibility path: exact deepscientist.research-team.result.v1 Worker result.'),
      delivery_id: z
        .string()
        .optional()
        .describe('Preferred durable receipt id. Copy the complete integration_item from the Worker message.'),
      assignment_id: z
        .string()
        .optional()
        .describe('Durable assignment id whose persisted Worker delivery should be integrated.'),
    })
    .strict()
    .refine(
      (value) =>
        [value.result !== undefined, value.delivery_id !== undefined, value.assignment_id !== undefined].filter(
          Boolean
        ).length === 1 || isConsistentDeliverySelectorPair(value),
      { message: 'Provide exactly one of result, delivery_id, or assignment_id.' }
    );
  if (!researchTeamRoleCapability.allowedActions.length) {
    throw new Error('Research Team role capability has no allowed actions');
  }
  const roleActions = [...researchTeamRoleCapability.allowedActions] as [
    ResearchTeamMcpAction,
    ...ResearchTeamMcpAction[],
  ];
  const actionSchema = z.enum(roleActions).describe(roleActions.join(' | '));
  const liteLeadToolSchema = {
    action: actionSchema,
    assignments: z.array(liteDispatchItemSchema).max(32).optional(),
    target_slot_id: z.string().min(1).max(128).optional(),
    task: z.string().trim().min(1).max(4000).optional(),
    ...liteDispatchIntentShape,
    target_slot_ids: z.array(z.string()).max(32).optional(),
    deliveries: z.array(deliveryItemSchema).max(32).optional(),
    artifact_ref: z.string().optional(),
    offset_bytes: mathArtifactReadShape.offsetBytes,
    max_bytes: mathArtifactReadShape.maxBytes.describe(
      'Read 1–2048 bytes (default 2048). Continue with offset_bytes set to the returned nextOffsetBytes.'
    ),
  };
  const researchTeamToolSchema =
    researchTeamRoleCapability.roleKind === 'lead'
      ? mathematicsLiteRole
        ? liteLeadToolSchema
        : {
            action: actionSchema,
            assignments: z
              .array(dispatchItemSchema)
              .max(32)
              .optional()
              .describe(
                mathematicsRole
                  ? 'dispatch only: independent assignments to the injected Worker IDs, at most one per available Worker.'
                  : 'dispatch only: one wave of independent assignments, at most one per Worker slot and never above the reasoning_concurrency returned by describe.'
              ),
            target_slot_id: z
              .string()
              .optional()
              .describe('dispatch only: flat single-assignment compatibility form.'),
            assignment: z.record(z.string(), z.unknown()).optional(),
            task: z.union([z.string(), z.record(z.string(), z.unknown())]).optional(),
            base_commit: z.string().optional(),
            role_template_id: z.string().optional(),
            role_kind: z.literal('generic').optional(),
            role_label: z.string().optional(),
            role_instructions: z.string().max(4000).optional(),
            execution_mode: z.enum(['advisory', 'artifact']).optional(),
            math: z.record(z.string(), z.unknown()).optional(),
            ...(mathematicsRole ? { math_assignment: z.record(z.string(), z.unknown()).optional() } : {}),
            acceptance_criteria: compactStringList(20).optional(),
            failure_criteria: compactStringList(20).optional(),
            expected_artifacts: compactStringList(50).optional(),
            budget: z
              .object({
                maxMinutes: z.number().int().positive().optional(),
                maxAttempts: z.number().int().positive().optional(),
              })
              .strict()
              .optional(),
            idempotency_key: z.string().optional(),
            target_slot_ids: z
              .array(z.string())
              .max(32)
              .optional()
              .describe(
                'status only: short Worker agent_id values to read in one real Core snapshot; omit for all Workers.'
              ),
            ...(mathematicsRole
              ? {}
              : {
                  wait_seconds: z
                    .number()
                    .int()
                    .min(0)
                    .max(600)
                    .optional()
                    .describe('status only compatibility form: 0-30 seconds, or exactly 60/300/600 seconds.'),
                  wait_level: z
                    .enum(TEAM_WAIT_LEVELS)
                    .optional()
                    .describe(
                      'status only: preferred Lead-only wait tier: 1m, 5m, or 10m; omit for an immediate snapshot.'
                    ),
                }),
            deliveries: z
              .array(deliveryItemSchema)
              .max(32)
              .optional()
              .describe(
                'integrate only: copy each Worker integration_item unchanged; it contains target_slot_id and exactly one delivery_id selector. Exact unchanged Worker results remain compatible.'
              ),
            ...(mathematicsRole && !mathematicsLiteRole
              ? {
                  source_artifacts: z
                    .array(mathSourceArtifactSchema)
                    .max(32)
                    .optional()
                    .describe(
                      'integrate only: one source artifact per durable v2 delivery, in the same order. pathRelative is relative to the assignment source root. File mode writes a candidate draft; patch mode applies a zero-fuzz single-file patch to an existing draft and verifies resultContentSha256. Staging does not complete Git integration or kernel verification.'
                    ),
                }
              : {}),
            ...(mathematicsRole
              ? {
                  artifact_ref: z
                    .string()
                    .optional()
                    .describe(
                      'read_artifact only: exact authorized math-artifact:// reference from assignment inputs or a share; never a local file path. Read authorized workspace files with ordinary file tools.'
                    ),
                  offset_bytes: mathArtifactReadShape.offsetBytes,
                  max_bytes: mathArtifactReadShape.maxBytes.describe(
                    'Read 1–2048 bytes (default 2048). Continue with offset_bytes set to the returned nextOffsetBytes.'
                  ),
                }
              : {}),
          }
      : {
          action: actionSchema,
          ...(mathematicsLiteRole
            ? {
                target_slot_id: z
                  .string()
                  .min(1)
                  .max(128)
                  .optional()
                  .describe(
                    'share only: optional related active Researcher slot. The host binds this finding to its current assignment; omit for normal proof-owner feedback.'
                  ),
              }
            : {}),
          result: (mathematicsLiteRole
            ? z.union([mathLiteDeliveryIntentSchema, mathLiteProgressIntentSchema])
            : z.record(z.string(), z.unknown())
          )
            .optional()
            .describe(
              mathematicsLiteRole
                ? 'share: {summary:string, files?:string[]} sends nonterminal findings while keeping your assignment active; no status or blockers. deliver: {status:"completed"|"blocked", summary:string, files?:string[], blockers?:string[]}. Put fields inside result. After a sealed delivery error, omit result to recover the exact host-frozen delivery. Formalizer files are relative to the assignment source root. Researcher share accepts root-level Markdown notes or auxiliary .lean files inside its private solver project (paths relative to its Git worktree); original-target source files cannot be shared as auxiliary proofs; Researcher delivery accepts RESEARCH.md there. Blocked delivery requires blockers; completed must omit blockers. Host owns identity and hashes.'
                : 'deliver only: one exact role-scoped Research Team result using the assigned execution mode.'
            ),
          ...(mathematicsRole
            ? {
                artifact_ref: z
                  .string()
                  .optional()
                  .describe(
                    'read_artifact only: exact authorized math-artifact:// reference from assignment inputs or a share; never a local file path. Read authorized workspace files with ordinary file tools.'
                  ),
                offset_bytes: mathArtifactReadShape.offsetBytes,
                max_bytes: mathArtifactReadShape.maxBytes.describe(
                  'Read 1–2048 bytes (default 2048). Continue with offset_bytes set to the returned nextOffsetBytes.'
                ),
              }
            : {}),
        };
  if (mathematicsRole) {
    transport = withMathematicsMcpValidation(
      transport,
      createMathematicsMcpValidator(researchTeamToolSchema, { liteDelivery: mathematicsLiteRole })
    );
  }
  type DispatchWireItem = Readonly<{
    target_slot_id?: string;
    kind?: 'research' | 'formalize';
    consumer_assignment_ids?: readonly string[];
    research_question?: MathResearchQuestion;
    assignment?: Record<string, unknown>;
    task?: string | Record<string, unknown>;
    base_commit?: string;
    role_template_id?: string;
    role_kind?: 'generic';
    role_label?: string;
    role_instructions?: string;
    execution_mode?: 'advisory' | 'artifact';
    math?: Record<string, unknown>;
    math_assignment?: Record<string, unknown>;
    acceptance_criteria?: readonly string[];
    failure_criteria?: readonly string[];
    expected_artifacts?: readonly string[];
    budget?: Readonly<{ maxMinutes?: number; maxAttempts?: number }>;
    idempotency_key?: string;
  }>;
  type ResearchTeamWireInput = Readonly<{
    action: ResearchTeamMcpAction;
    kind?: 'research' | 'formalize';
    consumer_assignment_ids?: readonly string[];
    research_question?: MathResearchQuestion;
    assignments?: readonly DispatchWireItem[];
    target_slot_id?: string;
    assignment?: Record<string, unknown>;
    task?: string | Record<string, unknown>;
    base_commit?: string;
    role_template_id?: string;
    role_kind?: 'generic';
    role_label?: string;
    role_instructions?: string;
    execution_mode?: 'advisory' | 'artifact';
    math?: Record<string, unknown>;
    math_assignment?: Record<string, unknown>;
    acceptance_criteria?: readonly string[];
    failure_criteria?: readonly string[];
    expected_artifacts?: readonly string[];
    budget?: Readonly<{ maxMinutes?: number; maxAttempts?: number }>;
    idempotency_key?: string;
    target_slot_ids?: readonly string[];
    wait_seconds?: number;
    wait_level?: (typeof TEAM_WAIT_LEVELS)[number];
    result?: Record<string, unknown>;
    deliveries?: readonly z.infer<typeof deliveryItemSchema>[];
    source_artifacts?: readonly MathSourceArtifact[];
    artifact_ref?: string;
    offset_bytes?: number;
    max_bytes?: number;
  }>;
  server.tool(
    'research_team',
    mathematicsRole
      ? 'Operate a Core-authenticated Research Team through role-scoped actions. Use the injected roles and task contracts directly; runtime validation errors include action-local repair help.'
      : 'Operate a Core-authenticated Research Team through role-scoped actions. System-preconfigured roles remain active; call describe once only when the contract is not already known.',
    researchTeamToolSchema,
    async (
      input: Parameters<ToolCallback<typeof researchTeamToolSchema>>[0],
      extra: Parameters<ToolCallback<typeof researchTeamToolSchema>>[1]
    ) => {
      const request = input as ResearchTeamWireInput;
      if (
        mathematicsLiteRole &&
        researchTeamRoleCapability.roleKind === 'worker' &&
        request.target_slot_id &&
        request.action !== 'share'
      )
        throw new Error('target_slot_id is only available for a nonterminal share.');
      const currentCapabilityKey = researchTeamCapabilityCacheKey(researchTeamCapability);
      if (researchTeamCapability && researchTeamCapabilityKey !== currentCapabilityKey) {
        researchTeamCapability = undefined;
      }
      if (researchTeamCapabilityResolution && researchTeamCapabilityResolutionKey !== currentCapabilityKey) {
        void researchTeamCapabilityResolution.catch((): undefined => undefined);
        researchTeamCapabilityResolution = undefined;
        researchTeamCapabilityResolutionKey = undefined;
      }
      if (!researchTeamCapabilityResolution && !researchTeamCapability) {
        const resolutionKey = researchTeamCapabilityCacheKey(undefined);
        const resolution = resolveResearchTeamRuntimeCapability(undefined).then((resolved) => {
          if (researchTeamCapabilityKey === resolutionKey && resolved) {
            researchTeamCapability = resolved;
            researchTeamCapabilityKey = researchTeamCapabilityCacheKey(resolved);
          }
          return resolved;
        });
        const trackedResolution = resolution.finally(() => {
          if (researchTeamCapabilityResolution === trackedResolution) {
            researchTeamCapabilityResolution = undefined;
            researchTeamCapabilityResolutionKey = undefined;
          }
        });
        researchTeamCapabilityResolution = trackedResolution;
        researchTeamCapabilityResolutionKey = resolutionKey;
        // Keep the identity key local to this resolution. It prevents a
        // runtime change from reusing a promise created for another
        // conversation/token pair; the token itself is never logged.
        researchTeamCapabilityKey = resolutionKey;
      }
      const resolvedCapability = researchTeamCapability ?? (await researchTeamCapabilityResolution);
      if (!resolvedCapability) throw new Error('Research Team capability is unavailable');
      researchTeamCapability = resolvedCapability;
      researchTeamCapabilityKey = researchTeamCapabilityCacheKey(resolvedCapability);
      const baseUrl = resolveActiveCoreBaseUrl();
      if (baseUrl && (!researchTeamClient || researchTeamClientBaseUrl !== baseUrl)) {
        researchTeamClient = createResearchCoreTeamClient({ baseUrl });
        researchTeamClientBaseUrl = baseUrl;
      }
      const flatDispatchRequested =
        request.action === 'dispatch' &&
        Boolean(request.target_slot_id || request.assignment || request.task || request.math_assignment);
      let dispatchItems: readonly DispatchWireItem[] | undefined =
        request.assignments ??
        (flatDispatchRequested
          ? [
              {
                target_slot_id: request.target_slot_id ?? '',
                assignment: request.assignment,
                task: request.task,
                kind: request.kind,
                consumer_assignment_ids: request.consumer_assignment_ids,
                research_question: request.research_question,
                base_commit: request.base_commit,
                role_template_id: request.role_template_id,
                role_kind: request.role_kind,
                role_label: request.role_label,
                role_instructions: request.role_instructions,
                execution_mode: request.execution_mode,
                math: request.math,
                math_assignment: request.math_assignment,
                acceptance_criteria: request.acceptance_criteria,
                failure_criteria: request.failure_criteria,
                expected_artifacts: request.expected_artifacts,
                budget: request.budget,
                idempotency_key: request.idempotency_key ?? '',
              },
            ]
          : undefined);
      if (mathematicsLiteRole && request.action === 'dispatch' && dispatchItems?.length) {
        const encoded = process.env[MATH_RUN_INPUTS_ENV];
        if (!encoded) throw new Error('Mathematics run binding is unavailable.');
        const binding = readMathRunBinding(verifyMathRunInputs(JSON.parse(encoded)));
        resolveMathRunProjectPaths(binding, resolvedCapability.projectRoot);
        if (!binding.problem?.verificationTargets?.length) {
          throw new Error('Mathematics lite verification targets are unavailable.');
        }
        const durableAssignments = listProjectGitResearchTeamAssignments({
          workspace: binding.workspace,
          teamId: resolvedCapability.teamId,
          strict: true,
        });
        const batchKinds = new Set(
          dispatchItems.map((item) => {
            if (item.kind) return item.kind;
            const slotId = resolveTeamAgentSlotId(item.target_slot_id, resolvedCapability.roster);
            return resolvedCapability.roster.find((member) => member.slotId === slotId)?.laneId === 'lean-engineering'
              ? 'formalize'
              : 'research';
          })
        );
        const initialProofBatch =
          batchKinds.has('formalize') &&
          batchKinds.has('research') &&
          !durableAssignments.some(
            (receipt) => normalizeRuntimeMathAssignment(receipt.assignment).request.kind === 'formalize'
          );
        let initialContextPublished = false;
        let contractedDispatch: Awaited<ReturnType<typeof contractMathNamedProofDispatch>>;
        const rejectLiteIntent = (code: string, message: string): never => {
          throw new Error(
            JSON.stringify({ status: 'rejected', accepted: false, error: { code, message, retryable: false } })
          );
        };
        const resolveLiteDispatch = async (item: NonNullable<typeof dispatchItems>[number]) => {
          // The math-lite surface is the outer MCP boundary, so it must
          // resolve the same short A001-style aliases as researchTeamTool
          // before looking up the authenticated Core roster.  Core stores
          // opaque slot ids; comparing the alias directly makes a valid
          // Lean Worker look unavailable and can route a caller toward a
          // different slot when it retries with a copied opaque id.
          const targetSlotId = resolveTeamAgentSlotId(item.target_slot_id, resolvedCapability.roster);
          const target = resolvedCapability.roster.find(
            (member) => member.slotId === targetSlotId && member.roleKind === 'worker'
          );
          if (!target) throw new Error('Mathematics lite dispatch target is not an available Worker.');
          const objective = typeof item.task === 'string' ? item.task.trim() : '';
          if (!objective) throw new Error('Mathematics lite dispatch requires one task string.');
          const kind = item.kind ?? (target.laneId === 'lean-engineering' ? 'formalize' : 'research');
          const formalize = kind === 'formalize';
          const consumerAssignmentIds = item.consumer_assignment_ids?.toSorted();
          const researchQuestion = item.research_question;
          if (formalize && researchQuestion)
            rejectLiteIntent(
              'math_lite_question_requires_research',
              'research_question is only available for kind=research.'
            );
          if (formalize && target.laneId !== 'lean-engineering')
            rejectLiteIntent(
              'math_lite_formalize_requires_lean_worker',
              'Use a Lean Worker for formalize, or kind=research for a bounded investigation.'
            );
          if (formalize && consumerAssignmentIds)
            rejectLiteIntent(
              'math_lite_consumers_require_research',
              'consumer_assignment_ids is only available for kind=research.'
            );
          const matchesIntent = (assignment: ReturnType<typeof normalizeRuntimeMathAssignment>) =>
            assignment.request.kind === kind &&
            assignment.request.objective === objective &&
            (assignment.request.researchQuestion
              ? mathAssignmentResearchQuestionId(binding, assignment.request.researchQuestion)
              : null) === (researchQuestion ? mathAssignmentResearchQuestionId(binding, researchQuestion) : null) &&
            canonicalMathJson(assignment.request.consumerAssignmentIds?.toSorted() ?? null) ===
              canonicalMathJson(consumerAssignmentIds ?? null);
          if (formalize) {
            const sourcePaths = new Set(binding.problem!.verificationTargets.map((value) => value.pathRelative));
            if (sourcePaths.size !== 1) {
              throw new Error('math_lite_unsupported_multiple_source_files');
            }
          }
          const chain = durableAssignments
            .filter(
              (receipt) =>
                receipt.slotId === target.slotId && receipt.schema === 'deepscientist.research_team_assignment.v2'
            )
            .flatMap((receipt) => {
              try {
                return [{ receipt, assignment: normalizeRuntimeMathAssignment(receipt.assignment) }];
              } catch {
                throw new Error('math_lite_repair_predecessor_integrity');
              }
            });
          const children = new Map<string, typeof chain>();
          for (const entry of chain) {
            const parent = entry.assignment.request.predecessorAssignmentId;
            if (!parent) continue;
            const siblings = children.get(parent) ?? [];
            siblings.push(entry);
            children.set(parent, siblings);
          }
          for (const siblings of children.values()) {
            if (siblings.length > 1) throw new Error('math_lite_repair_predecessor_ambiguous');
          }
          const reservedSuccessors = chain.filter((entry) => {
            const parentId = entry.assignment.request.predecessorAssignmentId;
            const parent = parentId
              ? chain.find((candidate) => candidate.receipt.assignmentId === parentId)
              : undefined;
            return (
              Boolean(
                parent &&
                (parent.receipt.integration?.verification?.disposition === 'candidate_rejected' ||
                  hasMathV2BlockedDelivery(parent.receipt))
              ) &&
              (entry.receipt.state === 'prepared' || entry.receipt.state === 'accepted') &&
              entry.receipt.integration?.verification?.disposition !== 'candidate_rejected' &&
              !hasMathV2BlockedDelivery(entry.receipt)
            );
          });
          if (reservedSuccessors.length > 1) throw new Error('math_lite_repair_predecessor_ambiguous');
          const reservedSuccessor = reservedSuccessors[0];
          if (reservedSuccessor) {
            if (reservedSuccessor.receipt.delivery || !matchesIntent(reservedSuccessor.assignment)) {
              const delivery = reservedSuccessor.receipt.delivery;
              throw new Error(
                JSON.stringify({
                  status: 'rejected',
                  accepted: false,
                  error: {
                    code: 'math_lite_repair_successor_active',
                    message: delivery
                      ? 'No new task was accepted. The existing repair has a frozen delivery; integrate it before requesting another repair.'
                      : 'No new task was accepted. A repair already owns this Worker; retry the original task without changing its objective.',
                  },
                  assignment_id: reservedSuccessor.receipt.assignmentId,
                  next_action: delivery
                    ? {
                        action: 'integrate',
                        deliveries: [{ target_slot_id: targetSlotId, delivery_id: delivery.deliveryId }],
                      }
                    : {
                        action: 'dispatch',
                        assignments: [
                          {
                            target_slot_id: targetSlotId,
                            task: reservedSuccessor.assignment.request.objective,
                            kind: reservedSuccessor.assignment.request.kind,
                            ...(reservedSuccessor.assignment.request.researchQuestion
                              ? { research_question: reservedSuccessor.assignment.request.researchQuestion }
                              : {}),
                            ...(reservedSuccessor.assignment.request.consumerAssignmentIds
                              ? {
                                  consumer_assignment_ids: reservedSuccessor.assignment.request.consumerAssignmentIds,
                                }
                              : {}),
                          },
                        ],
                      },
                })
              );
            }
            return {
              ...item,
              target_slot_id: targetSlotId,
              base_commit: reservedSuccessor.assignment.baseCommit,
              math_assignment: reservedSuccessor.assignment.request,
            };
          }
          // Replay frozen requests before consulting newer context or teaching resources.
          // This also protects proof tasks created by builds without worked examples.
          const retainedAssignments = chain.filter(
            ({ receipt, assignment }) =>
              (receipt.state === 'prepared' || receipt.state === 'accepted') &&
              !receipt.delivery &&
              !receipt.integration &&
              !receipt.supersessionPending &&
              !receipt.budgetCancellation &&
              matchesIntent(assignment)
          );
          if (retainedAssignments.length > 1)
            throw new Error(
              formalize ? 'math_lite_proof_assignment_ambiguous' : 'math_lite_research_assignment_ambiguous'
            );
          if (retainedAssignments.length === 1) {
            const { receipt, assignment } = retainedAssignments[0]!;
            projectRuntimeMathAssignmentToExecutionView(assignment, {
              expectedRunId: binding.runId,
              expectedBindingDigest: mathDigest(canonicalMathJson(binding)),
              expectedTargetSlotId: target.slotId,
              expectedBaseCommit: receipt.preparedGit?.baseCommit ?? assignment.baseCommit,
            });
            return {
              ...item,
              target_slot_id: targetSlotId,
              base_commit: assignment.baseCommit,
              math_assignment: assignment.request,
            };
          }
          const resumableLeaves = chain.filter(
            (entry) =>
              (entry.receipt.integration?.verification?.disposition === 'candidate_rejected' ||
                hasMathV2BlockedDelivery(entry.receipt)) &&
              !children.get(entry.receipt.assignmentId)?.length
          );
          if (resumableLeaves.length > 1) throw new Error('math_lite_repair_predecessor_ambiguous');
          const predecessor = resumableLeaves[0];
          if (predecessor && predecessor.assignment.request.kind !== kind) {
            const prior = predecessor.assignment.request;
            throw new Error(
              JSON.stringify({
                status: 'rejected',
                accepted: false,
                error: {
                  code: 'math_lite_repair_kind_conflict',
                  message:
                    'A blocked continuation must retain its task kind. Resume the original kind, or use another available Worker for a different kind.',
                  retryable: false,
                },
                next_action: {
                  action: 'dispatch',
                  assignments: [
                    {
                      target_slot_id: targetSlotId,
                      kind: prior.kind,
                      task: prior.objective,
                      ...(prior.researchQuestion ? { research_question: prior.researchQuestion } : {}),
                      ...(prior.consumerAssignmentIds
                        ? { consumer_assignment_ids: prior.consumerAssignmentIds }
                        : {}),
                    },
                  ],
                },
              })
            );
          }
          const pausedProofs = formalize
            ? []
            : durableAssignments
                .filter(
                  (receipt) =>
                    receipt.state === 'accepted' &&
                    !receipt.supersessionPending &&
                    !receipt.budgetCancellation &&
                    hasMathV2BlockedDelivery(receipt)
                )
                .map((receipt) =>
                  selectMathV2IntegrationDelivery(receipt, receipt.delivery!.deliveryId, {
                    expectedRunId: binding.runId,
                    expectedBindingDigest: mathDigest(canonicalMathJson(binding)),
                  })
                )
                .filter(
                  (selection) =>
                    selection.assignment.request.kind === 'formalize' &&
                    (!consumerAssignmentIds || consumerAssignmentIds.includes(selection.assignment.assignmentId))
                );
          const activeProofs = formalize
            ? []
            : durableAssignments
                .filter(
                  (receipt) =>
                    receipt.state === 'accepted' &&
                    !receipt.delivery &&
                    !receipt.integration &&
                    !receipt.supersessionPending &&
                    !receipt.budgetCancellation &&
                    receipt.schema === 'deepscientist.research_team_assignment.v2'
                )
                .filter(
                  (receipt) =>
                    normalizeRuntimeMathAssignment(receipt.assignment).request.kind === 'formalize' &&
                    (!consumerAssignmentIds || consumerAssignmentIds.includes(receipt.assignmentId))
                );
          if (consumerAssignmentIds) {
            const eligibleIds = new Set([
              ...activeProofs.map((receipt) => receipt.assignmentId),
              ...pausedProofs.map((selection) => selection.assignment.assignmentId),
            ]);
            if (consumerAssignmentIds.some((id) => !eligibleIds.has(id)))
              rejectLiteIntent(
                'math_lite_consumer_requires_active_or_blocked_proof_assignment',
                'Use exact active or blocked proof assignment IDs from status, not Worker slot IDs or research assignment IDs.'
              );
          }
          if (
            !formalize &&
            item.kind === undefined &&
            !consumerAssignmentIds &&
            !researchQuestion &&
            !predecessor &&
            dispatchItems.length === 1 &&
            activeProofs.length === 1 &&
            !chain.some(
              ({ receipt }) =>
                (receipt.state === 'prepared' || receipt.state === 'accepted') &&
                !receipt.integration &&
                !receipt.delivery
            )
          ) {
            contractedDispatch = await contractMathNamedProofDispatch({
              objective,
              proofOwner: {
                teamId: resolvedCapability.teamId,
                slotId: activeProofs[0]!.slotId,
                roleKind: 'worker',
                projectRoot: resolvedCapability.projectRoot,
              },
              signal: extra.signal,
              deadlineAt: Date.now() + 30_000,
            });
            if (contractedDispatch) return item;
          }
          // Each proof owner's refs bind research findings back to that owner, so every active or
          // paused owner contributes its own context and the input limit is shared between them.
          const ownerInputs: string[][] = [];
          const proofConsumers = [
            ...activeProofs,
            ...pausedProofs.map(
              (selection) =>
                durableAssignments.find((receipt) => receipt.assignmentId === selection.assignment.assignmentId)!
            ),
          ];
          for (const proof of proofConsumers) {
            const paused = pausedProofs.find((selection) => selection.assignment.assignmentId === proof.assignmentId);
            const refs = paused
              ? paused.delivery.delivery.evidence.map((evidence) => evidence.ref)
              : (readLatestMathLiteProgress(binding, proof, undefined, true)?.files.map((entry) => entry.ref) ?? []);
            if (!refs.length) {
              projectRuntimeMathAssignmentToExecutionView(proof.assignment, {
                expectedRunId: binding.runId,
                expectedBindingDigest: mathDigest(canonicalMathJson(binding)),
                expectedTargetSlotId: proof.slotId,
                ...(proof.preparedGit?.baseCommit ? { expectedBaseCommit: proof.preparedGit.baseCommit } : {}),
              });
              const artifactId = mathLiteProofContextArtifactId(binding, proof.assignmentId);
              const store = await ensureMathArtifactStore(resolvedCapability.projectRoot);
              extra.signal.throwIfAborted();
              await store.publishText({
                artifactId,
                assignmentId: proof.assignmentId,
                kind: 'evidence',
                sensitivity: 'solver-visible',
                mediaType: 'text/plain',
                text: `Frozen original target for the active proof assignment. This is not a current proof snapshot or verified result.\n\n${binding.problem!.formalStatement}`,
              });
              extra.signal.throwIfAborted();
              const current = listProjectGitResearchTeamAssignments({
                workspace: binding.workspace,
                teamId: resolvedCapability.teamId,
                strict: true,
              }).find((entry) => entry.assignmentId === proof.assignmentId);
              if (!current || canonicalMathJson(current) !== canonicalMathJson(proof))
                throw new Error('math_share_assignment_changed');
              refs.push(`math-artifact://${binding.runId}/${artifactId}`);
            }
            if (!paused)
              refs.push(
                ...readMathLiteBlockerLineage(binding, proof, durableAssignments).map(
                  ({ artifactId }) => `math-artifact://${binding.runId}/${artifactId}`
                )
              );
            ownerInputs.push(refs);
          }
          if (formalize && predecessor)
            ownerInputs.push(
              readMathLiteBlockerLineage(binding, predecessor.receipt, durableAssignments).map(
                ({ artifactId }) => `math-artifact://${binding.runId}/${artifactId}`
              )
            );
          if (initialProofBatch) {
            // These owners have no durable assignment IDs yet. Bind both sides to
            // the immutable original target, without treating it as proof progress.
            const artifactId = mathLiteInitialProofContextArtifactId(binding);
            if (!initialContextPublished) {
              const store = await ensureMathArtifactStore(resolvedCapability.projectRoot);
              extra.signal.throwIfAborted();
              await store.publishText({
                artifactId,
                kind: 'evidence',
                sensitivity: 'solver-visible',
                mediaType: 'text/plain',
                text: `Frozen original target for the initial proof and research batch. This is not a current proof snapshot or verified result.\n\n${binding.problem!.formalStatement}`,
              });
              extra.signal.throwIfAborted();
              initialContextPublished = true;
            }
            ownerInputs.push([`math-artifact://${binding.runId}/${artifactId}`]);
          }
          const ownerInputLimit =
            ownerInputs.length > 1 ? Math.floor(MATH_ASSIGNMENT_INPUT_LIMIT / ownerInputs.length) : Infinity;
          const researchInputs = [...new Set(ownerInputs.flatMap((refs) => refs.slice(0, ownerInputLimit)))].map(
            (artifactRef) => ({
              artifactRef,
              purpose:
                'Read the frozen context. Original-target context is not a current proof snapshot; progress artifacts contain the shared proof or notes.',
            })
          );
          // Optional teaching resources follow proof/context evidence in the ordinary input list.
          // Never evict evidence, relax the public limit, or mutate a retained request for them.
          if (researchInputs.length + MATHEMATICS_WORKED_EXAMPLES.length <= MATH_ASSIGNMENT_INPUT_LIMIT) {
            const store = await ensureMathArtifactStore(resolvedCapability.projectRoot);
            for (const example of MATHEMATICS_WORKED_EXAMPLES) {
              extra.signal.throwIfAborted();
              const artifactId = `math-worked-${example.id}-${mathDigest(example.body)}`;
              await store.publishText({
                artifactId,
                kind: 'evidence',
                sensitivity: 'solver-visible',
                mediaType: 'text/markdown',
                text: example.body,
              });
              extra.signal.throwIfAborted();
              researchInputs.push({
                artifactRef: `math-artifact://${binding.runId}/${artifactId}`,
                purpose: example.purpose,
              });
            }
          } else {
            console.error(
              'Optional mathematics worked examples omitted: existing evidence leaves fewer than three input slots.'
            );
          }
          const researchEvidenceVersion = researchQuestion
            ? mathAssignmentResearchEvidenceVersion(
                { inputs: researchInputs },
                predecessor?.receipt.integration?.mergedCommit ??
                  resolveProjectGitCommit({ workspace: binding.workspace, reference: 'HEAD' })
              )
            : undefined;
          const assignmentIdentity = {
            runId: binding.runId,
            targetSlotId: target.slotId,
            kind,
            ...(researchQuestion ? { researchQuestion } : {}),
            ...(researchEvidenceVersion ? { evidenceVersion: researchEvidenceVersion } : {}),
            ...(consumerAssignmentIds ? { consumerAssignmentIds } : {}),
            objective,
            ...(researchInputs.length ? { inputs: researchInputs } : {}),
            ...(predecessor ? { predecessorAssignmentId: predecessor.receipt.assignmentId } : {}),
          };
          if (researchQuestion) {
            const questionId = mathAssignmentResearchQuestionId(binding, researchQuestion);
            const existing = buildMathAssignmentResearchGraph(binding, durableAssignments).questions.find(
              (question) =>
                question.questionId === questionId &&
                question.evidenceVersion === researchEvidenceVersion &&
                (question.status === 'active' || question.status === 'reported')
            );
            if (existing)
              throw new Error(
                JSON.stringify({
                  status: 'rejected',
                  accepted: false,
                  error: {
                    code: 'math_research_question_already_owned',
                    message:
                      'This question already has a producer or report for the same frozen evidence. Read its result; do not dispatch the same gap under a different task wording.',
                    retryable: false,
                  },
                  question_id: questionId,
                  evidence_version: existing.evidenceVersion,
                  producer_assignment_ids: existing.producerAssignmentIds,
                  reports: existing.reports,
                  next_action: { action: 'status' },
                })
              );
          }
          return {
            ...item,
            target_slot_id: targetSlotId,
            base_commit: binding.baseCommit,
            math_assignment: {
              idempotencyKey: `math-lite-${mathDigest(canonicalMathJson(assignmentIdentity)).slice(0, 48)}`,
              targetSlotId: target.slotId,
              ...(predecessor ? { predecessorAssignmentId: predecessor.receipt.assignmentId } : {}),
              kind,
              ...(researchQuestion ? { researchQuestion } : {}),
              ...(consumerAssignmentIds ? { consumerAssignmentIds } : {}),
              objective,
              ...(researchInputs.length ? { inputs: researchInputs } : {}),
              acceptance: formalize
                ? ['Return the frozen original target as a complete Lean source file.']
                : [
                    'Return a bounded provisional report answering the assigned question, with checked evidence, applicability to the original hypotheses and remaining uncertainty. Completing this research task does not require or establish a complete proof of the original target.',
                    'Use actual types, original assumptions and the target relation. Choose a justified candidate form, substitute it and refine unmet conditions; sufficient choices are not necessary conditions. A failed candidate does not refute its family or the target. If a route adds a difficult premise, inspect its origin and give a checked alternative connection or keep uncertainty explicit. Read teaching examples only when useful; transfer relations, not answers.',
                    'Distinguish direct theorem reuse from mechanism transfer: align objects, operations, assumptions and the return to the target; do not invent stronger instances. Check a concrete use in the current target in a private draft; share sourceProbe before/after goals and diagnostics with their context, the actual call and remaining premises. Conditional work proves neither its premise nor the original goal. Preserve valid consumers via checked adapters; retain independent results.',
                    'Query for the intended transformation using authorized local definitions, relations and structure clues. Read the full local declaration, including section variables and typeclasses, then instantiate it; a parsed name or retrieval rank is not proof. Reuse available results and delegate only the remaining gap, preserving explicit-witness and formula obligations. Researchers use authorized source reads and private probe, not owner-only search actions. A search miss does not refute the mathematics.',
                    ...selectMathematicsMethodHints(objective).split('\n').filter(Boolean),
                  ],
              ...(formalize ? { verificationTargets: binding.problem!.verificationTargets } : {}),
            },
          };
        };
        const resolvedItems: Array<NonNullable<typeof dispatchItems>[number]> = [];
        for (const item of dispatchItems) {
          // Preserve dispatch order and check each context before processing the next item.
          resolvedItems.push(await resolveLiteDispatch(item));
        }
        if (contractedDispatch)
          return { content: [{ type: 'text' as const, text: JSON.stringify(contractedDispatch) }] };
        dispatchItems = resolvedItems;
      }
      const v2DispatchRequested =
        request.action === 'dispatch' && Boolean(dispatchItems?.some((item) => item.math_assignment !== undefined));
      return await runResearchTeamTool(
        {
          action: request.action,
          assignments: dispatchItems?.map((item) => ({
            targetSlotId: item.target_slot_id,
            assignment: item.assignment,
            task: item.task,
            baseCommit: item.base_commit,
            roleTemplateId: item.role_template_id,
            roleKind: item.role_kind,
            roleLabel: item.role_label,
            roleInstructions: item.role_instructions,
            executionMode: item.execution_mode,
            math: item.math,
            mathAssignment: item.math_assignment,
            acceptanceCriteria: item.acceptance_criteria,
            failureCriteria: item.failure_criteria,
            expectedArtifacts: item.expected_artifacts,
            budget: item.budget,
            idempotencyKey: item.idempotency_key,
          })),
          targetSlotIds: request.target_slot_ids,
          ...(request.action === 'share' && request.target_slot_id
            ? { shareTargetSlotId: request.target_slot_id }
            : {}),
          waitSeconds: request.wait_seconds,
          waitLevel: request.wait_level,
          result: request.result,
          sourceArtifacts: request.source_artifacts,
          deliveries: request.deliveries?.map((item) => ({
            targetSlotId: item.target_slot_id,
            result: item.result,
            deliveryId: item.delivery_id,
            // A matching assignment_id beside delivery_id is redundant; the delivery id is authoritative.
            assignmentId: item.delivery_id === undefined ? item.assignment_id : undefined,
          })),
          ...(request.action === 'read_artifact'
            ? {
                artifactRead: {
                  ref: request.artifact_ref ?? '',
                  ...(request.offset_bytes !== undefined ? { offsetBytes: request.offset_bytes } : {}),
                  ...(request.max_bytes !== undefined ? { maxBytes: request.max_bytes } : {}),
                },
              }
            : {}),
        },
        {
          capability: resolvedCapability,
          ...(mathematicsRole && request.action === 'integrate'
            ? { mathIntegrationJournal: getMathIntegrationJournal() }
            : {}),
          ...(mathematicsRole ? { enableConditionalReviewDispatch: true } : {}),
          ...(baseUrl && researchTeamClient ? { client: researchTeamClient } : {}),
          projectGit: createResearchTeamProjectGitDriver(),
          ...(v2DispatchRequested ? { mathAssignmentRegistry: getMathAssignmentRegistry() } : {}),
          ...(mathematicsRole ? { verifyRunInputs: () => verifyMathRunInputsEnvironment(process.env) } : {}),
          ...(mathematicsRole
            ? {
                prepareMathV2Worktree: true,
                prepareMathV2AssignmentSources: async ({ assignment, worktreePath, replaying }) => {
                  verifyMathRunInputsEnvironment(process.env);
                  const encoded = process.env[MATH_RUN_INPUTS_ENV];
                  if (!encoded) throw new Error('Mathematics run binding is unavailable.');
                  const binding = readMathRunBinding(verifyMathRunInputs(JSON.parse(encoded)));
                  const { solverProjectRoot } = resolveMathRunProjectPaths(
                    binding,
                    resolvedCapability.projectRoot,
                    worktreePath
                  );
                  const sourceRoot = path.resolve(solverProjectRoot, assignment.sourceRootRelative);
                  assertMathCanonicalPath(solverProjectRoot);
                  assertMathCanonicalPath(sourceRoot);
                  if (!isMathPathWithin(solverProjectRoot, sourceRoot)) {
                    throw new Error('Mathematics assignment source root is unauthorized.');
                  }
                  const predecessorAssignmentId = assignment.request.predecessorAssignmentId;
                  if (predecessorAssignmentId && mathematicsLiteRole) {
                    const predecessor = listProjectGitResearchTeamAssignments({
                      workspace: binding.workspace,
                      teamId: resolvedCapability.teamId,
                      strict: true,
                    }).find((candidate) => candidate.assignmentId === predecessorAssignmentId);
                    if (!predecessor?.delivery) throw new Error('math_lite_repair_predecessor_delivery_missing');
                    const predecessorDeliveryId = createProjectGitResearchTeamDeliveryId(
                      resolvedCapability.teamId,
                      predecessor.slotId,
                      predecessor.assignmentId
                    );
                    const sealed = readMathLiteSealedSet(
                      path.dirname(binding.artifactStoreRoot),
                      predecessorDeliveryId
                    );
                    if (!sealed || sealed.assignmentId !== predecessor.assignmentId) {
                      throw new Error('math_lite_repair_predecessor_seal_missing');
                    }
                    const store = await ensureMathArtifactStore(resolvedCapability.projectRoot);
                    for (const frozen of sealed.files) {
                      if (
                        path.isAbsolute(frozen.pathRelative) ||
                        frozen.pathRelative.split('/').includes('..') ||
                        frozen.pathRelative.includes('\0')
                      ) {
                        throw new Error('math_lite_repair_predecessor_path');
                      }
                      let offsetBytes = 0;
                      let text = '';
                      for (;;) {
                        const chunk = await store.read(
                          { ref: frozen.ref, offsetBytes, maxBytes: 2048 },
                          { role: 'lead', assignmentId: predecessor.assignmentId }
                        );
                        text += chunk.text;
                        if (chunk.nextOffsetBytes === undefined) break;
                        offsetBytes = chunk.nextOffsetBytes;
                      }
                      if (mathDigest(text) !== frozen.sha256) {
                        throw new Error('math_lite_repair_predecessor_artifact_integrity');
                      }
                      const destination = path.resolve(sourceRoot, frozen.pathRelative);
                      assertMathCanonicalPath(destination);
                      if (!isMathPathWithin(sourceRoot, destination)) {
                        throw new Error('math_lite_repair_predecessor_path');
                      }
                      fs.mkdirSync(path.dirname(destination), { recursive: true, mode: 0o700 });
                      if (fs.existsSync(destination)) {
                        if (!replaying && fs.readFileSync(destination, 'utf8') !== text) {
                          throw new Error('math_lite_repair_predecessor_source_conflict');
                        }
                      } else {
                        fs.writeFileSync(destination, text, { encoding: 'utf8', mode: 0o600 });
                      }
                    }
                  }
                  for (const target of assignment.request.verificationTargets ?? []) {
                    const baseline = path.resolve(solverProjectRoot, target.pathRelative);
                    const destination = path.resolve(sourceRoot, target.pathRelative);
                    assertMathCanonicalPath(baseline);
                    assertMathCanonicalPath(destination);
                    if (
                      !isMathPathWithin(solverProjectRoot, baseline) ||
                      !isMathPathWithin(sourceRoot, destination) ||
                      !fs.lstatSync(baseline).isFile()
                    ) {
                      throw new Error('Mathematics verification source is unavailable.');
                    }
                    fs.mkdirSync(path.dirname(destination), { recursive: true, mode: 0o700 });
                    if (!fs.existsSync(destination))
                      fs.copyFileSync(baseline, destination, fs.constants.COPYFILE_EXCL);
                  }
                  return { solverProjectRoot };
                },
                commitMathV2Worktree: commitMathV2PromotionWorktree,
                verifyMathV2Worktree: verifyMathV2SourceCommit,
                stageMathSources: (receipts, artifacts) =>
                  stageMathV2Sources(receipts, artifacts, {
                    teamId: resolvedCapability.teamId,
                    readBinding: () => {
                      verifyMathRunInputsEnvironment(process.env);
                      const encoded = process.env[MATH_RUN_INPUTS_ENV];
                      if (!encoded) throw new Error('Mathematics run binding is unavailable.');
                      const binding = readMathRunBinding(verifyMathRunInputs(JSON.parse(encoded)));
                      resolveMathRunProjectPaths(binding, resolvedCapability.projectRoot);
                      return binding;
                    },
                    readAssignments: () =>
                      createResearchTeamProjectGitDriver().listResearchTeamAssignments!({
                        workspace: resolvedCapability.projectRoot,
                        teamId: resolvedCapability.teamId,
                        strict: true,
                      }),
                    flockExecutable: '/usr/bin/flock',
                    signal: extra.signal,
                    allowHostFrozenDeliveryArtifacts: mathematicsLiteRole,
                  }),
                recoverMathSources: (receipts) =>
                  recoverMathV2SourceStages(receipts, {
                    teamId: resolvedCapability.teamId,
                    readBinding: () => {
                      verifyMathRunInputsEnvironment(process.env);
                      const encoded = process.env[MATH_RUN_INPUTS_ENV];
                      if (!encoded) throw new Error('Mathematics run binding is unavailable.');
                      const binding = readMathRunBinding(verifyMathRunInputs(JSON.parse(encoded)));
                      resolveMathRunProjectPaths(binding, resolvedCapability.projectRoot);
                      return binding;
                    },
                    readAssignments: () =>
                      createResearchTeamProjectGitDriver().listResearchTeamAssignments!({
                        workspace: resolvedCapability.projectRoot,
                        teamId: resolvedCapability.teamId,
                        strict: true,
                      }),
                    flockExecutable: '/usr/bin/flock',
                    signal: extra.signal,
                    allowHostFrozenDeliveryArtifacts: mathematicsLiteRole,
                  }),
                readMathAssignmentBinding: () => {
                  const encoded = process.env[MATH_RUN_INPUTS_ENV];
                  if (!encoded) throw new Error('Mathematics run binding is unavailable.');
                  const binding = readMathRunBinding(verifyMathRunInputs(JSON.parse(encoded)));
                  resolveMathRunProjectPaths(binding, resolvedCapability.projectRoot);
                  return {
                    runId: binding.runId,
                    projectRoot: binding.projectRoot,
                    bindingDigest: mathDigest(canonicalMathJson(binding)),
                    ...(binding.problem
                      ? {
                          statementHash: binding.problem.statementHash,
                          initialRouteFingerprint: binding.problem.initialRouteFingerprint,
                        }
                      : {}),
                  };
                },
                ...(mathematicsLiteRole
                  ? {
                      readMathLiteFeedback: ({ consume }) =>
                        readMathLiteFeedback({ resolvedCapability, signal: extra.signal, consume }),
                      readMathResearchGraph: () => {
                        verifyMathRunInputsEnvironment(process.env);
                        const binding = readMathRunBinding(
                          verifyMathRunInputs(JSON.parse(process.env[MATH_RUN_INPUTS_ENV]!))
                        );
                        const graph = buildMathAssignmentResearchGraph(
                          binding,
                          listProjectGitResearchTeamAssignments({
                            workspace: binding.workspace,
                            teamId: resolvedCapability.teamId,
                            strict: true,
                          })
                        );
                        return {
                          ...graph,
                          questions: graph.questions.slice(-32),
                          nodes: graph.nodes.slice(-64),
                          nextQuestions: graph.nextQuestions.slice(-32),
                          repeatedStatements: graph.repeatedStatements.slice(-32),
                          totalQuestions: graph.questions.length,
                          truncated: graph.questions.length > 32 || graph.nodes.length > 64,
                        };
                      },
                      relayMathLiteProgress: async (client) => {
                        if (resolvedCapability.roleKind !== 'lead' || !client.readRunState) return;
                        verifyMathRunInputsEnvironment(process.env);
                        const encoded = process.env[MATH_RUN_INPUTS_ENV];
                        if (!encoded) throw new Error('math_share_binding_unavailable');
                        const binding = readMathRunBinding(verifyMathRunInputs(JSON.parse(encoded)));
                        const live = await client.readRunState(resolvedCapability.teamId, extra.signal, true);
                        const active = listProjectGitResearchTeamAssignments({
                          workspace: binding.workspace,
                          teamId: resolvedCapability.teamId,
                          states: ['accepted', 'integrated'],
                          strict: true,
                        })
                          .filter(
                            (receipt) =>
                              (receipt.state === 'accepted' || receipt.state === 'integrated') &&
                              !receipt.supersessionPending &&
                              !receipt.budgetCancellation &&
                              receipt.schema === 'deepscientist.research_team_assignment.v2'
                          )
                          .map((receipt) => ({
                            receipt,
                            view: projectRuntimeMathAssignmentToExecutionView(receipt.assignment, {
                              expectedRunId: binding.runId,
                              expectedBindingDigest: mathDigest(canonicalMathJson(binding)),
                              expectedTargetSlotId: receipt.slotId,
                              ...(receipt.preparedGit?.baseCommit
                                ? { expectedBaseCommit: receipt.preparedGit.baseCommit }
                                : {}),
                            }),
                          }));
                        const workers = active.filter(
                          ({ receipt, view }) =>
                            (view.kind === 'formalize' || view.kind === 'research') &&
                            receipt.state === 'accepted' &&
                            !receipt.delivery &&
                            !receipt.integration &&
                            live.slots.some(
                              (slot) =>
                                slot.slotId === receipt.slotId &&
                                (live.activeSlotIds.includes(slot.slotId) ||
                                  (slot.state === 'idle' && !slot.blockedReason && !slot.runtimeHealth) ||
                                  slot.queuedForegroundCount > 0 ||
                                  slot.queuedBackgroundCount > 0 ||
                                  slot.pendingWakeCount > 0)
                            )
                        );
                        for (const { receipt: target } of workers) {
                          // The same reader governs notifications and actual access. An
                          // unrelated report cannot wake every member of the proof team.
                          const feedback = await readMathLiteFeedback({
                            resolvedCapability: { ...resolvedCapability, slotId: target.slotId, roleKind: 'worker' },
                            signal: extra.signal,
                            automatic: true,
                            consume: false,
                          });
                          if (!feedback.findings.length) continue;
                          const cursor = mathLiteFeedbackCursor(binding, target.assignmentId).read();
                          if (!feedback.findings.some((finding) => !cursor.seen.includes(finding.shareId))) continue;
                          const current = listProjectGitResearchTeamAssignments({
                            workspace: binding.workspace,
                            teamId: resolvedCapability.teamId,
                            strict: true,
                          }).find((entry) => entry.assignmentId === target.assignmentId);
                          if (!current || canonicalMathJson(current) !== canonicalMathJson(target))
                            throw new ResearchTeamOrchestrationError(
                              'math_share_assignment_changed',
                              'Progress relay assignment changed; re-read status.',
                              true
                            );
                          extra.signal.throwIfAborted();
                          const ack = await client.dispatch(
                            resolvedCapability.teamId,
                            target.slotId,
                            'Provisional mathematical findings are available. Finish your current edit, then call research_team read_feedback once at your next commit or turn boundary. Continue your current assignment and verify independently; do not poll unchanged checkpoints.',
                            extra.signal,
                            `math-share-relay-${target.assignmentId}-${mathDigest(canonicalMathJson(cursor.seen.toSorted()))}`
                          );
                          if (
                            ack.team_id !== resolvedCapability.teamId ||
                            ack.target_slot_id !== target.slotId ||
                            ack.accepted_slot_id !== target.slotId ||
                            ack.accepted_role !== 'teammate' ||
                            !isTeamRunAckPersisted(ack)
                          )
                            throw new ResearchTeamOrchestrationError(
                              'math_share_relay_pending',
                              'Progress relay was not acknowledged; retry status to replay the same frozen message.',
                              true
                            );
                        }
                      },
                      acknowledgeMathLiteShare: async (shareId, assignmentId) => {
                        verifyMathRunInputsEnvironment(process.env);
                        extra.signal.throwIfAborted();
                        if (!/^[a-f0-9]{64}$/u.test(shareId) || !/^[A-Za-z0-9_-]{1,128}$/u.test(assignmentId))
                          throw new Error('math_share_identity_invalid');
                        const binding = readMathRunBinding(
                          verifyMathRunInputs(JSON.parse(process.env[MATH_RUN_INPUTS_ENV]!))
                        );
                        const record = path.join(
                          path.dirname(binding.artifactStoreRoot),
                          'lite-shares',
                          assignmentId,
                          `${shareId}.json`
                        );
                        assertMathCanonicalPath(record);
                        const shared = mathLiteProgressSnapshotSchema.parse(readMathJson(record));
                        // The cursor atomically acknowledges wait intent before the general share
                        // marker. A crash between these writes must not lose a clear or re-arm a wait.
                        await acknowledgeMathLiteResearchWait(binding, shared, extra.signal);
                        if (!fs.existsSync(`${record}.ack`))
                          writeMathJsonDurable(`${record}.ack`, { shareId, observedAt: Date.now() }, 0o400);
                        try {
                          const acknowledgement = readMathJson(`${record}.ack`) as { observedAt?: unknown };
                          recordMathProofImpact(
                            { runRoot: path.dirname(binding.artifactStoreRoot), runId: binding.runId },
                            {
                              kind: 'shared',
                              runId: binding.runId,
                              assignmentId,
                              shareId,
                              observedAt:
                                typeof acknowledgement.observedAt === 'number' ? acknowledgement.observedAt : null,
                            }
                          );
                        } catch {
                          /* The durable share acknowledgement does not depend on optional telemetry. */
                        }
                      },
                      prepareMathLiteShare: async ({ rawResult, receipt, assignment, targetSlotId }) => {
                        verifyMathRunInputsEnvironment(process.env);
                        extra.signal.throwIfAborted();
                        const intent = mathLiteProgressIntentSchema.parse(rawResult);
                        if (intent.wait_for_question_ids !== undefined && assignment.kind !== 'formalize')
                          throw new Error('math_research_wait_requires_proof_owner');
                        const encoded = process.env[MATH_RUN_INPUTS_ENV];
                        if (!encoded || !receipt.preparedGit?.worktreePath || !assignment.sourceRootRelative) {
                          throw new Error('math_share_binding_unavailable');
                        }
                        const binding = readMathRunBinding(verifyMathRunInputs(JSON.parse(encoded)));
                        // Routing changes who may read this finding, not the original proof
                        // contract or assignment grants. Bind a live peer, never just a slot.
                        let recipient: { assignmentId: string; slotId: string } | undefined;
                        let recipientReceipt: typeof receipt | undefined;
                        if (targetSlotId) {
                          if (assignment.kind !== 'research') throw new Error('math_share_peer_research_required');
                          const peerSlot = resolveTeamAgentSlotId(targetSlotId, resolvedCapability.roster);
                          const peer = resolvedCapability.roster.find(
                            (member) => member.slotId === peerSlot && member.roleKind === 'worker'
                          );
                          const peers = listProjectGitResearchTeamAssignments({
                            workspace: binding.workspace,
                            teamId: resolvedCapability.teamId,
                            strict: true,
                          }).filter(
                            (entry) =>
                              entry.slotId === peerSlot &&
                              entry.state === 'accepted' &&
                              !entry.delivery &&
                              !entry.integration &&
                              !entry.supersessionPending &&
                              !entry.budgetCancellation
                          );
                          if (!peer || peerSlot === receipt.slotId || peers.length !== 1)
                            throw new Error('math_share_recipient_unavailable');
                          recipientReceipt = peers[0]!;
                          const view = projectRuntimeMathAssignmentToExecutionView(recipientReceipt.assignment, {
                            expectedRunId: binding.runId,
                            expectedBindingDigest: mathDigest(canonicalMathJson(binding)),
                            expectedTargetSlotId: peerSlot,
                            ...(recipientReceipt.preparedGit?.baseCommit
                              ? { expectedBaseCommit: recipientReceipt.preparedGit.baseCommit }
                              : {}),
                          });
                          if (view.kind !== 'research') throw new Error('math_share_peer_research_required');

                          recipient = { assignmentId: recipientReceipt.assignmentId, slotId: peerSlot };
                        }
                        const { solverProjectRoot } = resolveMathRunProjectPaths(
                          binding,
                          resolvedCapability.projectRoot,
                          receipt.preparedGit.worktreePath
                        );
                        if (
                          receipt.preparedGit.solverProjectRoot &&
                          receipt.preparedGit.solverProjectRoot !== solverProjectRoot
                        ) {
                          throw new Error('math_share_project_binding_invalid');
                        }
                        // Research assignments have no staged proof tree. Their ordinary notes live in
                        // the assigned worktree; formalizers remain confined to their staged sources.
                        const sourceRoot =
                          assignment.kind === 'research'
                            ? path.resolve(receipt.preparedGit.worktreePath)
                            : path.resolve(solverProjectRoot, assignment.sourceRootRelative);
                        if (assignment.kind === 'research') {
                          const originalSources = new Set(
                            (binding.problem?.verificationTargets ?? []).map((target) =>
                              path.resolve(solverProjectRoot, target.pathRelative)
                            )
                          );
                          for (const file of intent.files ?? []) {
                            const note = /^[^./\\][^/\\]*\.md$/u.test(file);
                            const draft = path.resolve(sourceRoot, file);
                            const auxiliary =
                              file.endsWith('.lean') &&
                              isMathPathWithin(solverProjectRoot, draft) &&
                              !originalSources.has(draft);
                            if (!note && !auxiliary) throw new Error('math_share_research_note_unauthorized');
                          }
                        }
                        let publicationError: unknown;
                        const attachmentFailure = (error: unknown): never => {
                          if (error === publicationError) throw error;
                          const ioError =
                            error instanceof Error && error.message === 'math_lite_delivery_file_missing'
                              ? error.cause
                              : error;
                          if (
                            ['ENOENT', 'ENOTDIR', 'EBUSY', 'EIO'].includes(
                              (ioError as NodeJS.ErrnoException)?.code ?? ''
                            )
                          ) {
                            throw new ResearchTeamOrchestrationError(
                              'math_share_attachment_unavailable',
                              'The finding was not sent because an attachment could not be frozen. Retry the same summary without files, then share attachments separately.',
                              true
                            );
                          }
                          throw error;
                        };
                        if (intent.files?.length) {
                          try {
                            assertMathCanonicalPath(sourceRoot);
                          } catch (error) {
                            attachmentFailure(error);
                          }
                        }
                        if (assignment.kind !== 'research' && !isMathPathWithin(solverProjectRoot, sourceRoot))
                          throw new Error('math_share_source_unauthorized');
                        // A proof owner's summary-only share still carries its current proof source and
                        // notes, so research dispatched from it reads the owner's actual state instead of
                        // rederiving it from the original target. Missing files are simply omitted.
                        const defaultFiles =
                          intent.files?.length || assignment.kind !== 'formalize'
                            ? []
                            : [
                                ...new Set([
                                  ...(binding.problem?.verificationTargets ?? []).map(
                                    (target) => target.pathRelative
                                  ),
                                  'RESEARCH.md',
                                ]),
                              ].filter((file) => {
                                const candidate = path.resolve(sourceRoot, file);
                                try {
                                  return (
                                    isMathPathWithin(sourceRoot, candidate) &&
                                    fs.lstatSync(candidate).isFile() &&
                                    fs.realpathSync(candidate) === candidate
                                  );
                                } catch {
                                  return false;
                                }
                              });
                        const store = await ensureMathArtifactStore(resolvedCapability.projectRoot);
                        const directory = path.join(
                          path.dirname(binding.artifactStoreRoot),
                          'lite-shares',
                          receipt.assignmentId
                        );
                        fs.mkdirSync(directory, { recursive: true, mode: 0o700 });
                        assertMathCanonicalPath(directory);
                        return withMathRuntimeLease(
                          {
                            lockPath: path.join(directory, '.lock'),
                            flockExecutable: '/usr/bin/flock',
                            signal: extra.signal,
                          },
                          async (lease) => {
                            const freezeFiles = (pathRelatives: readonly string[]) =>
                              freezeMathLiteDeliveryFileSet({
                                sourceRoot,
                                pathRelatives,
                                assertHeld: lease.assertHeld,
                                publish: async ({ pathRelative, text, sha256 }) => {
                                  const artifactId = `share_${mathDigest(canonicalMathJson({ assignmentId: receipt.assignmentId, pathRelative, sha256 }))}`;
                                  await store
                                    .publishText({
                                      artifactId,
                                      assignmentId: receipt.assignmentId,
                                      kind: 'evidence',
                                      sensitivity: 'solver-visible',
                                      mediaType: pathRelative.endsWith('.md') ? 'text/markdown' : 'text/x-lean',
                                      text,
                                    })
                                    .catch((error: unknown) => {
                                      publicationError = error;
                                      throw error;
                                    });
                                  return `math-artifact://${binding.runId}/${artifactId}`;
                                },
                              });
                            const waitQuestionIds = intent.wait_for_question_ids?.toSorted();
                            const requiredSources = (assignment.request.verificationTargets ?? []).map(
                              (entry) => entry.pathRelative
                            );
                            const frozen = waitQuestionIds?.length
                              ? await freezeFiles([
                                  ...new Set([
                                    ...(intent.files?.length ? intent.files : defaultFiles),
                                    ...requiredSources,
                                  ]),
                                ])
                              : intent.files?.length
                                ? await freezeFiles(intent.files).catch(attachmentFailure)
                                : defaultFiles.length
                                  ? // Default attachments are best effort: a file changing mid-freeze keeps the
                                    // summary-only share the owner asked for; artifact store failures still surface.
                                    await freezeFiles(defaultFiles).catch(
                                      (error: unknown): Awaited<ReturnType<typeof freezeFiles>> => {
                                        if (error === publicationError) throw error;
                                        return [];
                                      }
                                    )
                                  : [];
                            let waitMetadata: {
                              wait_for_question_ids?: string[];
                              wait_producer_assignment_ids?: string[];
                              wait_evidence_ids?: string[];
                            } = waitQuestionIds ? { wait_for_question_ids: waitQuestionIds } : {};
                            if (waitQuestionIds?.length) {
                              if (
                                !requiredSources.length ||
                                requiredSources.some((file) => !frozen.some((entry) => entry.pathRelative === file))
                              )
                                throw new Error('math_research_wait_requires_source_snapshot');
                              // A repeated wait shares the original evidence baseline, even if
                              // findings arrived after a lost acknowledgement. It cannot re-arm itself.
                              const previous = fs
                                .readdirSync(directory)
                                .filter((file) => /^[a-f0-9]{64}\.json$/u.test(file))
                                .map((file) => {
                                  const candidatePath = path.join(directory, file);
                                  assertMathCanonicalPath(candidatePath);
                                  const candidate = mathLiteProgressSnapshotSchema.parse(readMathJson(candidatePath));
                                  const { shareId: candidateId, ...content } = candidate;
                                  if (
                                    candidateId !== file.slice(0, -5) ||
                                    candidate.assignmentId !== receipt.assignmentId ||
                                    candidate.runId !== binding.runId ||
                                    candidate.targetSlotId !== resolvedCapability.slotId ||
                                    candidate.bindingDigest !== mathDigest(canonicalMathJson(binding)) ||
                                    mathDigest(
                                      canonicalMathJson({
                                        ...content,
                                        summary: normalizeMathProgressSummary(content.summary),
                                      })
                                    ) !== candidateId
                                  )
                                    throw new Error('math_share_snapshot_integrity');
                                  return candidate;
                                })
                                .find(
                                  (candidate) =>
                                    canonicalMathJson(candidate.wait_for_question_ids ?? null) ===
                                      canonicalMathJson(waitQuestionIds) &&
                                    normalizeMathProgressSummary(candidate.summary) ===
                                      normalizeMathProgressSummary(intent.summary) &&
                                    canonicalMathJson(candidate.files) ===
                                      canonicalMathJson(
                                        frozen.map(({ pathRelative, ref, sha256 }) => ({ pathRelative, ref, sha256 }))
                                      )
                                );
                              if (previous) {
                                if (!previous.wait_producer_assignment_ids?.length || !previous.wait_evidence_ids)
                                  throw new Error('math_share_snapshot_integrity');
                                waitMetadata = {
                                  wait_for_question_ids: waitQuestionIds,
                                  wait_producer_assignment_ids: previous.wait_producer_assignment_ids,
                                  wait_evidence_ids: previous.wait_evidence_ids,
                                };
                              } else {
                                const feedback = await readMathLiteFeedback({
                                  resolvedCapability,
                                  signal: extra.signal,
                                  consume: false,
                                });
                                const questions = feedback.research_questions.filter(
                                  (question) => question.pending && waitQuestionIds.includes(question.question_id)
                                );
                                if (
                                  waitQuestionIds.some(
                                    (id) => !questions.some((question) => question.question_id === id)
                                  )
                                )
                                  throw new Error('math_research_wait_question_not_authorized_or_active');
                                waitMetadata = {
                                  wait_for_question_ids: waitQuestionIds,
                                  wait_producer_assignment_ids: [
                                    ...new Set(questions.map((question) => question.producer_assignment_id)),
                                  ].toSorted(),
                                  wait_evidence_ids: [
                                    ...new Set(questions.flatMap((question) => question.finding_ids)),
                                  ].toSorted(),
                                };
                              }
                            }
                            const snapshot = {
                              schema: 'deepscientist.math.progress-share.v1' as const,
                              runId: binding.runId,
                              bindingDigest: mathDigest(canonicalMathJson(binding)),
                              assignmentId: receipt.assignmentId,
                              targetSlotId: resolvedCapability.slotId,
                              summary: intent.summary,
                              ...waitMetadata,
                              ...(recipient ? { recipient } : {}),
                              files: frozen.map(({ pathRelative, ref, sha256 }) => ({ pathRelative, ref, sha256 })),
                            };
                            const shareId = mathDigest(
                              canonicalMathJson({
                                ...snapshot,
                                summary: normalizeMathProgressSummary(snapshot.summary),
                              })
                            );
                            mathLiteProgressSnapshotSchema.parse({ ...snapshot, shareId });
                            lease.assertHeld();
                            extra.signal.throwIfAborted();
                            if (recipientReceipt) {
                              const livePeer = listProjectGitResearchTeamAssignments({
                                workspace: binding.workspace,
                                teamId: resolvedCapability.teamId,
                                strict: true,
                              }).find((entry) => entry.assignmentId === recipientReceipt!.assignmentId);
                              if (!livePeer || canonicalMathJson(livePeer) !== canonicalMathJson(recipientReceipt))
                                throw new Error('math_feedback_assignment_changed');
                            }
                            if (recipient) {
                              for (const file of fs.readdirSync(directory)) {
                                if (!/^[a-f0-9]{64}\.json$/u.test(file)) continue;
                                const priorPath = path.join(directory, file);
                                assertMathCanonicalPath(priorPath);
                                const prior = mathLiteProgressSnapshotSchema.parse(readMathJson(priorPath));
                                const { shareId: priorId, ...priorSnapshot } = prior;
                                if (
                                  priorId !== file.slice(0, -5) ||
                                  mathDigest(
                                    canonicalMathJson({
                                      ...priorSnapshot,
                                      summary: normalizeMathProgressSummary(priorSnapshot.summary),
                                    })
                                  ) !== priorId
                                )
                                  throw new Error('math_share_snapshot_integrity');
                                if (
                                  prior.recipient?.slotId === recipient.slotId &&
                                  normalizeMathProgressSummary(prior.summary) ===
                                    normalizeMathProgressSummary(snapshot.summary) &&
                                  canonicalMathJson(prior.files) === canonicalMathJson(snapshot.files) &&
                                  prior.recipient.assignmentId !== recipient.assignmentId
                                )
                                  throw new Error('math_share_recipient_changed');
                              }
                            }
                            const record = path.join(directory, `${shareId}.json`);
                            assertMathCanonicalPath(record);
                            if (!fs.existsSync(record)) writeMathJsonDurable(record, { ...snapshot, shareId }, 0o400);
                            // The identity ignores presentation-only wrapping, but a retry must
                            // send the first frozen bytes, including whitespace and indentation.
                            const retained = mathLiteProgressSnapshotSchema.parse(readMathJson(record));
                            const { shareId: retainedId, ...retainedSnapshot } = retained;
                            if (
                              retainedId !== shareId ||
                              canonicalMathJson({
                                ...retainedSnapshot,
                                summary: normalizeMathProgressSummary(retainedSnapshot.summary),
                              }) !==
                                canonicalMathJson({
                                  ...snapshot,
                                  summary: normalizeMathProgressSummary(snapshot.summary),
                                })
                            )
                              throw new Error('math_share_snapshot_integrity');
                            return {
                              shareId,
                              summary: retained.summary,
                              ...(retained.wait_for_question_ids
                                ? { wait_for_question_ids: retained.wait_for_question_ids }
                                : {}),
                              files: retained.files.map((file) => ({
                                pathRelative: file.pathRelative!,
                                ref: file.ref!,
                                sha256: file.sha256!,
                              })),
                              ...(retained.recipient
                                ? {
                                    recipient: {
                                      assignmentId: retained.recipient.assignmentId!,
                                      slotId: retained.recipient.slotId!,
                                    },
                                  }
                                : {}),
                            };
                          }
                        );
                      },
                      hasMathLiteSealedDelivery: (deliveryId) => {
                        const binding = readMathRunBinding(
                          verifyMathRunInputs(JSON.parse(process.env[MATH_RUN_INPUTS_ENV]!))
                        );
                        return Boolean(readMathLiteSealedSet(path.dirname(binding.artifactStoreRoot), deliveryId));
                      },
                      isUnchangedMathLiteBlockedRetry: async (receipt, rawResult) => {
                        const intent = normalizeMathLiteDeliveryIntent(rawResult);
                        const assignment = normalizeRuntimeMathAssignment(receipt.assignment);
                        if (
                          intent.status !== 'blocked' ||
                          assignment.request.kind !== 'formalize' ||
                          !assignment.request.predecessorAssignmentId
                        )
                          return false;
                        const binding = readMathRunBinding(
                          verifyMathRunInputs(JSON.parse(process.env[MATH_RUN_INPUTS_ENV]!))
                        );
                        const parent = listProjectGitResearchTeamAssignments({
                          workspace: binding.workspace,
                          teamId: resolvedCapability.teamId,
                          strict: true,
                        }).find((entry) => entry.assignmentId === assignment.request.predecessorAssignmentId);
                        if (
                          !parent?.delivery ||
                          parent.state !== 'superseded' ||
                          parent.slotId !== receipt.slotId ||
                          !hasMathV2BlockedDelivery(parent)
                        )
                          return false;
                        const selected = selectMathV2IntegrationDelivery(parent, parent.delivery.deliveryId, {
                          expectedRunId: binding.runId,
                          expectedBindingDigest: mathDigest(canonicalMathJson(binding)),
                        });
                        const sealed = readMathLiteSealedSet(
                          path.dirname(binding.artifactStoreRoot),
                          parent.delivery.deliveryId
                        );
                        if (
                          !sealed ||
                          sealed.assignmentId !== parent.assignmentId ||
                          sealed.targetSlotId !== receipt.slotId ||
                          sealed.runId !== binding.runId ||
                          canonicalMathJson(sealed.delivery) !== canonicalMathJson(selected.delivery.delivery)
                        )
                          return false;
                        const baselineRevision = mathLiteFeedbackCursor(binding, parent.assignmentId).read()
                          .blockedEvidenceRevision;
                        // Older seals lack an evidence boundary. Never silently swallow their blocked report.
                        if (!baselineRevision || !intent.files?.length || !receipt.preparedGit?.worktreePath)
                          return false;
                        const targetPaths = new Set(
                          assignment.request.verificationTargets?.map((target) => target.pathRelative)
                        );
                        if (intent.files.some((file) => !targetPaths.has(file) && file !== 'RESEARCH.md'))
                          return false;
                        const proofFiles = intent.files.filter((file) => targetPaths.has(file));
                        const frozenProofFiles = sealed.files.filter((file) => targetPaths.has(file.pathRelative));
                        // Notes are retained, but editing a note does not change the proof-source comparison.
                        if (!proofFiles.length || proofFiles.length !== frozenProofFiles.length) return false;
                        const { solverProjectRoot } = resolveMathRunProjectPaths(
                          binding,
                          resolvedCapability.projectRoot,
                          receipt.preparedGit.worktreePath
                        );
                        const sourceRoot = path.resolve(solverProjectRoot, assignment.sourceRootRelative);
                        if (!isMathPathWithin(solverProjectRoot, sourceRoot))
                          throw new Error('math_blocked_retry_source_root');
                        assertMathCanonicalPath(sourceRoot);
                        const evidenceRevision = await readMathLiteBlockedEvidenceRevision({
                          resolvedCapability,
                          signal: extra.signal,
                        });
                        if (baselineRevision !== evidenceRevision) return false;
                        extra.signal.throwIfAborted();
                        return proofFiles.every((relative) => {
                          const frozen = frozenProofFiles.find((entry) => entry.pathRelative === relative);
                          if (!frozen) return false;
                          const file = path.resolve(sourceRoot, relative);
                          if (!isMathPathWithin(sourceRoot, file)) return false;
                          assertMathCanonicalPath(file);
                          return (
                            fs.existsSync(file) &&
                            fs.statSync(file).isFile() &&
                            mathDigest(fs.readFileSync(file)) === frozen.sha256
                          );
                        });
                      },
                      prepareMathLiteDelivery: async ({ rawResult, deliveryId, receipt, assignment }) => {
                        verifyMathRunInputsEnvironment(process.env);
                        const encoded = process.env[MATH_RUN_INPUTS_ENV];
                        if (!encoded) throw new Error('Mathematics run binding is unavailable.');
                        const binding = readMathRunBinding(verifyMathRunInputs(JSON.parse(encoded)));
                        if (
                          !receipt.preparedGit?.worktreePath ||
                          !assignment.sourceRootRelative ||
                          !assignment.baseCommit
                        ) {
                          throw new Error('Mathematics lite delivery binding is incomplete.');
                        }
                        const { solverProjectRoot: workerProjectRoot } = resolveMathRunProjectPaths(
                          binding,
                          resolvedCapability.projectRoot,
                          receipt.preparedGit.worktreePath
                        );
                        if (
                          receipt.preparedGit.solverProjectRoot &&
                          receipt.preparedGit.solverProjectRoot !== workerProjectRoot
                        ) {
                          throw new Error('Mathematics lite delivery project binding is invalid.');
                        }
                        const sourceRoot =
                          assignment.kind === 'research'
                            ? path.resolve(receipt.preparedGit.worktreePath)
                            : path.resolve(workerProjectRoot, assignment.sourceRootRelative);
                        assertMathCanonicalPath(sourceRoot);
                        if (assignment.kind !== 'research' && !isMathPathWithin(workerProjectRoot, sourceRoot)) {
                          throw new Error('Mathematics lite delivery source root is unauthorized.');
                        }
                        const store = await ensureMathArtifactStore(resolvedCapability.projectRoot);
                        const runRoot = path.dirname(binding.artifactStoreRoot);
                        // An omitted result is a host-owned recovery request, never a new delivery.
                        const intent =
                          rawResult === undefined ? undefined : normalizeMathLiteDeliveryIntent(rawResult);
                        const intentHash = intent === undefined ? undefined : mathDigest(canonicalMathJson(intent));
                        fs.mkdirSync(path.join(runRoot, 'lite-deliveries'), { recursive: true, mode: 0o700 });
                        return withMathRuntimeLease(
                          {
                            lockPath: path.join(runRoot, 'lite-deliveries', `${deliveryId}.lock`),
                            flockExecutable: '/usr/bin/flock',
                            signal: extra.signal,
                          },
                          async (lease) => {
                            lease.assertHeld();
                            const restoreSealed = async (sealed: MathLiteSealedSet) => {
                              const frozenFiles = [] as Array<{
                                pathRelative: string;
                                ref: string;
                                text: string;
                                sha256: string;
                              }>;
                              for (const file of sealed.files) {
                                lease.assertHeld();
                                let offsetBytes = 0;
                                let text = '';
                                let totalBytes = 0;
                                for (;;) {
                                  // eslint-disable-next-line no-await-in-loop
                                  const chunk = await store.read(
                                    { ref: file.ref, offsetBytes, maxBytes: 2048 },
                                    { role: 'worker', assignmentId: receipt.assignmentId }
                                  );
                                  text += chunk.text;
                                  totalBytes = chunk.totalBytes;
                                  if (chunk.nextOffsetBytes === undefined) break;
                                  offsetBytes = chunk.nextOffsetBytes;
                                }
                                if (mathDigest(text) !== file.sha256 || totalBytes !== file.bytes) {
                                  throw new Error('math_lite_delivery_sealed_artifact_integrity');
                                }
                                lease.assertHeld();
                                frozenFiles.push({
                                  pathRelative: file.pathRelative,
                                  ref: file.ref,
                                  text,
                                  sha256: file.sha256,
                                });
                              }
                              const textByPath = new Map(frozenFiles.map((file) => [file.pathRelative, file.text]));
                              const sourceArtifacts = sealed.sourceArtifacts.map((artifact) => {
                                const content = textByPath.get(artifact.pathRelative);
                                if (content === undefined || mathDigest(content) !== artifact.contentSha256) {
                                  throw new Error('math_lite_delivery_sealed_source_integrity');
                                }
                                return { ...artifact, content };
                              });
                              return Object.freeze({
                                delivery: sealed.delivery,
                                sourceArtifacts: Object.freeze(sourceArtifacts),
                                frozenFiles: Object.freeze(frozenFiles),
                              });
                            };
                            const sealed = readMathLiteSealedSet(runRoot, deliveryId);
                            if (sealed) {
                              if (
                                sealed.runId !== binding.runId ||
                                sealed.assignmentId !== receipt.assignmentId ||
                                sealed.targetSlotId !== resolvedCapability.slotId
                              ) {
                                throw new Error('math_lite_delivery_sealed_identity');
                              }
                              if (intentHash !== undefined && sealed.intentHash !== intentHash)
                                throw new Error('math_lite_delivery_conflict');
                              return restoreSealed(sealed);
                            }
                            if (intentHash === undefined) throw new Error('math_lite_delivery_not_sealed');
                            const blockedEvidenceRevision =
                              assignment.kind === 'formalize' && intent?.status === 'blocked'
                                ? await readMathLiteBlockedEvidenceRevision({
                                    resolvedCapability,
                                    signal: extra.signal,
                                  })
                                : undefined;
                            const prepared = await prepareMathLiteWorkerDelivery(rawResult, {
                              deliveryId,
                              assignmentId: receipt.assignmentId,
                              baseCommit: assignment.baseCommit,
                              assignmentKind: assignment.kind,
                              verificationTargets: assignment.request.verificationTargets,
                              preflightFile: (pathRelative) => {
                                lease.assertHeld();
                                const sourceFile = path.resolve(sourceRoot, pathRelative);
                                if (!isMathPathWithin(sourceRoot, sourceFile)) {
                                  throw new Error('Mathematics lite delivery file is unauthorized.');
                                }
                                // Same rule as a research share: an auxiliary Lean file lives in
                                // the solver project and is never one of the original sources.
                                if (assignment.kind === 'research' && pathRelative.endsWith('.lean')) {
                                  const originalSources = new Set(
                                    (binding.problem?.verificationTargets ?? []).map((target) =>
                                      path.resolve(workerProjectRoot, target.pathRelative)
                                    )
                                  );
                                  if (
                                    !isMathPathWithin(workerProjectRoot, sourceFile) ||
                                    originalSources.has(sourceFile)
                                  )
                                    throw new Error('math_lite_delivery_file_unauthorized');
                                }
                                assertMathCanonicalPath(sourceFile);
                                let stat: fs.Stats;
                                try {
                                  stat = fs.lstatSync(sourceFile);
                                } catch (error) {
                                  if ((error as NodeJS.ErrnoException).code === 'ENOENT') {
                                    throw new Error('math_lite_delivery_file_missing');
                                  }
                                  throw error;
                                }
                                if (
                                  !stat.isFile() ||
                                  stat.isSymbolicLink() ||
                                  stat.nlink !== 1 ||
                                  stat.size > 5 * 1024 * 1024
                                ) {
                                  throw new Error('math_lite_delivery_file_invalid');
                                }
                              },
                              freezeFiles: async (pathRelatives) =>
                                freezeMathLiteDeliveryFileSet({
                                  sourceRoot,
                                  pathRelatives,
                                  assertHeld: lease.assertHeld,
                                  publish: async ({ pathRelative, text, sha256 }) => {
                                    const artifactId = mathLiteDeliveryArtifactId(deliveryId, pathRelative, sha256);
                                    const ref = `math-artifact://${binding.runId}/${artifactId}`;
                                    await store.publishText({
                                      artifactId,
                                      assignmentId: receipt.assignmentId,
                                      kind: 'evidence',
                                      sensitivity: 'solver-visible',
                                      mediaType: pathRelative.endsWith('.md') ? 'text/markdown' : 'text/x-lean',
                                      text,
                                    });
                                    lease.assertHeld();
                                    return ref;
                                  },
                                }),
                            });
                            lease.assertHeld();
                            writeMathLiteSealedSet(runRoot, {
                              schema: 'deepscientist.math.lite-sealed-set.v1',
                              runId: binding.runId,
                              deliveryId,
                              assignmentId: receipt.assignmentId,
                              targetSlotId: resolvedCapability.slotId,
                              intentHash,
                              delivery: prepared.delivery,
                              files: prepared.frozenFiles.map((file) => ({
                                pathRelative: file.pathRelative,
                                ref: file.ref,
                                sha256: file.sha256,
                                bytes: Buffer.byteLength(file.text, 'utf8'),
                              })),
                              sourceArtifacts: prepared.sourceArtifacts.map(
                                ({ content: _content, ...artifact }) => artifact
                              ),
                            });
                            if (blockedEvidenceRevision !== undefined) {
                              await recordMathLiteBlockedEvidence({
                                resolvedCapability,
                                signal: extra.signal,
                                revision: blockedEvidenceRevision,
                              });
                            }
                            if (blockedEvidenceRevision !== undefined && intent?.status === 'blocked') {
                              // A blocked handoff ends the assignment; the successor that resumes
                              // this slot needs the owner's own account of where the argument
                              // stopped. Run 23 attempt 14 recorded no mathematical boundary at
                              // all, so the resumed slot re-derived the gap from the original seed.
                              // The record is advisory: a failure here must not fail the delivery,
                              // but an abort or an integrity fault still has to surface.
                              await publishMathLiteBlockerBoundary(
                                binding,
                                receipt,
                                {
                                  ...(intent.summary ? { summary: intent.summary } : {}),
                                  ...(intent.blockers ? { blockers: intent.blockers } : {}),
                                },
                                extra.signal
                              ).catch((error: unknown): undefined => {
                                extra.signal.throwIfAborted();
                                if (isMathPlanningSafetyError(error)) throw error;
                                return undefined;
                              });
                            }
                            lease.assertHeld();
                            return prepared;
                          }
                        );
                      },
                    }
                  : {}),
                readMathArtifact: async (request, access) => {
                  if (!mathArtifactStoreInitialization) {
                    mathArtifactStoreInitialization = (async () => {
                      const encoded = process.env[MATH_RUN_INPUTS_ENV];
                      if (!encoded) throw new Error('Mathematics run binding is unavailable.');
                      const inputs = verifyMathRunInputs(JSON.parse(encoded));
                      const binding = readMathRunBinding(inputs);
                      resolveMathRunProjectPaths(binding, resolvedCapability.projectRoot);
                      const store = new MathArtifactStore({
                        runRoot: path.dirname(binding.artifactStoreRoot),
                        runId: binding.runId,
                        flockExecutable: '/usr/bin/flock',
                      });
                      await store.initialize();
                      await store.recover();
                      mathArtifactStore = store;
                      return store;
                    })().catch((error) => {
                      mathArtifactStoreInitialization = undefined;
                      throw error;
                    });
                  }
                  const store = await mathArtifactStoreInitialization;
                  try {
                    return await store.read(request, access);
                  } catch (error) {
                    if (
                      !mathematicsLiteRole ||
                      access.role !== 'worker' ||
                      !(error instanceof MathArtifactError) ||
                      error.code !== 'unauthorized'
                    )
                      throw error;
                    const linkedAccess = await readMathLiteFeedbackArtifact(
                      resolvedCapability,
                      extra.signal,
                      request.ref,
                      access
                    );
                    const artifact = await store.read(request, linkedAccess);
                    // Recheck the live association after the awaited read; no frozen
                    // grant or old WAL is mutated to provide late-arriving feedback.
                    await readMathLiteFeedbackArtifact(resolvedCapability, extra.signal, request.ref, access, true);
                    await recordMathLiteFeedbackUse({
                      resolvedCapability,
                      signal: extra.signal,
                      ref: request.ref,
                      sourceHash: artifact.sha256,
                      status: 'read',
                    });
                    return artifact;
                  }
                },
              }
            : {}),
          certifyMathematics: certifyFormalVerifications,
          verifyMathematicsHelperNode,
          signal: extra.signal,
          ...(resolvedCapability.roleKind === 'lead'
            ? {
                prepareBoundImoFastCheck: async (request: {
                  workspaceRoot: string;
                  baseCommit?: string;
                  signal?: AbortSignal;
                }) =>
                  runImo2026HostFastCheck({
                    workspaceRoot: request.workspaceRoot,
                    ...(request.baseCommit ? { baseCommit: request.baseCommit } : {}),
                    ...(request.signal ? { signal: request.signal } : {}),
                  }),
                preflightMathematicsRoute: runMathematicsRoutePreflight,
                checkLeanToolchainReadiness,
                prepareLeanEvalWorkspace: async ({ assignment, target }) => {
                  const repositoryRoot = process.env.DEEPSCIENTIST_LEAN_EVAL_ROOT?.trim();
                  const problemId = assignment.math?.problemContract?.problemId;
                  if (!repositoryRoot) {
                    return {
                      ok: false,
                      workspace: '',
                      baseCommit: assignment.git.baseCommit,
                      error: 'DEEPSCIENTIST_LEAN_EVAL_ROOT is not configured for the Research Team Lead.',
                    };
                  }
                  if (!problemId) {
                    return {
                      ok: false,
                      workspace: '',
                      baseCommit: assignment.git.baseCommit,
                      error: 'Lean-Eval assignment is missing problemContract.problemId.',
                    };
                  }
                  const branch = [
                    'deepscientist',
                    'agents',
                    'mathematics-research-team',
                    stableLeanEvalBranchSegment(resolvedCapability.teamId),
                    stableLeanEvalBranchSegment(target.roleId),
                    stableLeanEvalBranchSegment(assignment.assignmentId),
                  ].join('/');
                  try {
                    return await prepareLeanEvalTeamWorkspace({
                      repositoryRoot,
                      projectRoot: resolvedCapability.projectRoot,
                      assignmentId: assignment.assignmentId,
                      problemId,
                      expectedBaseCommit: assignment.git.baseCommit,
                      branch,
                      ...(assignment.math?.sessionContinuation?.mode === 'reuse_source_slot'
                        ? { sourceAssignmentId: assignment.math.sessionContinuation.sourceAssignmentId }
                        : {}),
                      teamId: resolvedCapability.teamId,
                      slotId: target.slotId,
                    });
                  } catch (error) {
                    return {
                      ok: false,
                      workspace: '',
                      baseCommit: assignment.git.baseCommit,
                      error: error instanceof Error ? error.message : String(error),
                    };
                  }
                },
              }
            : {}),
          ...(process.env.DEEPSCIENTIST_LEAN_EVAL_ROOT && resolvedCapability.roleKind === 'worker'
            ? {
                runLeanEvalCounterexampleProbe: async (request) =>
                  runLeanEvalCounterexampleProbe({
                    projectRoot: request.workspaceRoot,
                    expression: request.probe.expression,
                    ...(request.probe.precondition ? { precondition: request.probe.precondition } : {}),
                    ...(request.probe.cases ? { cases: request.probe.cases } : {}),
                    ...(request.probe.mode ? { mode: request.probe.mode } : {}),
                    ...(request.probe.imports ? { imports: request.probe.imports } : {}),
                    ...(request.probe.timeoutMs ? { timeoutMs: request.probe.timeoutMs } : {}),
                    signal: request.signal,
                  }),
                runLeanEvalProofSession: async (request) => {
                  const session = await runLeanEvalTeamSession({
                    assignment: request.assignment,
                    workspaceRoot: request.workspaceRoot,
                    projectRoot: resolvedCapability.projectRoot,
                    repositoryRoot: process.env.DEEPSCIENTIST_LEAN_EVAL_ROOT!,
                    signal: request.signal,
                    ...(leanEvalStructuredSearchProvider
                      ? { structuredSearch: leanEvalStructuredSearchProvider }
                      : {}),
                  });
                  return {
                    proofLoop: session.proofLoop,
                    ...(session.repairRequest ? { repairRequest: session.repairRequest } : {}),
                    resultPatch: {
                      math: session.math,
                      disposition: session.disposition,
                      gitHeadCommit: session.gitHeadCommit,
                      ...(session.mathCheckpoint ? { mathCheckpoint: session.mathCheckpoint } : {}),
                    },
                  };
                },
              }
            : {}),
        }
      );
    }
  );

  installMathMcpShutdown(() => server.close());
  await server.connect(transport);
}

function researchTeamCapabilityCacheKey(
  capability: { teamId: string } | undefined,
  env: Readonly<Record<string, string | undefined>> = process.env
): string {
  // The MCP process is scoped to one Core conversation. Include the runtime
  // token and bound Team id so a recycled process cannot reuse a snapshot for
  // a different authenticated context. This value is only compared in memory.
  return [
    env.AIONUI_CONVERSATION_ID?.trim() ?? '',
    env.AIONUI_RUNTIME_TOKEN?.trim() ?? '',
    capability?.teamId ?? '',
  ].join('\u0000');
}

function resolveActiveCoreBaseUrl(): string | undefined {
  // AIONUI_BASE_URL is injected by the currently attached Core runtime and is
  // therefore authoritative.  The persisted DeepScientist URL is retained as
  // a compatibility fallback for standalone/manual MCP launches only.
  return (
    process.env.AIONUI_BASE_URL?.trim() ||
    process.env[RESEARCH_TEAM_CORE_BASE_URL_ENV]?.trim() ||
    undefined
  );
}

main().catch((error) => {
  const runtimeError = error as {
    code?: unknown;
    reason?: unknown;
    message?: unknown;
    details?: unknown;
  };
  console.error(
    '[ResearchTeamMCP] Fatal error:',
    JSON.stringify({
      code: typeof runtimeError.code === 'string' ? runtimeError.code : 'mcp_startup_failed',
      reason: typeof runtimeError.reason === 'string' ? runtimeError.reason : 'unexpected_startup_error',
      message: typeof runtimeError.message === 'string' ? runtimeError.message : String(error),
      ...(runtimeError.details && typeof runtimeError.details === 'object' ? { details: runtimeError.details } : {}),
    })
  );
  process.exit(1);
});
