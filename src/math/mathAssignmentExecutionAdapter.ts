/**
 * Translate the compact v2 assignment protocol into the fields needed by a
 * Worker execution boundary.  This module deliberately does not construct a
 * ResearchTeamAssignment: v2 has no v1 workflow/lane/acceptance metadata and
 * treating the two contracts as interchangeable would drop runtime identity.
 */

import type { MathAssignmentRequest, RuntimeMathAssignment } from "../common/types/team/mathRuntimeContracts";
import { normalizeRuntimeMathAssignment } from "./mathAssignmentJournal";
import { MathWireValidationError, normalizeMathAssignment } from "./mathPublicWire";

export const MATH_EXECUTION_VIEW_SCHEMA = 'deepscientist.math.execution-view.v2' as const;
export const MATH_RESEARCH_TEAM_ENVELOPE_SCHEMA = 'deepscientist.math.research-team.envelope.v2' as const;

export type MathAssignmentAdapterErrorCode =
  | 'invalid_request'
  | 'integrity'
  | 'run_mismatch'
  | 'binding_mismatch'
  | 'target_slot_mismatch'
  | 'base_commit_mismatch';

export class MathAssignmentAdapterError extends Error {
  constructor(
    readonly code: MathAssignmentAdapterErrorCode,
    message: string
  ) {
    super(message);
    this.name = 'MathAssignmentAdapterError';
  }
}

/** Runtime checks supplied by the host at the v2 -> Worker boundary. */
export type MathAssignmentAdapterOptions = Readonly<{
  workerIds?: ReadonlySet<string>;
  expectedRunId?: string;
  expectedBindingDigest?: string;
  expectedTargetSlotId?: string;
  expectedBaseCommit?: string;
}>;

export type MathExecutionInput =
  | Readonly<{
      path: string;
      purpose: string;
    }>
  | Readonly<{
      artifactRef: string;
      purpose: string;
    }>;

/**
 * The stable, narrow view consumed by an execution adapter.  `source` keeps
 * request and durable runtime identities distinguishable during migration.
 * Runtime fields are omitted for a request view rather than invented.
 */
export type MathExecutionView = Readonly<{
  schema: typeof MATH_EXECUTION_VIEW_SCHEMA;
  source: 'dispatch-request' | 'runtime-assignment';
  targetSlotId: string;
  idempotencyKey: string;
  kind: MathAssignmentRequest['kind'];
  objective: string;
  sharedWritePaths: readonly string[];
  inputs: readonly MathExecutionInput[];
  acceptance: readonly string[];
  assignmentId?: string;
  runId?: string;
  bindingDigest?: string;
  scopeId?: string;
  baseCommit?: string;
  predecessorAssignmentId?: string;
  consumerAssignmentIds?: readonly string[];
  researchQuestion?: MathAssignmentRequest['researchQuestion'];
  payloadHash?: string;
  sourceRootRelative?: string;
  draftRoot?: string;
  artifactGrants: readonly string[];
  /** The normalized v2 request remains available without widening it to v1. */
  request: MathAssignmentRequest;
}>;

/** Shape compatible with the existing Research Team dispatch envelope. */
export type MathRuntimeResearchTeamEnvelope = Readonly<{
  schema: typeof MATH_RESEARCH_TEAM_ENVELOPE_SCHEMA;
  targetSlotId: string;
  idempotencyKey: string;
  assignment: MathExecutionView & Readonly<{ source: 'runtime-assignment' }>;
}>;

function deepFreeze<T>(value: T): T {
  if (!value || typeof value !== 'object' || Object.isFrozen(value)) return value;
  Object.freeze(value);
  for (const child of Object.values(value)) deepFreeze(child);
  return value;
}

function adapterError(code: MathAssignmentAdapterErrorCode, message: string): never {
  throw new MathAssignmentAdapterError(code, message);
}

function assertExpected(
  value: string,
  expected: string | undefined,
  code: MathAssignmentAdapterErrorCode,
  label: string
): void {
  if (expected !== undefined && value !== expected) adapterError(code, `${label} does not match the runtime binding.`);
}

function assertTargetAllowed(targetSlotId: string, options: MathAssignmentAdapterOptions): void {
  if (options.workerIds && !options.workerIds.has(targetSlotId)) {
    adapterError('target_slot_mismatch', 'targetSlotId is not present in the bound Worker roster.');
  }
  assertExpected(targetSlotId, options.expectedTargetSlotId, 'target_slot_mismatch', 'targetSlotId');
}

function copyRequest(request: MathAssignmentRequest): MathAssignmentRequest {
  // normalizeMathAssignment returns a detached object from Zod. Copy again so
  // callers cannot mutate an adapter view through a shared array reference.
  return deepFreeze({
    idempotencyKey: request.idempotencyKey,
    targetSlotId: request.targetSlotId,
    ...(request.predecessorAssignmentId ? { predecessorAssignmentId: request.predecessorAssignmentId } : {}),
    ...(request.consumerAssignmentIds ? { consumerAssignmentIds: [...request.consumerAssignmentIds] } : {}),
    ...(request.researchQuestion
      ? { researchQuestion: { ...request.researchQuestion, assumptions: [...request.researchQuestion.assumptions] } }
      : {}),
    kind: request.kind,
    objective: request.objective,
    ...(request.sharedWritePaths ? { sharedWritePaths: [...request.sharedWritePaths] } : {}),
    ...(request.inputs
      ? {
          inputs: request.inputs.map((input) =>
            'path' in input
              ? { path: input.path, purpose: input.purpose }
              : { artifactRef: input.artifactRef, purpose: input.purpose }
          ),
        }
      : {}),
    acceptance: [...request.acceptance],
    ...(request.verificationTargets
      ? {
          verificationTargets: request.verificationTargets.map((target) => ({ ...target })),
        }
      : {}),
  });
}

function requestView<S extends MathExecutionView['source']>(
  request: MathAssignmentRequest,
  source: S,
  runtime?: RuntimeMathAssignment
): MathExecutionView & Readonly<{ source: S }> {
  const normalized = copyRequest(request);
  return deepFreeze({
    schema: MATH_EXECUTION_VIEW_SCHEMA,
    source,
    targetSlotId: normalized.targetSlotId,
    idempotencyKey: normalized.idempotencyKey,
    kind: normalized.kind,
    ...(normalized.consumerAssignmentIds ? { consumerAssignmentIds: [...normalized.consumerAssignmentIds] } : {}),
    ...(normalized.researchQuestion ? { researchQuestion: normalized.researchQuestion } : {}),
    objective: normalized.objective,
    sharedWritePaths: [...(normalized.sharedWritePaths ?? [])],
    inputs: [...(normalized.inputs ?? [])],
    acceptance: [...normalized.acceptance],
    ...(runtime
      ? {
          assignmentId: runtime.assignmentId,
          runId: runtime.runId,
          bindingDigest: runtime.bindingDigest,
          scopeId: runtime.scopeId,
          baseCommit: runtime.baseCommit,
          ...(normalized.predecessorAssignmentId
            ? { predecessorAssignmentId: normalized.predecessorAssignmentId }
            : {}),
          payloadHash: runtime.payloadHash,
          sourceRootRelative: runtime.sourceRootRelative,
          draftRoot: runtime.draftRoot,
          artifactGrants: [...runtime.artifactGrants],
        }
      : { artifactGrants: [] }),
    request: normalized,
  });
}

/** Normalize a public v2 dispatch request into a narrow execution view. */
export function projectMathDispatchRequestToExecutionView(
  value: unknown,
  options: MathAssignmentAdapterOptions = {}
): MathExecutionView & Readonly<{ source: 'dispatch-request' }> {
  let request: MathAssignmentRequest;
  try {
    request = normalizeMathAssignment(value, options.workerIds);
  } catch (error) {
    if (error instanceof MathAssignmentAdapterError) throw error;
    if (
      error instanceof MathWireValidationError &&
      error.issues.some((issue) => issue.path === 'targetSlotId' && issue.code === 'unauthorized')
    ) {
      throw new MathAssignmentAdapterError(
        'target_slot_mismatch',
        'targetSlotId is not present in the bound Worker roster.'
      );
    }
    throw new MathAssignmentAdapterError('invalid_request', 'The v2 dispatch request is invalid.');
  }
  assertTargetAllowed(request.targetSlotId, options);
  return requestView(request, 'dispatch-request');
}

/**
 * Normalize a durable registry assignment and project all runtime-owned
 * identity into the execution view.  No v1 assignment cast is performed.
 */
export function projectRuntimeMathAssignmentToExecutionView(
  value: unknown,
  options: MathAssignmentAdapterOptions = {}
): MathExecutionView & Readonly<{ source: 'runtime-assignment' }> {
  let assignment: RuntimeMathAssignment;
  try {
    assignment = normalizeRuntimeMathAssignment(value);
  } catch (error) {
    if (error instanceof MathAssignmentAdapterError) throw error;
    throw new MathAssignmentAdapterError('integrity', 'The durable v2 assignment failed integrity validation.');
  }
  assertExpected(assignment.runId, options.expectedRunId, 'run_mismatch', 'runId');
  assertExpected(assignment.bindingDigest, options.expectedBindingDigest, 'binding_mismatch', 'bindingDigest');
  assertTargetAllowed(assignment.request.targetSlotId, options);
  assertExpected(assignment.baseCommit, options.expectedBaseCommit, 'base_commit_mismatch', 'baseCommit');
  return requestView(assignment.request, 'runtime-assignment', assignment);
}

/**
 * Build the generic Research Team dispatch envelope used during v2 migration.
 * Its `assignment` is explicitly a v2 execution view, never a v1 contract.
 */
export function runtimeMathAssignmentToResearchTeamEnvelope(
  value: unknown,
  options: MathAssignmentAdapterOptions = {}
): MathRuntimeResearchTeamEnvelope {
  const assignment = projectRuntimeMathAssignmentToExecutionView(value, options);
  return deepFreeze({
    schema: MATH_RESEARCH_TEAM_ENVELOPE_SCHEMA,
    targetSlotId: assignment.targetSlotId,
    idempotencyKey: assignment.idempotencyKey,
    assignment,
  });
}
