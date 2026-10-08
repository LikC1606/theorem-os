import type { RuntimeMathAssignment } from "../common/types/team/mathRuntimeContracts";
import type { ProjectGitResearchTeamAssignmentReceipt } from "../project-git/ProjectGitService";
import { normalizeRuntimeMathAssignment } from "./mathAssignmentJournal";
import { projectRuntimeMathAssignmentToExecutionView } from "./mathAssignmentExecutionAdapter";
import { MATH_DELIVERY_ENVELOPE_SCHEMA, projectMathWorkerDeliveryToEnvelope } from "./mathWorkerDeliveryAdapter";

export type MathV2IntegrationSelection = Readonly<{
  receipt: ProjectGitResearchTeamAssignmentReceipt;
  assignment: RuntimeMathAssignment;
  assignmentView: ReturnType<typeof projectRuntimeMathAssignmentToExecutionView>;
  delivery: ReturnType<typeof projectMathWorkerDeliveryToEnvelope>;
}>;

export type MathV2IntegrationPhase =
  | 'advisory_report'
  | 'blocked_report'
  | 'fresh_source'
  | 'private_pending'
  | 'private_rejected'
  | 'private_integrity_error'
  | 'canonical_pending'
  | 'canonical_rejected'
  | 'canonical_integrity_error'
  | 'canonical_verified'
  | 'superseded_history'
  | 'invalid_record';

/** A reported pause is a strict delivery fact, never a verification rejection. */
export function hasMathV2BlockedDelivery(receipt: ProjectGitResearchTeamAssignmentReceipt): boolean {
  if (receipt.schema !== 'deepscientist.research_team_assignment.v2' || !receipt.delivery) return false;
  return selectMathV2IntegrationDelivery(receipt, receipt.delivery.deliveryId).delivery.delivery.status === 'blocked';
}

/** Derive one mutually exclusive processing phase from the durable WAL facts. */
export function deriveMathV2IntegrationPhase(selection: MathV2IntegrationSelection): MathV2IntegrationPhase {
  const { receipt, assignment, delivery } = selection;
  if (receipt.state === 'superseded') return 'superseded_history';
  if (delivery.delivery.status === 'blocked') return 'blocked_report';
  if (assignment.request.kind === 'research') {
    return receipt.state === 'accepted' ||
      (receipt.state === 'integrated' && receipt.integration?.executionMode === 'advisory')
      ? 'advisory_report'
      : 'invalid_record';
  }
  const integration = receipt.integration;
  if (receipt.state === 'accepted' && integration === undefined) return 'fresh_source';
  if (integration?.executionMode !== 'artifact') return 'invalid_record';
  const disposition = integration.verification?.disposition;
  if (integration.retainedWithoutMerge === true && !integration.mergedCommit) {
    if (disposition === 'pending') return 'private_pending';
    if (disposition === 'candidate_rejected') return 'private_rejected';
    if (disposition === 'integrity_error') return 'private_integrity_error';
    return 'invalid_record';
  }
  if (!integration.mergedCommit) return 'invalid_record';
  if (disposition === 'candidate_rejected') return 'canonical_rejected';
  if (disposition === 'integrity_error') return 'canonical_integrity_error';
  if (disposition === 'pending' || integration.reverificationRequired === true) return 'canonical_pending';
  if (receipt.state === 'integrated' && integration.sourceVerificationReceipts?.length) {
    return 'canonical_verified';
  }
  return 'invalid_record';
}

export function selectMathV2IntegrationBatch(
  receipts: readonly ProjectGitResearchTeamAssignmentReceipt[],
  deliveryIds: readonly string[],
  options: Readonly<{ expectedRunId?: string; expectedBindingDigest?: string }> = {}
): readonly MathV2IntegrationSelection[] {
  if (receipts.length !== deliveryIds.length || receipts.length === 0)
    throw new Error('math_v2_integration_batch_invalid');
  const selections = receipts.map((receipt, index) =>
    selectMathV2IntegrationDelivery(receipt, deliveryIds[index]!, options)
  );
  if (
    new Set(selections.map((selection) => selection.delivery.deliveryId)).size !== selections.length ||
    new Set(selections.map((selection) => selection.assignment.assignmentId)).size !== selections.length ||
    new Set(selections.map((selection) => selection.assignmentView.targetSlotId)).size !== selections.length ||
    new Set(selections.map((selection) => selection.assignment.runId)).size !== 1 ||
    new Set(selections.map((selection) => selection.assignment.bindingDigest)).size !== 1
  )
    throw new Error('math_v2_integration_batch_conflict');
  return Object.freeze(selections);
}

export function selectMathV2IntegrationDelivery(
  receipt: ProjectGitResearchTeamAssignmentReceipt,
  deliveryId: string,
  options: Readonly<{ expectedRunId?: string; expectedBindingDigest?: string }> = {}
): MathV2IntegrationSelection {
  if (receipt.schema !== 'deepscientist.research_team_assignment.v2' || !receipt.delivery)
    throw new Error('math_v2_integration_delivery_missing');
  const assignment = normalizeRuntimeMathAssignment(receipt.assignment);
  if (assignment.assignmentId !== receipt.assignmentId) throw new Error('math_v2_integration_assignment_identity');
  const assignmentView = projectRuntimeMathAssignmentToExecutionView(assignment, {
    expectedTargetSlotId: receipt.slotId,
    ...(options.expectedRunId ? { expectedRunId: options.expectedRunId } : {}),
    ...(options.expectedBindingDigest ? { expectedBindingDigest: options.expectedBindingDigest } : {}),
  });
  if (receipt.delivery.deliveryId !== deliveryId) throw new Error('math_v2_integration_delivery_identity');
  const raw = receipt.delivery.result;
  if (
    !raw ||
    typeof raw !== 'object' ||
    Array.isArray(raw) ||
    (raw as Record<string, unknown>).schema !== MATH_DELIVERY_ENVELOPE_SCHEMA
  )
    throw new Error('math_v2_integration_schema');
  const envelope = raw as Record<string, unknown>;
  if (
    envelope.deliveryId !== deliveryId ||
    envelope.assignmentId !== receipt.assignmentId ||
    envelope.targetSlotId !== receipt.slotId
  )
    throw new Error('math_v2_integration_delivery_identity');
  const delivery = projectMathWorkerDeliveryToEnvelope(envelope.delivery, {
    deliveryId,
    assignmentId: receipt.assignmentId,
    targetSlotId: receipt.slotId,
  });
  if (envelope.payloadHash !== delivery.payloadHash) throw new Error('math_v2_integration_payload_hash');
  return Object.freeze({ receipt, assignment, assignmentView, delivery });
}
