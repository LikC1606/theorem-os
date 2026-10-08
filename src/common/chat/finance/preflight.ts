import { financeCompletionManifestSchema } from "./schemas";
import { getRequiredFinanceContractTools, resolveFinanceTaskContract } from "./taskContracts";
import type { FinanceCompletionManifest, FinanceToolRequirementCondition, StructuredReportCardKind } from "./types";

export type FinanceCompletionPreflightContext = {
  runId?: string;
  projectRoot?: string;
  projectGitHead?: string;
  artifactGitCommit?: string;
  activeConditions?: ReadonlySet<FinanceToolRequirementCondition>;
  activeCapabilities?: ReadonlySet<string>;
  verifiedReceiptIds?: ReadonlySet<string>;
  artifactKinds: ReadonlySet<string>;
  artifactRefs: ReadonlySet<string>;
  evidenceIds: ReadonlySet<string>;
  cardIds: ReadonlySet<string>;
  referencedCardIds: ReadonlySet<string>;
  cardKinds: ReadonlySet<StructuredReportCardKind>;
  sectionIds: ReadonlySet<string>;
  sectionRoles: ReadonlySet<string>;
  hasResultSummary: boolean;
  hasLimitations: boolean;
  /**
   * A report can still be useful when one provider or presentation helper is
   * unavailable.  The server sets this once there is a report block, evidence,
   * or an artifact to show the reader.  In that case validation gaps are
   * reported as partial instead of preventing publication.
   */
  hasReviewableOutput?: boolean;
};

export type FinanceCompletionPreflightResult =
  | { ok: true; manifest: FinanceCompletionManifest }
  | { ok: false; status: 'partial' | 'blocked'; gaps: string[]; manifest?: FinanceCompletionManifest };

const artifactRefKey = (artifactId: string, version: number): string => `${artifactId}@${version}`;

const partialReasonCode = (reason: string): string => {
  const separator = reason.indexOf(':');
  return (separator >= 0 ? reason.slice(0, separator) : reason).trim();
};

const isAllowedPartialReason = (reason: string, allowedReasons: readonly string[]): boolean =>
  allowedReasons.includes(partialReasonCode(reason));

export function preflightFinanceCompletion(
  value: unknown,
  context: FinanceCompletionPreflightContext
): FinanceCompletionPreflightResult {
  const parsed = financeCompletionManifestSchema.safeParse(value);
  if (!parsed.success) {
    return {
      ok: false,
      status: 'blocked',
      gaps: parsed.error.issues.map((issue) => `${issue.path.join('.') || 'manifest'}: ${issue.message}`),
    };
  }

  const manifest = parsed.data as FinanceCompletionManifest;
  const contract = resolveFinanceTaskContract(manifest.taskContract);
  if (!contract) return { ok: false, status: 'blocked', gaps: ['task_contract_unresolved'], manifest };

  // Preserve the model/runtime's original degradation reason so the report UI
  // can explain the real provider or data gap instead of showing only the
  // secondary contract checks derived below.
  const gaps: string[] = [...manifest.gaps];
  if (context.runId && manifest.runId !== context.runId) gaps.push('run_id_mismatch');
  if (contract.taskKind !== manifest.taskKind) gaps.push('task_kind_mismatch');
  const unsupportedPartialReasons =
    manifest.status === 'partial' || manifest.status === 'blocked'
      ? manifest.gaps.filter((gap) => !isAllowedPartialReason(gap, contract.allowedPartialReasons))
      : [];
  unsupportedPartialReasons.forEach((reason) => gaps.push(`partial_reason_not_allowed:${reason}`));

  const mismatchedReceipt = manifest.toolReceipts.find((receipt) => receipt.runId !== manifest.runId);
  if (mismatchedReceipt) gaps.push(`receipt_run_mismatch:${mismatchedReceipt.receiptId}`);
  manifest.toolReceipts.forEach((receipt) => {
    if (!context.verifiedReceiptIds?.has(receipt.receiptId)) {
      gaps.push(`unverified_tool_receipt:${receipt.receiptId}`);
    }
  });
  if (manifest.gate.kind === 'bound_write') {
    const workspaceStatusReceiptId = manifest.gate.workspaceStatusReceiptId;
    const workspaceReceipt = manifest.toolReceipts.find(
      (receipt) =>
        receipt.receiptId === workspaceStatusReceiptId &&
        receipt.toolName === 'project_workspace' &&
        receipt.status === 'succeeded'
    );
    if (!workspaceReceipt) gaps.push('workspace_status_receipt_unresolved');
    if (context.projectRoot && manifest.gate.workspace !== context.projectRoot) gaps.push('workspace_root_mismatch');
  } else if (manifest.status === 'completed') {
    gaps.push('unbound_run_not_reproducible');
  }
  if (context.projectRoot && manifest.projectGit?.root !== context.projectRoot) gaps.push('project_git_root_mismatch');
  if (context.projectGitHead && manifest.projectGit?.head !== context.projectGitHead)
    gaps.push('project_git_head_mismatch');
  if (context.artifactGitCommit && manifest.artifactGit?.evidenceSnapshotCommit !== context.artifactGitCommit) {
    gaps.push('artifact_git_commit_mismatch');
  }

  const activeConditions = new Set<FinanceToolRequirementCondition>(['always']);
  context.activeConditions?.forEach((condition) => activeConditions.add(condition));
  if (manifest.status === 'completed' || manifest.report.sectionIds.length > 0 || manifest.report.cardIds.length > 0) {
    activeConditions.add('when_terminal_report');
  }
  const requiredToolNames = getRequiredFinanceContractTools(contract, activeConditions);
  const failedReceipts = manifest.toolReceipts.filter(
    (receipt) =>
      (receipt.status === 'failed' || receipt.status === 'skipped') &&
      context.verifiedReceiptIds?.has(receipt.receiptId)
  );
  const failedToolNames = new Set(failedReceipts.map((receipt) => receipt.toolName));
  const failedCapabilities = new Set(failedReceipts.flatMap((receipt) => receipt.capabilities));
  const receiptNames = new Set(
    manifest.toolReceipts
      .filter((receipt) => receipt.status === 'succeeded' || receipt.status === 'partial')
      .map((receipt) => receipt.toolName)
  );
  requiredToolNames.forEach((toolName) => {
    if (receiptNames.has(toolName)) return;
    gaps.push(failedToolNames.has(toolName) ? `failed_tool_receipt:${toolName}` : `missing_tool_receipt:${toolName}`);
  });
  manifest.toolReceipts.forEach((receipt) => {
    if (receipt.status === 'partial' && requiredToolNames.includes(receipt.toolName)) {
      gaps.push(`partial_tool_receipt:${receipt.toolName}`);
    }
  });
  contract.requiredCapabilities.forEach((capability) => {
    if (context.activeCapabilities && !context.activeCapabilities.has(capability)) {
      gaps.push(
        failedCapabilities.has(capability)
          ? `provider_capability_unavailable:${capability}`
          : `missing_capability:${capability}`
      );
    }
  });
  if (!contract.requiredArtifactsWhen || activeConditions.has(contract.requiredArtifactsWhen)) {
    contract.requiredArtifactKinds.forEach((kind) => {
      if (!context.artifactKinds.has(kind)) gaps.push(`missing_artifact_kind:${kind}`);
    });
  }
  if (!contract.requiredReport.when || activeConditions.has(contract.requiredReport.when)) {
    contract.requiredReport.cardKinds.forEach((kind) => {
      if (!context.cardKinds.has(kind)) gaps.push(`missing_card_kind:${kind}`);
    });
    contract.requiredReport.sectionRoles.forEach((role) => {
      if (!context.sectionRoles.has(role)) gaps.push(`missing_section_role:${role}`);
    });
    if (contract.requiredReport.requiresResultSummary && !context.hasResultSummary) gaps.push('missing_result_summary');
    if (contract.requiredReport.requiresLimitations && !context.hasLimitations) gaps.push('missing_limitations');
  }

  manifest.evidenceIds.forEach((evidenceId) => {
    if (!context.evidenceIds.has(evidenceId)) gaps.push(`unknown_evidence:${evidenceId}`);
  });
  manifest.artifactRefs.forEach((ref) => {
    const key = artifactRefKey(ref.artifactId, ref.version);
    if (!context.artifactRefs.has(key)) gaps.push(`unknown_artifact:${key}`);
  });
  manifest.report.cardIds.forEach((cardId) => {
    if (!context.cardIds.has(cardId)) gaps.push(`unknown_card:${cardId}`);
    else if (!context.referencedCardIds.has(cardId)) gaps.push(`unreferenced_report_card:${cardId}`);
  });
  manifest.report.sectionIds.forEach((sectionId) => {
    if (!context.sectionIds.has(sectionId)) gaps.push(`unknown_section:${sectionId}`);
  });

  const uniqueGaps = [...new Set(gaps)];
  if (uniqueGaps.length) {
    const hasReviewableOutput = context.hasReviewableOutput === true;
    const hasUntrustedRuntimeInput = uniqueGaps.some(
      (gap) =>
        gap === 'run_id_mismatch' ||
        gap === 'task_kind_mismatch' ||
        gap.startsWith('receipt_run_mismatch:') ||
        gap.startsWith('unverified_tool_receipt:')
    );
    const unavailableWithoutFallback =
      !hasReviewableOutput &&
      uniqueGaps.some(
        (gap) =>
          gap.startsWith('missing_capability:') ||
          gap.startsWith('provider_capability_unavailable:') ||
          gap.startsWith('missing_tool_receipt:') ||
          gap.startsWith('failed_tool_receipt:')
      );
    const status =
      unsupportedPartialReasons.length > 0 ||
      hasUntrustedRuntimeInput ||
      unavailableWithoutFallback ||
      (manifest.status === 'blocked' && !hasReviewableOutput)
        ? 'blocked'
        : 'partial';
    return { ok: false, status, gaps: uniqueGaps, manifest };
  }
  if (manifest.status !== 'completed') {
    return { ok: false, status: manifest.status, gaps: manifest.gaps, manifest };
  }
  return { ok: true, manifest };
}
