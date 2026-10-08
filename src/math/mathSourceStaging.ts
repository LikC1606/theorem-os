import fs from 'node:fs';
import path from 'node:path';
import type { MathRunBinding, MathSourceArtifact } from "../common/types/team/mathRuntimeContracts";
import type { ProjectGitResearchTeamAssignmentReceipt } from "../project-git/ProjectGitService";
import { selectMathV2IntegrationBatch } from "./mathIntegrationSelector";
import {
  persistMathV2SourcePlan,
  planMathV2SourceIntegration,
  readMathV2SourcePlan,
} from "./mathIntegrationSourcePlan";
import {
  assertMathSourceArtifactBatch,
  applyMathSourceArtifactToText,
  mathSourceArtifactOutputSha256,
  normalizeMathSourceArtifact,
  writeMathSourceArtifactToDraft,
} from "./mathSourceArtifact";
import {
  assertMathCanonicalPath,
  isMathPathWithin,
  mathAssignmentSourceRoot,
  normalizeMathRunBinding,
} from "./mathRunBinding";
import {
  canonicalMathJson,
  mathDigest,
  readMathJson,
  withMathRuntimeLease,
  writeMathJsonDurable,
} from "./mathRuntimeIo";
import { selectMathV2IntegrationDelivery } from "./mathIntegrationSelector";

export type MathSourceStageRecovery = Readonly<{
  deliveryId: string;
  assignmentId: string;
  planId: string;
  state: 'prepared' | 'staged';
  pathRelative: string;
  contentSha256: string;
  resultContentSha256?: string;
  verificationTargetId: string;
  theoremName: string;
  statementHash: string;
  leanStatementHash?: string;
  expectedSourceDeclarationHash: string;
  claim?: 'statement' | 'negation';
  sourceRoot: string;
  draftRoot: string;
  ready: boolean;
  reason?: 'missing_draft' | 'draft_hash_mismatch' | 'plan_incomplete';
}>;

export type MathSourceStageResult = Readonly<{
  deliveryId: string;
  assignmentId: string;
  planId: string;
  pathRelative: string;
  contentSha256: string;
}>;

type SourceStageRecord = Readonly<{
  schema: 'deepscientist.math.source-stage.v1';
  deliveryId: string;
  planId: string;
  payloadHash: string;
  state: 'prepared' | 'staged';
  mode?: 'file' | 'patch';
  pathRelative?: string;
  preimageSha256?: string;
  outputSha256?: string;
}>;

function readSourceStageRecord(file: string, expectedDeliveryId: string): SourceStageRecord {
  const value = readMathJson(file);
  if (!value || typeof value !== 'object' || Array.isArray(value)) throw new Error('math_source_stage_conflict');
  const record = value as Record<string, unknown>;
  if (
    record.schema !== 'deepscientist.math.source-stage.v1' ||
    record.deliveryId !== expectedDeliveryId ||
    typeof record.planId !== 'string' ||
    !/^[a-f0-9]{64}$/u.test(record.planId) ||
    typeof record.payloadHash !== 'string' ||
    !/^[a-f0-9]{64}$/u.test(record.payloadHash) ||
    (record.state !== 'prepared' && record.state !== 'staged')
  )
    throw new Error('math_source_stage_conflict');
  return Object.freeze({
    schema: record.schema,
    deliveryId: record.deliveryId,
    planId: record.planId,
    payloadHash: record.payloadHash,
    state: record.state,
    ...(record.mode === 'file' || record.mode === 'patch' ? { mode: record.mode } : {}),
    ...(typeof record.pathRelative === 'string' ? { pathRelative: record.pathRelative } : {}),
    ...(typeof record.preimageSha256 === 'string' && /^[a-f0-9]{64}$/u.test(record.preimageSha256)
      ? { preimageSha256: record.preimageSha256 }
      : {}),
    ...(typeof record.outputSha256 === 'string' && /^[a-f0-9]{64}$/u.test(record.outputSha256)
      ? { outputSha256: record.outputSha256 }
      : {}),
  }) as SourceStageRecord;
}

/**
 * Discover source stages left by an earlier process and make complete
 * prepared writes resumable. The returned entries contain only hashes and
 * frozen verification metadata; source bytes remain in the runtime-owned
 * draft and are checked again by the promotion helper.
 */
export async function recoverMathV2SourceStages(
  receipts: readonly ProjectGitResearchTeamAssignmentReceipt[],
  options: Readonly<{
    teamId: string;
    readBinding: () => MathRunBinding;
    readAssignments: () => readonly ProjectGitResearchTeamAssignmentReceipt[];
    flockExecutable: string;
    signal?: AbortSignal;
    allowHostFrozenDeliveryArtifacts?: boolean;
  }>
): Promise<readonly MathSourceStageRecovery[]> {
  const binding = normalizeMathRunBinding(options.readBinding());
  const bindingDigest = mathDigest(canonicalMathJson(binding));
  const runRoot = path.dirname(binding.artifactStoreRoot);
  if (
    path.basename(runRoot) !== binding.runId ||
    path.basename(path.dirname(runRoot)) !== 'runs' ||
    path.basename(binding.artifactStoreRoot) !== 'artifacts'
  )
    throw new Error('math_source_stage_binding');
  assertMathCanonicalPath(runRoot);
  return withMathRuntimeLease(
    { lockPath: path.join(runRoot, 'math-run.lock'), flockExecutable: options.flockExecutable, signal: options.signal },
    async (lease) => {
      if (mathDigest(canonicalMathJson(normalizeMathRunBinding(options.readBinding()))) !== bindingDigest)
        throw new Error('math_source_stage_binding');
      const current = options.readAssignments();
      const stageDirectory = path.join(runRoot, 'integrations', 'source-stages');
      if (!fs.existsSync(stageDirectory)) return Object.freeze([]);
      assertMathCanonicalPath(stageDirectory);
      if (!fs.statSync(stageDirectory).isDirectory()) throw new Error('math_source_stage_conflict');
      const currentByAssignment = new Map(current.map((receipt) => [receipt.assignmentId, receipt]));
      const recoveries: MathSourceStageRecovery[] = [];
      for (const receipt of receipts) {
        if (receipt.teamId !== options.teamId || !receipt.delivery?.deliveryId) continue;
        const durable = currentByAssignment.get(receipt.assignmentId);
        if (!durable || canonicalMathJson(durable) !== canonicalMathJson(receipt))
          throw new Error('math_source_stage_receipt_changed');
        const deliveryId = receipt.delivery.deliveryId;
        const file = path.join(stageDirectory, `${mathDigest(deliveryId)}.json`);
        assertMathCanonicalPath(file);
        if (!fs.existsSync(file)) continue;
        const record = readSourceStageRecord(file, deliveryId);
        const selected = selectMathV2IntegrationDelivery(receipt, deliveryId, {
          expectedRunId: binding.runId,
          expectedBindingDigest: bindingDigest,
        });
        const plan = readMathV2SourcePlan(runRoot, record.planId);
        const expectedPlan = planMathV2SourceIntegration(selected, binding.projectRoot, {
          allowHostFrozenDeliveryArtifacts: options.allowHostFrozenDeliveryArtifacts,
        });
        const { schema: _schema, planId: _planId, sourceArtifact: _storedArtifact, ...storedWithoutArtifact } = plan;
        if (canonicalMathJson(storedWithoutArtifact) !== canonicalMathJson(expectedPlan))
          throw new Error('math_source_stage_conflict');
        const { schema: _planSchema, planId: _storedPlanId, ...planPayload } = plan;
        const expectedPayloadHash = mathDigest(
          canonicalMathJson({ plan: planPayload, deliveryPayloadHash: selected.delivery.payloadHash, bindingDigest })
        );
        if (record.payloadHash !== expectedPayloadHash) throw new Error('math_source_stage_conflict');
        const sourceArtifact = plan.sourceArtifact;
        if (!sourceArtifact) {
          recoveries.push(
            Object.freeze({
              deliveryId,
              assignmentId: receipt.assignmentId,
              planId: record.planId,
              state: record.state,
              pathRelative: '',
              contentSha256: ''.padStart(64, '0'),
              verificationTargetId: '',
              theoremName: '',
              statementHash: ''.padStart(64, '0'),
              expectedSourceDeclarationHash: ''.padStart(64, '0'),
              sourceRoot: plan.sourceRoot,
              draftRoot: plan.draftRoot,
              ready: false,
              reason: 'plan_incomplete',
            })
          );
          continue;
        }
        const target = path.resolve(plan.draftRoot, sourceArtifact.pathRelative);
        if (target === path.resolve(plan.draftRoot) || !isMathPathWithin(path.resolve(plan.draftRoot), target))
          throw new Error('math_source_stage_conflict');
        assertMathCanonicalPath(target);
        const expectedContentSha256 = sourceArtifact.resultContentSha256 ?? sourceArtifact.contentSha256;
        let ready = false;
        let reason: MathSourceStageRecovery['reason'];
        if (!fs.existsSync(target)) reason = 'missing_draft';
        else if (!fs.lstatSync(target).isFile()) reason = 'draft_hash_mismatch';
        else {
          const actual = mathDigest(fs.readFileSync(target));
          if (actual !== expectedContentSha256) reason = 'draft_hash_mismatch';
          else ready = true;
        }
        const normalized: MathSourceStageRecovery = Object.freeze({
          deliveryId,
          assignmentId: receipt.assignmentId,
          planId: record.planId,
          state: ready ? 'staged' : record.state,
          pathRelative: sourceArtifact.pathRelative,
          contentSha256: sourceArtifact.contentSha256,
          ...(sourceArtifact.resultContentSha256 ? { resultContentSha256: sourceArtifact.resultContentSha256 } : {}),
          verificationTargetId: sourceArtifact.verificationTargetId,
          theoremName: sourceArtifact.theoremName,
          statementHash: sourceArtifact.statementHash,
          ...(sourceArtifact.leanStatementHash ? { leanStatementHash: sourceArtifact.leanStatementHash } : {}),
          expectedSourceDeclarationHash: sourceArtifact.expectedSourceDeclarationHash,
          ...(sourceArtifact.claim ? { claim: sourceArtifact.claim } : {}),
          sourceRoot: plan.sourceRoot,
          draftRoot: plan.draftRoot,
          ready,
          ...(reason ? { reason } : {}),
        });
        if (ready && record.state === 'prepared') {
          lease.assertHeld();
          writeMathJsonDurable(file, { ...record, state: 'staged' });
        }
        recoveries.push(normalized);
      }
      lease.assertHeld();
      return Object.freeze(recoveries);
    }
  );
}

/** Stage candidates only. Assignment completion and canonical Git changes belong to the integration writer. */
export async function stageMathV2Sources(
  receipts: readonly ProjectGitResearchTeamAssignmentReceipt[],
  artifacts: readonly MathSourceArtifact[],
  options: Readonly<{
    teamId: string;
    readBinding: () => MathRunBinding;
    readAssignments: () => readonly ProjectGitResearchTeamAssignmentReceipt[];
    flockExecutable: string;
    signal?: AbortSignal;
    allowHostFrozenDeliveryArtifacts?: boolean;
  }>
): Promise<readonly MathSourceStageResult[]> {
  const binding = normalizeMathRunBinding(options.readBinding());
  const bindingDigest = mathDigest(canonicalMathJson(binding));
  const runRoot = path.dirname(binding.artifactStoreRoot);
  if (
    path.basename(runRoot) !== binding.runId ||
    path.basename(path.dirname(runRoot)) !== 'runs' ||
    path.basename(binding.artifactStoreRoot) !== 'artifacts'
  )
    throw new Error('math_source_stage_binding');
  assertMathCanonicalPath(runRoot);
  return withMathRuntimeLease(
    { lockPath: path.join(runRoot, 'math-run.lock'), flockExecutable: options.flockExecutable, signal: options.signal },
    async (lease) => {
      if (mathDigest(canonicalMathJson(normalizeMathRunBinding(options.readBinding()))) !== bindingDigest)
        throw new Error('math_source_stage_binding');
      const current = options.readAssignments();
      const fresh = receipts.map((receipt) => {
        const matches = current.filter((candidate) => candidate.assignmentId === receipt.assignmentId);
        if (matches.length !== 1 || canonicalMathJson(matches[0]) !== canonicalMathJson(receipt))
          throw new Error('math_source_stage_receipt_changed');
        return matches[0]!;
      });
      const selections = selectMathV2IntegrationBatch(
        fresh,
        fresh.map((receipt) => receipt.delivery?.deliveryId ?? ''),
        {
          expectedRunId: binding.runId,
          expectedBindingDigest: bindingDigest,
        }
      );
      assertMathSourceArtifactBatch(
        artifacts,
        selections.map((selection) => selection.delivery.deliveryId)
      );
      if (!artifacts) throw new Error('math_source_stage_artifacts_missing');
      const artifactsByDelivery = new Map<string, MathSourceArtifact[]>();
      for (const rawArtifact of artifacts) {
        const group = artifactsByDelivery.get(rawArtifact.deliveryId) ?? [];
        group.push(rawArtifact);
        artifactsByDelivery.set(rawArtifact.deliveryId, group);
      }
      const directory = path.join(runRoot, 'integrations', 'source-stages');
      assertMathCanonicalPath(directory);
      // Validate the complete batch, including replay conflicts, before creating any files.
      const entries = selections.map((selection) => {
        const { assignment, receipt } = selection;
        if (receipt.teamId !== options.teamId || receipt.state !== 'accepted')
          throw new Error('math_source_stage_assignment');
        const sourceRoot = mathAssignmentSourceRoot(binding, assignment.assignmentId);
        const draftRoot = path.join(runRoot, 'drafts', `A_${mathDigest(assignment.assignmentId)}`);
        if (
          path.resolve(binding.projectRoot, assignment.sourceRootRelative) !== sourceRoot ||
          assignment.draftRoot !== draftRoot
        )
          throw new Error('math_source_stage_paths');
        const rawArtifacts = artifactsByDelivery.get(selection.delivery.deliveryId) ?? [];
        if (!rawArtifacts.length) throw new Error('math_source_stage_artifacts_missing');
        const normalizedArtifacts = rawArtifacts.map((rawArtifact) =>
          normalizeMathSourceArtifact(rawArtifact, {
            assignmentId: assignment.assignmentId,
            deliveryId: selection.delivery.deliveryId,
            baseCommit: assignment.baseCommit,
            sourceRoot,
            verificationTargets: assignment.request.verificationTargets,
          })
        );
        const artifact = normalizedArtifacts[0]!;
        const artifactIdentity = (candidate: MathSourceArtifact): string =>
          `${candidate.pathRelative}\u0000${candidate.mode}\u0000${mathSourceArtifactOutputSha256(candidate)}`;
        if (normalizedArtifacts.some((candidate) => artifactIdentity(candidate) !== artifactIdentity(artifact)))
          throw new Error('math_source_stage_target_conflict');
        const expectedTargets = (assignment.request.verificationTargets ?? []).filter(
          (target) => target.pathRelative === artifact.pathRelative
        );
        if (
          expectedTargets.length > 1 &&
          !expectedTargets.every((target) => normalizedArtifacts.some((candidate) => candidate.verificationTargetId === target.targetId))
        )
          throw new Error('math_source_stage_target_missing');
        const target = path.join(draftRoot, artifact.pathRelative);
        let parent = path.dirname(target);
        while (!fs.existsSync(parent)) parent = path.dirname(parent);
        if (!fs.statSync(parent).isDirectory()) throw new Error('math_source_stage_target');
        assertMathCanonicalPath(target);
        if (artifact.mode === 'patch' && (!fs.existsSync(target) || !fs.lstatSync(target).isFile()))
          throw new Error('math_source_artifact_patch_target');
        if (fs.existsSync(target) && !fs.statSync(target).isFile()) throw new Error('math_source_stage_target');
        const plan = {
          ...planMathV2SourceIntegration(selection, binding.projectRoot, {
            allowHostFrozenDeliveryArtifacts: options.allowHostFrozenDeliveryArtifacts,
          }),
          sourceArtifact: {
            pathRelative: artifact.pathRelative,
            contentSha256: artifact.contentSha256,
            ...(artifact.resultContentSha256 ? { resultContentSha256: artifact.resultContentSha256 } : {}),
            verificationTargetId: artifact.verificationTargetId,
            theoremName: artifact.theoremName,
            statementHash: artifact.statementHash,
            ...(artifact.leanStatementHash ? { leanStatementHash: artifact.leanStatementHash } : {}),
            expectedSourceDeclarationHash: artifact.expectedSourceDeclarationHash,
            ...(artifact.claim ? { claim: artifact.claim } : {}),
          },
        };
        const file = path.join(directory, `${mathDigest(selection.delivery.deliveryId)}.json`);
        assertMathCanonicalPath(file);
        const payloadHash = mathDigest(
          canonicalMathJson({ plan, deliveryPayloadHash: selection.delivery.payloadHash, bindingDigest })
        );
        let old: SourceStageRecord | undefined;
        try {
          old = readSourceStageRecord(file, selection.delivery.deliveryId);
        } catch (error) {
          if ((error as NodeJS.ErrnoException).code !== 'ENOENT') throw error;
        }
        if (
          old &&
          (old.schema !== 'deepscientist.math.source-stage.v1' ||
            old.payloadHash !== payloadHash ||
            old.deliveryId !== selection.delivery.deliveryId ||
            (old.state !== 'prepared' && old.state !== 'staged'))
        )
          throw new Error('math_source_stage_conflict');
        if (old) {
          if (
            (old.mode && old.mode !== artifact.mode) ||
            (old.pathRelative && old.pathRelative !== artifact.pathRelative) ||
            (old.outputSha256 && old.outputSha256 !== mathSourceArtifactOutputSha256(artifact))
          )
            throw new Error('math_source_stage_conflict');
          const storedPlan = readMathV2SourcePlan(runRoot, String(old.planId));
          const { schema: _schema, planId: _planId, ...stored } = storedPlan;
          if (canonicalMathJson(stored) !== canonicalMathJson(plan)) throw new Error('math_source_stage_conflict');
        }
        const outputSha256 = mathSourceArtifactOutputSha256(artifact);
        const currentSha256 =
          fs.existsSync(target) && fs.lstatSync(target).isFile() ? mathDigest(fs.readFileSync(target)) : undefined;
        let preimageSha256 = currentSha256;
        let skipWrite = false;
        let markStaged = false;
        if (old) {
          const oldOutputSha256 = typeof old.outputSha256 === 'string' ? old.outputSha256 : outputSha256;
          const oldPreimageSha256 = typeof old.preimageSha256 === 'string' ? old.preimageSha256 : undefined;
          const oldMode = old.mode === 'patch' || old.mode === 'file' ? old.mode : artifact.mode;
          if (currentSha256 === oldOutputSha256) {
            // A visible result proves the write happened even if stage confirmation
            // was interrupted. Complete the journal without replaying a patch.
            skipWrite = true;
            markStaged = old.state === 'prepared';
          } else if (old.state === 'staged' && oldMode === 'file' && currentSha256 === undefined) {
            // A complete file payload can restore a missing target after a
            // crash; an existing but changed staged target remains a conflict.
            preimageSha256 = currentSha256;
          } else if (old.state === 'staged') {
            // Never overwrite a staged result that was changed externally.
            throw new Error('math_source_stage_conflict');
          } else if (oldMode === 'patch') {
            // A prepared patch may be replayed only from its recorded preimage.
            if (!oldPreimageSha256 || currentSha256 !== oldPreimageSha256)
              throw new Error('math_source_stage_conflict');
            preimageSha256 = oldPreimageSha256;
          } else {
            // File mode remains compatible with the historical retry behavior.
            preimageSha256 = currentSha256;
          }
        } else if (artifact.mode === 'patch') {
          if (!currentSha256) throw new Error('math_source_artifact_patch_target');
          // Parse and verify exactly once during preflight; the write below repeats
          // the same operation under the run lease while recording this preimage.
          applyMathSourceArtifactToText(artifact, fs.readFileSync(target, 'utf8'));
        }
        return { artifact, plan, file, payloadHash, old, outputSha256, preimageSha256, skipWrite, markStaged };
      });
      lease.assertHeld();
      fs.mkdirSync(directory, { recursive: true, mode: 0o700 });
      const prepared = entries.map((entry) => {
        const plan = persistMathV2SourcePlan(entry.plan, runRoot);
        const record = {
          schema: 'deepscientist.math.source-stage.v1',
          deliveryId: plan.deliveryId,
          planId: plan.planId,
          payloadHash: entry.payloadHash,
          mode: entry.artifact.mode,
          pathRelative: entry.artifact.pathRelative,
          ...(entry.preimageSha256 ? { preimageSha256: entry.preimageSha256 } : {}),
          outputSha256: entry.outputSha256,
        };
        if (!entry.old) writeMathJsonDurable(entry.file, { ...record, state: 'prepared' });
        return { artifact: entry.artifact, file: entry.file, record, plan };
      });
      const results = prepared.map((entry) => {
        lease.assertHeld();
        const sourceEntry = entries.find((candidate) => candidate.file === entry.file)!;
        if (!sourceEntry.skipWrite) writeMathSourceArtifactToDraft(entry.artifact, entry.plan.draftRoot);
        if (!sourceEntry.skipWrite || sourceEntry.markStaged)
          writeMathJsonDurable(entry.file, { ...entry.record, state: 'staged' });
        return Object.freeze({
          deliveryId: entry.plan.deliveryId,
          assignmentId: entry.plan.assignmentId,
          planId: entry.plan.planId,
          pathRelative: entry.artifact.pathRelative,
          contentSha256: mathSourceArtifactOutputSha256(entry.artifact),
        });
      });
      return Object.freeze(results);
    }
  );
}
