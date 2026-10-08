import path from 'node:path';
import fs from 'node:fs';
import { z } from 'zod';
import type { MathV2IntegrationSelection } from "./mathIntegrationSelector";
import { assertMathCanonicalPath, isMathPathWithin } from "./mathRunBinding";
import { canonicalMathJson, mathDigest, readMathJson, writeMathJsonDurable } from "./mathRuntimeIo";
import { parseMathArtifactReference } from "./mathPublicWire";

export type MathIntegrationSourcePlan = Readonly<{
  assignmentId: string;
  deliveryId: string;
  runId: string;
  baseCommit: string;
  sourceRoot: string;
  draftRoot: string;
  evidenceRefs: readonly string[];
  sourceArtifact?: Readonly<{
    pathRelative: string;
    contentSha256: string;
    resultContentSha256?: string;
    verificationTargetId: string;
    theoremName: string;
    statementHash: string;
    leanStatementHash?: string;
    expectedSourceDeclarationHash: string;
    claim?: 'statement' | 'negation';
  }>;
}>;

export type MathIntegrationPlanReceipt = Readonly<
  MathIntegrationSourcePlan & {
    schema: 'deepscientist.math.integration-source-plan.v1';
    planId: string;
  }
>;

/** Build the constrained input for the eventual runtime-owned source writer. */
export function planMathV2SourceIntegration(
  selection: MathV2IntegrationSelection,
  projectRoot: string,
  options: Readonly<{ allowHostFrozenDeliveryArtifacts?: boolean }> = {}
): MathIntegrationSourcePlan {
  assertMathCanonicalPath(projectRoot);
  const { assignmentView, assignment, delivery } = selection;
  if (!assignmentView.sourceRootRelative || !assignmentView.draftRoot)
    throw new Error('math_v2_source_plan_paths_missing');
  const sourceRoot = path.resolve(projectRoot, assignmentView.sourceRootRelative);
  assertMathCanonicalPath(sourceRoot);
  if (!isMathPathWithin(projectRoot, sourceRoot)) throw new Error('math_v2_source_plan_path_escape');
  assertMathCanonicalPath(assignmentView.draftRoot);
  const grants = new Set(assignment.artifactGrants);
  const hostFrozenArtifactIds = options.allowHostFrozenDeliveryArtifacts
    ? new Set(
        delivery.delivery.evidence.flatMap((entry) => {
          const ref = parseMathArtifactReference(entry.ref);
          return ref?.scheme === 'math-artifact' && ref.runId === assignment.runId ? [ref.artifactId] : [];
        })
      )
    : undefined;
  const evidenceRefs = delivery.delivery.evidence.map((entry) => entry.ref);
  for (const evidence of delivery.delivery.evidence) {
    const ref = parseMathArtifactReference(evidence.ref);
    if (
      !ref ||
      (ref.scheme === 'math-artifact' &&
        (ref.runId !== assignment.runId ||
          (!grants.has(ref.artifactId) && !hostFrozenArtifactIds?.has(ref.artifactId))))
    )
      throw new Error('math_v2_source_plan_artifact_denied');
  }
  return Object.freeze({
    assignmentId: assignment.assignmentId,
    deliveryId: delivery.deliveryId,
    runId: assignment.runId,
    baseCommit: assignment.baseCommit,
    sourceRoot,
    draftRoot: assignmentView.draftRoot,
    evidenceRefs: Object.freeze([...evidenceRefs]),
  });
}

/** Persist a replayable source plan before any checkout or file mutation. */
export function persistMathV2SourcePlan(plan: MathIntegrationSourcePlan, runRoot: string): MathIntegrationPlanReceipt {
  assertMathCanonicalPath(runRoot);
  const planId = mathDigest(
    canonicalMathJson({
      assignmentId: plan.assignmentId,
      deliveryId: plan.deliveryId,
      runId: plan.runId,
      baseCommit: plan.baseCommit,
      sourceRoot: plan.sourceRoot,
      draftRoot: plan.draftRoot,
      evidenceRefs: plan.evidenceRefs,
      ...(plan.sourceArtifact ? { sourceArtifact: plan.sourceArtifact } : {}),
    })
  );
  const receipt = Object.freeze({ schema: 'deepscientist.math.integration-source-plan.v1' as const, planId, ...plan });
  const directory = path.join(runRoot, 'integrations', 'plans');
  assertMathCanonicalPath(directory);
  fs.mkdirSync(directory, { recursive: true, mode: 0o700 });
  assertMathCanonicalPath(directory);
  writeMathJsonDurable(path.join(directory, `${planId}.json`), receipt);
  return receipt;
}

export function readMathV2SourcePlan(runRoot: string, planId: string): MathIntegrationPlanReceipt {
  assertMathCanonicalPath(runRoot);
  if (!/^[a-f0-9]{64}$/u.test(planId)) throw new Error('math_v2_source_plan_identity');
  const file = path.join(runRoot, 'integrations', 'plans', `${planId}.json`);
  assertMathCanonicalPath(file);
  const raw = sourcePlanSchema.parse(readMathJson(file)) as MathIntegrationPlanReceipt;
  if (raw.schema !== 'deepscientist.math.integration-source-plan.v1' || raw.planId !== planId)
    throw new Error('math_v2_source_plan_integrity');
  const { schema: _schema, planId: _id, ...payload } = raw;
  if (mathDigest(canonicalMathJson(payload)) !== planId) throw new Error('math_v2_source_plan_integrity');
  return Object.freeze({
    ...raw,
    evidenceRefs: Object.freeze(raw.evidenceRefs),
    ...(raw.sourceArtifact ? { sourceArtifact: Object.freeze(raw.sourceArtifact) } : {}),
  });
}

export function assertMathV2SourcePlanReady(plan: MathIntegrationSourcePlan): void {
  assertMathCanonicalPath(plan.sourceRoot);
  assertMathCanonicalPath(plan.draftRoot);
  const draftStat = fs.statSync(plan.draftRoot);
  if (!draftStat.isDirectory()) throw new Error('math_v2_source_plan_draft_invalid');
}

const sourcePlanSchema = z
  .object({
    schema: z.literal('deepscientist.math.integration-source-plan.v1'),
    planId: z.string().regex(/^[a-f0-9]{64}$/u),
    assignmentId: z.string().regex(/^[A-Za-z0-9_-]{1,128}$/u),
    deliveryId: z.string().regex(/^[A-Za-z0-9_:-]{1,512}$/u),
    runId: z.string().regex(/^[A-Za-z0-9_-]{1,128}$/u),
    baseCommit: z.string().regex(/^(?:[a-f0-9]{40}|[a-f0-9]{64})$/u),
    sourceRoot: z.string().refine(path.isAbsolute),
    draftRoot: z.string().refine(path.isAbsolute),
    evidenceRefs: z.array(z.string()),
    sourceArtifact: z
      .object({
        pathRelative: z.string(),
        contentSha256: z.string().regex(/^[a-f0-9]{64}$/u),
        resultContentSha256: z
          .string()
          .regex(/^[a-f0-9]{64}$/u)
          .optional(),
        verificationTargetId: z.string().regex(/^[A-Za-z0-9_-]{1,128}$/u),
        theoremName: z.string().min(1).max(512),
        statementHash: z.string().regex(/^[a-f0-9]{64}$/u),
        leanStatementHash: z
          .string()
          .regex(/^[a-f0-9]{64}$/u)
          .optional(),
        expectedSourceDeclarationHash: z.string().regex(/^[a-f0-9]{64}$/u),
        claim: z.enum(['statement', 'negation']).optional(),
      })
      .strict()
      .optional(),
  })
  .strict();
