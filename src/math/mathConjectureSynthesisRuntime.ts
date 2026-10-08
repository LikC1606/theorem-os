import fs from 'node:fs';
import path from 'node:path';
import { Worker } from 'node:worker_threads';
import { parseMathSynthesisInput, type MathSynthesisInput, type MathSynthesisResult } from "./mathConjectureSynthesis";
import { MathArtifactStore, type MathArtifactAccess } from "./mathArtifactStore";
import { readMathRunBinding, resolveMathRunProjectPaths } from "./mathRunBinding";
import { verifyMathRunInputsEnvironment, verifyMathRunInputs, MATH_RUN_INPUTS_ENV } from "./mathRunInputs";
import { normalizeRuntimeMathAssignment } from "./mathAssignmentJournal";
import { projectRuntimeMathAssignmentToExecutionView } from "./mathAssignmentExecutionAdapter";
import { listProjectGitResearchTeamAssignments } from "../project-git/index";
import { canonicalMathJson, mathDigest } from "./mathRuntimeIo";
import { readMathLiteFeedbackArtifact, recordMathLiteFeedbackUse } from "./mathLiteFeedback";
import { parseMathArtifactReference } from "./mathPublicWire";
import type { ResearchTeamToolCapability } from "../team/toolCapability";
import { printMathExpressionLean, printMathDomainLean } from "./mathExactAlgebra";
import { verifyMathProofBlocks } from "./mathProofBlocks";
import { inspectLeanDeclarations } from "./verifier";

export function buildMathSynthesisLeanDrafts(input: MathSynthesisInput, result: MathSynthesisResult) {
  if (!result.candidates.length) return [];
  const type = input.scalar === 'real' ? 'ℝ' : 'ℚ';
  const binders = input.variables.map((name) => `«${name}»`).join(' ');
  const originalArguments = input.variables.map((name) => `«${name}»`).join(' ');
  const changedArguments = input.variables
    .map(
      (name) => `(${printMathExpressionLean((input.shift ?? input.transition)![name], input.variables, input.scalar)})`
    )
    .join(' ');
  const conditions = [...new Set([...(input.domain ?? []), ...result.domainObligations])].map((condition) =>
    printMathDomainLean(condition, input.variables, input.scalar)
  );
  const hypotheses = conditions.map((condition, index) => `(h${index} : ${condition})`).join(' ');
  return result.candidates.map((candidate, index) => {
    const name = `discovered_object_${index}`;
    const left = `${name} ${changedArguments} - ${name} ${originalArguments}`;
    const right = printMathExpressionLean(input.rhs ?? '0', input.variables, input.scalar);
    return {
      definition: `${input.scalar === 'real' ? 'noncomputable ' : ''}def ${name} (${binders} : ${type}) : ${type} := ${printMathExpressionLean(candidate.expression, input.variables, input.scalar)}`,
      relation: `theorem ${name}_relation (${binders} : ${type}) ${hypotheses} : ${left} = ${right}`,
      conditions,
      boundary:
        input.kind === 'finite_difference'
          ? `Establish the required starting value and telescope this exact difference on the original index domain.`
          : 'Prove domain preservation along the original recurrence, then prove the exact connection from this invariant to the original target.',
      authority: 'unproved_draft' as const,
    };
  });
}

/** Only the host chooses this packaged executable. No request supplies a path or code. */
export async function runMathSynthesisWorker(
  input: MathSynthesisInput,
  options: { signal: AbortSignal; deadlineAt: number; workerPath?: string }
): Promise<MathSynthesisResult> {
  options.signal.throwIfAborted();
  if (Date.now() >= options.deadlineAt) throw new Error('math_synthesis_deadline');
  const workerPath = options.workerPath ?? path.join(__dirname, 'math-conjecture-worker.js');
  if (!fs.statSync(workerPath).isFile()) throw new Error('math_synthesis_worker_unavailable');
  return await new Promise((resolve, reject) => {
    const worker = new Worker(workerPath, {
      workerData: { input, deadlineAt: options.deadlineAt },
      env: {},
      resourceLimits: { maxOldGenerationSizeMb: 128, maxYoungGenerationSizeMb: 16, stackSizeMb: 4 },
    });
    let settled = false;
    const finish = (error?: Error, result?: MathSynthesisResult) => {
      if (settled) return;
      settled = true;
      clearTimeout(timer);
      options.signal.removeEventListener('abort', abort);
      void worker.terminate().then(() => (error ? reject(error) : resolve(result!)), reject);
    };
    const abort = () => finish(new Error('math_synthesis_cancelled'));
    const timer = setTimeout(
      () => finish(new Error('math_synthesis_deadline')),
      Math.max(1, options.deadlineAt - Date.now())
    );
    options.signal.addEventListener('abort', abort, { once: true });
    if (options.signal.aborted) abort();
    worker.once('message', (message) => {
      if (message?.error) finish(new Error(String(message.error)));
      else if (message?.result) finish(undefined, message.result);
      else finish(new Error('math_synthesis_worker_protocol'));
    });
    worker.once('error', (error) => finish(error));
    worker.once('exit', () => {
      if (!settled) finish(new Error('math_synthesis_worker_exited'));
    });
  });
}

/** A computation record is ordinary evidence, never a proof or an adoption receipt. */
export async function executeMathSynthesis(input: {
  capability: ResearchTeamToolCapability;
  projectRoot: string;
  assignmentId: string;
  synthesis: unknown;
  signal: AbortSignal;
  deadlineAt: number;
}) {
  const { capability, signal } = input;
  signal.throwIfAborted();
  if (capability.profileId !== 'mathematics-research-team' || !['lead', 'worker'].includes(capability.roleKind))
    throw new Error('math_synthesis_role_unauthorized');
  if (fs.realpathSync(capability.projectRoot) !== fs.realpathSync(input.projectRoot))
    throw new Error('math_synthesis_project_identity');
  verifyMathRunInputsEnvironment(process.env);
  const binding = readMathRunBinding(verifyMathRunInputs(JSON.parse(process.env[MATH_RUN_INPUTS_ENV]!)));
  resolveMathRunProjectPaths(binding, input.projectRoot);
  const assignments = () =>
    listProjectGitResearchTeamAssignments({ workspace: input.projectRoot, teamId: capability.teamId, strict: true });
  const receipt = assignments().find((entry) => entry.assignmentId === input.assignmentId);
  if (
    !receipt ||
    receipt.state !== 'accepted' ||
    receipt.delivery ||
    receipt.integration ||
    receipt.budgetCancellation ||
    receipt.supersessionPending ||
    (capability.roleKind === 'worker' && receipt.slotId !== capability.slotId)
  )
    throw new Error('math_synthesis_assignment_unavailable');
  projectRuntimeMathAssignmentToExecutionView(receipt.assignment, {
    expectedRunId: binding.runId,
    expectedBindingDigest: mathDigest(canonicalMathJson(binding)),
    expectedTargetSlotId: receipt.slotId,
    ...(receipt.preparedGit?.baseCommit ? { expectedBaseCommit: receipt.preparedGit.baseCommit } : {}),
  });
  const assignment = normalizeRuntimeMathAssignment(receipt.assignment);
  const context = {
    runId: binding.runId,
    bindingDigest: mathDigest(canonicalMathJson(binding)),
    scopeId: assignment.scopeId,
  };
  const parsed = parseMathSynthesisInput(input.synthesis);
  const store = new MathArtifactStore({
    runRoot: path.dirname(binding.artifactStoreRoot),
    runId: binding.runId,
    flockExecutable: '/usr/bin/flock',
  });
  await store.initialize();
  const baseAccess: MathArtifactAccess =
    capability.roleKind === 'lead'
      ? { role: 'lead' }
      : { role: 'worker', assignmentId: receipt.assignmentId, grants: new Set(assignment.artifactGrants) };
  const read = async (ref: string) => {
    const reference = parseMathArtifactReference(ref);
    if (reference?.scheme !== 'math-artifact' || reference.runId !== binding.runId)
      throw new Error('math_synthesis_evidence_identity');
    let access = baseAccess;
    let feedbackLinked = false;
    try {
      await store.read({ ref, offsetBytes: 0, maxBytes: 1 }, access);
    } catch (error) {
      if (
        capability.roleKind !== 'worker' ||
        !(error instanceof Error) ||
        error.message !== 'math_artifact_unauthorized'
      )
        throw error;
      access = await readMathLiteFeedbackArtifact(capability, signal, ref, access);
      feedbackLinked = true;
    }
    let text = '';
    let offsetBytes = 0;
    for (;;) {
      signal.throwIfAborted();
      if (Date.now() >= input.deadlineAt) throw new Error('math_synthesis_deadline');
      const part = await store.read({ ref, offsetBytes, maxBytes: 2048 }, access);
      text += part.text;
      if (Buffer.byteLength(text) > 2_000_000) throw new Error('math_synthesis_evidence_too_large');
      if (part.nextOffsetBytes === undefined) break;
      offsetBytes = part.nextOffsetBytes;
    }
    if (feedbackLinked)
      await recordMathLiteFeedbackUse({
        resolvedCapability: capability,
        signal,
        ref,
        sourceHash: mathDigest(text),
        status: 'read',
      });
    return text;
  };
  try {
    const samples = [...(parsed.seedSamples ?? [])];
    const evidence: {
      ref: string;
      sha256: string;
      kind: string;
      text?: string;
      declarations?: { name: string; status: string; declarationHash?: string; reason?: string }[];
    }[] = [];
    for (const ref of new Set([
      ...(parsed.evidenceRefs ?? []),
      ...(parsed.previousResultRef ? [parsed.previousResultRef] : []),
    ])) {
      const text = await read(ref);
      let record: Record<string, unknown> | undefined;
      try {
        record = JSON.parse(text);
      } catch {
        /* Lean source is source evidence, not algebraic proof authority. */
      }
      if (record?.schema === 'deepscientist.math.synthesis.v1') {
        const reference = parseMathArtifactReference(ref);
        if (reference?.scheme !== 'math-artifact' || reference.artifactId !== `synthesis-${mathDigest(text)}`)
          throw new Error('math_synthesis_previous_not_host_produced');
        if (canonicalMathJson(record.context) !== canonicalMathJson(context))
          throw new Error('math_synthesis_previous_context');
        const previous = parseMathSynthesisInput(record.input);
        if (
          previous.scalar !== parsed.scalar ||
          canonicalMathJson(previous.variables.toSorted()) !== canonicalMathJson(parsed.variables.toSorted())
        )
          throw new Error('math_synthesis_previous_variables_or_scalar');
        // Re-evaluate points by variable name under the CURRENT transition, basis and domain.
        // Serialized coefficient rows or a claimed verified flag are never trusted.
        const result = record.result as MathSynthesisResult;
        for (const row of result.constraints ?? []) samples.push(row.sample);
        samples.push(...(previous.seedSamples ?? []));
        evidence.push({ ref, sha256: mathDigest(text), kind: 'revalidated_sample_points' });
      } else {
        if (ref === parsed.previousResultRef) throw new Error('math_synthesis_previous_record_required');
        const declarations = inspectLeanDeclarations(text).filter((declaration) => declaration.kind === 'theorem');
        if (declarations.length > 32) throw new Error('math_synthesis_evidence_declaration_limit');
        const checked: { name: string; status: string; declarationHash?: string; reason?: string }[] = [];
        if (declarations.length) {
          const paths = resolveMathRunProjectPaths(binding, input.projectRoot, receipt.preparedGit?.worktreePath);
          // This digest scopes a fresh kernel check; it is never a cache authority.
          const environmentId = mathDigest(
            canonicalMathJson(
              ['lean-toolchain', 'lakefile.toml', 'lakefile.lean', 'lake-manifest.json'].map((file) => {
                const absolute = path.join(paths.solverProjectRoot, file);
                return [file, fs.existsSync(absolute) ? mathDigest(fs.readFileSync(absolute, 'utf8')) : null];
              })
            )
          );
          const verifiedBlocks = await verifyMathProofBlocks({
            projectRoot: paths.solverProjectRoot,
            proofPath: path.posix.join(assignment.sourceRootRelative, 'SynthesisEvidence.lean'),
            source: text,
            theoremNames: declarations.map((declaration) => declaration.name),
            scope: { runId: binding.runId, assignmentId: receipt.assignmentId, artifactRef: ref, environmentId },
            deadlineAt: input.deadlineAt,
            signal,
          });
          for (const declaration of declarations) {
            const verified = verifiedBlocks.get(declaration.name)!;
            checked.push({
              name: declaration.name,
              status: verified.block ? 'kernel_verified' : 'unverified',
              declarationHash: verified.block?.declarationHash,
              reason: verified.reason,
            });
          }
        }
        evidence.push({
          ref,
          sha256: mathDigest(text),
          kind:
            checked.length && checked.every((item) => item.status === 'kernel_verified')
              ? 'freshly_checked_source'
              : 'authorized_source_not_automatically_a_fact',
          text,
          ...(checked.length ? { declarations: checked } : {}),
        });
      }
    }
    const computationInput = parseMathSynthesisInput({
      ...parsed,
      ...(parsed.seedSamples !== undefined || samples.length
        ? { seedSamples: [...new Map(samples.map((sample) => [canonicalMathJson(sample), sample])).values()] }
        : {}),
    });
    const result = await runMathSynthesisWorker(computationInput, { signal, deadlineAt: input.deadlineAt });
    signal.throwIfAborted();
    const current = assignments().find((entry) => entry.assignmentId === receipt.assignmentId);
    if (canonicalMathJson(current) !== canonicalMathJson(receipt)) throw new Error('math_synthesis_assignment_changed');
    const leanDrafts = buildMathSynthesisLeanDrafts(computationInput, result);
    const record = {
      schema: 'deepscientist.math.synthesis.v1',
      context,
      assignmentId: receipt.assignmentId,
      input: computationInput,
      evidence,
      result,
      leanDrafts,
      solverReady: false,
      originalTargetAccepted: false,
    };
    const text = canonicalMathJson(record);
    const artifactId = `synthesis-${mathDigest(text)}`;
    await store.publishText({
      artifactId,
      assignmentId: receipt.assignmentId,
      kind: 'evidence',
      sensitivity: 'solver-visible',
      mediaType: 'application/json',
      text,
    });
    return {
      result,
      resultRef: `math-artifact://${binding.runId}/${artifactId}`,
      evidence,
      computationInput,
      leanDrafts,
      solverReady: false,
      originalTargetAccepted: false,
    };
  } finally {
    await store.closeReaders();
  }
}
