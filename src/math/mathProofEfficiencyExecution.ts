import fs from 'node:fs';
import path from 'node:path';
import { MathArtifactStore } from "./mathArtifactStore";
import {
  readMathLiteFeedback,
  readMathLiteProofLineage,
  readLatestMathLiteProgress,
  recordMathLiteFeedbackUse,
} from "./mathLiteFeedback";
import { parseMathArtifactReference } from "./mathPublicWire";
import {
  verifyMathProofBlock,
  verifyMathProofBlocks,
  type CheckedMathProofBlock,
  type MathProofBlockResult,
} from "./mathProofBlocks";
import { inspectLeanDeclarations, inspectLeanDeclarationRegions } from "./verifier";
import { canonicalMathJson, mathDigest } from "./mathRuntimeIo";
import type { MathRunInputs } from "./mathRunInputs";
import { resolveMathRunProjectPaths, assertMathCanonicalPath } from "./mathRunBinding";
import { normalizeRuntimeMathAssignment } from "./mathAssignmentJournal";
import { MathProofWorkFrontier } from "./mathProofWorkFrontier";
import { startMathematicsLeanSession } from "./leanInteractiveSession";
import {
  mathProofImpactDeclarationHash,
  mathProofImpactSupportingDeclarations,
  recordMathProofImpact,
} from "./mathProofImpact";
import { inspectMathDiscoveryObstructions, type MathDiscoveryObstruction } from "./mathDiscoveryFrontier";

type Capability = { teamId: string; slotId: string; roleKind: string; projectRoot: string };

/** Host-only search hook. Authorization is re-derived before every kernel check.
 * Reads never call this hook: shares remain provisional until an explicit execution boundary. */
export async function collectMathCheckedProofSupport(input: {
  capability: Capability;
  environmentId: string;
  signal: AbortSignal;
  deadlineAt: number;
  runInputs?: MathRunInputs;
  env?: NodeJS.ProcessEnv;
  /** Host-bound current source; never accepted from a research evidence record. */
  proofSource?: Readonly<{ file: string; sha256: string }>;
  onDiscoveryObstructions?: (observations: readonly MathDiscoveryObstruction[]) => void;
}): Promise<readonly CheckedMathProofBlock[]> {
  input.signal.throwIfAborted();
  if (!input.environmentId) return [];
  const lineage = readMathLiteProofLineage(input.capability, input.signal, input.runInputs, true);
  const feedback = await readMathLiteFeedback({
    resolvedCapability: input.capability,
    signal: input.signal,
    runInputs: input.runInputs,
    operationContext: lineage,
    // Notifications intentionally expose only the latest share. Proof composition
    // needs the bounded, still-authorized history so a new premise does not erase
    // the earlier connection it was requested to discharge.
    historyLimit: 6,
  });
  const paths = resolveMathRunProjectPaths(
    lineage.binding,
    input.capability.projectRoot,
    lineage.target.preparedGit?.worktreePath
  );
  const store = new MathArtifactStore({
    runRoot: path.dirname(lineage.binding.artifactStoreRoot),
    runId: lineage.binding.runId,
    flockExecutable: '/usr/bin/flock',
  });
  await store.initialize();
  const blocks: CheckedMathProofBlock[] = [];
  // One collection may contain the same frozen reference in several share records.
  // Re-read authorization and bytes on every occurrence; reuse only this call's result.
  const checkedSources = new Map<string, ReadonlyMap<string, MathProofBlockResult>>();
  try {
    // A feedback relation is a revocable grant, not ambient Lead authority.
    for (const finding of feedback.findings) {
      for (const ref of finding.fullRefs) {
        input.signal.throwIfAborted();
        if (Date.now() >= input.deadlineAt) throw new Error('math_search_deadline');
        const parsed = parseMathArtifactReference(ref);
        if (parsed?.scheme !== 'math-artifact' || parsed.runId !== lineage.binding.runId)
          throw new Error('math_feedback_delivery_identity');
        const access = {
          role: 'worker' as const,
          assignmentId: lineage.target.assignmentId,
          grants: new Set([parsed.artifactId]),
        };
        const metadata = (await store.listMetadata(access)).find((entry) => entry.artifactId === parsed.artifactId);
        if (!metadata || metadata.truncated || metadata.assignmentId !== finding.sourceAssignmentId) continue;
        let source = '';
        let offsetBytes = 0;
        for (;;) {
          input.signal.throwIfAborted();
          if (Date.now() >= input.deadlineAt) throw new Error('math_search_deadline');
          const chunk = await store.read({ ref, offsetBytes, maxBytes: 2048 }, access);
          source += chunk.text;
          if (Buffer.byteLength(source) > 1_048_576) {
            source = '';
            break;
          }
          if (chunk.nextOffsetBytes === undefined) break;
          offsetBytes = chunk.nextOffsetBytes;
          input.signal.throwIfAborted();
        }
        const declarations = inspectLeanDeclarations(source).filter((item) => item.kind === 'theorem');
        if (!declarations.length || declarations.length > 32) continue;
        // The frozen file is checked once; every theorem retains its own kernel
        // type, dependency closure and source binding. Nothing is reused across calls.
        const sourceHash = mathDigest(source);
        const key = canonicalMathJson([ref, sourceHash, finding.sourceAssignmentId, input.environmentId]);
        const previous = checkedSources.get(key);
        const startedAt = performance.now();
        const results =
          previous ??
          (await verifyMathProofBlocks({
            projectRoot: paths.solverProjectRoot,
            proofPath: path.posix.join(
              normalizeRuntimeMathAssignment(lineage.target.assignment).sourceRootRelative,
              'SharedProof.lean'
            ),
            source,
            theoremNames: declarations.map((declaration) => declaration.name),
            scope: {
              runId: lineage.binding.runId,
              assignmentId: finding.sourceAssignmentId,
              artifactRef: ref,
              environmentId: input.environmentId,
            },
            deadlineAt: input.deadlineAt,
            signal: input.signal,
            env: input.env,
          }));
        // Duration is the shared batch check, recorded only when this occurrence ran it.
        const durationMs = previous ? undefined : performance.now() - startedAt;
        for (const declaration of declarations) {
          const result = results.get(declaration.name);
          const block = result?.block;
          recordMathProofImpact(
            { runRoot: path.dirname(lineage.binding.artifactStoreRoot), runId: lineage.binding.runId },
            {
              kind: 'checked',
              runId: lineage.binding.runId,
              assignmentId: finding.sourceAssignmentId,
              consumerAssignmentId: lineage.target.assignmentId,
              shareId: finding.shareId,
              artifactId: parsed.artifactId,
              ...(block ? { blockId: block.id } : {}),
              sourceHash,
              declarationName: declaration.name,
              declarationSourceHash: mathProofImpactDeclarationHash(source, declaration.name),
              supportingDeclarations: mathProofImpactSupportingDeclarations(source),
              outcome: block
                ? 'verified'
                : result?.verification?.status === 'blocked'
                  ? 'blocked'
                  : result?.verification?.status === 'unavailable'
                    ? 'unavailable'
                    : 'failed',
              observedAt: Date.now(),
              ...(durationMs === undefined ? {} : { durationMs }),
            }
          );
        }
        const checked = [...results.values()].every((result) => !!result.block);
        const incomplete = [...results.values()].some(
          (result) => !result.verification || ['blocked', 'unavailable'].includes(result.verification.status)
        );
        await recordMathLiteFeedbackUse({
          resolvedCapability: input.capability,
          signal: input.signal,
          runInputs: input.runInputs,
          ref,
          sourceHash,
          environmentId: input.environmentId,
          status: checked ? 'checked' : incomplete ? 'check_incomplete' : 'check_failed',
          ...(!checked
            ? {
                diagnostic: [...results.values()]
                  .map((result) => result.reason)
                  .filter(Boolean)
                  .join('\n')
                  .slice(0, 2000),
              }
            : {}),
        });
        if (!previous) {
          checkedSources.set(key, results);
          for (const result of results.values()) {
            if (result.block) blocks.push(result.block);
          }
        }
      }
    }
    const now = lineage.readAssignments().find((receipt) => receipt.assignmentId === lineage.target.assignmentId);
    if (!now || canonicalMathJson(now) !== canonicalMathJson(lineage.target))
      throw new Error('math_feedback_assignment_changed');
    if (input.proofSource && blocks.length >= 2) {
      const inspected = await inspectMathDiscoveryObstructions(
        {
          projectRoot: paths.solverProjectRoot,
          proofPath: input.proofSource.file,
          sourceHash: input.proofSource.sha256,
          deadlineAt: input.deadlineAt,
          signal: input.signal,
          env: input.env,
        },
        blocks
      );
      input.onDiscoveryObstructions?.(inspected.observations);
      const excluded = new Set(inspected.unsupportedConnectionIds);
      return blocks.filter((block) => !excluded.has(block.id));
    }
    return blocks;
  } finally {
    await store.closeReaders();
  }
}

/** Only an exact, sole named-proof request is eligible. Research/explanation tasks remain intact.
 * The caller must perform WAL replay first; this function never prepares or deletes assignments. */
export async function contractMathNamedProofDispatch(input: {
  objective: string;
  proofOwner: Capability;
  signal: AbortSignal;
  deadlineAt: number;
  runInputs?: MathRunInputs;
  env?: NodeJS.ProcessEnv;
}) {
  const name = /^Prove\s+([A-Za-z_][A-Za-z0-9_'.]*?)(?:\.)?$/u.exec(input.objective.trim())?.[1];
  if (!name) return undefined;
  const lineage = readMathLiteProofLineage(input.proofOwner, input.signal, input.runInputs);
  const latest = readLatestMathLiteProgress(lineage.binding, lineage.target, undefined, true);
  const files = latest?.files.filter((file) => file.pathRelative.endsWith('.lean')) ?? [];
  if (files.length !== 1) return undefined;
  const file = files[0]!;
  const paths = resolveMathRunProjectPaths(
    lineage.binding,
    input.proofOwner.projectRoot,
    lineage.target.preparedGit?.worktreePath
  );
  // Conservative project configuration binding. Every proposed success below still receives
  // fresh full kernel verification; this is not an immutable-package cache certificate.
  const configuration = [
    'lean-toolchain',
    'lakefile.toml',
    'lakefile.lean',
    'lake-manifest.json',
    '.lake/package-overrides.json',
  ].map((relative) => {
    const absolute = path.join(paths.solverProjectRoot, relative);
    if (fs.existsSync(absolute)) assertMathCanonicalPath(absolute);
    return [relative, fs.existsSync(absolute) ? fs.readFileSync(absolute, 'utf8') : null];
  });
  const environmentId = mathDigest(canonicalMathJson(configuration));
  const store = new MathArtifactStore({
    runRoot: path.dirname(lineage.binding.artifactStoreRoot),
    runId: lineage.binding.runId,
    flockExecutable: '/usr/bin/flock',
  });
  await store.initialize();
  try {
    const parsed = parseMathArtifactReference(file.ref);
    if (parsed?.scheme !== 'math-artifact' || parsed.runId !== lineage.binding.runId)
      throw new Error('math_share_snapshot_integrity');
    let source = '';
    let offsetBytes = 0;
    for (;;) {
      input.signal.throwIfAborted();
      if (Date.now() >= input.deadlineAt) throw new Error('math_search_deadline');
      const chunk = await store.read(
        { ref: file.ref, offsetBytes, maxBytes: 2048 },
        { role: 'worker', assignmentId: lineage.target.assignmentId }
      );
      if (chunk.sha256 !== file.sha256) throw new Error('math_share_snapshot_integrity');
      source += chunk.text;
      if (Buffer.byteLength(source) > 1_048_576) return undefined;
      if (chunk.nextOffsetBytes === undefined) break;
      offsetBytes = chunk.nextOffsetBytes;
    }
    const regions = inspectLeanDeclarationRegions(source).filter((declaration) => declaration.name === name);
    if (
      regions.length !== 1 ||
      !inspectLeanDeclarations(source).some(
        (declaration) => declaration.name === name && declaration.kind === 'theorem'
      )
    )
      return undefined;
    const request = {
      projectRoot: paths.solverProjectRoot,
      proofPath: path.posix.join(
        normalizeRuntimeMathAssignment(lineage.target.assignment).sourceRootRelative,
        'NamedObligation.lean'
      ),
      source,
      theoremName: name,
      scope: {
        runId: lineage.binding.runId,
        assignmentId: lineage.target.assignmentId,
        artifactRef: file.ref,
        environmentId,
      },
      deadlineAt: input.deadlineAt,
      signal: input.signal,
      env: input.env,
    };
    let result = await verifyMathProofBlock(request);
    if (!result.block) {
      const blocks = await collectMathCheckedProofSupport({
        capability: input.proofOwner,
        environmentId,
        signal: input.signal,
        deadlineAt: input.deadlineAt,
        runInputs: input.runInputs,
        env: input.env,
      });
      const frontier = new MathProofWorkFrontier();
      blocks.forEach((block) => frontier.register(block));
      if (!blocks.length) return undefined;
      input.signal.throwIfAborted();
      if (Date.now() >= input.deadlineAt) throw new Error('math_search_deadline');
      const workspaceRoot = lineage.target.preparedGit!.worktreePath!;
      const started = await startMathematicsLeanSession({
        workspaceRoot,
        projectRelative: path.relative(workspaceRoot, paths.solverProjectRoot),
        sourceFile: path.posix.join(
          normalizeRuntimeMathAssignment(lineage.target.assignment).sourceRootRelative,
          file.pathRelative
        ),
        sourceText: source,
        contractSource: source,
        statementHash: lineage.binding.problem!.statementHash,
        routeFingerprint: `named-${mathDigest(file.ref)}`,
        episodeId: lineage.target.assignmentId,
        timeoutMs: input.deadlineAt - Date.now(),
        signal: input.signal,
        env: input.env,
      });
      const session = started.session;
      if (!session) return undefined;
      try {
        const firstLine = source.slice(0, regions[0]!.startOffset).split('\n').length;
        const lastLine = source.slice(0, regions[0]!.endOffset).split('\n').length;
        const goalIndex = session.state.openGoals.findIndex((_, index) => {
          const line = session.goalLocation(index)?.line;
          return line !== undefined && line >= firstLine && line < lastLine;
        });
        if (goalIndex < 0) return undefined;
        const location = session.goalLocation(goalIndex)!;
        const outcome = await frontier.consume(
          {
            request,
            targetName: name,
            prepared: false,
            goal: {
              source,
              premises: [],
              openGoal: session.state.openGoals[goalIndex],
              targetLine: location.line,
              targetRange: location.range,
              goalIndex: location.localIndex ?? 0,
              diagnostics: session.diagnostics,
            },
          },
          blocks.map((block) => block.id)
        );
        if (!outcome.checked) return undefined;
        result = { block: outcome.checked, verification: outcome.checked.receipt };
      } finally {
        await session.close();
      }
    }
    input.signal.throwIfAborted();
    const current = lineage.readAssignments().find((receipt) => receipt.assignmentId === lineage.target.assignmentId);
    if (
      !current ||
      canonicalMathJson(current) !== canonicalMathJson(lineage.target) ||
      readLatestMathLiteProgress(lineage.binding, current, undefined, true)?.shareId !== latest!.shareId
    )
      throw new Error('math_feedback_assignment_changed');
    const block = result.block!;
    const artifactId = `proof-work-${mathDigest(canonicalMathJson([block.id, block.sourceHash]))}`;
    await store.publishText({
      artifactId,
      assignmentId: lineage.target.assignmentId,
      kind: 'evidence',
      sensitivity: 'solver-visible',
      mediaType: 'text/plain',
      text: block.source,
    });
    return {
      status: 'not_dispatched' as const,
      accepted: false as const,
      reason: 'The exact frozen named obligation has a complete checked proof; no new assignment was prepared.',
      theorem: name,
      sourceArtifact: file.ref,
      checkedArtifact: `math-artifact://${lineage.binding.runId}/${artifactId}`,
      declarationHash: block.declarationHash,
      sourceHash: block.sourceHash,
      authority: 'lean-kernel',
      originalTargetAccepted: false,
    };
  } finally {
    await store.closeReaders();
  }
}
