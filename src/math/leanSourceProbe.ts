import { resolveMathProofEnvironment } from "./mathProofEnvironment";
import crypto from 'node:crypto';
import fs from 'node:fs';
import path from 'node:path';
import { execFileSync } from 'node:child_process';
import { z } from 'zod';
import { runLeanEvalLeanProbe, type LeanEvalLeanProbeRequest } from "./leanEvalLeanProbe";
import { readMathRunHistoryIdentity } from "./mathRunHistory";
import { createLeanProbeSnapshot } from "./leanProbeSnapshot";
import {
  acquireSharedLeanPackages,
  sharedLeanPackagesUnavailableReason,
  SharedLeanEnvironmentUnavailableError,
  type SharedLeanPackagesLease,
} from "./leanSharedPackages";
import { resolveMathematicsLakePackagesCache } from "./verifier";
import { resolveMathematicsRuntimeEnvironment } from "./mathRuntimeEnvironment";

export const leanSourceProbeInput = z
  .object({
    targetCommit: z.string().regex(/^[a-f0-9]{40}(?:[a-f0-9]{24})?$/u),
    sourceFile: z.string().min(1).max(1024),
    sourceHash: z.string().regex(/^[a-f0-9]{64}$/u),
    startOffset: z.number().int().nonnegative(),
    endOffset: z.number().int().positive(),
    spanHash: z.string().regex(/^[a-f0-9]{64}$/u),
    tactic: z
      .string()
      .min(1)
      .max(12_000)
      .refine((value) => value.trim().length > 0),
  })
  .strict();
export type LeanSourceProbeInput = z.infer<typeof leanSourceProbeInput>;
const observation = z
  .object({
    accepted: z.boolean(),
    before: z.array(z.object({ id: z.string(), goal: z.string() })).max(128),
    after: z.array(z.object({ id: z.string(), goal: z.string() })).max(128),
    error: z.string().optional(),
  })
  .strict();
const hash = (value: string | Buffer) => crypto.createHash('sha256').update(value).digest('hex');

/** Parsing the candidate inside Lean avoids injecting its text into the instrumentation. */
const probeTactic = (candidate: string, marker: string): string => {
  // A parenthesized sequence accepts multiple tactics while retaining nested
  // indentation. Trimming only the first line would change Lean's layout.
  const sequence = `(\n${candidate
    .split(/\r?\n/u)
    .map((line) => `  ${line}`)
    .join('\n')}\n)`;
  return `run_tac do
  let describeGoals : Lean.Elab.Tactic.TacticM (Array Lean.Json) := do
    let goals <- Lean.Elab.Tactic.getGoals
    goals.toArray.mapM fun goal => do
      let pretty <- Lean.Meta.ppGoal goal
      pure (Lean.Json.mkObj [("id", Lean.toJson goal.name.toString), ("goal", Lean.toJson pretty.pretty)])
  let before <- describeGoals
  let originalGoals <- Lean.Elab.Tactic.getGoals
  try
    let tactic <- match Lean.Parser.runParserCategory (<- Lean.getEnv) (Lean.Name.mkSimple "tactic") ${JSON.stringify(sequence)} with
      | .ok stx => pure stx
      | .error message => throwError "{message}"
    Lean.Elab.Tactic.evalTactic tactic
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let after <- describeGoals
    if after.isEmpty then
      for goal in originalGoals do
        let proof <- Lean.instantiateMVars (Lean.mkMVar goal)
        if proof.hasMVar || proof.hasSorry then
          throwError "Candidate left unresolved metavariables or admitted a goal"
    let result := Lean.Json.mkObj [("accepted", Lean.toJson true), ("before", .arr before), ("after", .arr after)]
    Lean.logInfo m!"${marker}{result.compress}"
  catch error =>
    let after <- describeGoals
    let message <- error.toMessageData.toString
    let result := Lean.Json.mkObj [("accepted", Lean.toJson false), ("before", .arr before), ("after", .arr after), ("error", Lean.toJson message)]
    Lean.logInfo m!"${marker}{result.compress}"
    throw error`;
};

/** An observation at a bound source position never creates a verifier receipt or mutates the candidate. */
export async function runLeanSourceProbe(
  workspaceRoot: string,
  value: LeanSourceProbeInput,
  options: Pick<LeanEvalLeanProbeRequest, 'env' | 'signal' | 'timeoutMs' | 'lakePackagesPath'> &
    Readonly<{ sharedPackages?: 'auto' | 'off' | 'required' }> = {}
) {
  let input = leanSourceProbeInput.parse(value);
  readMathRunHistoryIdentity(options.env ?? process.env);
  const root = path.resolve(workspaceRoot);
  const git = (...args: string[]) =>
    execFileSync('git', ['-C', root, ...args], { encoding: 'utf8', maxBuffer: 16 * 1024 * 1024, timeout: 10_000 });
  const [worktreeRoot, head] = git('rev-parse', '--show-toplevel', 'HEAD').trim().split('\n');
  if (head !== input.targetCommit) throw new Error('Source probe commit is stale.');
  const projectPrefix = path.relative(worktreeRoot!, root).split(path.sep).join('/');
  if (projectPrefix && input.sourceFile.startsWith(`${projectPrefix}/`))
    input = { ...input, sourceFile: input.sourceFile.slice(projectPrefix.length + 1) };
  const sourcePath = path.resolve(root, input.sourceFile);
  const relative = path.relative(root, sourcePath);
  if (
    !relative ||
    relative.startsWith('..') ||
    path.isAbsolute(relative) ||
    !relative.endsWith('.lean') ||
    relative.split(path.sep).includes('Solution.lean')
  ) {
    throw new Error('Source probe requires an authorized project-relative Lean file.');
  }
  if (fs.realpathSync(root) !== root || fs.realpathSync(sourcePath) !== sourcePath)
    throw new Error('Source probe rejects symbolic links.');
  const source = fs.readFileSync(sourcePath, 'utf8');
  // Terminal scripts and Lean report UTF-8 byte positions. Preserve existing
  // UTF-16 callers too: only accept the interpretation with the exact span hash.
  if (hash(source.slice(input.startOffset, input.endOffset)) !== input.spanHash) {
    const bytes = Buffer.from(source, 'utf8');
    const before = bytes.subarray(0, input.startOffset);
    const span = bytes.subarray(input.startOffset, input.endOffset);
    if (
      input.endOffset <= bytes.length &&
      hash(span) === input.spanHash &&
      Buffer.from(before.toString('utf8')).equals(before) &&
      Buffer.from(span.toString('utf8')).equals(span)
    ) {
      const startOffset = before.toString('utf8').length;
      input = { ...input, startOffset, endOffset: startOffset + span.toString('utf8').length };
    }
  }
  if (
    hash(source) !== input.sourceHash ||
    input.endOffset > source.length ||
    input.startOffset >= input.endOffset ||
    hash(source.slice(input.startOffset, input.endOffset)) !== input.spanHash
  ) {
    throw new Error('Source probe position or source identity is stale.');
  }
  const marker = `DS_SOURCE_PROBE_${crypto.randomBytes(16).toString('hex')}:`;
  const linePrefix = source.slice(source.lastIndexOf('\n', input.startOffset - 1) + 1, input.startOffset);
  if (!/^\s*$/u.test(linePrefix)) throw new Error('Source probe must start at the first tactic on its line.');
  const spanIndentation = /^[\t ]*/u.exec(source.slice(input.startOffset, input.endOffset))![0];
  const indentation = linePrefix + spanIndentation;
  const replacement = spanIndentation + probeTactic(input.tactic, marker).replaceAll('\n', `\n${indentation}`);
  // Import the instrumentation dependencies instead of the full Lean umbrella.
  // The candidate retains its own imports; unrelated compiler and tactic modules
  // otherwise dominate even a tiny source probe on the disk-backed toolchain.
  const instrumented = `import Lean.Elab.Tactic.BuiltinTactic\nimport Lean.Elab.Tactic.Rfl\nimport Lean.Meta.PPGoal\n${source.slice(0, input.startOffset)}${replacement}${source.slice(input.endOffset)}`;
  const startedAt = Date.now();
  const environment = resolveMathematicsRuntimeEnvironment(options.env ?? process.env);
  const packages = resolveMathematicsLakePackagesCache(root, environment);
  const proofEnvironment = resolveMathProofEnvironment(root, environment);
  if (
    options.lakePackagesPath &&
    (proofEnvironment ? options.lakePackagesPath : fs.realpathSync(options.lakePackagesPath)) !== packages
  )
    throw new Error('Source probe package cache does not match the project manifest.');
  const deadlineAt = startedAt + Math.min(options.timeoutMs ?? 120_000, 120_000);
  // A run-bound sealed environment already replaces the package copy; never reseal its descriptor path.
  let unavailableReason =
    !packages || options.sharedPackages === 'off'
      ? undefined
      : proofEnvironment
        ? 'sealed_proof_environment'
        : sharedLeanPackagesUnavailableReason();
  if (options.sharedPackages === 'required' && (!packages || unavailableReason))
    throw new Error(`Shared Lean environment unavailable: ${unavailableReason ?? 'no_package_cache'}`);
  let shared: SharedLeanPackagesLease | undefined;
  if (packages && options.sharedPackages !== 'off' && !unavailableReason) {
    try {
      shared = await acquireSharedLeanPackages(packages, { signal: options.signal, deadlineAt });
    } catch (error) {
      if (options.sharedPackages === 'required' || !(error instanceof SharedLeanEnvironmentUnavailableError))
        throw error;
      unavailableReason = 'native_namespace_or_fuse_unavailable';
    }
  }
  let snapshot: ReturnType<typeof createLeanProbeSnapshot>;
  try {
    snapshot = createLeanProbeSnapshot(root, input.sourceFile, packages, {
      signal: options.signal,
      deadlineAt,
      immutablePackages: shared,
      proofEnvironment,
    });
  } catch (error) {
    shared?.release();
    throw error;
  }
  let result: Awaited<ReturnType<typeof runLeanEvalLeanProbe>>;
  try {
    if (hash(fs.readFileSync(path.join(snapshot.workspaceRoot, input.sourceFile), 'utf8')) !== input.sourceHash)
      throw new Error('Source changed during snapshot creation.');
    const remainingMs = deadlineAt - Date.now();
    if (remainingMs < 100 || options.signal?.aborted) throw new Error('Source probe deadline exceeded or cancelled.');
    result = await runLeanEvalLeanProbe({
      ...options,
      sharedPackages: shared,
      env: environment,
      timeoutMs: remainingMs,
      workspaceRoot: snapshot.workspaceRoot,
      lakePackagesPath: proofEnvironment?.packagesRoot,
      useWorkspacePackagesOnly: !proofEnvironment,
      // A sealed proof environment already contains the authorized compiled
      // dependency tree. Rebuilding it with `lake --no-cache` defeats the
      // persistent disk cache and can exceed the bounded probe deadline.
      prepareLocalDependencies: !proofEnvironment,
      sourceFile: input.sourceFile,
      sourceText: instrumented,
      mode: 'compile',
    });
    snapshot.verify();
  } finally {
    try {
      snapshot.dispose();
    } finally {
      shared?.release();
    }
  }
  if (git('rev-parse', 'HEAD').trim() !== head || hash(fs.readFileSync(sourcePath, 'utf8')) !== input.sourceHash) {
    throw new Error('Source or commit changed during the probe.');
  }
  const observations: z.infer<typeof observation>[] = [];
  for (const line of result.diagnostics.split('\n')) {
    let message = line;
    try {
      const diagnostic = JSON.parse(line);
      if (typeof diagnostic?.data === 'string') message = diagnostic.data;
    } catch {
      // Plain-text Lean output can carry the same marker.
    }
    const markerOffset = message.indexOf(marker);
    if (markerOffset < 0) continue;
    try {
      observations.push(observation.parse(JSON.parse(message.slice(markerOffset + marker.length))));
    } catch {
      // Missing or malformed instrumentation remains an unknown context.
    }
  }
  const parsed = observations.length === 1 ? observations[0] : undefined;
  const status =
    result.status === 'unavailable'
      ? 'environment_unavailable'
      : !parsed
        ? 'context_unavailable'
        : !parsed.accepted
          ? 'action_failed'
          : parsed.after.length
            ? 'conditions_remaining'
            : 'goal_closed';
  return Object.freeze({
    status,
    authority: 'observation' as const,
    targetCommit: input.targetCommit,
    sourceHash: input.sourceHash,
    position: { startOffset: input.startOffset, endOffset: input.endOffset, spanHash: input.spanHash },
    contextFingerprint: hash(JSON.stringify([input, snapshot.digest, parsed ?? null])),
    dependencySnapshot: {
      sha256: snapshot.digest,
      files: snapshot.fileCount,
      bytes: snapshot.bytes,
      metrics: snapshot.metrics(),
      ...(shared ? { sharedEnvironment: shared.metrics } : {}),
      ...(unavailableReason ? { sharedEnvironmentUnavailableReason: unavailableReason } : {}),
    },
    ...(parsed ? { before: parsed.before, after: parsed.after, error: parsed.error } : {}),
    ...(result.status === 'unavailable' && result.error ? { error: result.error } : {}),
    diagnostics: result.diagnostics,
    durationMs: Date.now() - startedAt,
    requiresFinalVerification: true as const,
  });
}
