import fs from 'node:fs';
import path from 'node:path';
import { z } from 'zod';
import { assertMathConstructionSources, mathLocalModuleBuildOrder } from './mathConstructionSources';
import { parseLeanDiagnosticOutput } from './leanDiagnosticMessages';
import { inspectLeanDeclarationRegions, inspectScopedLeanDeclarations } from './leanSource';
import { resolveMathProofEnvironment } from './mathProofEnvironment';
import { mathDigest, readMathFile } from './mathRuntimeIo';
import { resolveMathematicsRuntimeEnvironment } from './mathRuntimeEnvironment';
import { assertMathCanonicalPath } from './paths';
import { formalVerificationToolIdentity } from './verifier';
import type { LeanDiagnosticMessage } from './leanTypes';

const CONFIGURATION_FILES = ['lean-toolchain', 'lakefile.toml', 'lakefile.lean', 'lake-manifest.json', '.lake/package-overrides.json'];
const digest = z.string().regex(/^[a-f0-9]{64}$/u);
const diagnosticExit = z.union([z.literal(0), z.literal(1)]);
const sourceFile = z.object({ file: z.string(), digest });
const reference = z.object({ path: z.string(), digest, sourceDigest: digest, environmentDigest: digest,
  captureComplete: z.boolean().nullable() });
const latestSchema = z.object({ schema: z.literal('theoremos.lean-diagnostics-latest.v1'),
  authority: z.literal('advisory-lean-process'), sourceDigest: digest, environmentDigest: digest, toolIdentity: digest,
  requestedFiles: z.array(z.string()).min(1).max(4096),
  configuration: z.array(z.object({ file: z.string(), digest: digest.nullable() })).length(CONFIGURATION_FILES.length),
  sourceFiles: z.array(sourceFile).min(1).max(4096), exitCode: diagnosticExit,
  timedOut: z.literal(false), aborted: z.literal(false), diagnosticArtifacts: z.array(reference).max(4096) });
const artifactSchema = z.object({ schema: z.literal('theoremos.lean-diagnostics.v1'),
  authority: z.literal('advisory-lean-process'), sourceDigest: digest, environmentDigest: digest, toolIdentity: digest,
  file: z.string(), sourceCurrent: z.literal(true), sourceFiles: z.array(sourceFile).min(1).max(4096),
  exitCode: diagnosticExit, timedOut: z.literal(false), aborted: z.literal(false), captureComplete: z.literal(true),
  stdout: z.string(), stderr: z.string(), stdoutSha256: digest, stderrSha256: digest });

export type LeanResidualGoalConsumer = { taskId?: string; taskDigest?: string; theoremName: string; proofPath: string };
export type LeanResidualGoal = {
  authority: 'advisory-lean-process'; consumer: LeanResidualGoalConsumer; goalText: string;
  sourceDigest: string; environmentDigest: string; toolIdentity: string;
  artifact: { path: string; digest: string }; file: string; line: number; column: number;
};
export type LeanResidualGoalOmission = {
  consumer: LeanResidualGoalConsumer; count: number; reason: 'diagnostic-reader-budget';
};
export type LeanResidualGoalSnapshot = { goals: LeanResidualGoal[]; omissions: LeanResidualGoalOmission[] };

/** Shared by diagnostic capture and advisory readers; unknown tools cannot authorize goal reuse. */
export function leanDiagnosticEnvironmentIdentity(projectRoot: string, source: NodeJS.ProcessEnv) {
  const env = resolveMathematicsRuntimeEnvironment(source);
  const sealed = resolveMathProofEnvironment(projectRoot, env);
  const toolIdentity = formalVerificationToolIdentity(projectRoot, env);
  return { environmentDigest: mathDigest(JSON.stringify([
    'lean-json-diagnostics.v1', sealed?.identity, env.PATH, env.ELAN_HOME, env.LEAN_PATH, env.LEAN_SYSROOT, toolIdentity,
  ])), ...(toolIdentity ? { toolIdentity } : {}) };
}

function readRegular(file: string, limit: number): string {
  assertMathCanonicalPath(file);
  return new TextDecoder('utf-8', { fatal: true, ignoreBOM: true }).decode(readMathFile(file, limit).bytes);
}

function sourceSnapshot(project: string, requested: readonly string[]) {
  assertMathConstructionSources(project, requested);
  const configuration = CONFIGURATION_FILES.map(file => {
    const absolute = path.join(project, file);
    assertMathCanonicalPath(absolute);
    return { file, digest: fs.existsSync(absolute) ? mathDigest(readRegular(absolute, 16_000_000)) : null };
  });
  const sourceFiles = mathLocalModuleBuildOrder(project, requested).map(({ file }) =>
    ({ file, digest: mathDigest(readRegular(path.join(project, file), 16_000_000)) }));
  return { configuration, sourceFiles, sourceDigest: mathDigest(JSON.stringify([
    configuration.map(item => item.digest ?? ''), sourceFiles.map(item => [item.file, item.digest]),
  ])) };
}

/** Lean JSON columns count Unicode code points, while declaration offsets count UTF-16 units. */
function sourceOffset(source: string, line: number | undefined, column: number | undefined): number | undefined {
  if (!Number.isSafeInteger(line) || line! < 1 || !Number.isSafeInteger(column) || column! < 0) return undefined;
  let offset = 0;
  for (let current = 1; current < line!; current++) {
    const newline = source.indexOf('\n', offset);
    if (newline < 0) return undefined;
    offset = newline + 1;
  }
  const end = source.indexOf('\n', offset);
  const characters = [...source.slice(offset, end < 0 ? undefined : end)];
  if (column! > characters.length) return undefined;
  return offset + characters.slice(0, column).join('').length;
}

function consumerAt(project: string, file: string, message: LeanDiagnosticMessage, consumers: readonly LeanResidualGoalConsumer[]) {
  const source = readRegular(path.join(project, file), 16_000_000);
  const start = sourceOffset(source, message.line, message.column);
  if (start === undefined) return undefined;
  const end = message.endLine === undefined && message.endColumn === undefined ? start :
    sourceOffset(source, message.endLine, message.endColumn);
  if (end === undefined || end < start) return undefined;
  const regions = inspectLeanDeclarationRegions(source).filter(region =>
    start >= region.startOffset && start < region.endOffset && end <= region.endOffset);
  if (regions.length !== 1) return undefined;
  const declarations = inspectScopedLeanDeclarations(source);
  const declaration = declarations.find(item => item.startOffset === regions[0].startOffset);
  if (!declaration || declarations.filter(item => item.qualifiedName === declaration.qualifiedName).length !== 1) return undefined;
  const matches = consumers.filter(item => item.proofPath === file && item.theoremName === declaration.qualifiedName);
  return matches.length === 1 ? matches[0] : undefined;
}

/** Worker-writable metadata and matching hashes remain advisory, never kernel proof evidence. */
export function readLeanResidualGoals(input: {
  projectRoot: string; env?: NodeJS.ProcessEnv; consumers: readonly LeanResidualGoalConsumer[];
}): LeanResidualGoal[] {
  return readLeanResidualGoalSnapshot(input).goals;
}

export function readLeanResidualGoalSnapshot(input: {
  projectRoot: string; env?: NodeJS.ProcessEnv; consumers: readonly LeanResidualGoalConsumer[];
}): LeanResidualGoalSnapshot {
  const empty = (): LeanResidualGoalSnapshot => ({ goals: [], omissions: [] });
  if (!input.consumers.length) return empty();
  try {
    const residuals: LeanResidualGoal[] = [];
    const omissions: LeanResidualGoalOmission[] = [];
    const project = fs.realpathSync(input.projectRoot);
    const latest = latestSchema.parse(JSON.parse(readRegular(path.join(project, '.lake/lean-diagnostics-latest.json'), 2_000_000)));
    const env = resolveMathematicsRuntimeEnvironment(input.env ?? process.env);
    if (!resolveMathProofEnvironment(project, env)?.identity) return empty();
    const identity = leanDiagnosticEnvironmentIdentity(project, env);
    if (!identity.toolIdentity) return empty();
    const current = sourceSnapshot(project, latest.requestedFiles);
    if (latest.environmentDigest !== identity.environmentDigest || latest.toolIdentity !== identity.toolIdentity ||
        latest.sourceDigest !== current.sourceDigest || JSON.stringify(latest.configuration) !== JSON.stringify(current.configuration) ||
        JSON.stringify(latest.sourceFiles) !== JSON.stringify(current.sourceFiles)) return empty();
    const files = new Set(current.sourceFiles.map(item => item.file));
    for (const artifactReference of latest.diagnosticArtifacts) {
      if (artifactReference.captureComplete !== true || artifactReference.environmentDigest !== latest.environmentDigest ||
          artifactReference.sourceDigest !== latest.sourceDigest ||
          artifactReference.path !== `.lake/diagnostic-artifacts/${artifactReference.digest}.json`) continue;
      let artifact: z.infer<typeof artifactSchema>;
      try {
        const text = readRegular(path.join(project, artifactReference.path), 32_000_000);
        if (mathDigest(text) !== artifactReference.digest) continue;
        artifact = artifactSchema.parse(JSON.parse(text));
      } catch { continue; }
      if (artifact.sourceDigest !== latest.sourceDigest || artifact.environmentDigest !== latest.environmentDigest ||
          artifact.toolIdentity !== latest.toolIdentity || !files.has(artifact.file) ||
          JSON.stringify(artifact.sourceFiles) !== JSON.stringify(current.sourceFiles) ||
          mathDigest(artifact.stdout) !== artifact.stdoutSha256 || mathDigest(artifact.stderr) !== artifact.stderrSha256) continue;
      const messages = [...parseLeanDiagnosticOutput(artifact.stdout).messages, ...parseLeanDiagnosticOutput(artifact.stderr).messages];
      for (const message of messages) {
        if (message.format !== 'lean-json' || message.severity !== 'error' || !message.goalText ||
            Buffer.byteLength(message.goalText) > 16_000 || typeof message.file !== 'string') continue;
        const file = path.isAbsolute(message.file) ? path.relative(project, message.file) : message.file;
        if (file !== artifact.file || !files.has(file)) continue;
        const consumer = consumerAt(project, file, message, input.consumers);
        if (!consumer) continue;
        if (residuals.length >= 8) {
          const omission = omissions.find(item => JSON.stringify(item.consumer) === JSON.stringify(consumer));
          if (omission) omission.count++;
          else omissions.push({ consumer: { ...consumer }, count: 1, reason: 'diagnostic-reader-budget' });
          continue;
        }
        residuals.push({ authority: 'advisory-lean-process', consumer: { ...consumer }, goalText: message.goalText,
          sourceDigest: current.sourceDigest, ...identity, toolIdentity: identity.toolIdentity,
          artifact: { path: artifactReference.path, digest: artifactReference.digest }, file, line: message.line!, column: message.column! });
      }
    }
    if (leanDiagnosticEnvironmentIdentity(project, env).environmentDigest !== identity.environmentDigest ||
        sourceSnapshot(project, latest.requestedFiles).sourceDigest !== current.sourceDigest) return empty();
    return { goals: residuals, omissions };
  } catch { /* Missing, stale, unsupported, or incomplete advisory diagnostics do not supply goals. */ }
  return empty();
}
