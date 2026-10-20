import fs from 'node:fs';
import path from 'node:path';
import { assertMathConstructionSources, mathLocalModuleBuildOrder } from '../math/mathConstructionSources';
import { canonicalMathJson, mathDigest, readMathFile } from '../math/mathRuntimeIo';
import { inspectLeanDeclarationRegions, inspectScopedLeanDeclarations, leanDeclarationContextCommands } from '../math/leanSource';
import { maskLeanCommentsAndStrings } from '../math/leanSyntax';
import { checkLeanType, leanTypeDiagnosticProjection } from '../math/leanTypeDiagnostics';
import { assertMathCanonicalPath, isMathPathWithin } from '../math/paths';
import { formalVerificationToolIdentity } from '../math/verifier';
import { renderLeanDiagnosticMessage } from '../math/leanDiagnosticMessages';
import { proofReuseEnvironment } from './proofReuse';
import type { SolverProblem } from './problem';
import { taskVersion, type CooperativeTask } from './tasks';

export type TaskTypePreflight = {
  status: 'elaborated' | 'invalid' | 'deferred' | 'unavailable'; inputDigest: string; reason: string;
  taskDigest: string; context?: string; type?: string;
  artifact?: { path: string; digest: string }; evidence: 'advisory-type-elaboration'; proofAcceptance: 'not-assessed';
  projectionReuse?: { originInputDigest: string; originSourceDigest: string; sourceDigest: string; projectionDigest: string };
};
type Input = { problem: SolverProblem; task: CooperativeTask; projectRoot: string; dependencies: readonly CooperativeTask[];
  environmentDigest: string; env: NodeJS.ProcessEnv; signal?: AbortSignal; timeoutMs: number };

/** Later independent source edits must not reopen an unchanged invalid canonical contract. */
export function taskTypePreflightEnvironmentIdentity(projectRoot: string, env: NodeJS.ProcessEnv): string | undefined {
  const environment = proofReuseEnvironment(projectRoot, env);
  const tools = formalVerificationToolIdentity(projectRoot, environment.env);
  return environment.reusable && tools ? mathDigest(canonicalMathJson([environment.digest, tools])) : undefined;
}

/** The query helper only restores namespace/section/open. Other active scopes need a fuller projection. */
function unsupportedScope(source: string, offset: number): boolean {
  const regions = inspectLeanDeclarationRegions(source), clean = maskLeanCommentsAndStrings(source);
  const frames = [false];
  for (const match of clean.slice(0, offset).matchAll(/^.*$/gmu)) {
    if (regions.some(region => match.index! >= region.startOffset && match.index! < region.endOffset)) continue;
    const line = match[0].trim();
    if (/^(?:namespace|section)\b/u.test(line)) frames.push(false);
    else if (/^end(?:\s|$)/u.test(line) && frames.length > 1) frames.pop();
    else if (/^(?:variables?|universes?|include|omit|local|scoped|attribute|set_option)\b/u.test(line) ||
        /^@\[[^\]]*\blocal\b/u.test(line)) frames[frames.length - 1] = true;
  }
  return frames.some(Boolean);
}

function prepare(input: Input) {
  const project = fs.realpathSync(input.projectRoot);
  const taskDigest = taskVersion(input.task), environment = proofReuseEnvironment(project, input.env);
  const tools = formalVerificationToolIdentity(project, environment.env);
  assertMathConstructionSources(project, [input.task.proofPath!]);
  const modules = mathLocalModuleBuildOrder(project, input.task.proofPath!);
  const configs = ['lean-toolchain', 'lakefile.toml', 'lakefile.lean', 'lake-manifest.json', '.lake/package-overrides.json'];
  const files = [...modules.map(module => module.file), ...configs.filter(file => fs.existsSync(path.join(project, file)))];
  const snapshots = files.map(file => {
    const read = readMathFile(path.join(project, file), 4_000_000);
    return { file, source: read.bytes.toString('utf8'), digest: mathDigest(read.bytes), identity: read.identity };
  });
  const sourceDigest = mathDigest(canonicalMathJson(snapshots.map(({ file, digest }) => ({ file, digest }))));
  const source = snapshots.find(file => file.file === input.task.proofPath)!.source;
  const declarations = inspectScopedLeanDeclarations(source);
  const requested = input.task.theoremName!.replace(/^_root_\./u, '');
  const namespace = requested.includes('.') ? requested.slice(0, requested.lastIndexOf('.')) : undefined;
  const exact = declarations.filter(item => item.qualifiedName === requested);
  const anchors = exact.length ? exact : declarations.filter(item => item.kind === 'theorem' &&
    (namespace === undefined || item.namespace === namespace) && input.problem.targets.some(target =>
      target.proofPath === input.task.proofPath && target.theoremName === item.qualifiedName));
  const anchor = anchors[0];
  let reason: string | undefined;
  if (!anchor || exact.length > 1 || !exact.length && new Set(anchors.map(item =>
    canonicalMathJson(leanDeclarationContextCommands(source, item.qualifiedName)))).size > 1)
    reason = 'declaration-context-unavailable';
  else if (anchors.some(item => unsupportedScope(source, item.startOffset))) reason = 'declaration-scope-not-reproducible';
  const available = new Set(snapshots.filter(file => file.file.endsWith('.lean')).flatMap(file =>
    inspectScopedLeanDeclarations(file.source).map(item => item.qualifiedName)));
  if (input.dependencies.some(task => task.kind === 'lemma' && task.theoremName && !available.has(task.theoremName)))
    reason = 'future-dependency-unavailable';
  const projection = !reason && anchor ? leanTypeDiagnosticProjection({ files: snapshots, modules,
    file: input.task.proofPath!, context: anchor.qualifiedName, type: input.task.type! }) : undefined;
  const binding = { project, taskDigest, context: anchor?.qualifiedName,
    dependencies: input.dependencies.map(task => [task.id, taskVersion(task)]), environmentDigest: input.environmentDigest,
    timeoutMs: Number.isFinite(input.timeoutMs) ? input.timeoutMs : 'unlimited',
    environment: environment.digest ?? mathDigest(canonicalMathJson(environment.env)), tools: tools ?? null };
  const key = mathDigest(canonicalMathJson({ ...binding, sourceDigest }));
  const projectionKey = projection && mathDigest(canonicalMathJson({ ...binding, projectionDigest: projection.digest }));
  const current = () => {
    try {
      const now = proofReuseEnvironment(project, input.env);
      return !input.signal?.aborted && fs.realpathSync(input.projectRoot) === project && formalVerificationToolIdentity(project, now.env) === tools &&
        canonicalMathJson(now.env) === canonicalMathJson(environment.env) && now.digest === environment.digest &&
        snapshots.every(file => { const read = readMathFile(path.join(project, file.file), 4_000_000);
          return read.identity === file.identity && mathDigest(read.bytes) === file.digest; }) &&
        canonicalMathJson(mathLocalModuleBuildOrder(project, input.task.proofPath!)) === canonicalMathJson(modules) &&
        canonicalMathJson(configs.filter(file => fs.existsSync(path.join(project, file)))) ===
          canonicalMathJson(files.filter(file => configs.includes(file)));
    } catch { return false; }
  };
  return { key, projectionKey, projection, project, taskDigest, sourceDigest, environment, tools, context: anchor?.qualifiedName, reason, current };
}

function artifactCurrent(project: string, artifact: TaskTypePreflight['artifact']): boolean {
  if (!artifact || path.isAbsolute(artifact.path)) return false;
  try {
    const file = path.resolve(project, artifact.path);
    if (!isMathPathWithin(project, file)) return false;
    assertMathCanonicalPath(file);
    return mathDigest(readMathFile(file, 4_000_000).bytes) === artifact.digest;
  } catch { return false; }
}

/** A normal compiler exit also carries resource, internal and IO errors; those do not invalidate a type. */
function definiteTypeError(message: string): boolean {
  if (/\b(?:heartbeats?|deterministic\W+timeout|timeout|timed\s+out|deadline|recursion\s+depth|maxRecDepth|stack\s+overflow|out\s+of\s+memory|memory\s+limit|resource\s+(?:limit|exhausted)|internal\s+(?:error|exception)|uncaught\s+exception|panic|IO(?:[.\s]+error|[.\s]+exception)|system\s+error|permission\s+denied|no\s+space\s+left|input\/output|failed\s+to\s+(?:open|read|write|allocate))\b/iu.test(message)) return false;
  return /^(?:(?:application\s+)?type mismatch|unknown (?:identifier|constant)|function expected|invalid (?:binder annotation|field(?: notation)?)|unexpected (?:token|identifier|end of input)|expected (?:token|term|type)|requested type must be closed)\b/iu.test(message.trim());
}

/** Process-local and content-bound; checkpoint JSON never authorizes skipping a new preflight. */
export class TaskTypePreflightCache {
  private readonly results = new Map<string, { result: TaskTypePreflight; sourceDigest: string; projectionKey?: string }>();
  private readonly projections = new Map<string, string>();
  private remember(key: string, value: TaskTypePreflight, sourceDigest: string, projectionKey?: string) {
    const previous = this.results.get(key);
    if (previous?.projectionKey && this.projections.get(previous.projectionKey) === key) this.projections.delete(previous.projectionKey);
    this.results.delete(key);
    if (this.results.size >= 64) {
      const oldest = this.results.keys().next().value!, evicted = this.results.get(oldest)!;
      if (evicted.projectionKey && this.projections.get(evicted.projectionKey) === oldest) this.projections.delete(evicted.projectionKey);
      this.results.delete(oldest);
    }
    this.results.set(key, { result: structuredClone(value), sourceDigest, projectionKey });
    if (projectionKey) this.projections.set(projectionKey, key);
  }
  async check(input: Input): Promise<{ result: TaskTypePreflight; current: () => boolean }> {
    const base = { taskDigest: taskVersion(input.task), evidence: 'advisory-type-elaboration' as const,
      proofAcceptance: 'not-assessed' as const };
    let snapshot: ReturnType<typeof prepare>;
    try { snapshot = prepare(input); }
    catch {
      return { result: { ...base, inputDigest: mathDigest(canonicalMathJson([base.taskDigest, input.environmentDigest])),
        status: 'unavailable', reason: 'type-context-or-environment-unavailable' }, current: () => !input.signal?.aborted };
    }
    const result = (status: TaskTypePreflight['status'], reason: string, extra: Partial<TaskTypePreflight> = {}) =>
      ({ ...base, inputDigest: snapshot.key, context: snapshot.context, status, reason, ...extra });
    const done = (value: TaskTypePreflight, reused = false) => ({ result: structuredClone(value),
      current: reused ? () => snapshot.current() && artifactCurrent(snapshot.project, value.artifact) : snapshot.current });
    if (snapshot.reason) return done(result('deferred', snapshot.reason));
    if (!snapshot.environment.reusable) return done(result('deferred', 'proof-environment-not-frozen'));
    if (!snapshot.tools) return done(result('unavailable', 'actual-lean-tools-unavailable'));
    const cached = snapshot.environment.reusable && this.results.get(snapshot.key);
    if (cached && artifactCurrent(snapshot.project, cached.result.artifact)) return done(cached.result, true);
    const origin = snapshot.projectionKey && this.projections.get(snapshot.projectionKey);
    const projected = origin && this.results.get(origin);
    if (projected && artifactCurrent(snapshot.project, projected.result.artifact)) {
      const reused = result('elaborated', 'closed-type-elaboration-projection-reused', {
        type: projected.result.type, artifact: projected.result.artifact,
        projectionReuse: { originInputDigest: projected.result.inputDigest, originSourceDigest: projected.sourceDigest,
          sourceDigest: snapshot.sourceDigest, projectionDigest: snapshot.projection!.digest },
      });
      return done(reused, true);
    }
    try {
      const checked = await checkLeanType({ projectRoot: snapshot.project, file: input.task.proofPath!,
        context: snapshot.context!, type: input.task.type!, env: snapshot.environment.env,
        signal: input.signal, timeoutMs: input.timeoutMs });
      if (!snapshot.current() || checked.sourceSnapshotDigest !== snapshot.sourceDigest || checked.projectionDigest !== snapshot.projection!.digest)
        return done(result('unavailable', 'type-input-changed-during-check'));
      let value: TaskTypePreflight;
      if (checked.status === 'elaborated') value = result('elaborated', 'closed-type-elaborated', { type: checked.type, artifact: checked.artifact });
      else if (checked.exitCode === 1 && !checked.timedOut && !('aborted' in checked && checked.aborted) &&
          checked.phases.at(-1)?.file === 'TypeDiagnostic.lean' && checked.firstBlocking?.format === 'lean-json' &&
          checked.firstBlocking.file && path.basename(checked.firstBlocking.file) === 'TypeDiagnostic.lean' &&
          definiteTypeError(checked.firstBlocking.message) &&
          checked.diagnosticArtifacts.length > 0 && checked.diagnosticArtifacts.every(item => item.captureComplete === true)) {
        value = result(snapshot.environment.reusable ? 'invalid' : 'deferred',
          renderLeanDiagnosticMessage(checked.firstBlocking), { artifact: checked.artifact });
      } else value = result(checked.exitCode === 1 && !checked.timedOut ? 'deferred' : 'unavailable',
        checked.firstBlocking ? renderLeanDiagnosticMessage(checked.firstBlocking) : 'type-check-inconclusive', { artifact: checked.artifact });
      if (snapshot.environment.reusable && ['elaborated', 'invalid'].includes(value.status) && artifactCurrent(snapshot.project, value.artifact)) {
        this.remember(snapshot.key, value, snapshot.sourceDigest, value.status === 'elaborated' ? snapshot.projectionKey : undefined);
      }
      return done(value);
    } catch {
      return done(result('unavailable', input.signal?.aborted ? 'type-check-aborted' : 'type-check-or-environment-unavailable'));
    }
  }
}
