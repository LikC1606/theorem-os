import fs from 'node:fs';
import path from 'node:path';
import { limitMathOutput, runLeanProcess } from './mathProcess';
import { assertMathConstructionSources, mathLocalModuleBuildOrder } from './mathConstructionSources';
import { assertMathCanonicalPath } from './paths';
import { canonicalMathJson, mathDigest, writeMathJsonDurable } from './mathRuntimeIo';
import { runMathematicsSandboxedCommand } from './verifier';
import { resolveMathematicsRuntimeEnvironment } from './mathRuntimeEnvironment';
import { acquireMathProofEnvironmentLease, resolveMathProofEnvironment, MATH_PROOF_ENVIRONMENT_SANDBOX_ENV } from './mathProofEnvironment';
import { checkResolvedLeanToolchainReadiness } from './leanToolchainReadiness';
import { parseLeanDiagnosticOutput, renderLeanDiagnosticOutput } from './leanDiagnosticMessages';
import type { LeanDiagnosticArtifactReference, LeanDiagnosticMessage } from './leanTypes';

const DIAGNOSTIC_CAPTURE_LIMIT = 4_000_000;
type DiagnosticCacheRecord = { source: string; output: string; stdout?: string; stderr?: string;
  diagnosticArtifact?: LeanDiagnosticArtifactReference; messages?: LeanDiagnosticMessage[] };

/** Advisory checks already inside the host's isolated worker must not nest a namespace sandbox. */
async function runWorkerLean(project: string, module: { file: string; sourceRoot: string }, output: string,
  env: NodeJS.ProcessEnv, timeoutMs: number, signal: AbortSignal | undefined, outputLimit: number) {
  const startedAt = Date.now(), deadlineAt = startedAt + timeoutMs;
  const stopped = () => ({ started: false, exitCode: null, timedOut: !signal?.aborted, aborted: Boolean(signal?.aborted),
    durationMs: Date.now() - startedAt, stdout: '', stderr: '' });
  let lease;
  try { lease = await acquireMathProofEnvironmentLease(project, env, signal, deadlineAt); }
  catch (error) {
    if (signal?.aborted || (error instanceof Error && error.name === 'TimeoutError')) return stopped();
    throw error;
  }
  if (!lease) throw new Error('math_diagnostics_worker_environment_missing');
  try {
    if (signal?.aborted || Date.now() >= deadlineAt) return stopped();
    const readiness = checkResolvedLeanToolchainReadiness({ projectRoot: project, env, timeoutMs: Math.min(10_000, deadlineAt - Date.now()) });
    if (signal?.aborted || Date.now() >= deadlineAt) return stopped();
    if (readiness.status !== 'ready' || !readiness.leanPath) throw new Error('math_diagnostics_lean_unavailable');
    const libraries = [path.join(project, '.lake/build/lib/lean'),
      ...fs.readdirSync(lease.packagesRoot).map(name => path.join(lease.packagesRoot, name, '.lake/build/lib/lean'))]
      .filter(file => fs.existsSync(file));
    fs.mkdirSync(path.dirname(path.join(project, output)), { recursive: true });
    signal?.throwIfAborted();
    const result = await runLeanProcess(readiness.leanPath!, ['--json', '-j1', '-R', module.sourceRoot, '-o', output, module.file], {
      cwd: project, env: { ...env, LEAN_PATH: libraries.join(path.delimiter), LEAN_NUM_THREADS: '1' },
      timeoutMs: Math.max(0, deadlineAt - Date.now()), signal, outputCapture: 'head', outputLimit, stopGraceMs: 0,
    });
    const cap = (text: string) => limitMathOutput(text, outputLimit, 'head');
    return { ...result, started: result.started && !result.errorCode, durationMs: Date.now() - startedAt,
      stdout: cap(result.stdout), stderr: cap(result.stderr + (result.errorMessage ?? '')) };
  } finally { await lease.release(); }
}

/** Local diagnostics are advisory; final acceptance still requires the independent verifier. */
export async function runLeanDiagnostics(input: {
  projectRoot: string; files: readonly string[]; env?: NodeJS.ProcessEnv; signal?: AbortSignal;
  timeoutMs: number; dependenciesOnly?: boolean; excludedFiles?: readonly string[];
  onProgress?: (file: string) => void;
  /** Host projections retain a larger diagnostic window than ordinary model prompts. */
  outputLimit?: number;
}) {
  const outputLimit = input.outputLimit ?? 8000;
  if (!Number.isSafeInteger(outputLimit) || outputLimit < 1 || outputLimit > 4_000_000)
    throw new Error('math_diagnostics_output_limit_invalid');
  const project = fs.realpathSync(input.projectRoot);
  const env = resolveMathematicsRuntimeEnvironment(input.env || process.env);
  assertMathConstructionSources(project, input.files);
  const modules = mathLocalModuleBuildOrder(project, input.files);
  const excluded = new Set(input.excludedFiles ?? []);
  const cacheFile = path.join(project, '.lake', 'lean-diagnostics.json');
  assertMathCanonicalPath(cacheFile);
  let cache: Record<string, DiagnosticCacheRecord> = {};
  try {
    const saved = JSON.parse(fs.readFileSync(cacheFile, 'utf8'));
    if (saved && typeof saved === 'object' && !Array.isArray(saved)) cache = saved;
  } catch { /* Missing or stale advisory cache. */ }
  const configuration = () => ['lean-toolchain', 'lakefile.toml', 'lakefile.lean', 'lake-manifest.json', '.lake/package-overrides.json'].map(file => {
    const absolute = path.join(project, file);
    return fs.existsSync(absolute) ? mathDigest(fs.readFileSync(absolute)) : '';
  });
  const config = configuration();
  const environmentIdentity = mathDigest(JSON.stringify([
    'lean-json-diagnostics.v1', resolveMathProofEnvironment(project, env)?.identity, env.PATH, env.ELAN_HOME, env.LEAN_PATH, env.LEAN_SYSROOT,
  ]));
  const sourceFiles = () => modules.map(module => [module.file, mathDigest(fs.readFileSync(path.join(project, module.file)))]);
  const initialSources = sourceFiles();
  const sourceIdentity = () => mathDigest(JSON.stringify([configuration(), sourceFiles()]));
  const sourceDigest = sourceIdentity();
  const sources: string[] = [];
  const deadline = Date.now() + input.timeoutMs;
  const phases: { file: string; cached: boolean; durationMs: number; exitCode: number | null }[] = [];
  const cap = (text: string) => {
    if (Buffer.byteLength(text) <= outputLimit) return text;
    const notice = '\n[truncated; inspect diagnosticArtifacts for captured output and completeness]';
    return limitMathOutput(text, Math.max(0, outputLimit - Buffer.byteLength(notice)), 'head') +
      limitMathOutput(notice, outputLimit, 'head');
  };
  const artifactDigest = (output: string) => mathDigest(JSON.stringify([
    output, output + '.private', output + '.server', output.replace(/\.olean$/u, '.ir'), output.replace(/\.olean$/u, '.ir.sig'),
  ].map(file => {
    assertMathCanonicalPath(file);
    return fs.existsSync(file) ? mathDigest(fs.readFileSync(file)) : null;
  })));
  let stdout = '', stderr = '';
  const messages: LeanDiagnosticMessage[] = [], diagnosticArtifacts: LeanDiagnosticArtifactReference[] = [];
  const captured = (reference: LeanDiagnosticArtifactReference) => {
    try {
      if (!reference || typeof reference.digest !== 'string' || !/^[a-f0-9]{64}$/u.test(reference.digest) ||
          reference.path !== `.lake/diagnostic-artifacts/${reference.digest}.json` || reference.environmentDigest !== environmentIdentity) return false;
      const file = path.join(project, reference.path); assertMathCanonicalPath(file);
      const text = fs.readFileSync(file, 'utf8');
      return mathDigest(text) === reference.digest;
    } catch { return false; }
  };
  const messagePreview = (message: LeanDiagnosticMessage) => ({ ...message, message: cap(message.message),
    ...(message.goalText ? { goalText: cap(message.goalText) } : {}), truncated: Buffer.byteLength(message.message) > outputLimit });
  const summary = () => {
    const firstBlocking = messages.find(message => message.severity === 'error');
    const selected: ReturnType<typeof messagePreview>[] = [];
    let bytes = 0;
    for (const message of messages.slice(0, 64)) {
      const preview = messagePreview(message), size = Buffer.byteLength(JSON.stringify(preview));
      if (bytes + size > outputLimit) break;
      selected.push(preview); bytes += size;
    }
    return { sourceDigest, environmentDigest: environmentIdentity,
      firstBlocking: firstBlocking && messagePreview(firstBlocking), messages: selected,
      omittedMessages: messages.length - selected.length, diagnosticArtifacts,
      previewTruncated: selected.length < messages.length || Boolean(firstBlocking && Buffer.byteLength(firstBlocking.message) > outputLimit) ||
        diagnosticArtifacts.some(reference => reference.captureComplete === false) || /\[truncated;/u.test(stdout + stderr) };
  };
  const retain = (file: string, result: { stdout: string; stderr: string; stdoutSha256?: string; stderrSha256?: string;
    exitCode: number | null; timedOut: boolean; aborted?: boolean }) => {
    const capturedComplete = (text: string, hash?: string) => hash ? mathDigest(text) === hash : null;
    const complete = [capturedComplete(result.stdout, result.stdoutSha256), capturedComplete(result.stderr, result.stderrSha256)];
    const captureComplete = complete.includes(false) ? false : complete.includes(null) ? null : true;
    const observed = [...parseLeanDiagnosticOutput(result.stdout).messages, ...parseLeanDiagnosticOutput(result.stderr).messages];
    const artifact = { schema: 'theoremos.lean-diagnostics.v1', authority: 'advisory-lean-process', sourceDigest,
      environmentDigest: environmentIdentity, file, sourceCurrent: sourceIdentity() === sourceDigest,
      sourceFiles: initialSources.map(([file, digest]) => ({ file, digest })),
      exitCode: result.exitCode, timedOut: result.timedOut, aborted: result.aborted ?? false,
      captureComplete, captureLimit: DIAGNOSTIC_CAPTURE_LIMIT,
      stdout: result.stdout, stderr: result.stderr, stdoutSha256: result.stdoutSha256 ?? null, stderrSha256: result.stderrSha256 ?? null,
      messages: observed };
    const text = canonicalMathJson(artifact), digest = mathDigest(text), relative = `.lake/diagnostic-artifacts/${digest}.json`;
    const artifactFile = path.join(project, relative); assertMathCanonicalPath(artifactFile);
    fs.mkdirSync(path.dirname(artifactFile), { recursive: true, mode: 0o700 });
    writeMathJsonDurable(artifactFile, artifact);
    const reference = { path: relative, digest, sourceDigest, environmentDigest: environmentIdentity, captureComplete };
    diagnosticArtifacts.push(reference); messages.push(...observed);
    return { reference, observed };
  };
  const quote = (value: string) => "'" + value.replaceAll("'", "'\\''") + "'";
  for (const module of modules) {
    input.signal?.throwIfAborted();
    sources.push(mathDigest(fs.readFileSync(path.join(project, module.file))));
    if (input.dependenciesOnly && (input.files.includes(module.file) || excluded.has(module.file))) continue;
    const output = `.lake/build/lib/lean/${path.posix.relative(module.sourceRoot, module.file).replace(/\.lean$/u, '.olean')}`;
    const absoluteOutput = path.join(project, output);
    assertMathCanonicalPath(absoluteOutput);
    const digest = mathDigest(JSON.stringify([environmentIdentity, config, sources]));
    const saved = cache[module.file];
    if (saved?.source === digest && fs.existsSync(absoluteOutput) && saved.output === artifactDigest(absoluteOutput) &&
        saved.diagnosticArtifact && captured(saved.diagnosticArtifact)) {
      phases.push({ file: module.file, cached: true, durationMs: 0, exitCode: 0 });
      stdout = cap(stdout + cap(typeof saved.stdout === 'string' ? saved.stdout : ''));
      stderr = cap(stderr + cap(typeof saved.stderr === 'string' ? saved.stderr : ''));
      diagnosticArtifacts.push(saved.diagnosticArtifact); messages.push(...(saved.messages ?? []));
      sources.push(saved.output);
      continue;
    }
    input.onProgress?.(module.file);
    const remainingMs = deadline - Date.now();
    if (remainingMs <= 0) return { exitCode: null, timedOut: true, stdout, stderr, phases, ...summary() };
    const result = env[MATH_PROOF_ENVIRONMENT_SANDBOX_ENV]
      ? await runWorkerLean(project, module, output, env, remainingMs, input.signal, DIAGNOSTIC_CAPTURE_LIMIT)
      : await runMathematicsSandboxedCommand({ checkoutRoot: project, command: 'lake',
      args: ['env', '/bin/sh', '-ceu', `mkdir -p ${quote(path.posix.dirname(output))}\nexec lean --json -j1 -R ${quote(module.sourceRoot)} -o ${quote(output)} ${quote(module.file)}`],
      env, signal: input.signal, timeoutMs: remainingMs, outputCapture: 'head', outputLimit: DIAGNOSTIC_CAPTURE_LIMIT });
    phases.push({ file: module.file, cached: false, durationMs: result.durationMs, exitCode: result.exitCode });
    const retained = retain(module.file, result);
    if (sourceIdentity() !== sourceDigest) return { exitCode: 1, timedOut: false,
      stdout: cap(renderLeanDiagnosticOutput(result.stdout)), stderr: 'math_diagnostics_source_changed: saved sources changed during compilation',
      phases, ...summary() };
    const moduleStdout = cap(renderLeanDiagnosticOutput(result.stdout)), moduleStderr = cap(renderLeanDiagnosticOutput(result.stderr));
    stdout = cap(stdout + moduleStdout); stderr = cap(stderr + moduleStderr);
    if (result.exitCode !== 0 || result.timedOut || result.aborted || !result.started) return {
      ...result, stdout: moduleStdout, stderr: moduleStderr, phases, ...summary(),
    };
    if (fs.existsSync(absoluteOutput)) {
      const artifact = artifactDigest(absoluteOutput);
      cache[module.file] = { source: digest, output: artifact,
        stdout: renderLeanDiagnosticOutput(result.stdout), stderr: renderLeanDiagnosticOutput(result.stderr),
        diagnosticArtifact: retained.reference, messages: retained.observed };
      sources.push(artifact);
      fs.mkdirSync(path.dirname(cacheFile), { recursive: true });
      fs.writeFileSync(cacheFile, JSON.stringify(cache) + '\n', { mode: 0o600 });
    }
  }
  if (sourceIdentity() !== sourceDigest) return { exitCode: 1, timedOut: false, stdout,
    stderr: 'math_diagnostics_source_changed: saved sources changed during diagnostics', phases, ...summary() };
  return { exitCode: 0, timedOut: false, stdout, stderr, phases, ...summary() };
}

/** Rebind an existing or broken package link without deleting a real package directory. */
export function bindLeanPackages(project: string, authorizedPackagesRoot: string): void {
  const root = fs.realpathSync(authorizedPackagesRoot);
  if (!fs.statSync(root).isDirectory()) throw new Error('math_lean_packages_not_directory');
  const packages = path.join(project, '.lake', 'packages');
  assertMathCanonicalPath(path.dirname(packages));
  fs.mkdirSync(path.dirname(packages), { recursive: true });
  const existing = fs.lstatSync(packages, { throwIfNoEntry: false });
  if (existing?.isSymbolicLink()) {
    if (path.resolve(path.dirname(packages), fs.readlinkSync(packages)) === root) return;
    fs.unlinkSync(packages);
  } else if (existing) {
    if (!existing.isDirectory()) throw new Error('math_lean_packages_not_directory');
    return;
  }
  fs.symlinkSync(root, packages, 'dir');
}

/** Make ordinary model-side Lake commands consume the pinned packages without Git refreshes. */
export function prepareLeanDiagnosticOverrides(project: string): void {
  const manifestFile = path.join(project, 'lake-manifest.json');
  if (!fs.existsSync(manifestFile)) return;
  const manifest = JSON.parse(fs.readFileSync(manifestFile, 'utf8'));
  const packages = manifest.packages.map((entry: { name: string }) => {
    const name = entry.name.replace(/^«(.+)»$/u, '$1');
    if (!name || /[/\\\0]/u.test(name) || name === '.' || name === '..') throw new Error('math_invalid_package_name');
    return { ...entry, type: 'path', dir: path.join(project, '.lake', 'packages', name) };
  });
  const file = path.join(project, '.lake', 'package-overrides.json');
  assertMathCanonicalPath(file);
  fs.mkdirSync(path.dirname(file), { recursive: true });
  fs.writeFileSync(file, JSON.stringify({ schemaVersion: '1.2.0', packages }) + '\n', { mode: 0o600 });
}
