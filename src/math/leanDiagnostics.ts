import fs from 'node:fs';
import path from 'node:path';
import { spawn } from 'node:child_process';
import { assertMathConstructionSources, mathLocalModuleBuildOrder } from './mathConstructionSources';
import { assertMathCanonicalPath } from './paths';
import { mathDigest } from './mathRuntimeIo';
import { runMathematicsSandboxedCommand } from './verifier';
import { resolveMathematicsRuntimeEnvironment } from './mathRuntimeEnvironment';
import { acquireMathProofEnvironmentLease, resolveMathProofEnvironment, MATH_PROOF_ENVIRONMENT_SANDBOX_ENV } from './mathProofEnvironment';
import { checkResolvedLeanToolchainReadiness } from './leanToolchainReadiness';

/** Advisory checks already inside the host's isolated worker must not nest a namespace sandbox. */
async function runWorkerLean(project: string, module: { file: string; sourceRoot: string }, output: string,
  env: NodeJS.ProcessEnv, timeoutMs: number, signal?: AbortSignal) {
  const lease = await acquireMathProofEnvironmentLease(project, env, signal, Date.now() + timeoutMs);
  if (!lease) throw new Error('math_diagnostics_worker_environment_missing');
  try {
    const readiness = checkResolvedLeanToolchainReadiness({ projectRoot: project, env });
    if (readiness.status !== 'ready' || !readiness.leanPath) throw new Error('math_diagnostics_lean_unavailable');
    const libraries = [path.join(project, '.lake/build/lib/lean'),
      ...fs.readdirSync(lease.packagesRoot).map(name => path.join(lease.packagesRoot, name, '.lake/build/lib/lean'))]
      .filter(file => fs.existsSync(file));
    fs.mkdirSync(path.dirname(path.join(project, output)), { recursive: true });
    signal?.throwIfAborted();
    const startedAt = Date.now();
    return await new Promise<{ started: boolean; exitCode: number | null; timedOut: boolean; aborted: boolean;
      durationMs: number; stdout: string; stderr: string }>(resolve => {
      const child = spawn(readiness.leanPath!, ['-j1', '-R', module.sourceRoot, '-o', output, module.file], {
        cwd: project, env: { ...env, LEAN_PATH: libraries.join(path.delimiter), LEAN_NUM_THREADS: '1' },
        detached: true, stdio: ['ignore', 'pipe', 'pipe'],
      });
      let stdout = Buffer.alloc(0), stderr = Buffer.alloc(0), timedOut = false, aborted = false, started = false;
      const capture = (previous: Buffer, chunk: Buffer) => Buffer.concat([previous, chunk.subarray(0, Math.max(0, 8000 - previous.length))]);
      child.stdout.on('data', chunk => { stdout = capture(stdout, chunk); });
      child.stderr.on('data', chunk => { stderr = capture(stderr, chunk); });
      child.once('spawn', () => { started = true; if (signal?.aborted) abort(); });
      child.once('error', error => { stderr = capture(stderr, Buffer.from(error.message)); });
      const stop = () => { if (child.pid) { try { process.kill(-child.pid, 'SIGKILL'); } catch { /* Already exited. */ } } };
      const abort = () => { aborted = true; stop(); };
      signal?.addEventListener('abort', abort, { once: true });
      const timer = Number.isFinite(timeoutMs) ? setTimeout(() => { timedOut = true; stop(); }, timeoutMs) : undefined;
      child.once('close', exitCode => {
        clearTimeout(timer); signal?.removeEventListener('abort', abort);
        resolve({ started, exitCode, timedOut, aborted, durationMs: Date.now() - startedAt,
          stdout: stdout.toString('utf8'), stderr: stderr.toString('utf8') });
      });
    });
  } finally { await lease.release(); }
}

/** Local diagnostics are advisory; final acceptance still requires the independent verifier. */
export async function runLeanDiagnostics(input: {
  projectRoot: string; files: readonly string[]; env?: NodeJS.ProcessEnv; signal?: AbortSignal;
  timeoutMs: number; dependenciesOnly?: boolean; excludedFiles?: readonly string[];
  onProgress?: (file: string) => void;
}) {
  const project = fs.realpathSync(input.projectRoot);
  const env = resolveMathematicsRuntimeEnvironment(input.env || process.env);
  assertMathConstructionSources(project, input.files);
  const modules = [...new Map(input.files.flatMap(file => mathLocalModuleBuildOrder(project, file))
    .map(module => [module.file, module])).values()];
  const excluded = new Set(input.excludedFiles ?? []);
  const cacheFile = path.join(project, '.lake', 'lean-diagnostics.json');
  assertMathCanonicalPath(cacheFile);
  let cache: Record<string, { source: string; output: string; stdout?: string; stderr?: string }> = {};
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
    resolveMathProofEnvironment(project, env)?.identity, env.PATH, env.ELAN_HOME, env.LEAN_PATH, env.LEAN_SYSROOT,
  ]));
  const sourceIdentity = () => mathDigest(JSON.stringify([configuration(), modules.map(module =>
    [module.file, mathDigest(fs.readFileSync(path.join(project, module.file)))])]));
  const sourceDigest = sourceIdentity();
  const sources: string[] = [];
  const deadline = Date.now() + input.timeoutMs;
  const phases: { file: string; cached: boolean; durationMs: number; exitCode: number | null }[] = [];
  const cap = (text: string) => Buffer.from(text).subarray(0, 8000).toString('utf8');
  let stdout = '', stderr = '';
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
    if (saved?.source === digest && fs.existsSync(absoluteOutput) &&
      saved.output === mathDigest(fs.readFileSync(absoluteOutput))) {
      phases.push({ file: module.file, cached: true, durationMs: 0, exitCode: 0 });
      stdout = cap(stdout + (typeof saved.stdout === 'string' ? saved.stdout : ''));
      stderr = cap(stderr + (typeof saved.stderr === 'string' ? saved.stderr : ''));
      continue;
    }
    input.onProgress?.(module.file);
    const remainingMs = deadline - Date.now();
    if (remainingMs <= 0) return { exitCode: null, timedOut: true, stdout, stderr, phases };
    const result = env[MATH_PROOF_ENVIRONMENT_SANDBOX_ENV]
      ? await runWorkerLean(project, module, output, env, remainingMs, input.signal)
      : await runMathematicsSandboxedCommand({ checkoutRoot: project, command: 'lake',
      args: ['env', '/bin/sh', '-ceu', `mkdir -p ${quote(path.posix.dirname(output))}\nexec lean -j1 -R ${quote(module.sourceRoot)} -o ${quote(output)} ${quote(module.file)}`],
      env, signal: input.signal, timeoutMs: remainingMs, outputCapture: 'head' });
    phases.push({ file: module.file, cached: false, durationMs: result.durationMs, exitCode: result.exitCode });
    if (sourceIdentity() !== sourceDigest) return { exitCode: 1, timedOut: false,
      stdout: cap(result.stdout), stderr: 'math_diagnostics_source_changed: saved sources changed during compilation',
      sourceDigest, phases };
    stdout = cap(stdout + result.stdout); stderr = cap(stderr + result.stderr);
    if (result.exitCode !== 0 || result.timedOut || result.aborted || !result.started) return {
      ...result, stdout: cap(result.stdout), stderr: cap(result.stderr), sourceDigest, phases,
    };
    if (fs.existsSync(absoluteOutput)) {
      cache[module.file] = { source: digest, output: mathDigest(fs.readFileSync(absoluteOutput)),
        stdout: cap(result.stdout), stderr: cap(result.stderr) };
      fs.mkdirSync(path.dirname(cacheFile), { recursive: true });
      fs.writeFileSync(cacheFile, JSON.stringify(cache) + '\n', { mode: 0o600 });
    }
  }
  if (sourceIdentity() !== sourceDigest) return { exitCode: 1, timedOut: false, stdout,
    stderr: 'math_diagnostics_source_changed: saved sources changed during diagnostics', sourceDigest, phases };
  return { exitCode: 0, timedOut: false, stdout, stderr, sourceDigest, phases };
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
