import fs from 'node:fs';
import path from 'node:path';
import { assertMathConstructionSources, mathLocalModuleBuildOrder } from './mathConstructionSources';
import { assertMathCanonicalPath } from './paths';
import { mathDigest } from './mathRuntimeIo';
import { runMathematicsSandboxedCommand } from './verifier';

/** Local diagnostics are advisory; final acceptance still requires the independent verifier. */
export async function runLeanDiagnostics(input: {
  projectRoot: string; files: readonly string[]; env?: NodeJS.ProcessEnv; signal?: AbortSignal;
  timeoutMs: number; dependenciesOnly?: boolean; excludedFiles?: readonly string[];
  onProgress?: (file: string) => void;
}) {
  const project = fs.realpathSync(input.projectRoot);
  assertMathConstructionSources(project, input.files);
  const modules = [...new Map(input.files.flatMap(file => mathLocalModuleBuildOrder(project, file))
    .map(module => [module.file, module])).values()];
  const excluded = new Set(input.excludedFiles ?? []);
  const cacheFile = path.join(project, '.lake', 'lean-diagnostics.json');
  assertMathCanonicalPath(cacheFile);
  let cache: Record<string, { source: string; output: string }> = {};
  try {
    const saved = JSON.parse(fs.readFileSync(cacheFile, 'utf8'));
    if (saved && typeof saved === 'object' && !Array.isArray(saved)) cache = saved;
  } catch { /* Missing or stale advisory cache. */ }
  const config = ['lean-toolchain', 'lakefile.toml', 'lakefile.lean', 'lake-manifest.json'].map(file => {
    const absolute = path.join(project, file);
    return fs.existsSync(absolute) ? mathDigest(fs.readFileSync(absolute)) : '';
  });
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
    const digest = mathDigest(JSON.stringify([config, sources]));
    const saved = cache[module.file];
    if (!input.files.includes(module.file) && saved?.source === digest && fs.existsSync(absoluteOutput) &&
      saved.output === mathDigest(fs.readFileSync(absoluteOutput))) {
      phases.push({ file: module.file, cached: true, durationMs: 0, exitCode: 0 });
      continue;
    }
    input.onProgress?.(module.file);
    const remainingMs = deadline - Date.now();
    if (remainingMs <= 0) return { exitCode: null, timedOut: true, stdout, stderr, phases };
    const result = await runMathematicsSandboxedCommand({ checkoutRoot: project, command: 'lake',
      args: ['env', '/bin/sh', '-ceu', `mkdir -p ${quote(path.posix.dirname(output))}\nexec lean -j1 -R ${quote(module.sourceRoot)} -o ${quote(output)} ${quote(module.file)}`],
      env: input.env, signal: input.signal, timeoutMs: remainingMs, outputCapture: 'head' });
    phases.push({ file: module.file, cached: false, durationMs: result.durationMs, exitCode: result.exitCode });
    stdout = cap(stdout + result.stdout); stderr = cap(stderr + result.stderr);
    if (result.exitCode !== 0 || result.timedOut || result.aborted || !result.started) return {
      ...result, stdout: cap(result.stdout), stderr: cap(result.stderr), phases,
    };
    if (fs.existsSync(absoluteOutput)) {
      cache[module.file] = { source: digest, output: mathDigest(fs.readFileSync(absoluteOutput)) };
      fs.mkdirSync(path.dirname(cacheFile), { recursive: true });
      fs.writeFileSync(cacheFile, JSON.stringify(cache) + '\n', { mode: 0o600 });
    }
  }
  return { exitCode: 0, timedOut: false, stdout, stderr, phases };
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
