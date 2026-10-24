import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { LAKE_CONFIGURATION_FILES, mathLocalModuleBuildOrder } from './mathConstructionSources';
import { resolveMathProofEnvironment } from './mathProofEnvironment';
import { canonicalMathJson, mathDigest, readMathFile } from './mathRuntimeIo';
import { assertMathCanonicalPath } from './paths';

type Module = { file: string; sourceRoot: string; module: string };
type Input = { projectRoot: string; modules: readonly Module[]; trustedFiles: Readonly<Record<string, string>>;
  env: NodeJS.ProcessEnv; toolIdentity: (projectRoot: string) => string | undefined; signal?: AbortSignal };
type Compilation = { started: boolean; exitCode: number | null; timedOut: boolean; aborted?: boolean;
  errorCode?: string; stdout: string; stderr: string; durationMs: number };
type Artifact = { file: string; sha256: string | null; bytes: number };
type Entry = { directory: string; artifacts: Artifact[]; bytes: number; stdout: string; stderr: string };

const outputs = (module: Module) => {
  const output = `.lake/build/lib/lean/${path.posix.relative(module.sourceRoot, module.file).replace(/\.lean$/u, '.olean')}`;
  return [output, output + '.private', output + '.server', output.replace(/\.olean$/u, '.ir'), output.replace(/\.olean$/u, '.ir.sig')];
};

function snapshot(input: Input) {
  if (!input.modules.length || input.env.LEAN_PATH?.trim() || input.env.LEAN_SYSROOT?.trim()) return;
  // The supported task environment uses a frozen TOML configuration, not an executable Lake script.
  if (!fs.existsSync(path.join(input.projectRoot, 'lakefile.toml')) || fs.existsSync(path.join(input.projectRoot, 'lakefile.lean'))) return;
  const sealed = resolveMathProofEnvironment(input.projectRoot, input.env), tools = input.toolIdentity(input.projectRoot);
  if (!sealed || !tools) return;
  const closure = mathLocalModuleBuildOrder(input.projectRoot, input.modules.map(module => module.file));
  if (canonicalMathJson(closure) !== canonicalMathJson(input.modules)) return;
  const sources = input.modules.map(module => {
    const bytes = readMathFile(path.join(input.projectRoot, module.file)).bytes;
    if (mathDigest(bytes) !== input.trustedFiles[module.file]) throw new Error('math_fixed_dependency_source_not_trusted');
    return { ...module, bytes, sha256: mathDigest(bytes) };
  });
  const files = sources.flatMap(outputs);
  if (new Set(files).size !== files.length) return;
  const configuration = LAKE_CONFIGURATION_FILES.filter(file => file !== '.lake/package-overrides.json').map(file => {
    try { return { file, bytes: readMathFile(path.join(input.projectRoot, file)).bytes }; }
    catch (error) { if ((error as NodeJS.ErrnoException).code === 'ENOENT') return { file, bytes: null }; throw error; }
  });
  const environment = Object.fromEntries(['PATH', 'LANG', 'LC_ALL', 'ELAN_HOME', 'LAKE_HOME', 'LEAN_PATH', 'LEAN_SYSROOT',
    'DEEPSCIENTIST_MATH_SANDBOX_BACKEND', 'DEEPSCIENTIST_MATH_SANDBOX_IMAGE', 'DEEPSCIENTIST_TEST_LEAN_AXIOMS']
    .map(name => [name, input.env[name] ?? null]));
  const key = mathDigest(canonicalMathJson({ schema: 'theorem-os.fixed-lean-dependencies.v1',
    profile: 'sealed-dependency-only;lean-j1-R-o;no-target-sources', packages: sealed.identity, tools, environment,
    configuration: configuration.map(({ file, bytes }) => [file, bytes && mathDigest(bytes)]),
    sources: sources.map(({ file, sourceRoot, module, sha256 }) => ({ file, sourceRoot, module, sha256 })) }));
  return { key, sources, configuration };
}

/** Process-owned dependency artifacts. No worker path or serialized metadata can publish an entry. */
export class FixedLeanDependencyCache {
  private readonly entries = new Map<string, Entry>();
  private root?: string;
  private bytes = 0;
  constructor(private readonly maxBytes = 512 * 1024 * 1024) {}
  private readonly cleanup = () => { if (this.root) fs.rmSync(this.root, { recursive: true, force: true }); };
  dispose() { this.cleanup(); this.root = undefined; this.entries.clear(); this.bytes = 0; process.off('exit', this.cleanup); }
  private directory() {
    if (!this.root) {
      this.root = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'math-fixed-dependencies-')));
      fs.chmodSync(this.root, 0o700); process.once('exit', this.cleanup);
    }
    return fs.mkdtempSync(path.join(this.root, 'entry-'));
  }
  private restore(entry: Entry, project: string) {
    // Read and verify the complete set before exposing any artifact to a target sandbox.
    const files = entry.artifacts.map(artifact => {
      if (artifact.sha256 === null) return { ...artifact, data: null };
      const data = readMathFile(path.join(entry.directory, artifact.file), artifact.bytes).bytes;
      if (data.length !== artifact.bytes || mathDigest(data) !== artifact.sha256) throw new Error('math_fixed_dependency_artifact_changed');
      return { ...artifact, data };
    });
    for (const { file, data } of files) {
      const output = path.join(project, file); assertMathCanonicalPath(output);
      if (data) { fs.mkdirSync(path.dirname(output), { recursive: true }); fs.writeFileSync(output, data, { mode: 0o600 }); }
      else fs.rmSync(output, { force: true });
    }
  }
  private clearRestored(input: Input) {
    for (const file of input.modules.flatMap(outputs)) {
      const output = path.join(input.projectRoot, file);
      assertMathCanonicalPath(path.dirname(output)); fs.rmSync(output, { force: true });
    }
  }
  async prepare<T extends Compilation>(input: Input, compile: (project: string) => Promise<T>): Promise<
    { kind: 'ready'; hit: boolean; stdout: string; stderr: string; durationMs: number } |
    { kind: 'failed'; result: T } | undefined> {
    input.signal?.throwIfAborted();
    let before: ReturnType<typeof snapshot>;
    try { before = snapshot(input); } catch { return; }
    if (!before) return;
    const cached = this.entries.get(before.key);
    if (cached) {
      try {
        this.restore(cached, input.projectRoot);
        if (snapshot(input)?.key !== before.key) { this.clearRestored(input); return; }
        this.entries.delete(before.key); this.entries.set(before.key, cached);
        return { kind: 'ready', hit: true, stdout: cached.stdout, stderr: cached.stderr, durationMs: 0 };
      } catch {
        try { this.clearRestored(input); } catch { /* The original compiler remains authoritative. */ }
        this.entries.delete(before.key); this.bytes -= cached.bytes;
        try { fs.rmSync(cached.directory, { recursive: true, force: true }); } catch { /* Retried at process exit. */ }
      }
    }
    let directory: string | undefined, retained = false, restoring = false;
    try {
      directory = this.directory();
      const project = path.join(directory, 'project');
      for (const { file, bytes } of [...before.configuration, ...before.sources]) if (bytes) {
        const output = path.join(project, file); fs.mkdirSync(path.dirname(output), { recursive: true }); fs.writeFileSync(output, bytes);
      }
      const result = await compile(project);
      input.signal?.throwIfAborted();
      if (result.exitCode !== 0 || result.timedOut || result.aborted || !result.started || result.errorCode) return { kind: 'failed', result };
      if (snapshot(input)?.key !== before.key || snapshot({ ...input, projectRoot: project })?.key !== before.key) return;
      const artifacts: Artifact[] = [];
      for (const module of input.modules) for (const file of outputs(module)) {
        try {
          const source = path.join(project, file); assertMathCanonicalPath(source);
          const data = readMathFile(source).bytes;
          const output = path.join(directory, file); fs.mkdirSync(path.dirname(output), { recursive: true }); fs.writeFileSync(output, data, { mode: 0o400 });
          artifacts.push({ file, sha256: mathDigest(data), bytes: data.length });
        } catch (error) {
          if ((error as NodeJS.ErrnoException).code !== 'ENOENT' || file.endsWith('.olean')) throw error;
          artifacts.push({ file, sha256: null, bytes: 0 });
        }
      }
      const entry: Entry = { directory, artifacts, bytes: artifacts.reduce((sum, item) => sum + item.bytes, 0), stdout: result.stdout, stderr: result.stderr };
      restoring = true;
      this.restore(entry, input.projectRoot);
      if (snapshot(input)?.key !== before.key) { this.clearRestored(input); return; }
      fs.rmSync(project, { recursive: true, force: true });
      if (entry.bytes <= this.maxBytes) {
        const replaced = this.entries.get(before.key);
        if (replaced) {
          this.entries.delete(before.key); this.bytes -= replaced.bytes;
          fs.rmSync(replaced.directory, { recursive: true, force: true });
        }
        while (this.entries.size && this.bytes + entry.bytes > this.maxBytes) {
          const [key, oldest] = this.entries.entries().next().value!;
          this.entries.delete(key); this.bytes -= oldest.bytes; fs.rmSync(oldest.directory, { recursive: true, force: true });
        }
        this.entries.set(before.key, entry); this.bytes += entry.bytes; retained = true;
      }
      return { kind: 'ready', hit: false, stdout: entry.stdout, stderr: entry.stderr, durationMs: result.durationMs };
    } catch (error) {
      if (input.signal?.aborted) throw error;
      // Artifact reuse is optional. The caller still compiles the complete closure on a miss.
      if (restoring) try { this.clearRestored(input); } catch { /* The original compiler remains authoritative. */ }
      return;
    } finally {
      if (!retained && directory) try { fs.rmSync(directory, { recursive: true, force: true }); } catch { /* Retried at process exit. */ }
    }
  }
}

export const fixedLeanDependencyCache = new FixedLeanDependencyCache();
