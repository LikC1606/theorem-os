import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { stringify as stringifyToml } from 'smol-toml';
import { bootstrapLeanTask } from '../../src/math/leanTask';
import { getLeanTaskEnvironment } from '../../src/math/leanTaskEnvironment';
import { readMathJson, readMathText } from '../../src/math/mathRuntimeIo';
import { readMathBuildManifest } from '../../src/math/mathBuildManifest';
import { createCodexMathSession } from '../../src/runtime/codexSession';
import { sub2apiModelCatalog } from '../../src/runtime/sub2api';
import type { SolverModules } from '../../src/solver/modules';
import { configurableSolverModules } from '../../src/solver/modules/custom';
import { researchWorkers } from '../../src/solver/modules/organization';
import { runSolver } from '../../src/solver/run';
import { translateWebProgress } from './progress';
import { webArtifactMaxBytes, type WebArtifact, type WorkerInput, type WorkerMessage } from './shared';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '../..');
type WebWorkerState = {
  worktree: string;
  workers?: { id: string; worktree: string }[];
  check?: { passed: boolean; verification?: { status?: string; results?: Record<string, unknown>[] } };
};

function readCandidateSource(directory: string, file: string): { source: string; modifiedAt: number } | undefined {
  let descriptor: number | undefined;
  try {
    if (!file.startsWith(directory + path.sep)) return;
    const segments = path.relative(directory, file).split(path.sep);
    let current = directory;
    for (const [index, segment] of segments.entries()) {
      current = path.join(current, segment);
      const info = fs.lstatSync(current);
      if (info.isSymbolicLink() || (index < segments.length - 1 && !info.isDirectory())) return;
    }
    if (fs.realpathSync(file) !== file) return;
    descriptor = fs.openSync(file, fs.constants.O_RDONLY | fs.constants.O_NOFOLLOW | fs.constants.O_NONBLOCK);
    const before = fs.fstatSync(descriptor);
    if (!before.isFile() || before.nlink !== 1 || before.size < 1 || before.size > webArtifactMaxBytes) return;
    // Resolve the opened inode on Linux as well as the path, so directory swaps cannot escape the run.
    const openedPath = () => process.platform === 'linux' ? fs.realpathSync(`/proc/self/fd/${descriptor}`) : fs.realpathSync(file);
    if (openedPath() !== file) return;
    const buffer = Buffer.alloc(webArtifactMaxBytes + 1);
    let bytes = 0;
    while (bytes < buffer.length) {
      const count = fs.readSync(descriptor, buffer, bytes, buffer.length - bytes, null);
      if (!count) break;
      bytes += count;
    }
    const after = fs.fstatSync(descriptor), currentInfo = fs.lstatSync(file);
    if (bytes > webArtifactMaxBytes || bytes !== before.size || after.size !== before.size ||
      after.mtimeMs !== before.mtimeMs || after.ctimeMs !== before.ctimeMs ||
      currentInfo.isSymbolicLink() || currentInfo.ino !== after.ino || currentInfo.dev !== after.dev ||
      fs.realpathSync(file) !== file || openedPath() !== file) return;
    return { source: new TextDecoder('utf-8', { fatal: true }).decode(buffer.subarray(0, bytes)), modifiedAt: after.mtimeMs };
  } catch { return undefined; }
  finally { if (descriptor !== undefined) fs.closeSync(descriptor); }
}

export function createWebArtifactSampler(options: {
  directory: string; output: string; workers: number; source: string; apiKey: string;
  onArtifact(artifact: WebArtifact): void;
}) {
  const directory = fs.realpathSync(options.directory);
  const workers = researchWorkers(path.join(options.output + '.runtime', 'worktree'), [], options.workers);
  const previous = new Map(workers.map(worker => [worker.id, options.source]));
  let lastSource = options.source;
  return () => {
    let latest: { workerId: string; source: string; modifiedAt: number } | undefined;
    for (const worker of workers) {
      const candidate = readCandidateSource(directory, path.join(worker.worktree, 'generated/problem/Submission.lean'));
      if (!candidate || candidate.source === previous.get(worker.id)) continue;
      previous.set(worker.id, candidate.source);
      if (!latest || candidate.modifiedAt >= latest.modifiedAt) latest = { ...candidate, workerId: worker.id };
    }
    if (!latest || latest.source === lastSource) return;
    const source = options.apiKey ? latest.source.replaceAll(options.apiKey, '[REDACTED]') : latest.source;
    if (Buffer.byteLength(source) > webArtifactMaxBytes) return;
    lastSource = latest.source;
    options.onArtifact({ source, workerId: latest.workerId, capturedAt: new Date().toISOString(), status: 'candidate' });
  };
}

export function readWebResultProof(options: {
  directory: string; workspace: string; status: unknown; winningWorker: unknown;
  state?: WebWorkerState; artifact?: WebArtifact;
}): string {
  const accepted = options.status === 'evaluated_passed';
  const selected = typeof options.winningWorker === 'string' && options.winningWorker.length > 0;
  // A parallel attempt can finish before any winner exists while another worker has useful live source.
  if (!accepted && !selected && !options.state?.check?.passed && options.artifact) return options.artifact.source;
  if (!options.state) return '';
  const tree = accepted ? options.workspace :
    options.state.workers?.find(worker => worker.id === options.winningWorker)?.worktree ?? options.state.worktree;
  const file = path.resolve(tree, 'generated/problem/Submission.lean');
  if (file.startsWith(options.directory + path.sep)) {
    try { return readMathText(file, webArtifactMaxBytes); } catch { /* Rejected or oversized candidates have no downloadable source. */ }
  }
  return '';
}

export function webProviderConfig(input: WorkerInput, modelCatalog?: string): string {
  return stringifyToml({
    model: input.input.model, model_provider: 'web_provider', model_reasoning_effort: input.input.effort,
    ...(modelCatalog ? { model_catalog_json: modelCatalog,
      features: { multi_agent: false, multi_agent_v2: false, goals: false, view_image: false } } : {}),
    approval_policy: 'never', sandbox_mode: 'workspace-write',
    model_providers: { web_provider: { name: input.provider.name, base_url: input.provider.baseUrl,
      wire_api: 'responses', env_key: 'THEOREMOS_PROVIDER_API_KEY', requires_openai_auth: false,
      request_max_retries: 0, stream_max_retries: 0, stream_idle_timeout_ms: 60_000 } },
    shell_environment_policy: { inherit: 'all', exclude: ['THEOREMOS_PROVIDER_API_KEY'] },
    history: { persistence: 'none' }, analytics: { enabled: false },
  });
}

export function prepareWebProviderProfile(profile: string, request: WorkerInput): void {
  fs.mkdirSync(profile, { mode: 0o700 });
  const modelCatalog = request.provider.id === 'sub2api' ? path.join(profile, 'models.json') : undefined;
  if (modelCatalog) fs.writeFileSync(modelCatalog, JSON.stringify(sub2apiModelCatalog()), { mode: 0o600, flag: 'wx' });
  fs.writeFileSync(path.join(profile, 'config.toml'), webProviderConfig(request, modelCatalog), { mode: 0o600, flag: 'wx' });
}

export function webSolverModules(request: WorkerInput): SolverModules {
  const base = configurableSolverModules(request.input.modulePlan, request.input.coordination, request.input.workers);
  return { ...base, id: `${base.id}/web-byok-v1`,
    M1: { ...base.M1, version: `${base.M1.version}/web-byok-v1`,
      open: options => createCodexMathSession({ ...options,
        environment: { ...options.environment, THEOREMOS_PROVIDER_API_KEY: request.input.apiKey } }) } };
}

async function main() {
  let bytes = 0;
  const chunks: Buffer[] = [];
  for await (const chunk of process.stdin) {
    bytes += chunk.length;
    if (bytes > 180 * 1024) throw new Error('运行输入过大。');
    chunks.push(chunk);
  }
  const request = JSON.parse(new TextDecoder('utf-8', { fatal: true }).decode(Buffer.concat(chunks))) as WorkerInput;
  const key = request.input.apiKey;
  const send = (message: WorkerMessage) => process.stdout.write(
    JSON.stringify(message).replaceAll(JSON.stringify(key).slice(1, -1), '[REDACTED]') + '\n');
  const workspaceRoot = process.env.THEOREMOS_WORKER_ROOT || '/work';
  const directory = fs.mkdtempSync(path.join(workspaceRoot, 'run-'));
  const profile = path.join(directory, 'codex');
  prepareWebProviderProfile(profile, request);
  fs.mkdirSync(process.env.HOME || '/work/home', { recursive: true, mode: 0o700 });
  // Each container owns this profile. No machine profile or authentication file is read.
  process.env.CODEX_HOME = profile;
  process.env.DEEPSCIENTIST_MATH_ENV_FILE = path.join(directory, 'math.env');
  fs.writeFileSync(process.env.DEEPSCIENTIST_MATH_ENV_FILE, '', { mode: 0o400, flag: 'wx' });
  const originalLog = console.log;
  let sampleArtifact: (() => void) | undefined;
  let artifactTimer: ReturnType<typeof setInterval> | undefined;
  let latestArtifact: WebArtifact | undefined;
  console.log = (...args: unknown[]) => {
    for (const value of args) if (typeof value === 'string') {
      try {
        const event = JSON.parse(value);
        const progress = translateWebProgress(event);
        if (progress) send(progress);
        if (['turn_checkpoint', 'proof_check_started', 'candidate_selected', 'evaluation_started'].includes(event.event)) sampleArtifact?.();
      } catch { /* Unstructured runtime output stays private to this disposable container. */ }
    }
  };
  console.error = () => {};
  try {
    const environment = getLeanTaskEnvironment(request.input.environment ?? 'standard');
    const receipt = bootstrapLeanTask(path.join(directory, 'workspace'), {
      source: request.input.source, task: request.input.task, environment: environment.id });
    const buildIndex = readMathJson(process.env.THEOREMOS_WORKER_BUILD || '/opt/theoremos-build.json') as { buildManifestRef: string };
    readMathBuildManifest(buildIndex.buildManifestRef, root, path.join(root, 'out/main'));
    const taskFile = path.join(directory, 'task.md');
    fs.writeFileSync(taskFile, request.input.task + '\nPreserve all original declarations. Prove every target in generated/problem/Submission.lean.\n', { mode: 0o600 });
    const output = path.join(directory, 'result.json');
    sampleArtifact = createWebArtifactSampler({ directory, output, workers: request.input.workers,
      source: request.input.source, apiKey: key, onArtifact: artifact => {
        latestArtifact = artifact;
        send({ type: 'artifact', artifact });
      } });
    artifactTimer = setInterval(sampleArtifact, 1_500);
    const modules = webSolverModules(request);
    await runSolver(['--workspace', receipt.workspaceRoot, '--task-file', taskFile, '--output', output,
      '--receipt-file', receipt.activeProblemPath, '--build-manifest', buildIndex.buildManifestRef,
      '--model', request.input.model, '--effort', request.input.effort, '--workers', String(request.input.workers),
      '--coordination', request.input.coordination, '--max-turns', String(request.input.maxTurns),
      '--max-run-seconds', String(request.input.maxRunSeconds), '--max-turn-seconds', '120',
      '--prepare-timeout-seconds', environment.id === 'mathlib' ? '600' : '120',
      '--evaluator-timeout-seconds', '120'], root, modules);
    sampleArtifact();
    clearInterval(artifactTimer);
    const raw = readMathJson(output) as Record<string, unknown>;
    const report = Object.fromEntries(['schema', 'runId', 'problemId', 'status', 'solution_commit',
      'solver_ready_receipt_valid', 'completion_signal_valid', 'evaluator', 'turns', 'solveWallMs', 'usage',
      'winningWorker', 'workers', 'reason'].filter(field => Object.hasOwn(raw, field)).map(field => [field, raw[field]]));
    report.environment = { id: environment.id, toolchain: environment.toolchain,
      dependencyDigest: environment.dependencyDigest,
      ...(environment.mathlibRevision ? { mathlibRevision: environment.mathlibRevision } : {}) };
    const stateFile = `${output}.runtime/state.json`;
    const state = fs.existsSync(stateFile) ? readMathJson(stateFile) as WebWorkerState : undefined;
    if (state) {
      if (state.check) report.candidateCheck = { passed: state.check.passed,
        status: state.check.verification?.status,
        results: state.check.verification?.results?.slice(0, 64).map(result => Object.fromEntries(
          ['theoremName', 'status', 'sorryCount', 'admitCount', 'error', 'stdoutPreview', 'stderrPreview']
            .filter(field => Object.hasOwn(result, field)).map(field => [field,
              typeof result[field] === 'string' ? result[field].slice(0, 2_000) : result[field]]))) };
    }
    const proof = readWebResultProof({ directory, workspace: receipt.workspaceRoot, status: raw.status,
      winningWorker: raw.winningWorker, state, artifact: latestArtifact });
    send({ type: 'result', result: { status: String(raw.status || 'runtime_error'), proof, report } });
  } catch {
    send({ type: 'error', message: '运行未能完成。请检查 Lean 原题、模型服务配置与隔离环境。' });
    process.exitCode = 1;
  } finally {
    clearInterval(artifactTimer);
    request.input.apiKey = '';
    console.log = originalLog;
  }
}

if (process.argv[1] && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  main().catch(() => {
    process.stdout.write(JSON.stringify({ type: 'error', message: '运行输入无效或环境无法初始化。' }) + '\n');
    process.exitCode = 1;
  });
}
