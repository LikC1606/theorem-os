import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { stringify as stringifyToml } from 'smol-toml';
import { bootstrapLeanTask } from '../../src/math/leanTask';
import { getLeanTaskEnvironment } from '../../src/math/leanTaskEnvironment';
import { readMathJson, readMathText } from '../../src/math/mathRuntimeIo';
import { readMathBuildManifest } from '../../src/math/mathBuildManifest';
import { createCodexMathSession } from '../../src/runtime/codexSession';
import { directSolverModules, type SolverModules } from '../../src/solver/modules';
import { runSolver } from '../../src/solver/run';
import type { WorkerInput, WorkerMessage } from './shared';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '../..');
const descriptions: Record<string, string> = {
  ready: '原题与运行环境已固定', dependency_check: '正在检查 Lean 依赖',
  proof_environment: '正在准备只读数学依赖', library_index: '正在准备数学库检索',
  preparation_finished: '题目准备完成', solve_started: '开始研究', turn_started: 'Agent 正在构造候选',
  worker_activity: 'Agent 正在运行', turn_checkpoint: '当前尝试已保存', turn_failed: '当前尝试未完成',
  turn_retry: '准备继续尝试', proof_check_started: '正在检查候选证明',
  proof_checked: '候选检查完成', candidate_selected: '已选出候选，准备最终验收',
  evaluation_started: '正在独立验收完整原题', evaluation_finished: '完整原题验收结束',
  lemma_checked: '辅助引理检查完成', assembly_started: '正在集成候选证明',
  source_rejected: '候选更改了原题约束，已拒绝', preparation_failed: '运行环境预检未通过',
  worker_failed: 'Agent 会话已停止', finished: '求解流程结束',
};
const failureDescriptions: Record<string, string> = {
  math_model_authentication_failed: 'API Key 认证失败，请检查密钥和服务商',
  math_model_concurrency_limit: '服务商限制了当前请求，请检查配额或并发',
  math_model_request_failed: '模型服务连接失败',
  math_model_request_timeout: '模型服务请求超时',
  math_codex_transport_closed: '模型会话连接已中断',
};

export function webProviderConfig(input: WorkerInput): string {
  return stringifyToml({
    model: input.input.model, model_provider: 'web_provider', model_reasoning_effort: input.input.effort,
    approval_policy: 'never', sandbox_mode: 'workspace-write',
    model_providers: { web_provider: { name: input.provider.name, base_url: input.provider.baseUrl,
      wire_api: 'responses', env_key: 'THEOREMOS_PROVIDER_API_KEY', requires_openai_auth: false,
      request_max_retries: 0, stream_max_retries: 0, stream_idle_timeout_ms: 60_000 } },
    shell_environment_policy: { inherit: 'all', exclude: ['THEOREMOS_PROVIDER_API_KEY'] },
    history: { persistence: 'none' }, analytics: { enabled: false },
  });
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
  fs.mkdirSync(profile, { mode: 0o700 });
  fs.writeFileSync(path.join(profile, 'config.toml'), webProviderConfig(request), { mode: 0o600, flag: 'wx' });
  fs.mkdirSync(process.env.HOME || '/work/home', { recursive: true, mode: 0o700 });
  // Each container owns this profile. No machine profile or authentication file is read.
  process.env.CODEX_HOME = profile;
  process.env.DEEPSCIENTIST_MATH_ENV_FILE = path.join(directory, 'math.env');
  fs.writeFileSync(process.env.DEEPSCIENTIST_MATH_ENV_FILE, '', { mode: 0o400, flag: 'wx' });
  const originalLog = console.log;
  console.log = (...args: unknown[]) => {
    for (const value of args) if (typeof value === 'string') {
      try {
        const event = JSON.parse(value);
        if (typeof event.event === 'string' && descriptions[event.event]) send({ type: 'progress', event: event.event,
          message: (failureDescriptions[event.reason] || descriptions[event.event]) +
            (typeof event.workerId === 'string' ? ` · ${event.workerId.slice(0, 30)}` : '') });
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
    const modules: SolverModules = { ...directSolverModules, id: `${directSolverModules.id}/web-byok-v1`,
      M1: { ...directSolverModules.M1, version: `${directSolverModules.M1.version}/web-byok-v1`,
        open: options => createCodexMathSession({ ...options,
          environment: { ...options.environment, THEOREMOS_PROVIDER_API_KEY: key } }) } };
    await runSolver(['--workspace', receipt.workspaceRoot, '--task-file', taskFile, '--output', output,
      '--receipt-file', receipt.activeProblemPath, '--build-manifest', buildIndex.buildManifestRef,
      '--model', request.input.model, '--effort', request.input.effort, '--workers', String(request.input.workers),
      '--coordination', request.input.coordination, '--max-turns', String(request.input.maxTurns),
      '--max-run-seconds', String(request.input.maxRunSeconds), '--max-turn-seconds', '120',
      '--prepare-timeout-seconds', environment.id === 'mathlib' ? '600' : '120',
      '--evaluator-timeout-seconds', '120'], root, modules);
    const raw = readMathJson(output) as Record<string, unknown>;
    const report = Object.fromEntries(['schema', 'runId', 'problemId', 'status', 'solution_commit',
      'solver_ready_receipt_valid', 'completion_signal_valid', 'evaluator', 'turns', 'solveWallMs', 'usage',
      'winningWorker', 'workers', 'reason'].filter(field => Object.hasOwn(raw, field)).map(field => [field, raw[field]]));
    report.environment = { id: environment.id, toolchain: environment.toolchain,
      dependencyDigest: environment.dependencyDigest,
      ...(environment.mathlibRevision ? { mathlibRevision: environment.mathlibRevision } : {}) };
    let proof = '';
    const stateFile = `${output}.runtime/state.json`;
    if (fs.existsSync(stateFile)) {
      const state = readMathJson(stateFile) as { worktree: string; workers?: { id: string; worktree: string }[];
        check?: { passed: boolean; verification?: { status?: string; results?: Record<string, unknown>[] } } };
      if (state.check) report.candidateCheck = { passed: state.check.passed,
        status: state.check.verification?.status,
        results: state.check.verification?.results?.slice(0, 64).map(result => Object.fromEntries(
          ['theoremName', 'status', 'sorryCount', 'admitCount', 'error', 'stdoutPreview', 'stderrPreview']
            .filter(field => Object.hasOwn(result, field)).map(field => [field,
              typeof result[field] === 'string' ? result[field].slice(0, 2_000) : result[field]]))) };
      const tree = raw.status === 'evaluated_passed' ? receipt.workspaceRoot :
        state.workers?.find(worker => worker.id === raw.winningWorker)?.worktree ?? state.worktree;
      const file = path.resolve(tree, 'generated/problem/Submission.lean');
      if (file.startsWith(directory + path.sep)) {
        try { proof = readMathText(file, 128 * 1024); } catch { /* Rejected or oversized candidates have no downloadable source. */ }
      }
    }
    send({ type: 'result', result: { status: String(raw.status || 'runtime_error'), proof, report } });
  } catch {
    send({ type: 'error', message: '运行未能完成。请检查 Lean 原题、模型服务配置与隔离环境。' });
    process.exitCode = 1;
  } finally {
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
