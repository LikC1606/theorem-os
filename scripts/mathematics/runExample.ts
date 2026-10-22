#!/usr/bin/env bun
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { parseArgs } from 'node:util';
import { bootstrapLocalExample, LOCAL_EXAMPLE_FAILED_PROOF, LOCAL_EXAMPLE_PROOF } from '../../src/math/localExample';
import { readMathBuildManifest } from '../../src/math/mathBuildManifest';
import { readMathJson, writeMathJsonDurable } from '../../src/math/mathRuntimeIo';
import { runMathProcess } from '../../src/math/mathProcess';
import { assertMathCanonicalPath, isMathPathWithin } from '../../src/math/paths';
import { runSolver } from '../../src/solver/run';
import { directSolverModules, type SolverModules } from '../../src/solver/modules';
import type { MathAgentOptions, MathAgentSession } from '../../src/runtime/codexSession';
import { componentPaths } from '../../src/solver/componentTemplate';
import { MAX_RESEARCH_WORKERS } from '../../src/solver/modules/organization';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '../..');
const task = 'Prove both original natural-number addition targets in generated/addition/Submission.lean. Preserve their declarations and all protected files. Use Lean feedback to repair your proofs.';
type ExampleCase = { schema: 'theorem-os.example-case.v1'; buildManifestRef: string; mode: 'model' | 'replay';
  component?: string; workers: number; model: string; effort: string; codex?: string };

async function prepare(directory: string, configuration: Omit<ExampleCase, 'schema' | 'buildManifestRef'>): Promise<void> {
  assertMathCanonicalPath(directory);
  if (isMathPathWithin(root, directory)) throw new Error('Choose a new example directory outside the source checkout.');
  if (fs.existsSync(directory)) throw new Error('Example directory already exists; use a new directory.');
  fs.mkdirSync(directory, { recursive: true, mode: 0o700 });
  const build = await runMathProcess(process.execPath, [path.join(root, 'scripts/build.ts'), '--state-root', path.join(directory, 'builds')],
    { cwd: root, env: process.env, timeoutMs: 120_000, outputLimit: 8_000 });
  if (build.exitCode !== 0) throw new Error(`Example build failed: ${build.stderr || build.stdout}`);
  const { buildManifestRef } = JSON.parse(build.stdout);
  readMathBuildManifest(buildManifestRef, root, path.join(root, 'out/main'));
  const receipt = bootstrapLocalExample(path.join(directory, 'workspace'));
  fs.writeFileSync(path.join(directory, 'task.md'), task + '\n', { flag: 'wx', mode: 0o600 });
  writeMathJsonDurable(path.join(directory, 'case.json'), { schema: 'theorem-os.example-case.v1', buildManifestRef, ...configuration } satisfies ExampleCase);
  console.log(`Prepared: ${directory}\nLean project: ${receipt.projectRoot}`);
}

function replayModules(base: SolverModules = directSolverModules): SolverModules {
  let attempt = 0;
  return { ...base, id: `${base.id}/tutorial-replay-v1`, M1: { ...base.M1, version: 'preset-addition-replay-v1',
    open: async (_options: MathAgentOptions): Promise<MathAgentSession> => ({
      threadId: 'tutorial-preset-candidates',
      run: async (_message, _messageId, worktree, onStarted) => {
        onStarted(`preset-${++attempt}`);
        fs.writeFileSync(path.join(worktree, 'generated/addition/Submission.lean'),
          attempt === 1 ? LOCAL_EXAMPLE_FAILED_PROOF : LOCAL_EXAMPLE_PROOF);
        console.log(JSON.stringify({ event: 'tutorial_candidate', source: 'preset-replay', attempt,
          description: attempt === 1 ? 'Try rfl for both targets; zero_add should fail.' : 'Repair zero_add with Nat.zero_add.' }));
        return 'completed';
      }, interrupt: async () => {}, close: async () => {},
    }),
  } };
}

async function main(): Promise<number> {
  const { values, positionals } = parseArgs({ allowPositionals: true, options: {
    dir: { type: 'string' }, model: { type: 'string' }, effort: { type: 'string' }, codex: { type: 'string' },
    component: { type: 'string' }, workers: { type: 'string' }, help: { type: 'boolean' },
  } });
  if (values.help) {
    console.log(`Usage: theorem-os example prepare|check|solve|resume|replay --dir DIR [--component NAME] [--workers 1..${MAX_RESEARCH_WORKERS}] [--model MODEL] [--effort LEVEL] [--codex FILE]\nprepare: create a small Lean-only problem and freeze the build and configuration.\ncheck: run the startup preflight without a model.\nsolve / resume: use the saved configuration (default: single agent, at most 5 dispatches).\nreplay: prepare a NEW directory and check two preset candidates with real Lean; no model or provider connection.\n--component uses src/components/NAME.ts; M3.ready ordering is exercised by cooperative model runs with at least 3 workers.\nInstall leanprover/lean4:v4.33.0 first. Keep the same build and environment when resuming.`);
    return 0;
  }
  const action = positionals[0];
  if (positionals.length !== 1 || !['prepare', 'check', 'solve', 'resume', 'replay'].includes(action) || !values.dir?.trim())
    throw new Error('Use example prepare|check|solve|resume|replay --dir /absolute/path/to/case.');
  const directory = path.resolve(values.dir);
  assertMathCanonicalPath(directory);
  if (isMathPathWithin(root, directory)) throw new Error('Keep example cases outside the source checkout.');
  const workers = values.workers === undefined ? 1 : Number(values.workers);
  if (!Number.isSafeInteger(workers) || workers < 1 || workers > MAX_RESEARCH_WORKERS)
    throw new Error(`--workers must be an integer from 1 to ${MAX_RESEARCH_WORKERS}.`);
  if (action === 'replay' && (workers !== 1 || values.model || values.effort || values.codex))
    throw new Error('Replay uses preset candidates with one worker; prepare a separate case for model runs.');
  if (values.component) {
    const file = componentPaths(root, values.component).source;
    assertMathCanonicalPath(file);
    fs.accessSync(file, fs.constants.R_OK);
  }
  if (action === 'prepare' || action === 'replay') await prepare(directory, {
    mode: action === 'replay' ? 'replay' : 'model', component: values.component, workers,
    model: values.model || 'deepseek-flash', effort: values.effort || 'max', codex: values.codex,
  });
  if (action === 'prepare') return 0;
  const config = readMathJson(path.join(directory, 'case.json')) as ExampleCase;
  if (config.schema !== 'theorem-os.example-case.v1' || !['model', 'replay'].includes(config.mode) ||
      !Number.isSafeInteger(config.workers) || config.workers < 1 || config.workers > MAX_RESEARCH_WORKERS || !config.model || !config.effort)
    throw new Error('Invalid example case.');
  for (const key of ['model', 'effort', 'codex', 'component', 'workers'] as const)
    if (values[key] !== undefined && String(values[key]) !== String(config[key])) throw new Error(`--${key} differs from the prepared case; use its saved configuration or prepare a new case.`);
  if (config.mode === 'replay' && (action !== 'replay' || values.model || values.effort || values.codex))
    throw new Error('Replay uses preset candidates in a new case; use a separately prepared case for a model run.');
  const output = path.join(directory, 'result.json');
  const args = ['--workspace', path.join(directory, 'workspace'), '--task-file', path.join(directory, 'task.md'),
    '--build-manifest', config.buildManifestRef, '--output', output, '--workers', String(config.workers), '--max-turns', '5', '--max-run-seconds', '300'];
  for (const key of ['model', 'effort', 'codex'] as const) if (config[key]) args.push(`--${key}`, config[key]);
  if (action === 'check') {
    args.push('--startup-only');
    if (fs.existsSync(`${output}.runtime/state.json`)) args.push('--resume');
  } else if (action === 'resume') args.push('--resume');
  const custom = config.component ? (await import(pathToFileURL(componentPaths(root, config.component).source).href)).modules as SolverModules : undefined;
  if (config.component && typeof custom?.M3?.ready !== 'function') throw new Error('The component must export modules with M3.ready.');
  const stateFile = `${output}.runtime/state.json`;
  const previousTurns = fs.existsSync(stateFile) ? (readMathJson(stateFile) as { turns: number }).turns : 0;
  const previousResult = fs.existsSync(output) ? fs.readFileSync(output, 'utf8') : undefined;
  const code = await runSolver(args, root, config.mode === 'replay' ? replayModules(custom) : custom);
  if (code !== 0 && previousResult !== undefined && fs.readFileSync(output, 'utf8') === previousResult) {
    console.error('Run rejected or stopped without a new result; the previous result has been preserved.');
    return code;
  }
  const result = fs.existsSync(output) ? readMathJson(output) as { status: string } : undefined;
  const turns = fs.existsSync(stateFile) ? (readMathJson(stateFile) as { turns: number }).turns : previousTurns;
  const example = { source: config.mode === 'replay' ? 'preset-replay' : 'model',
    modelInvoked: config.mode === 'model' && turns > previousTurns, component: config.component };
  if (result) writeMathJsonDurable(output, { ...result, example });
  writeMathJsonDurable(path.join(directory, 'summary.json'), { ...example, status: result?.status ?? 'unavailable', resultFile: output, official: false });
  console.log(`\n${config.mode === 'replay' ? 'Preset replay with real Lean checks' : 'Model example'}: ${result?.status ?? 'no result'}\nResult: ${output}\nInspect: bun run math inspect --run ${JSON.stringify(output)}`);
  return code;
}
main().then(code => { process.exitCode = code; }, error => {
  console.error(error instanceof Error ? error.message : 'Example failed.'); process.exitCode = 1;
});
