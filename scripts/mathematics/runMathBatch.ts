#!/usr/bin/env bun
import fs from 'node:fs';
import path from 'node:path';
import { spawn, type ChildProcess } from 'node:child_process';
import { parseArgs } from 'node:util';
import { fileURLToPath } from 'node:url';
import { stopMathProcess } from '../../src/math/mathProcess';
import { readMathText, writeMathJsonDurable } from '../../src/math/mathRuntimeIo';

type BatchJob = {
  launch: string;
  workspace: string;
  output: string;
  log: string;
  codexHome?: string;
  status: 'pending' | 'running' | 'completed' | 'failed' | 'cancelled' | 'skipped';
  pid?: number;
  startedAt?: string;
  finishedAt?: string;
  exitCode?: number | null;
  signal?: NodeJS.Signals | null;
  error?: string;
};

/** Each launch reuses the ordinary single-problem command, including --resume. */
export async function runMathBatch(argv: string[]): Promise<number> {
  const { values, tokens } = parseArgs({ args: argv, tokens: true, options: {
    launch: { type: 'string', multiple: true },
    concurrency: { type: 'string', default: '2' },
    output: { type: 'string' },
    help: { type: 'boolean' },
  } });
  if (values.help) {
    console.log('Usage: theorem-os batch --launch FILE [--launch FILE ...] --output FILE [--concurrency 2]\n'
      + 'Launch JSON: {"args":["bun","/path/to/math-solver.js","--workspace","...","--output","...",...],"cwd":"...","envFile":"...","codexHome":"..."}\n'
      + 'cwd defaults to the launch file directory; envFile and codexHome are optional. Workspaces must already be prepared.');
    return 0;
  }
  for (const name of ['concurrency', 'output']) {
    if (tokens.filter(token => token.kind === 'option' && token.name === name).length > 1)
      throw new Error(`Duplicate argument: --${name}`);
  }
  const concurrency = Number(values.concurrency);
  if (!Number.isSafeInteger(concurrency) || concurrency < 1) throw new Error('--concurrency must be a positive integer');
  if (!values.launch?.length) throw new Error('At least one --launch is required');
  if (!values.output?.trim()) throw new Error('--output is required');
  const output = path.resolve(values.output);
  const logRoot = output + '.logs';
  const launches = values.launch.map(file => {
    const launch = fs.realpathSync(file);
    const config = JSON.parse(readMathText(launch, 64 * 1024));
    if (!config || !Array.isArray(config.args) || !config.args.length
      || config.args.some((arg: unknown) => typeof arg !== 'string' || arg.includes('\0'))
      || !config.args[0].trim()) throw new Error(`Invalid launch args: ${launch}`);
    for (const key of ['cwd', 'envFile', 'codexHome']) {
      if (config[key] !== undefined && (typeof config[key] !== 'string' || !config[key].trim()))
        throw new Error(`Invalid ${key}: ${launch}`);
    }
    const args: string[] = config.args;
    const cwd = fs.realpathSync(path.resolve(path.dirname(launch), config.cwd ?? '.'));
    const argument = (name: string): string => {
      const matches = args.flatMap((arg, index) => arg === name ? [args[index + 1]]
        : arg.startsWith(name + '=') ? [arg.slice(name.length + 1)] : []);
      if (matches.length !== 1 || !matches[0]?.trim() || matches[0].startsWith('--'))
        throw new Error(`Launch needs exactly one ${name}: ${launch}`);
      return path.resolve(cwd, matches[0]);
    };
    const workspace = fs.realpathSync(argument('--workspace'));
    if (!fs.statSync(workspace).isDirectory()) throw new Error(`Invalid workspace: ${launch}`);
    const result = argument('--output');
    const canonicalOutput = fs.existsSync(result) ? fs.realpathSync(result)
      : path.join(fs.realpathSync(path.dirname(result)), path.basename(result));
    const envFile = config.envFile ? path.resolve(path.dirname(launch), config.envFile) : undefined;
    if (envFile) fs.accessSync(envFile, fs.constants.R_OK);
    const codexHome = config.codexHome ? fs.realpathSync(path.resolve(path.dirname(launch), config.codexHome)) : undefined;
    if (codexHome && !fs.statSync(codexHome).isDirectory()) throw new Error(`Invalid codexHome: ${launch}`);
    return { launch, args, cwd, workspace, output: canonicalOutput, envFile, codexHome };
  });
  const within = (parent: string, child: string) => child === parent || child.startsWith(parent + path.sep);
  for (let i = 0; i < launches.length; i++) for (let j = 0; j < i; j++) {
    const a = launches[i], b = launches[j];
    if (within(a.workspace, b.workspace) || within(b.workspace, a.workspace) || a.output === b.output
      || within(a.workspace, b.output) || within(b.workspace, a.output))
      throw new Error(`Batch jobs must use separate workspaces and outputs: ${a.launch}, ${b.launch}`);
  }
  if (launches.some(job => within(job.workspace, output) || job.output === output))
    throw new Error('Batch --output must be separate from problem workspaces and outputs');
  fs.mkdirSync(path.dirname(output), { recursive: true, mode: 0o700 });
  // A fresh log directory prevents a repeated batch from overwriting earlier evidence.
  fs.mkdirSync(logRoot, { mode: 0o700 });
  const jobs: BatchJob[] = launches.map((launch, index) => ({
    launch: launch.launch, workspace: launch.workspace, output: launch.output,
    log: path.join(logRoot, `${index + 1}.log`), status: 'pending',
    ...(launch.codexHome ? { codexHome: launch.codexHome } : {}),
  }));
  const state = { concurrency, startedAt: new Date().toISOString(), finishedAt: undefined as string | undefined,
    interruptedBy: undefined as NodeJS.Signals | undefined, jobs };
  const save = () => writeMathJsonDurable(output, state);
  const active = new Set<ChildProcess>();
  let forceStop: NodeJS.Timeout | undefined;
  const cancel = (signal: NodeJS.Signals) => {
    if (state.interruptedBy) {
      for (const child of active) stopMathProcess(child, 'SIGKILL');
      return;
    }
    state.interruptedBy = signal;
    // Let each solver save its checkpoints before terminating descendants.
    for (const child of active) child.kill(signal);
    forceStop = setTimeout(() => {
      for (const child of active) stopMathProcess(child, 'SIGKILL');
    }, 30_000);
    forceStop.unref();
  };
  const interrupt = () => cancel('SIGINT'), terminate = () => cancel('SIGTERM');
  process.on('SIGINT', interrupt); process.on('SIGTERM', terminate);
  const run = async (index: number) => {
    const launch = launches[index], job = jobs[index];
    job.status = 'running'; job.startedAt = new Date().toISOString();
    await new Promise<void>(resolve => {
      let descriptor: number | undefined;
      const finish = (code: number | null, signal: NodeJS.Signals | null) => {
        job.exitCode = code; job.signal = signal; job.finishedAt = new Date().toISOString();
        job.status = state.interruptedBy ? 'cancelled' : code === 0 && !job.error ? 'completed' : 'failed';
        resolve();
      };
      try {
        descriptor = fs.openSync(job.log, 'wx', 0o600);
        const child = spawn(launch.args[0], launch.args.slice(1), {
          cwd: launch.cwd, detached: process.platform !== 'win32',
          env: { ...process.env, ...(launch.envFile ? { DEEPSCIENTIST_MATH_ENV_FILE: launch.envFile } : {}),
            ...(launch.codexHome ? { CODEX_HOME: launch.codexHome } : {}) },
          stdio: ['ignore', descriptor, descriptor],
        });
        active.add(child); job.pid = child.pid;
        child.once('error', error => { job.error = error.message; });
        child.once('close', (code, signal) => { active.delete(child); finish(code, signal); });
      } catch (error) {
        job.error = error instanceof Error ? error.message : String(error);
        finish(null, null);
      } finally {
        if (descriptor !== undefined) fs.closeSync(descriptor);
      }
    });
  };
  let next = 0;
  const worker = async () => {
    let running: Promise<void> | undefined;
    try {
      while (!state.interruptedBy && next < jobs.length) {
        const index = next++;
        running = run(index);
        save();
        console.log(JSON.stringify({ event: 'batch_started', launch: jobs[index].launch, log: jobs[index].log }));
        await running;
        running = undefined;
        save();
        console.log(JSON.stringify({ event: 'batch_finished', ...jobs[index] }));
      }
    } catch (error) { cancel('SIGTERM'); await running; throw error; }
  };
  try {
    save();
    const results = await Promise.allSettled(Array.from({ length: Math.min(concurrency, jobs.length) }, worker));
    for (const job of jobs) if (job.status === 'pending') job.status = 'skipped';
    state.finishedAt = new Date().toISOString(); save();
    const failed = results.find(result => result.status === 'rejected');
    if (failed?.status === 'rejected') throw failed.reason;
    return state.interruptedBy === 'SIGINT' ? 130 : state.interruptedBy ? 143
      : jobs.every(job => job.status === 'completed') ? 0 : 1;
  } finally {
    clearTimeout(forceStop);
    process.removeListener('SIGINT', interrupt); process.removeListener('SIGTERM', terminate);
  }
}

if (process.argv[1] && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  runMathBatch(process.argv.slice(2)).then(code => { process.exitCode = code; }, error => {
    console.error(error instanceof Error ? error.message : String(error)); process.exitCode = 1;
  });
}
