#!/usr/bin/env bun
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawn } from 'node:child_process';
import os from 'node:os';
import { launchMathRuntime } from '../src/runtime/launchRuntime';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const commands: Readonly<Record<string, string>> = {
  build: 'scripts/build.ts',
  runtime: 'out/main/math-runtime.js',
  run: 'scripts/mathematics/runMathProofTeam.ts',
  'bootstrap-imo': 'scripts/mathematics/bootstrapImo2026.ts',
  'bootstrap-lean-eval': 'scripts/mathematics/bootstrapLeanEvalHeldOut.ts',
  'freeze-retrieval': 'scripts/mathematics/freezeMathRetrievalCorpus.ts',
  summarize: 'scripts/mathematics/summarizeMathProofRuns.ts',
};
const [command, ...args] = process.argv.slice(2);
if (!command || ['help', '--help', '-h'].includes(command)) {
  console.log(`deepscientist-math <command> [arguments]

  build                Build headless MCP bundles and freeze a build manifest
  runtime              Start the bundled mathematics runtime (optional)
  run                  Run or resume a mathematics proof Team
  bootstrap-imo        Prepare an IMO2026 proof workspace
  bootstrap-lean-eval   Prepare a public Lean-Eval workspace
  freeze-retrieval     Freeze allowed local Lean declaration sources
  summarize           Summarize saved proof-run receipts

Use deepscientist-math <command> --help for command arguments.`);
} else if (!Object.hasOwn(commands, command)) {
  console.error(`Unknown command: ${command}`);
  process.exitCode = 1;
} else {
  const env = { ...process.env, CODEX_HOME: process.env.CODEX_HOME || path.join(os.homedir(), '.config', 'deepscientist', 'math-sol-codex') };
  const needsRuntime = command === 'run' && !args.some(arg => ['--runtime-url', '--core-url', '--help', '-h', '--resume-evaluation-request', '--check-provider-only'].includes(arg));
  const output = args[args.indexOf('--output') + 1];
  const runtime = needsRuntime && args.includes('--output') && output
    ? await launchMathRuntime(root, output, env) : undefined;
  // Argument arrays preserve literal task/evaluator arguments without a shell.
  const child = spawn(process.execPath, [path.join(root, commands[command]!), ...args, ...(runtime ? ['--runtime-url', runtime.runtimeUrl] : [])], {
    cwd: process.cwd(),
    env,
    stdio: 'inherit',
  });
  const forward = (signal: NodeJS.Signals) => child.kill(signal);
  const interrupt = () => forward('SIGINT');
  const terminate = () => forward('SIGTERM');
  process.on('SIGINT', interrupt);
  process.on('SIGTERM', terminate);
  child.once('error', (error) => { console.error(error.message); process.exitCode = 1; void runtime?.stop(); });
  child.once('exit', async (code, signal) => {
    process.removeListener('SIGINT', interrupt);
    process.removeListener('SIGTERM', terminate);
    process.exitCode = code ?? (signal === 'SIGINT' ? 130 : signal === 'SIGTERM' ? 143 : 1);
    await runtime?.stop();
  });
}
