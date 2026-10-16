#!/usr/bin/env bun
import path from 'node:path';
import fs from 'node:fs';
import { fileURLToPath } from 'node:url';
import { spawn } from 'node:child_process';
import os from 'node:os';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const commands: Readonly<Record<string, string>> = {
  build: 'scripts/build.ts',
  doctor: 'scripts/mathematics/doctor.ts',
  example: 'scripts/mathematics/runExample.ts',
  component: 'scripts/mathematics/component.ts',
  run: 'out/main/math-solver.js',
  batch: 'scripts/mathematics/runMathBatch.ts',
  'bootstrap-imo': 'scripts/mathematics/bootstrapImo2026.ts',
  'bootstrap-lean-eval': 'scripts/mathematics/bootstrapLeanEvalHeldOut.ts',
  'list-lean-eval': 'scripts/mathematics/listLeanEval.ts',
  'freeze-retrieval': 'scripts/mathematics/freezeMathRetrievalCorpus.ts',
  'search-lean': fs.existsSync(path.join(root, 'out/main/search-lean.js')) ? 'out/main/search-lean.js' : 'scripts/mathematics/searchLean.ts',
  'check-lean': 'scripts/mathematics/checkLean.ts',
  inspect: 'scripts/mathematics/inspectMathRun.ts',
  recover: 'scripts/mathematics/recoverMathSnapshot.ts',
  edit: 'scripts/mathematics/editMathRun.ts',
  compare: 'scripts/mathematics/compareMathRuns.ts',
  summarize: 'scripts/mathematics/summarizeMathProofRuns.ts',
};
const [command, ...args] = process.argv.slice(2);
if (!command || ['help', '--help', '-h'].includes(command)) {
  console.log(`theorem-os <command> [arguments]

  build                Freeze mathematical sources and build the solver
  doctor               Check local tools, login and sandbox permissions
  example              Replay or solve a small Lean tutorial without Mathlib
  component            Create and check a replaceable search component
  run                  Run or resume an isolated mathematics proof
  batch                Run prepared problems concurrently in separate processes
  bootstrap-imo        Prepare an IMO2026 proof workspace
  bootstrap-lean-eval   Prepare a public Lean-Eval workspace
  list-lean-eval        List V1 obligations and public formalization gap warnings
  freeze-retrieval     Freeze allowed local Lean declaration sources
  search-lean          Find declarations in verified local Lean packages
  check-lean           Check changed Lean files with bounded diagnostics
  inspect              Read a research report or export a versioned task plan
  recover              Restore a research snapshot and recheck saved helpers
  edit                 Validate and queue a human plan edit
  compare              Prepare, run or report three fixed-budget public baselines
  summarize           Summarize saved proof-run receipts

Use theorem-os <command> --help for command arguments.`);
} else if (!Object.hasOwn(commands, command)) {
  console.error(`Unknown command: ${command}`);
  process.exitCode = 1;
} else {
  const env = { ...process.env, CODEX_HOME: process.env.CODEX_HOME || path.join(os.homedir(), '.config', 'deepscientist', 'math-sol-codex') };
  // Argument arrays preserve literal task/evaluator arguments without a shell.
  const child = spawn(process.execPath, [path.join(root, commands[command]!), ...args], {
    cwd: process.cwd(),
    env,
    stdio: 'inherit',
  });
  const forward = (signal: NodeJS.Signals) => child.kill(signal);
  const interrupt = () => forward('SIGINT');
  const terminate = () => forward('SIGTERM');
  process.on('SIGINT', interrupt);
  process.on('SIGTERM', terminate);
  child.once('error', (error) => { console.error(error.message); process.exitCode = 1; });
  child.once('exit', (code, signal) => {
    process.removeListener('SIGINT', interrupt);
    process.removeListener('SIGTERM', terminate);
    process.exitCode = code ?? (signal === 'SIGINT' ? 130 : signal === 'SIGTERM' ? 143 : 1);
  });
}
