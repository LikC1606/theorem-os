#!/usr/bin/env bun
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { runSolver } from '../../src/solver/run';
import { directSolverModules, type SolverModules } from '../../src/solver/modules';
import { goalsFirstResearchTasks } from '../../src/solver/modules/search';

const modules: SolverModules = {
  ...directSolverModules,
  id: 'goals-first-example-v1',
  M3: {
    ...directSolverModules.M3,
    version: `${directSolverModules.M3.version}/example-goals-first-v1`,
    ready: goalsFirstResearchTasks,
  },
};

process.env.CODEX_HOME ||= path.join(os.homedir(), '.config', 'deepscientist', 'math-sol-codex');
const root = path.resolve(path.dirname(fs.realpathSync(process.argv[1])), '../..');
runSolver(process.argv.slice(2), root, modules).then(
  code => { process.exitCode = code; },
  error => { console.error(error instanceof Error ? error.message : 'math_run_failed'); process.exitCode = 1; }
);
