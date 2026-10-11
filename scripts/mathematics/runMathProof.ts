#!/usr/bin/env bun
import path from 'node:path';
import fs from 'node:fs';
import { runSolver } from '../../src/solver/run';

runSolver(process.argv.slice(2), path.resolve(path.dirname(fs.realpathSync(process.argv[1])), '../..')).then(
  code => { process.exitCode = code; },
  error => { console.error(error instanceof Error ? error.message : 'math_run_failed'); process.exitCode = 1; }
);
