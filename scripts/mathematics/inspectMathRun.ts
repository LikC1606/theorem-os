#!/usr/bin/env bun
import fs from 'node:fs';
import path from 'node:path';
import { parseFlags, required } from './arguments';
import { buildRunInspection, exportRunPlan, readRunInspection, renderRunInspection } from '../../src/solver/inspection';

try {
  const flags = parseFlags(process.argv.slice(2), ['run', 'format', 'output']);
  if (flags.has('help')) {
    console.log('Usage: theorem-os inspect --run RESULT_OR_STATE [--format markdown|json|plan] [--output NEW_FILE]\nReads stored evidence without starting a model or rerunning Lean. Plan exports include the required base version.');
  } else {
    const format = flags.get('format') ?? 'markdown';
    if (!['markdown', 'json', 'plan'].includes(format)) throw new Error('invalid --format');
    const { state, result } = readRunInspection(required(flags, 'run'));
    const text = format === 'plan' ? JSON.stringify(exportRunPlan(state), null, 2) :
      format === 'json' ? JSON.stringify(buildRunInspection(state, result), null, 2) : renderRunInspection(buildRunInspection(state, result));
    if (flags.has('output')) fs.writeFileSync(path.resolve(required(flags, 'output')), text.trimEnd() + '\n', { flag: 'wx', mode: 0o600 });
    else process.stdout.write(text.trimEnd() + '\n');
  }
} catch (error) {
  console.error(error instanceof Error ? error.message : String(error)); process.exitCode = 1;
}
