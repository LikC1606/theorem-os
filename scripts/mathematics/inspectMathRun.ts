#!/usr/bin/env bun
import fs from 'node:fs';
import path from 'node:path';
import { parseFlags, required } from './arguments';
import { exportRunPlan, readRunInspection, renderRunInspection } from '../../src/solver/inspection';
import { inspectStoredRun } from '../../src/solver/storedRunInspection';

try {
  const flags = parseFlags(process.argv.slice(2), ['run', 'format', 'output', 'batch', 'log']);
  if (flags.has('help')) {
    console.log('Usage: theorem-os inspect --run RESULT_OR_STATE [--format markdown|json|plan] [--batch BATCH_FILE | --log LOG_FILE] [--output NEW_FILE]\nReads stored evidence without starting a model or rerunning Lean. Optional journal input explains recorded contribution flow; missing or partial history remains unknown. Logs are read as a fixed prefix of at most 16 MiB. Plan exports include the required base version and do not read journals.');
  } else {
    const format = flags.get('format') ?? 'markdown';
    if (!['markdown', 'json', 'plan'].includes(format)) throw new Error('invalid --format');
    if (flags.has('batch') && flags.has('log')) throw new Error('--batch and --log are mutually exclusive');
    const run = required(flags, 'run');
    let text: string;
    if (format === 'plan') text = JSON.stringify(exportRunPlan(readRunInspection(run).state), null, 2);
    else {
      const report = await inspectStoredRun(run, { journal: flags.has('batch') ? { batchFile: required(flags, 'batch') }
        : flags.has('log') ? { logFile: required(flags, 'log') } : undefined });
      text = format === 'json' ? JSON.stringify(report, null, 2) : renderRunInspection(report);
    }
    if (flags.has('output')) fs.writeFileSync(path.resolve(required(flags, 'output')), text.trimEnd() + '\n', { flag: 'wx', mode: 0o600 });
    else process.stdout.write(text.trimEnd() + '\n');
  }
} catch (error) {
  console.error(error instanceof Error ? error.message : String(error)); process.exitCode = 1;
}
