#!/usr/bin/env bun
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { parseFlags, required } from './arguments';
import { seedSolverContinuation } from '../../src/solver/continuationSeed';

try {
  const flags = parseFlags(process.argv.slice(2), ['source-run', 'run', 'build-manifest', 'timeout-seconds']);
  if (flags.has('help')) console.log('Usage: theorem-os continuation-seed --source-run OLD_RESULT_OR_STATE --run NEW_RESULT_OR_STATE --build-manifest NEW_MANIFEST [--timeout-seconds N]\nInitializes an idle, zero-turn run prepared by the new build, using the same workspace, task and frozen problem receipt. Captures canonical sources, task identities and all worker drafts as advisory continuation material, then creates fresh helper receipts without a model. The source run stays unchanged. Interrupted initialization can be retried with the same arguments. Use 0 to disable the verification timeout.');
  else {
    const timeout = Number(flags.get('timeout-seconds') ?? '180');
    if (!Number.isSafeInteger(timeout) || timeout < 0) throw new Error('invalid --timeout-seconds');
    const controller = new AbortController(), abort = () => controller.abort();
    process.once('SIGINT', abort); process.once('SIGTERM', abort);
    try {
      const report = await seedSolverContinuation({ sourceRun: required(flags, 'source-run'), run: required(flags, 'run'),
        buildManifest: required(flags, 'build-manifest'), root: path.resolve(path.dirname(fileURLToPath(import.meta.url)), '../..'),
        signal: controller.signal, timeoutMs: timeout === 0 ? Infinity : timeout * 1000,
        onProgress: (event, details) => console.log(JSON.stringify({ event, ...details })) });
      console.log(JSON.stringify(report));
      if (report.failed.length) process.exitCode = 2;
    } finally { process.removeListener('SIGINT', abort); process.removeListener('SIGTERM', abort); }
  }
} catch (error) { console.error(error instanceof Error ? error.message : String(error)); process.exitCode = 1; }
