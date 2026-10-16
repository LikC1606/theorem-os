#!/usr/bin/env bun
import { parseFlags, required } from './arguments';
import { recoverMathSnapshot, recheckMathSnapshot } from '../../src/solver/recovery';
import { resolveMathematicsRuntimeEnvironment } from '../../src/math/mathRuntimeEnvironment';
import { buildRunInspection } from '../../src/solver/inspection';

try {
  const flags = parseFlags(process.argv.slice(2), ['snapshot', 'output', 'source-repo', 'recheck', 'packages', 'timeout-seconds']);
  if (flags.has('help')) {
    console.log('Usage: theorem-os recover --snapshot DIR --output NEW_DIR [--source-repo LEAN_EVAL_REPO]\n       theorem-os recover --recheck RECOVERED_DIR --packages PINNED_CACHE [--timeout-seconds N]\nVerifies snapshot hashes, imports filtered history, restores frozen sources and worker drafts in a separate directory. Recheck generates fresh helper receipts without a model. Old receipts and checkpoints stay unchanged; recovery output is not a resumable run or official acceptance.');
  } else if (flags.has('recheck')) {
    const timeout = Number(flags.get('timeout-seconds') ?? '180');
    if (!Number.isSafeInteger(timeout) || timeout < 0) throw new Error('invalid --timeout-seconds');
    const env = { ...resolveMathematicsRuntimeEnvironment(), DEEPSCIENTIST_MATH_TRUSTED_CACHE_ROOTS: required(flags, 'packages') };
    const controller = new AbortController();
    const abort = () => controller.abort(); process.once('SIGINT', abort); process.once('SIGTERM', abort);
    try {
      const { report, state } = await recheckMathSnapshot(required(flags, 'recheck'), { env, signal: controller.signal,
        timeoutMs: timeout === 0 ? Infinity : timeout * 1000,
        onProgress: tasks => console.log(JSON.stringify({ event: 'recovery_check', tasks })) });
      console.log(JSON.stringify({ recovery: report.stateFile, ...buildRunInspection(state).progress }));
      if (state.cooperation!.tasks.some(node => report.candidates.includes(node.task.id) && node.status !== 'integrated')) process.exitCode = 2;
    } finally { process.removeListener('SIGINT', abort); process.removeListener('SIGTERM', abort); }
  } else {
    const report = recoverMathSnapshot({ snapshot: required(flags, 'snapshot'), output: required(flags, 'output'),
      sourceRepository: flags.get('source-repo') });
    console.log(JSON.stringify({ stateFile: report.stateFile, workspace: report.workspace,
      workers: report.workerCommits, candidates: report.candidates.length, missingCommitReferences: report.missingCommitReferences.length }));
  }
} catch (error) {
  console.error(error instanceof Error ? error.message : String(error)); process.exitCode = 1;
}
