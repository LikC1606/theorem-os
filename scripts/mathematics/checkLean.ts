#!/usr/bin/env bun
import { parseArgs } from 'node:util';
import fs from 'node:fs';
import path from 'node:path';
import { runLeanDiagnostics } from '../../src/math/leanDiagnostics';
import { readMathJson } from '../../src/math/mathRuntimeIo';
import { assertSolverProjectSources, type SolverSourceConstraints } from '../../src/solver/problem';

async function main() {
  const args = process.argv.slice(2);
  if (args[0] === 'check-lean') args.shift();
  const { values } = parseArgs({ args, options: {
    workspace: { type: 'string' }, file: { type: 'string', multiple: true },
    'timeout-seconds': { type: 'string', default: '0' }, help: { type: 'boolean' },
  } });
  if (values.help) console.log('Usage: deepscientist-math check-lean --workspace DIR --file FILE [--file FILE --timeout-seconds N]\nChecks the saved files against pinned packages. Timeout 0 waits until completion. Diagnostics are advisory, not proof acceptance.');
  else {
    const timeout = Number(values['timeout-seconds']);
    if (!values.workspace || !values.file?.length || !Number.isSafeInteger(timeout) || timeout < 0)
      throw new Error('--workspace, --file and a nonnegative --timeout-seconds are required');
    const project = fs.realpathSync(values.workspace);
    const constraints = path.join(project, '.lake/source-constraints.json');
    if (fs.existsSync(constraints)) assertSolverProjectSources(readMathJson(constraints) as SolverSourceConstraints, project);
    const controller = new AbortController();
    const abort = () => controller.abort();
    process.once('SIGINT', abort); process.once('SIGTERM', abort);
    let result;
    try { result = await runLeanDiagnostics({ projectRoot: values.workspace, files: values.file,
      timeoutMs: timeout === 0 ? Infinity : timeout * 1000, signal: controller.signal,
      onProgress: file => console.error(JSON.stringify({ event: 'lean_check_started', file })) });
    } finally { process.removeListener('SIGINT', abort); process.removeListener('SIGTERM', abort); }
    console.log(JSON.stringify(result));
    process.exitCode = result.timedOut ? 124 : result.exitCode ?? 1;
  }
}
void main().catch(error => {
  console.error(error instanceof Error ? error.message : 'math_diagnostics_failed');
  process.exitCode = 1;
});
