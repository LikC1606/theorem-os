#!/usr/bin/env bun
import { parseArgs } from 'node:util';
import fs from 'node:fs';
import path from 'node:path';
import { runLeanDiagnostics } from '../../src/math/leanDiagnostics';
import { checkLeanType } from '../../src/math/leanTypeDiagnostics';
import { readMathJson } from '../../src/math/mathRuntimeIo';
import { assertSolverProjectSources, SolverSourceError, type SolverSourceConstraints } from '../../src/solver/problem';

async function main() {
  const args = process.argv.slice(2);
  if (args[0] === 'check-lean') args.shift();
  const { values } = parseArgs({ args, options: {
    workspace: { type: 'string' }, file: { type: 'string', multiple: true },
    type: { type: 'string' }, context: { type: 'string' },
    'timeout-seconds': { type: 'string', default: '0' }, help: { type: 'boolean' },
  } });
  if (values.help) console.log('Usage: theorem-os check-lean --workspace DIR --file FILE [--file FILE --timeout-seconds N]\n'
    + 'Optional: --type TYPE --context DECLARATION elaborates one closed type in a proof-erased snapshot of the single --file context.\n'
    + 'Checks saved sources against pinned packages. Timeout 0 waits until completion. Diagnostics and type elaboration are advisory, not proof acceptance.');
  else {
    const timeout = Number(values['timeout-seconds']);
    if (!values.workspace || !values.file?.length || !Number.isSafeInteger(timeout) || timeout < 0)
      throw new Error('--workspace, --file and a nonnegative --timeout-seconds are required');
    if ((values.type !== undefined || values.context !== undefined) && (!values.type || !values.context || values.file.length !== 1))
      throw new Error('--type requires --context and exactly one --file');
    const project = fs.realpathSync(values.workspace);
    const constraints = path.join(project, '.lake/source-constraints.json');
    if (fs.existsSync(constraints)) assertSolverProjectSources(readMathJson(constraints) as SolverSourceConstraints, project);
    const controller = new AbortController();
    const abort = () => controller.abort();
    process.once('SIGINT', abort); process.once('SIGTERM', abort);
    let result;
    const shared = { projectRoot: values.workspace, timeoutMs: timeout === 0 ? Infinity : timeout * 1000,
      signal: controller.signal, onProgress: (file: string) => console.error(JSON.stringify({ event: 'lean_check_started', file })) };
    try { result = values.type ? await checkLeanType({ ...shared, file: values.file[0], type: values.type, context: values.context! }) :
      await runLeanDiagnostics({ ...shared, files: values.file });
    } finally { process.removeListener('SIGINT', abort); process.removeListener('SIGTERM', abort); }
    console.log(JSON.stringify(result));
    process.exitCode = result.timedOut ? 124 : result.exitCode ?? 1;
  }
}
void main().catch(error => {
  console.error(error instanceof SolverSourceError
    ? `${error.message}\nFile: ${error.proofPath}\n${error.recovery}\nRepair the saved file and rerun check-lean; no Lean compilation has started.`
    : error instanceof Error ? error.message : 'math_diagnostics_failed');
  process.exitCode = 1;
});
