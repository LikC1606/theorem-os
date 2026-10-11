#!/usr/bin/env bun
import { parseArgs } from 'node:util';
import { runLeanDiagnostics } from '../../src/math/leanDiagnostics';

async function main() {
  const args = process.argv.slice(2);
  if (args[0] === 'check-lean') args.shift();
  const { values } = parseArgs({ args, options: {
    workspace: { type: 'string' }, file: { type: 'string', multiple: true },
    'timeout-seconds': { type: 'string', default: '90' }, help: { type: 'boolean' },
  } });
  if (values.help) console.log('Usage: deepscientist-math check-lean --workspace DIR --file FILE [--file FILE --timeout-seconds N]\nChecks local imports and the requested files against pinned packages. Diagnostics are advisory, not proof acceptance.');
  else {
    const timeout = Number(values['timeout-seconds']);
    if (!values.workspace || !values.file?.length || !Number.isSafeInteger(timeout) || timeout < 1)
      throw new Error('--workspace, --file and a positive --timeout-seconds are required');
    const result = await runLeanDiagnostics({ projectRoot: values.workspace, files: values.file, timeoutMs: timeout * 1000,
      onProgress: file => console.error(JSON.stringify({ event: 'lean_check_started', file })) });
    console.log(JSON.stringify(result));
    process.exitCode = result.timedOut ? 124 : result.exitCode ?? 1;
  }
}
void main().catch(error => {
  console.error(error instanceof Error ? error.message : 'math_diagnostics_failed');
  process.exitCode = 1;
});
