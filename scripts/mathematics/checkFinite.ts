#!/usr/bin/env bun
import { parseArgs } from 'node:util';
import { checkFiniteBooleanConstraints, FINITE_BOOLEAN_LIMITS } from '../../src/math/finiteBooleanCheck';
import { mathDigest, readMathText } from '../../src/math/mathRuntimeIo';

function main() {
  const args = process.argv.slice(2);
  if (args[0] === 'check-finite') args.shift();
  const { values } = parseArgs({ args, options: { input: { type: 'string' }, json: { type: 'string' },
    witnesses: { type: 'string', default: '16' }, help: { type: 'boolean' } } });
  if (values.help) {
    console.log('Usage: theorem-os check-finite (--input FILE | --json JSON) [--witnesses N]\n'
      + 'Schema: {"schema":"theorem-os.finite-boolean-cnf.v1","variables":["A"],"fixed":[],"clauses":[[{"variable":"A","value":true}]]}.\n'
      + 'Each clause requires at least one literal to match; all clauses must hold. Empty clauses are false; an empty clause set is true.\n'
      + 'Returns canonical data and raw-input digests, exact assignment/witness counts and bounded complete assignments.\n'
      + 'Results concern only the supplied constraints and remain advisory; they do not check their translation from a theorem or grant proof acceptance.\n'
      + `Limits: ${JSON.stringify(FINITE_BOOLEAN_LIMITS)}. Unsupported enumeration sizes are inconclusive. No wall-clock cutoff.`);
    return;
  }
  if (Boolean(values.input) === Boolean(values.json)) throw new Error('Supply exactly one of --input or --json');
  const text = values.input ? readMathText(values.input, FINITE_BOOLEAN_LIMITS.inputBytes) : values.json!;
  if (Buffer.byteLength(text) > FINITE_BOOLEAN_LIMITS.inputBytes) throw new Error('math_finite_input_too_large');
  const result = checkFiniteBooleanConstraints(JSON.parse(text), Number(values.witnesses));
  console.log(JSON.stringify({ ...result, sourceDigest: mathDigest(text) }));
  if (!result.complete) process.exitCode = 2;
}
try { main(); } catch (error) {
  console.error(error instanceof Error ? error.message : 'math_finite_check_failed');
  process.exitCode = 1;
}
