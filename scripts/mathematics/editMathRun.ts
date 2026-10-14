#!/usr/bin/env bun
import { parseArgs } from 'node:util';
import { readMathText } from '../../src/math/mathRuntimeIo';
import { queueRunEdit } from '../../src/solver/humanEdit';

try {
  const { values } = parseArgs({ args: process.argv.slice(2), options: {
    run: { type: 'string' }, plan: { type: 'string' }, 'dry-run': { type: 'boolean' }, help: { type: 'boolean' },
  } });
  if (values.help) console.log('Usage: deepscientist-math edit --run RESULT_OR_STATE --plan FILE [--dry-run]\nValidates and queues a versioned plan edit. The running or resumed solver applies it and separately rechecks affected proofs.');
  else {
    if (!values.run || !values.plan) throw new Error('--run and --plan are required');
    console.log(JSON.stringify(await queueRunEdit(values.run, JSON.parse(readMathText(values.plan, 1024 * 1024)), values['dry-run'])));
  }
} catch (error) {
  console.error(error instanceof Error ? error.message : String(error)); process.exitCode = 1;
}
