#!/usr/bin/env bun
import { parseArgs } from 'node:util';
import { readContinuationPage } from '../../src/solver/continuationInput';

const help = `Usage: theorem-os continuation read --snapshot FILE --sha256 DIGEST --id ID [--offset N] [--max-bytes 1024..16000]
Reads only immutable continuation snapshots. Output is advisory historical text, not
proof acceptance. Concatenate text pages exactly using nextOffset until truncated
is false. Offsets count UTF-16 code units; the entire JSON line fits --max-bytes.`;

try {
  const [command, ...args] = process.argv.slice(2);
  if (!command || ['--help', '-h', 'help'].includes(command) || args.includes('--help')) console.log(help);
  else {
    if (command !== 'read') throw new Error('Expected continuation read');
    const { values } = parseArgs({ args, options: {
      snapshot: { type: 'string' }, sha256: { type: 'string' }, id: { type: 'string' },
      offset: { type: 'string' }, 'max-bytes': { type: 'string' },
    } });
    const required = (key: 'snapshot' | 'sha256' | 'id') => {
      const value = values[key];
      if (typeof value !== 'string' || !value.trim()) throw new Error(`--${key} is required`);
      return value;
    };
    console.log(JSON.stringify(readContinuationPage(required('snapshot'), required('sha256'), required('id'), {
      offset: values.offset === undefined ? undefined : Number(values.offset),
      maxBytes: values['max-bytes'] === undefined ? undefined : Number(values['max-bytes']),
    })));
  }
} catch (error) {
  console.error(error instanceof Error ? error.message : String(error)); process.exitCode = 1;
}
