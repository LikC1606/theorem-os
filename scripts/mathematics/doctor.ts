#!/usr/bin/env bun
import { parseArgs } from 'node:util';
import { diagnoseEnvironment, formatDoctorReport } from '../../src/math/doctor';

async function main(): Promise<number> {
  const { values } = parseArgs({ options: { project: { type: 'string' }, codex: { type: 'string' },
    network: { type: 'boolean' }, 'lean-only': { type: 'boolean' }, prepare: { type: 'boolean' }, 'cache-dir': { type: 'string' },
    json: { type: 'boolean' }, help: { type: 'boolean' } } });
  if (values.help) {
    console.log('Usage: theorem-os doctor [--project DIR] [--codex FILE] [--network] [--lean-only] [--prepare] [--cache-dir DIR] [--json]\nChecks local tools, login, sandbox permissions and pinned project dependencies without model calls.\n--lean-only skips Codex checks for the preset tutorial replay.\n--prepare also builds or mounts and verifies the reusable immutable dependency image.\n--network also checks the provider HTTP route without credentials or inference.\nExit 1 means a required check failed; warnings do not change the exit code.');
    return 0;
  }
  if (values['lean-only'] && values.network) throw new Error('--lean-only cannot be combined with --network.');
  const report = await diagnoseEnvironment({ ...values, leanOnly: values['lean-only'], cacheDir: values['cache-dir'] });
  console.log(values.json ? JSON.stringify(report, null, 2) : formatDoctorReport(report));
  return report.status === 'ready' ? 0 : 1;
}
main().then(code => { process.exitCode = code; }, error => {
  console.error(error instanceof Error ? error.message : 'Environment check failed.');
  process.exitCode = 1;
});
