#!/usr/bin/env bun
import fs from 'node:fs';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import environment from '../resources/mathlib/environment.json';

// Build-time only. Every URL and revision comes from the checked-in environment.
const root = path.resolve(process.argv[2] || '/opt/theoremos-mathlib');
const downloadCache = path.resolve(process.env.MATHLIB_CACHE_DIR || path.join(root, 'download-cache'));
if (fs.existsSync(root)) throw new Error('Use a new Mathlib installation directory.');
fs.mkdirSync(root, { recursive: true });
fs.writeFileSync(path.join(root, 'lean-toolchain'), environment.toolchain + '\n');
fs.writeFileSync(path.join(root, 'lakefile.toml'), environment.lakefile);
const manifest = JSON.stringify(environment.manifest, null, 2) + '\n';
fs.writeFileSync(path.join(root, 'lake-manifest.json'), manifest);
const run = (command: string, args: string[], cwd = root) => {
  const result = spawnSync(command, args, { cwd, stdio: 'inherit',
    env: { ...process.env, LEAN_NUM_THREADS: '2', MATHLIB_CACHE_DIR: downloadCache },
    timeout: 30 * 60 * 1000 });
  if (result.error || result.status !== 0) throw new Error(`Mathlib preparation failed: ${command}`);
};
for (const item of environment.manifest.packages) {
  if (!/^[A-Za-z_][A-Za-z0-9_]*$/.test(item.name) || !/^[a-f0-9]{40}$/.test(item.rev) ||
      !item.url.startsWith('https://github.com/')) throw new Error('Invalid pinned package.');
  const directory = path.join(root, '.lake/packages', item.name);
  fs.mkdirSync(directory, { recursive: true });
  run('git', ['init', '--quiet', directory]);
  run('git', ['remote', 'add', 'origin', item.url], directory);
  run('git', ['-c', 'protocol.file.allow=never', 'fetch', '--depth=1', 'origin', item.rev], directory);
  run('git', ['checkout', '--detach', '--quiet', 'FETCH_HEAD'], directory);
}
// Retry missing downloads in place; compile any modules absent from upstream's cache.
for (let attempt = 1; ; attempt++) {
  try { run('lake', ['exe', 'cache', 'get']); break; }
  catch {
    if (attempt === 3) {
      console.warn('Mathlib cache is incomplete; compiling the remaining Mathlib modules.');
      break;
    }
    console.warn(`Retrying Mathlib cache download (${attempt + 1}/3).`);
  }
}
run('lake', ['build', 'Mathlib']);
if (fs.readFileSync(path.join(root, 'lake-manifest.json'), 'utf8') !== manifest)
  throw new Error('Lake changed the frozen Mathlib dependency manifest.');
const probe = path.join(root, 'MathlibProbe.lean');
fs.writeFileSync(probe, 'import Mathlib\nexample (a b : ℝ) : (a + b)^2 = a^2 + 2*a*b + b^2 := by ring\n');
run('lake', ['env', 'lean', '-j', '2', probe]);
fs.unlinkSync(probe);
if (downloadCache === path.join(root, 'download-cache'))
  fs.rmSync(downloadCache, { recursive: true, force: true });
console.log(`Installed Mathlib ${environment.mathlibRevision} with ${environment.toolchain}.`);
