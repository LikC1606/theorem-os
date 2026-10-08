#!/usr/bin/env bun
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawn } from 'node:child_process';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const args = process.argv.slice(2);
const option = (name: string, fallback: string): string => {
  const index = args.indexOf(name);
  if (index < 0) return fallback;
  const value = args[index + 1];
  if (!value || value.startsWith('--')) throw new Error(`Missing value for ${name}`);
  return value;
};
if (args.includes('--help') || args.includes('-h')) {
  console.log('Usage: deepscientist-math core [--bundle DIRECTORY] [--data-dir DIRECTORY] [--work-dir DIRECTORY] [--port PORT]\nCore listens on loopback; no desktop or WebUI is started.');
} else {
  const bundle = fs.realpathSync(option('--bundle', path.join(root, 'runtime', `${process.platform}-${process.arch}`)));
  const binary = path.join(bundle, process.platform === 'win32' ? 'deepscientist-core.exe' : 'deepscientist-core');
  fs.accessSync(binary, fs.constants.X_OK);
  if (!fs.statSync(path.join(bundle, 'managed-resources')).isDirectory()) throw new Error('math_managed_resources_missing');
  const dataDir = path.resolve(option('--data-dir', path.join(os.homedir(), '.local', 'share', 'deepscientist-math')));
  const workDir = path.resolve(option('--work-dir', path.join(dataDir, 'workspaces')));
  const port = option('--port', '25820');
  if (!/^\d+$/.test(port) || Number(port) > 65535) throw new Error('Invalid Core port');
  const codexHome = process.env.CODEX_HOME || path.join(os.homedir(), '.config', 'deepscientist', 'math-sol-codex');
  const child = spawn(binary, [
    '--host', '127.0.0.1', '--port', port, '--data-dir', dataDir, '--work-dir', workDir,
    '--local', '--managed-resources-mode', 'bundled', '--log-dir', path.join(dataDir, 'logs'),
    '--app-version', '2.1.16', '--parent-pid', String(process.pid),
  ], {
    cwd: root,
    env: {
      ...process.env, CODEX_HOME: codexHome,
      DEEPSCIENTIST_WORK_DIR: workDir, DEEPSCIENTIST_LOG_DIR: path.join(dataDir, 'logs'),
      DEEPSCIENTIST_CACHE_DIR: path.join(dataDir, 'cache'),
    },
    stdio: 'inherit',
  });
  const interrupt = () => child.kill('SIGINT');
  const terminate = () => child.kill('SIGTERM');
  process.on('SIGINT', interrupt);
  process.on('SIGTERM', terminate);
  child.once('error', (error) => { console.error(error.message); process.exitCode = 1; });
  child.once('exit', (code, signal) => {
    process.removeListener('SIGINT', interrupt);
    process.removeListener('SIGTERM', terminate);
    process.exitCode = code ?? (signal === 'SIGINT' ? 130 : signal === 'SIGTERM' ? 143 : 1);
  });
}
