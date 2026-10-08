import fs from 'node:fs';
import path from 'node:path';
import { spawn } from 'node:child_process';
import { createInterface } from 'node:readline';
import { writeMathJsonDurable } from '../math/mathRuntimeIo';

/** A run owns its private host and keeps its loopback endpoint stable across resumes. */
export async function launchMathRuntime(root: string, output: string, env: NodeJS.ProcessEnv) {
  const parent = path.dirname(path.resolve(output));
  fs.mkdirSync(parent, { recursive: true, mode: 0o700 });
  const parentStat = fs.lstatSync(parent);
  if (!parentStat.isDirectory() || parentStat.isSymbolicLink() || (parentStat.mode & 0o077) ||
      (process.getuid && parentStat.uid !== process.getuid())) throw new Error('math_output_parent_not_private');
  const directory = `${path.resolve(output)}.runtime`;
  fs.mkdirSync(directory, { recursive: true, mode: 0o700 });
  const stat = fs.lstatSync(directory);
  if (!stat.isDirectory() || stat.isSymbolicLink() || (stat.mode & 0o077) ||
      (process.getuid && stat.uid !== process.getuid())) throw new Error('math_runtime_data_directory_not_private');
  const endpoint = path.join(directory, 'endpoint.json');
  let port = 0;
  if (fs.existsSync(endpoint)) {
    const stat = fs.lstatSync(endpoint);
    if (!stat.isFile() || stat.nlink !== 1 || (stat.mode & 0o077)) throw new Error('math_runtime_endpoint_not_private');
    const url = new URL(JSON.parse(fs.readFileSync(endpoint, 'utf8')).runtimeUrl);
    if (url.protocol !== 'http:' || url.hostname !== '127.0.0.1' || !url.port) throw new Error('math_runtime_endpoint_invalid');
    port = Number(url.port);
  }
  const entry = path.join(root, 'out/main/math-runtime.js');
  if (!fs.existsSync(entry)) throw new Error('Mathematics runtime is not built; run bun run build first.');
  const child = spawn(process.execPath, [entry, '--data-dir', directory, '--port', String(port)], { env, stdio: ['ignore', 'pipe', 'inherit'] });
  const stopped = new Promise<void>(resolve => child.once('close', () => resolve()));
  const stop = async () => {
    child.kill('SIGTERM');
    const timer = setTimeout(() => child.kill('SIGKILL'), 10_000);
    try { await stopped; } finally { clearTimeout(timer); }
  };
  const abort = () => child.kill('SIGTERM');
  process.once('SIGINT', abort);
  process.once('SIGTERM', abort);
  const lines = createInterface({ input: child.stdout });
  try {
    const runtimeUrl = await new Promise<string>((resolve, reject) => {
      const timer = setTimeout(() => reject(new Error('math_runtime_start_timeout')), 10_000);
      const finish = () => clearTimeout(timer);
      child.once('error', error => { finish(); reject(error); });
      child.once('exit', () => { finish(); reject(new Error('math_runtime_start_failed')); });
      lines.once('line', line => {
        finish();
        try {
          const ready = JSON.parse(line);
          const url = new URL(ready.runtimeUrl);
          if (url.protocol !== 'http:' || url.hostname !== '127.0.0.1' || Number(ready.pid) !== child.pid)
            throw new Error('math_runtime_start_identity_invalid');
          resolve(url.origin);
        } catch (error) { reject(error); }
      });
    });
    writeMathJsonDurable(endpoint, { runtimeUrl });
    return { runtimeUrl, stop };
  } catch (error) { await stop(); throw error; }
  finally { lines.close(); process.removeListener('SIGINT', abort); process.removeListener('SIGTERM', abort); }
}
