#!/usr/bin/env bun
import fs from 'node:fs';
import path from 'node:path';
import os from 'node:os';
import { MathRuntime } from '../src/runtime/mathRuntime';

type Socket = { send: (value: string) => void };
type BunServer = { port: number; upgrade: (request: Request) => boolean; stop: (closeConnections: boolean) => void };
declare const Bun: { serve: (options: {
  hostname: string; port: number;
  fetch: (request: Request, server: BunServer) => Response | Promise<Response> | undefined;
  websocket: { open: (socket: Socket) => void; message: (socket: Socket, message: string | Buffer) => void; close: (socket: Socket) => void };
}) => BunServer };

const args = process.argv.slice(2);
const value = (flag: string, fallback: string): string => {
  const index = args.indexOf(flag);
  if (index < 0) return fallback;
  if (!args[index + 1] || args[index + 1].startsWith('--')) throw new Error(`Missing value for ${flag}`);
  return args[index + 1];
};
if (args.includes('--help') || args.includes('-h')) {
  console.log('Usage: deepscientist-math runtime [--data-dir DIRECTORY] [--port PORT] [--codex EXECUTABLE]\nStarts the bundled mathematics runtime on loopback. No native Core bundle is needed.');
} else {
  const port = Number(value('--port', '25820'));
  if (!Number.isInteger(port) || port < 0 || port > 65535) throw new Error('Invalid runtime port');
  const dataDirectory = path.resolve(value('--data-dir', path.join(os.homedir(), '.local/share/deepscientist-math')));
  fs.mkdirSync(dataDirectory, { recursive: true, mode: 0o700 });
  const stat = fs.lstatSync(dataDirectory);
  if (!stat.isDirectory() || stat.isSymbolicLink() || (stat.mode & 0o077) || (process.getuid && stat.uid !== process.getuid()))
    throw new Error('math_runtime_data_directory_not_private');
  const lock = path.join(dataDirectory, 'math-runtime.lock');
  const identity = (pid: number): string | undefined => {
    try { const stat = fs.readFileSync(`/proc/${pid}/stat`, 'utf8'); return stat.slice(stat.lastIndexOf(')') + 2).split(' ')[19]; }
    catch { return undefined; }
  };
  if (fs.existsSync(lock)) {
    const owner = JSON.parse(fs.readFileSync(lock, 'utf8'));
    if (owner.start && owner.start === identity(owner.pid)) throw new Error('math_runtime_already_running');
    fs.unlinkSync(lock);
  }
  fs.writeFileSync(lock, JSON.stringify({ pid: process.pid, start: identity(process.pid) }), { flag: 'wx', mode: 0o600 });
  const entry = fs.realpathSync(process.argv[1]);
  const root = path.resolve(path.dirname(entry), path.basename(path.dirname(entry)) === 'scripts' ? '..' : '../..');
  const sockets = new Set<Socket>();
  let runtime: MathRuntime | undefined;
  let server: BunServer | undefined;
  try {
    server = Bun.serve({
      hostname: '127.0.0.1', port,
      fetch: (request, server) => {
        const url = new URL(request.url);
        if (url.pathname === '/ws') {
          if (request.headers.get('origin') && request.headers.get('origin') !== `http://127.0.0.1:${server.port}`)
            return new Response('Forbidden', { status: 403 });
          if (server.upgrade(request)) return;
          return new Response('WebSocket upgrade required', { status: 400 });
        }
        return runtime!.handle(request);
      },
      websocket: {
        open: socket => { sockets.add(socket); },
        message: (socket, data) => {
          try {
            if (String(data).length > 4096) return;
            const message = JSON.parse(String(data));
            if (message.name === 'runtime.subscribe') socket.send(JSON.stringify({ name: 'runtime.subscriptionReady', data: { protocolVersion: 1 } }));
          } catch { /* A malformed client message cannot mutate runtime state. */ }
        },
        close: socket => { sockets.delete(socket); },
      },
    });
    const baseUrl = `http://127.0.0.1:${server.port}`;
    runtime = new MathRuntime({ dataDirectory, root, baseUrl, entryFile: entry,
      codexExecutable: value('--codex', process.env.DEEPSCIENTIST_MATH_CODEX_EXECUTABLE || 'codex'),
      codexProfile: process.env.CODEX_HOME || path.join(os.homedir(), '.config/deepscientist/math-sol-codex'),
      onEvent: (name, data) => {
        const message = JSON.stringify({ name, data });
        for (const socket of sockets) {
          try { socket.send(message); } catch { sockets.delete(socket); }
        }
      },
    });
    let stopping = false;
    const stop = async (code: number): Promise<void> => {
      if (stopping) return;
      stopping = true;
      try { await runtime!.close(); }
      finally { server!.stop(true); fs.unlinkSync(lock); process.exit(code); }
    };
    process.once('SIGINT', () => void stop(130));
    process.once('SIGTERM', () => void stop(0));
    process.stdout.write(`${JSON.stringify({ runtimeUrl: baseUrl, dataDirectory, pid: process.pid })}\n`);
  } catch (error) {
    server?.stop(true);
    fs.unlinkSync(lock);
    throw error;
  }
}
