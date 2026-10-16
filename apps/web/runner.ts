import { spawn } from 'node:child_process';
import { execFile } from 'node:child_process';
import { promisify } from 'node:util';
import { z } from 'zod';
import type { WebConfig } from './config';
import type { WorkerInput, WorkerMessage } from './shared';

export type WebRunner = {
  readiness(): Promise<{ ready: boolean; message: string }>;
  run(input: WorkerInput, onMessage: (message: WorkerMessage) => void, signal: AbortSignal): Promise<void>;
};
const execute = promisify(execFile);
const workerMessageSchema = z.discriminatedUnion('type', [
  z.object({ type: z.literal('progress'), event: z.string().min(1).max(100), message: z.string().max(2_000) }).strict(),
  z.object({ type: z.literal('error'), message: z.string().min(1).max(2_000) }).strict(),
  z.object({ type: z.literal('result'), result: z.object({ status: z.string().min(1).max(100),
    proof: z.string().max(128 * 1024), report: z.record(z.unknown()) }).strict() }).strict(),
]);

export function parseWorkerMessage(line: string): WorkerMessage | undefined {
  try {
    const message = workerMessageSchema.safeParse(JSON.parse(line));
    return message.success ? message.data as WorkerMessage : undefined;
  } catch { return undefined; }
}

export class DockerWebRunner implements WebRunner {
  private cached?: { at: number; result: { ready: boolean; message: string } };
  constructor(private readonly config: Pick<WebConfig, 'workerImage'>) {}

  async readiness() {
    if (this.cached && Date.now() - this.cached.at < 10_000) return this.cached.result;
    const ready = await new Promise<boolean>(resolve => {
      const child = spawn('docker', ['image', 'inspect', this.config.workerImage], { stdio: 'ignore' });
      const timer = setTimeout(() => { child.kill('SIGKILL'); resolve(false); }, 5_000);
      child.once('error', () => { clearTimeout(timer); resolve(false); });
      child.once('close', code => { clearTimeout(timer); resolve(code === 0); });
    });
    const result = { ready, message: ready ? '运行环境就绪' : '运行镜像尚未就绪，请先构建 theorem-os-worker 镜像。' };
    this.cached = { at: Date.now(), result };
    return result;
  }

  async run(input: WorkerInput, onMessage: (message: WorkerMessage) => void, signal: AbortSignal): Promise<void> {
    signal.throwIfAborted();
    const name = `theoremos-web-${input.id}`;
    const environment = input.input.environment ?? 'standard';
    const mathlib = environment === 'mathlib';
    const memory = mathlib ? '8g' : '4g';
    const args = ['create', '--interactive', '--pull=never', '--name', name,
      '--log-driver=none', '--read-only', '--cap-drop=ALL', '--security-opt=no-new-privileges',
      '--security-opt=seccomp=unconfined', '--security-opt=apparmor=unconfined',
      '--security-opt=systempaths=unconfined',
      '--cpus=2', `--memory=${memory}`, `--memory-swap=${memory}`, '--pids-limit=256',
      '--tmpfs', '/work:rw,nosuid,nodev,size=536870912,uid=10001,gid=10001,mode=0700',
      '--tmpfs', '/tmp:rw,exec,nosuid,nodev,size=134217728,mode=1777',
      '--ulimit', 'nofile=1024:1024',
      ...(mathlib ? ['--device=/dev/fuse:/dev/fuse:rw', '--mount', 'type=volume,destination=/var/tmp'] : []),
      this.config.workerImage, environment];
    // Create first so cancellation always has a known container to remove.
    try {
      await execute('docker', args, { timeout: 30_000, maxBuffer: 8_192 });
    } catch {
      await execute('docker', ['rm', '--force', '--volumes', name], { timeout: 15_000 }).catch(() => {});
      throw new Error('无法创建隔离运行环境，请检查 Docker 与 worker 镜像。');
    }
    if (signal.aborted) {
      await execute('docker', ['rm', '--force', '--volumes', name], { timeout: 15_000 }).catch(() => {});
      signal.throwIfAborted();
    }
    try { await new Promise<void>((resolve, reject) => {
      const child = spawn('docker', ['start', '--attach', '--interactive', name], { stdio: ['pipe', 'pipe', 'ignore'] });
      let buffer = '', finished = false, receivedResult = false;
      let stopping: Promise<void> | undefined;
      const stop = () => stopping ??= new Promise<void>(done => {
        const cleanup = spawn('docker', ['rm', '--force', '--volumes', name], { stdio: 'ignore' });
        const timer = setTimeout(() => { cleanup.kill('SIGKILL'); child.kill('SIGKILL'); done(); }, 15_000);
        const complete = () => { clearTimeout(timer); child.kill('SIGTERM'); done(); };
        cleanup.once('error', complete); cleanup.once('close', complete);
      });
      const abort = () => { void stop(); };
      const timer = setTimeout(abort, (input.input.maxRunSeconds + (mathlib ? 600 : 0) + 240) * 1_000);
      signal.addEventListener('abort', abort, { once: true });
      const finish = async (error?: Error) => {
        if (finished) return;
        finished = true; clearTimeout(timer); signal.removeEventListener('abort', abort);
        if (error || signal.aborted) await stop();
        await stopping;
        if (error) reject(error); else resolve();
      };
      child.stdout.setEncoding('utf8');
      child.stdout.on('data', chunk => {
        buffer += chunk;
        if (buffer.length > 2 * 1024 * 1024) { void finish(new Error('运行输出超出限制。')); return; }
        for (;;) {
          const newline = buffer.indexOf('\n');
          if (newline < 0) break;
          const line = buffer.slice(0, newline); buffer = buffer.slice(newline + 1);
          const message = parseWorkerMessage(line);
          if (message) {
            if (message.type === 'result') receivedResult = true;
            onMessage(message);
          }
        }
      });
      child.stdin.on('error', () => {});
      child.once('error', () => { void finish(new Error('无法启动隔离运行环境。')); });
      child.once('close', () => { void finish(!signal.aborted && !receivedResult ? new Error('运行环境已退出，未返回验收结果。') : undefined); });
      // Credentials travel over the private input pipe, never Docker args, env or logs.
      child.stdin.end(JSON.stringify(input) + '\n');
      if (signal.aborted) abort();
    }); } finally {
      await execute('docker', ['rm', '--force', '--volumes', name], { timeout: 15_000 }).catch(() => {});
    }
  }
}
