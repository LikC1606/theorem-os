import crypto from 'node:crypto';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, describe, expect, it, vi } from 'vitest';
import { spawn, type ChildProcess } from 'node:child_process';
import { EventEmitter } from 'node:events';
import { closeMathProcess, confirmMathProcessStopped, limitMathOutput, MATH_PROCESS_OUTPUT_LIMIT, runMathProcess, runLeanProcess } from '../src/math/mathProcess';

const roots: string[] = [];
afterEach(() => { for (const root of roots.splice(0)) fs.rmSync(root, { recursive: true, force: true }); });

describe('process lifecycle and bounded output', () => {
  it.skipIf(process.platform !== 'linux')('serializes processes sharing a Lean lock and cancels a waiting check', async () => {
    const root = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'math-lean-lock-'))); roots.push(root);
    const marker = path.join(root, 'events');
    const lockEvents: string[] = [];
    const env = { ...process.env, DEEPSCIENTIST_MATH_LEAN_LOCK: path.join(root, 'compile.lock') };
    const script = `const fs = require('node:fs'); fs.appendFileSync(${JSON.stringify(marker)}, 'start\\n');
      setTimeout(() => fs.appendFileSync(${JSON.stringify(marker)}, 'end\\n'), 300);`;
    const first = runLeanProcess(process.execPath, ['-e', script], { cwd: root, env, timeoutMs: 5000 });
    await expect.poll(() => fs.existsSync(marker)).toBe(true);
    const controller = new AbortController();
    const cancelled = runLeanProcess(process.execPath, ['-e', script], { cwd: root, env, timeoutMs: 5000, signal: controller.signal,
      onLockProgress: event => lockEvents.push(event) });
    controller.abort();
    const second = runLeanProcess(process.execPath, ['-e', script], { cwd: root, env, timeoutMs: 5000 });
    expect(await cancelled).toMatchObject({ aborted: true });
    expect(lockEvents).toEqual(['lean_lock_waiting']);
    for (const result of await Promise.all([first, second])) expect(result).toMatchObject({ exitCode: 0, timedOut: false });
    expect(fs.readFileSync(marker, 'utf8')).toBe('start\nend\nstart\nend\n');
  });

  it.skipIf(process.platform !== 'linux')('preserves inherited descriptors through the Lean lock wrapper', async () => {
    const root = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'math-lean-fd-'))); roots.push(root);
    const input = path.join(root, 'input'); fs.writeFileSync(input, 'pinned input');
    const descriptor = fs.openSync(input, 'r');
    const lockEvents: string[] = [];
    try {
      const result = await runLeanProcess(process.execPath, ['-e', "process.stdout.write(require('node:fs').readFileSync(3, 'utf8'))"], {
        cwd: root, timeoutMs: 5000, inheritedFds: [descriptor],
        onLockProgress: event => lockEvents.push(event),
        env: { ...process.env, DEEPSCIENTIST_MATH_LEAN_LOCK: path.join(root, 'compile.lock') },
      });
      expect(result).toMatchObject({ exitCode: 0, stdout: 'pinned input' });
      expect(result.stderr).toBe('');
      expect(lockEvents).toEqual(['lean_lock_waiting', 'lean_lock_acquired']);
    } finally { fs.closeSync(descriptor); }
  });

  it('bounds graceful shutdown when a child ignores EOF and TERM', async () => {
    const child = spawn(process.execPath, ['-e', "process.on('SIGTERM', () => {}); process.stdout.write('ready'); setInterval(() => {}, 1000)"],
      { detached: process.platform !== 'win32', stdio: 'pipe' });
    await new Promise(resolve => child.stdout!.once('data', resolve));
    await closeMathProcess(child, true, 20);
    expect(child.signalCode).toBe('SIGKILL');
    if (process.platform !== 'win32') expect(await confirmMathProcessStopped(child)).toEqual({ status: 'stopped' });
  });

  it.skipIf(process.platform === 'win32')('does not turn a fallback cleanup resolution into confirmed writer exit', async () => {
    vi.useFakeTimers();
    const child = Object.assign(new EventEmitter(), { pid: 424242, exitCode: null, signalCode: null,
      stdin: { destroy: vi.fn() }, stdout: { destroy: vi.fn() }, stderr: { destroy: vi.fn() } }) as unknown as ChildProcess;
    const kill = vi.spyOn(process, 'kill').mockImplementation((_pid, signal) => {
      if (signal === 0) throw Object.assign(new Error('No process'), { code: 'ESRCH' });
      return true;
    });
    try {
      const closed = closeMathProcess(child, false, 0);
      await vi.advanceTimersByTimeAsync(1000); await closed;
      expect(await confirmMathProcessStopped(child, 0)).toEqual({ status: 'unconfirmed', reason: 'process-exit-unconfirmed' });
    } finally { kill.mockRestore(); vi.useRealTimers(); }
  });

  it.skipIf(process.platform === 'win32')('requires both observed child exit and an absent owned process group', async () => {
    const child = { pid: 424242, exitCode: 0, signalCode: null } as ChildProcess;
    const kill = vi.spyOn(process, 'kill').mockReturnValue(true);
    try {
      expect(await confirmMathProcessStopped(child, 0)).toEqual({ status: 'unconfirmed', reason: 'process-group-active' });
      kill.mockImplementation(() => { throw Object.assign(new Error('No permission'), { code: 'EPERM' }); });
      expect(await confirmMathProcessStopped(child, 0)).toEqual({ status: 'unconfirmed', reason: 'process-group-unavailable' });
      kill.mockImplementation(() => { throw Object.assign(new Error('No process'), { code: 'ESRCH' }); });
      expect(await confirmMathProcessStopped(child, 0)).toEqual({ status: 'stopped' });
    } finally { kill.mockRestore(); }
  });
  it('does not report a missing executable as started', async () => {
    const result = await runMathProcess('/nonexistent/math-command', [], { cwd: os.tmpdir(), timeoutMs: 1000 });
    expect(result).toMatchObject({ started: false, errorCode: 'ENOENT', timedOut: false });
  });

  it.each(['head', 'tail'] as const)('bounds %s output in bytes while hashing the complete stream', async outputCapture => {
    const output = 'start' + '数😀'.repeat(3000) + 'end';
    const result = await runMathProcess(process.execPath, ['-e', `process.stdout.write(${JSON.stringify(output)})`],
      { cwd: os.tmpdir(), timeoutMs: 5000, outputCapture });
    expect(result).toMatchObject({ started: true, exitCode: 0, stdoutSha256: crypto.createHash('sha256').update(output).digest('hex') });
    expect(Buffer.byteLength(result.stdout)).toBeLessThanOrEqual(MATH_PROCESS_OUTPUT_LIMIT);
    expect(result.stdout).not.toContain('�');
    expect(outputCapture === 'head' ? output.startsWith(result.stdout) : output.endsWith(result.stdout)).toBe(true);
    expect(limitMathOutput('😀', 3, outputCapture)).toBe('');
  });

  it('retains a true output prefix when a character crossing the byte limit arrives before a later chunk', async () => {
    const prefix = 'x'.repeat(MATH_PROCESS_OUTPUT_LIMIT - 1);
    const script = `process.stdout.write(${JSON.stringify(prefix)}); setTimeout(() => {
      process.stdout.write('😀'); setTimeout(() => process.stdout.write('a'), 20); }, 20);`;
    const result = await runMathProcess(process.execPath, ['-e', script], { cwd: os.tmpdir(), timeoutMs: 5000, outputCapture: 'head' });
    expect(result.stdout).toBe(prefix);
  });

  it.each(['head', 'tail'] as const)('retains bounded %s reports larger than the default limit for batched checks', async outputCapture => {
    const outputLimit = MATH_PROCESS_OUTPUT_LIMIT * 2;
    const output = 'start' + 'x'.repeat(outputLimit) + 'end';
    const result = await runMathProcess(process.execPath, ['-e', `process.stdout.write(${JSON.stringify(output)})`],
      { cwd: os.tmpdir(), timeoutMs: 5000, outputCapture, outputLimit });
    expect(result.exitCode).toBe(0);
    expect(result.stdout).toBe(outputCapture === 'head' ? output.slice(0, outputLimit) : output.slice(-outputLimit));
    expect(result.stdoutSha256).toBe(crypto.createHash('sha256').update(output).digest('hex'));
  });

  it.skipIf(process.platform === 'win32')('kills descendants after their wrapper has already exited', async () => {
    const root = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'math-process-'))); roots.push(root);
    const marker = path.join(root, 'child.pid');
    const script = `const child = require('node:child_process').spawn(process.execPath, ['-e', 'setInterval(() => {}, 1000)'], { stdio: ['ignore', 1, 2] });
      require('node:fs').writeFileSync(${JSON.stringify(marker)}, String(child.pid)); child.unref();`;
    let pid: number | undefined;
    try {
      const result = await runMathProcess(process.execPath, ['-e', script], { cwd: root, timeoutMs: 600, stopGraceMs: 0 });
      pid = Number(fs.readFileSync(marker, 'utf8'));
      expect(result).toMatchObject({ started: true, timedOut: true });
      await expect.poll(() => {
        try {
          process.kill(pid!, 0);
          return process.platform === 'linux' && /\) Z /.test(fs.readFileSync(`/proc/${pid}/stat`, 'utf8'));
        } catch { return true; }
      }).toBe(true);
    } finally {
      if (pid === undefined && fs.existsSync(marker)) pid = Number(fs.readFileSync(marker, 'utf8'));
      if (pid) try { process.kill(pid, 'SIGKILL'); } catch { /* Already reaped. */ }
    }
  });
});
