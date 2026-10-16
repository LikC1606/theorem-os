import crypto from 'node:crypto';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, describe, expect, it } from 'vitest';
import { spawn } from 'node:child_process';
import { closeMathProcess, limitMathOutput, MATH_PROCESS_OUTPUT_LIMIT, runMathProcess, runLeanProcess } from '../src/math/mathProcess';

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
    const cancelledResult = await cancelled;
    expect(cancelledResult).toMatchObject({ aborted: true, lockAcquired: false });
    expect(cancelledResult.lockWaitMs).toBe(cancelledResult.durationMs);
    expect(cancelledResult.executionMs).toBeUndefined();
    expect(lockEvents).toEqual(['lean_lock_waiting']);
    for (const result of await Promise.all([first, second])) {
      expect(result).toMatchObject({ exitCode: 0, timedOut: false, lockAcquired: true });
      expect(result.lockWaitMs).toBeGreaterThanOrEqual(0);
      expect(result.executionMs).toBeGreaterThan(0);
      expect(result.lockWaitMs! + result.executionMs!).toBe(result.durationMs);
    }
    expect(fs.readFileSync(marker, 'utf8')).toBe('start\nend\nstart\nend\n');
  });

  it.skipIf(process.platform !== 'linux')('reports a timeout waiting for a Lean lock without claiming execution', async () => {
    const root = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'math-lean-lock-timeout-'))); roots.push(root);
    const holderMarker = path.join(root, 'holder');
    const waiterMarker = path.join(root, 'waiter');
    const env = { ...process.env, DEEPSCIENTIST_MATH_LEAN_LOCK: path.join(root, 'compile.lock') };
    const controller = new AbortController();
    const holder = runLeanProcess(process.execPath, ['-e', `require('node:fs').writeFileSync(${JSON.stringify(holderMarker)}, 'held'); setInterval(() => {}, 1000)`],
      { cwd: root, env, timeoutMs: Infinity, signal: controller.signal });
    const lockEvents: string[] = [];
    try {
      await expect.poll(() => fs.existsSync(holderMarker)).toBe(true);
      const result = await runLeanProcess(process.execPath, ['-e', `require('node:fs').writeFileSync(${JSON.stringify(waiterMarker)}, 'ran')`],
        { cwd: root, env, timeoutMs: 60, stopGraceMs: 0, onLockProgress: event => lockEvents.push(event) });
      expect(result).toMatchObject({ started: true, timedOut: true, aborted: false, lockAcquired: false });
      expect(result.lockWaitMs).toBe(result.durationMs);
      expect(result.lockWaitMs).toBeGreaterThan(0);
      expect(result.executionMs).toBeUndefined();
      expect(lockEvents).toEqual(['lean_lock_waiting']);
      expect(fs.existsSync(waiterMarker)).toBe(false);
    } finally {
      controller.abort();
      await holder;
    }
  });

  it.skipIf(process.platform !== 'linux')('separates a contended Lean lock wait from execution with no deadline', async () => {
    const root = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'math-lean-lock-wait-'))); roots.push(root);
    const holderMarker = path.join(root, 'holder');
    const releaseMarker = path.join(root, 'release');
    const env = { ...process.env, DEEPSCIENTIST_MATH_LEAN_LOCK: path.join(root, 'compile.lock') };
    const holderController = new AbortController();
    const waiterController = new AbortController();
    const holder = runLeanProcess(process.execPath, ['-e', `const fs = require('node:fs'); fs.writeFileSync(${JSON.stringify(holderMarker)}, 'held');
      const timer = setInterval(() => { if (fs.existsSync(${JSON.stringify(releaseMarker)})) clearInterval(timer); }, 10)`],
      { cwd: root, env, timeoutMs: Infinity, signal: holderController.signal });
    let waiter: ReturnType<typeof runLeanProcess> | undefined;
    const lockEvents: string[] = [];
    try {
      await expect.poll(() => fs.existsSync(holderMarker)).toBe(true);
      waiter = runLeanProcess(process.execPath, ['-e', "setTimeout(() => process.stdout.write('checked'), 40)"],
        { cwd: root, env, timeoutMs: Infinity, signal: waiterController.signal, onLockProgress: event => lockEvents.push(event) });
      await new Promise(resolve => setTimeout(resolve, 40));
      expect(lockEvents).toEqual(['lean_lock_waiting']);
      fs.writeFileSync(releaseMarker, 'release');
      const result = await waiter;
      expect(result).toMatchObject({ exitCode: 0, timedOut: false, aborted: false, lockAcquired: true, stdout: 'checked' });
      expect(result.lockWaitMs).toBeGreaterThanOrEqual(40);
      expect(result.executionMs).toBeGreaterThan(0);
      expect(result.lockWaitMs! + result.executionMs!).toBe(result.durationMs);
      expect(lockEvents).toEqual(['lean_lock_waiting', 'lean_lock_acquired']);
      expect(await holder).toMatchObject({ exitCode: 0 });
    } finally {
      holderController.abort(); waiterController.abort();
      await Promise.all([holder, waiter]);
    }
  });

  it.skipIf(process.platform !== 'linux')('records execution when a running locked check is cancelled', async () => {
    const root = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'math-lean-lock-abort-'))); roots.push(root);
    const marker = path.join(root, 'running');
    const controller = new AbortController();
    const pending = runLeanProcess(process.execPath, ['-e', `require('node:fs').writeFileSync(${JSON.stringify(marker)}, 'running'); setInterval(() => {}, 1000)`],
      { cwd: root, timeoutMs: Infinity, signal: controller.signal,
        env: { ...process.env, DEEPSCIENTIST_MATH_LEAN_LOCK: path.join(root, 'compile.lock') } });
    try {
      await expect.poll(() => fs.existsSync(marker)).toBe(true);
      controller.abort();
      const result = await pending;
      expect(result).toMatchObject({ aborted: true, timedOut: false, lockAcquired: true });
      expect(result.executionMs).toBeGreaterThan(0);
      expect(result.lockWaitMs! + result.executionMs!).toBe(result.durationMs);
    } finally { controller.abort(); await pending; }
  });

  it.skipIf(process.platform !== 'linux')('does not claim execution when the Lean lock cannot be opened', async () => {
    const root = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'math-lean-lock-error-'))); roots.push(root);
    const result = await runLeanProcess(process.execPath, ['-e', "process.stdout.write('unexpected')"], {
      cwd: root, timeoutMs: 5000,
      env: { ...process.env, DEEPSCIENTIST_MATH_LEAN_LOCK: path.join(root, 'missing/compile.lock') },
    });
    expect(result).toMatchObject({ lockAcquired: false, stdout: '' });
    expect(result.exitCode).not.toBe(0);
    expect(result.lockWaitMs).toBe(result.durationMs);
    expect(result.executionMs).toBeUndefined();
  });

  it('keeps unlocked process results compatible without lock timings', async () => {
    const result = await runLeanProcess(process.execPath, ['-e', "process.stdout.write('checked')"], {
      cwd: os.tmpdir(), timeoutMs: 5000, env: { ...process.env, DEEPSCIENTIST_MATH_LEAN_LOCK: '' },
    });
    expect(result).toMatchObject({ started: true, exitCode: 0, stdout: 'checked' });
    expect(result).not.toHaveProperty('lockAcquired');
    expect(result).not.toHaveProperty('lockWaitMs');
    expect(result).not.toHaveProperty('executionMs');
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
