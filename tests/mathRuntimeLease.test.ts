import fs from 'node:fs';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import { afterEach, describe, expect, it } from 'vitest';
import { withMathRuntimeLease, type MathLease } from '../src/math/mathRuntimeIo';
import { temporaryDirectory } from './helpers/files';

const directories: string[] = [];

function fixture() {
  const directory = temporaryDirectory('math-runtime-lease-');
  directories.push(directory);
  return { directory, lockPath: path.join(directory, 'run.lock') };
}

function competingLock(lockPath: string): number | null {
  const result = spawnSync('/usr/bin/flock', ['--exclusive', '--nonblock', '--conflict-exit-code', '73',
    lockPath, '/usr/bin/true'], { timeout: 5_000 });
  if (result.error) throw result.error;
  return result.status;
}

afterEach(() => {
  for (const directory of directories.splice(0)) fs.rmSync(directory, { recursive: true, force: true });
});

describe('runtime lease ownership', () => {
  it('holds a real exclusive lock only for the operation scope', async () => {
    const current = fixture();
    let expired!: MathLease;
    await withMathRuntimeLease({ lockPath: current.lockPath, flockExecutable: '/usr/bin/flock' }, async lease => {
      expired = lease;
      expect(() => lease.assertOwned()).not.toThrow();
      expect(() => lease.assertHeld()).not.toThrow();
      expect(competingLock(current.lockPath)).toBe(73);
    });
    expect(competingLock(current.lockPath)).toBe(0);
    expect(() => expired.assertOwned()).toThrow('math_runtime_lease_lost');
    expect(() => expired.assertHeld()).toThrow('math_runtime_lease_lost');
  });

  it('permits a cancellation checkpoint while retaining the lock and rejects more work', async () => {
    const current = fixture(), controller = new AbortController();
    const checkpoint = path.join(current.directory, 'checkpoint.json');
    await expect(withMathRuntimeLease({ lockPath: current.lockPath, flockExecutable: '/usr/bin/flock',
      signal: controller.signal }, async lease => {
      controller.abort();
      expect(lease.signal.aborted).toBe(true);
      expect(() => lease.assertHeld()).toThrow('math_runtime_lease_lost');
      expect(() => lease.assertOwned()).not.toThrow();
      expect(competingLock(current.lockPath)).toBe(73);
      fs.writeFileSync(checkpoint, '{"status":"cancelled"}');
    })).rejects.toThrow('math_runtime_lease_lost');
    expect(fs.readFileSync(checkpoint, 'utf8')).toBe('{"status":"cancelled"}');
    expect(competingLock(current.lockPath)).toBe(0);
  });

  it('rejects ownership when the locked path is replaced, including after cancellation', async () => {
    const current = fixture(), controller = new AbortController();
    await expect(withMathRuntimeLease({ lockPath: current.lockPath, flockExecutable: '/usr/bin/flock',
      signal: controller.signal }, async lease => {
      fs.unlinkSync(current.lockPath);
      fs.writeFileSync(current.lockPath, '', { mode: 0o600 });
      expect(competingLock(current.lockPath)).toBe(0);
      expect(() => lease.assertOwned()).toThrow('math_runtime_lease_lost');
      controller.abort();
      expect(() => lease.assertOwned()).toThrow('math_runtime_lease_lost');
      expect(() => lease.assertHeld()).toThrow('math_runtime_lease_lost');
    })).rejects.toThrow('math_runtime_lease_lost');
  });
});
