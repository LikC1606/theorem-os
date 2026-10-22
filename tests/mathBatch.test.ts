import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { spawn } from 'node:child_process';
import { afterEach, describe, expect, it, vi } from 'vitest';
import { runMathBatch } from '../scripts/mathematics/runMathBatch';

const roots: string[] = [];
const temp = () => {
  const root = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'math-batch-')));
  roots.push(root); return root;
};
afterEach(() => {
  vi.restoreAllMocks();
  for (const root of roots.splice(0)) fs.rmSync(root, { recursive: true, force: true });
});

function fixture(root: string, id: string, exitCode = 0) {
  const directory = path.join(root, id), workspace = path.join(directory, 'workspace');
  fs.mkdirSync(workspace, { recursive: true });
  const script = path.join(directory, 'fake-solver.cjs');
  fs.writeFileSync(script, `const fs = require('node:fs');
    const envFile = process.env.DEEPSCIENTIST_MATH_ENV_FILE || '';
    fs.writeFileSync('started', String(process.pid));
    console.log('stdout:' + ${JSON.stringify(id)}); console.error('stderr:' + ${JSON.stringify(id)});
    process.on('SIGTERM', () => { fs.writeFileSync('checkpoint', 'saved'); process.exit(0); });
    const timer = setInterval(() => { if (fs.existsSync('release')) {
      fs.writeFileSync('result.json', JSON.stringify({ fixture: true, envFile, codexHome: process.env.CODEX_HOME || '' }));
      clearInterval(timer); process.exit(${exitCode});
    } }, 10);`);
  const launch = path.join(directory, 'launch.json');
  const config = { args: [process.execPath, script, '--workspace', workspace, '--output', path.join(directory, 'result.json')] };
  fs.writeFileSync(launch, JSON.stringify(config));
  return { directory, workspace, launch, config };
}

describe('independent problem batches', () => {
  it('limits concurrency, fills a freed slot after failure, and keeps logs and environments separate', async () => {
    vi.spyOn(console, 'log').mockImplementation(() => {});
    const root = temp(), a = fixture(root, 'a', 7), b = fixture(root, 'b'), c = fixture(root, 'c');
    const envFile = path.join(a.directory, 'math.env'); fs.writeFileSync(envFile, '');
    fs.writeFileSync(a.launch, JSON.stringify({ ...a.config, envFile: 'math.env' }));
    const output = path.join(root, 'batch.json');
    const running = runMathBatch(['--launch', a.launch, '--launch', b.launch, '--launch', c.launch, '--output', output]);
    try {
      await expect.poll(() => [a, b].every(job => fs.existsSync(path.join(job.directory, 'started')))).toBe(true);
      expect(fs.existsSync(path.join(c.directory, 'started'))).toBe(false);
      expect(JSON.parse(fs.readFileSync(output, 'utf8')).jobs.map(job => job.status)).toEqual(['running', 'running', 'pending']);
      fs.writeFileSync(path.join(a.directory, 'release'), '');
      await expect.poll(() => fs.existsSync(path.join(c.directory, 'started'))).toBe(true);
      expect(JSON.parse(fs.readFileSync(output, 'utf8')).jobs.map(job => job.status)).toEqual(['failed', 'running', 'running']);
    } finally {
      for (const job of [a, b, c]) fs.writeFileSync(path.join(job.directory, 'release'), '');
      await running;
    }
    expect(await running).toBe(1);
    const result = JSON.parse(fs.readFileSync(output, 'utf8'));
    expect(result.jobs.map(job => job.status)).toEqual(['failed', 'completed', 'completed']);
    expect(result.jobs.map(job => job.exitCode)).toEqual([7, 0, 0]);
    expect(result.finishedAt).toBeTruthy();
    expect(JSON.parse(fs.readFileSync(path.join(a.directory, 'result.json'), 'utf8')).envFile).toBe(envFile);
    expect(JSON.parse(fs.readFileSync(path.join(b.directory, 'result.json'), 'utf8')).envFile).toBe(process.env.DEEPSCIENTIST_MATH_ENV_FILE || '');
    for (const [index, id] of ['a', 'b', 'c'].entries()) {
      const log = fs.readFileSync(result.jobs[index].log, 'utf8');
      expect(log).toContain('stdout:' + id); expect(log).toContain('stderr:' + id);
      expect(log).not.toContain('stdout:' + (id === 'a' ? 'b' : 'a'));
    }
  });

  it('bounds an idle attempt, records it as stalled and continues the remaining jobs', async () => {
    vi.spyOn(console, 'log').mockImplementation(() => {});
    const root = temp(), idle = fixture(root, 'idle'), done = fixture(root, 'done');
    fs.writeFileSync(path.join(done.directory, 'release'), '');
    const output = path.join(root, 'batch.json');
    expect(await runMathBatch(['--launch', idle.launch, '--launch', done.launch,
      '--idle-timeout-seconds', '1', '--output', output])).toBe(0);
    const { jobs } = JSON.parse(fs.readFileSync(output, 'utf8'));
    expect(jobs[0]).toMatchObject({ status: 'stalled', stalled: true, error: 'idle-timeout' });
    expect(jobs[1]).toMatchObject({ status: 'completed', exitCode: 0 });
  }, 20_000);

  it('rejects an invalid idle timeout before starting jobs', async () => {
    vi.spyOn(console, 'log').mockImplementation(() => {});
    const root = temp(), a = fixture(root, 'a');
    await expect(runMathBatch(['--launch', a.launch, '--idle-timeout-seconds', 'soon',
      '--output', path.join(root, 'batch.json')])).rejects.toThrow('--idle-timeout-seconds must be a non-negative integer');
  });

  it('continues queued problems when an executable cannot start', async () => {
    vi.spyOn(console, 'log').mockImplementation(() => {});
    const root = temp(), a = fixture(root, 'a'), b = fixture(root, 'b');
    a.config.args[0] = '/nonexistent/math-batch-solver';
    fs.writeFileSync(a.launch, JSON.stringify(a.config));
    fs.writeFileSync(path.join(b.directory, 'release'), '');
    const output = path.join(root, 'batch.json');
    expect(await runMathBatch(['--launch', a.launch, '--launch', b.launch, '--concurrency', '1', '--output', output])).toBe(1);
    const { jobs } = JSON.parse(fs.readFileSync(output, 'utf8'));
    expect(jobs[0]).toMatchObject({ status: 'failed', error: expect.stringContaining('ENOENT') });
    expect(jobs[1]).toMatchObject({ status: 'completed', exitCode: 0 });
  });

  it('binds each launch to its prepared Codex profile instead of the caller profile', async () => {
    vi.spyOn(console, 'log').mockImplementation(() => {});
    const root = temp(), a = fixture(root, 'a'), b = fixture(root, 'b');
    for (const job of [a, b]) {
      fs.mkdirSync(path.join(job.directory, 'codex'), { mode: 0o700 });
      fs.writeFileSync(job.launch, JSON.stringify({ ...job.config, codexHome: 'codex' }));
      fs.writeFileSync(path.join(job.directory, 'release'), '');
    }
    const output = path.join(root, 'batch.json');
    expect(await runMathBatch(['--launch', a.launch, '--launch', b.launch, '--output', output])).toBe(0);
    const { jobs } = JSON.parse(fs.readFileSync(output, 'utf8'));
    for (const [index, job] of [a, b].entries()) {
      const expected = path.join(job.directory, 'codex');
      expect(JSON.parse(fs.readFileSync(path.join(job.directory, 'result.json'), 'utf8')).codexHome).toBe(expected);
      expect(jobs[index].codexHome).toBe(expected);
    }
  });

  it('rejects an invalid selected profile before starting any problem', async () => {
    const root = temp(), job = fixture(root, 'a');
    fs.writeFileSync(job.launch, JSON.stringify({ ...job.config, codexHome: job.launch }));
    await expect(runMathBatch(['--launch', job.launch, '--output', path.join(root, 'batch.json')])).rejects.toThrow('Invalid codexHome');
    expect(fs.existsSync(path.join(job.directory, 'started'))).toBe(false);
  });

  it('rejects shared workspaces and output paths before starting any problem', async () => {
    const root = temp(), a = fixture(root, 'a'), b = fixture(root, 'b');
    const output = path.join(root, 'batch.json');
    for (const flag of ['--workspace', '--output']) {
      const args = [...b.config.args];
      args[args.indexOf(flag) + 1] = a.config.args[a.config.args.indexOf(flag) + 1];
      fs.writeFileSync(b.launch, JSON.stringify({ args }));
      await expect(runMathBatch(['--launch', a.launch, '--launch', b.launch, '--output', output])).rejects.toThrow('separate workspaces and outputs');
    }
    expect(fs.existsSync(path.join(a.directory, 'started'))).toBe(false);
    expect(fs.existsSync(output)).toBe(false);
  });

  it('forwards cancellation through the CLI, lets active solvers checkpoint, and skips queued problems', async () => {
    const root = temp(), a = fixture(root, 'a'), b = fixture(root, 'b');
    const output = path.join(root, 'batch.json');
    const child = spawn('bun', [path.resolve('bin/math.ts'), 'batch', '--launch', a.launch,
      '--launch', b.launch, '--concurrency', '1', '--output', output], { stdio: 'ignore' });
    const closed = new Promise<number | null>((resolve, reject) => {
      child.once('error', reject); child.once('close', resolve);
    });
    try {
      await expect.poll(() => fs.existsSync(path.join(a.directory, 'started'))).toBe(true);
      child.kill('SIGTERM');
      expect(await closed).toBe(143);
      expect(fs.readFileSync(path.join(a.directory, 'checkpoint'), 'utf8')).toBe('saved');
      expect(fs.existsSync(path.join(b.directory, 'started'))).toBe(false);
      expect(JSON.parse(fs.readFileSync(output, 'utf8')).jobs.map(job => job.status)).toEqual(['cancelled', 'skipped']);
    } finally {
      if (child.exitCode === null && child.signalCode === null) child.kill('SIGTERM');
      await closed;
    }
  });
});
