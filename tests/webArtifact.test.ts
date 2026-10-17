import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { createWebArtifactSampler, readWebResultProof } from '../apps/web/worker';
import { webArtifactMaxBytes, type WebArtifact } from '../apps/web/shared';

describe('live web Lean candidates without model calls', () => {
  let directory: string;
  let output: string;
  let artifacts: WebArtifact[];
  const source = 'theorem example : True := by sorry\n';
  const candidate = 'theorem example : True := by trivial\n';
  const roots: string[] = [];
  const temporary = () => {
    const root = fs.mkdtempSync(path.join(os.tmpdir(), 'theoremos-artifact-'));
    roots.push(root);
    return root;
  };
  const file = (index = 0, result = output) => path.join(result + '.runtime',
    index ? `worktree-${index + 1}` : 'worktree', 'generated/problem/Submission.lean');
  const write = (text: string | Buffer, index = 0, result = output) => {
    const target = file(index, result);
    fs.mkdirSync(path.dirname(target), { recursive: true });
    fs.writeFileSync(target, text);
    return target;
  };
  const sampler = (workers = 1, apiKey = 'sk-local-test-only', result = output) => createWebArtifactSampler({
    directory, output: result, workers, source, apiKey, onArtifact: artifact => artifacts.push(artifact),
  });
  beforeEach(() => {
    directory = temporary();
    output = path.join(directory, 'result.json');
    artifacts = [];
  });
  afterEach(() => {
    vi.restoreAllMocks();
    roots.splice(0).forEach(root => fs.rmSync(root, { recursive: true, force: true }));
  });

  it('publishes changed source once and always identifies it as an unaccepted candidate', () => {
    const sample = sampler();
    sample();
    write(source);
    sample();
    expect(artifacts).toEqual([]);
    write(candidate);
    sample(); sample();
    expect(artifacts).toHaveLength(1);
    expect(artifacts[0]).toEqual({ source: candidate, workerId: 'solver',
      capturedAt: expect.stringMatching(/^\d{4}-\d\d-\d\dT.*Z$/), status: 'candidate' });
    write(source);
    sample();
    expect(artifacts.at(-1)?.source).toBe(source);
    expect(artifacts.every(artifact => artifact.status === 'candidate')).toBe(true);
  });

  it('keeps the most recently changed fixed worker source and deduplicates identical content across workers', () => {
    const sample = sampler(3);
    [0, 1, 2].forEach(index => write(source, index));
    sample();
    const lead = write(candidate, 0), engineer = write(candidate + '-- Engineer\n', 2);
    fs.utimesSync(lead, 1_700_000_000, 1_700_000_001);
    fs.utimesSync(engineer, 1_700_000_000, 1_700_000_002);
    sample();
    expect(artifacts.at(-1)).toMatchObject({ workerId: 'engineer', source: candidate + '-- Engineer\n' });
    write(candidate + '-- Researcher\n', 1);
    sample();
    expect(artifacts.at(-1)?.workerId).toBe('researcher-1');
    write(candidate + '-- Researcher\n', 0);
    sample();
    expect(artifacts).toHaveLength(2);
  });

  it('never searches arbitrary directories or unconfigured worker slots', () => {
    write(candidate, 1);
    const arbitrary = path.join(directory, 'unexpected/generated/problem');
    fs.mkdirSync(arbitrary, { recursive: true });
    fs.writeFileSync(path.join(arbitrary, 'Submission.lean'), candidate);
    sampler()();
    expect(artifacts).toEqual([]);
  });

  it.each(['file', 'parent', 'worktree', 'runtime'] as const)('rejects a symlink at the %s boundary even when it points inside the run', kind => {
    write(candidate);
    const target = kind === 'file' ? file() : kind === 'parent' ? path.dirname(file())
      : kind === 'worktree' ? path.join(output + '.runtime', 'worktree') : output + '.runtime';
    const moved = path.join(directory, 'moved');
    fs.renameSync(target, moved);
    fs.symlinkSync(moved, target, kind === 'file' ? 'file' : 'dir');
    sampler()();
    expect(artifacts).toEqual([]);
  });

  it('rejects escaping paths, external symlinks and hardlinks', () => {
    const external = path.join(temporary(), 'result.json');
    const externalFile = write(candidate, 0, external);
    sampler(1, 'sk-local-test-only', external)();
    expect(artifacts).toEqual([]);
    fs.mkdirSync(path.dirname(file()), { recursive: true });
    fs.symlinkSync(externalFile, file());
    sampler()();
    expect(artifacts).toEqual([]);
    fs.unlinkSync(file());
    fs.linkSync(externalFile, file());
    sampler()();
    expect(artifacts).toEqual([]);
  });

  it('rejects a directory replaced by a symlink between inspection and opening the file', () => {
    write(candidate);
    const external = path.join(temporary(), 'result.json');
    write('-- private outside the run\n', 0, external);
    const localTree = path.join(output + '.runtime', 'worktree');
    const externalTree = path.join(external + '.runtime', 'worktree');
    const open = fs.openSync;
    vi.spyOn(fs, 'openSync').mockImplementation((target, flags, mode) => {
      if (target === file()) {
        fs.renameSync(localTree, localTree + '-moved');
        fs.symlinkSync(externalTree, localTree, 'dir');
      }
      return open(target, flags, mode);
    });
    sampler()();
    expect(artifacts).toEqual([]);
  });

  it.each(['empty', 'invalid utf8', 'oversized ascii', 'oversized utf8', 'directory'] as const)('ignores %s files and preserves the latest usable candidate', kind => {
    const sample = sampler();
    write(candidate); sample();
    if (kind === 'directory') { fs.unlinkSync(file()); fs.mkdirSync(file()); }
    else write(kind === 'empty' ? '' : kind === 'invalid utf8' ? Buffer.from([0xff, 0xfe])
      : kind === 'oversized utf8' ? '\u8bc1'.repeat(Math.floor(webArtifactMaxBytes / 3) + 1)
        : 'x'.repeat(webArtifactMaxBytes + 1));
    sample();
    expect(artifacts).toHaveLength(1);
    expect(artifacts[0].source).toBe(candidate);
  });

  it('redacts the key before publishing source and enforces the byte limit after redaction', () => {
    const key = 'sk-quote-"-slash-\\-secret';
    write(`-- ${key}\n${candidate}`);
    sampler(1, key)();
    expect(artifacts).toHaveLength(1);
    expect(artifacts[0].source).toBe(`-- [REDACTED]\n${candidate}`);
    expect(JSON.stringify(artifacts)).not.toContain(JSON.stringify(key).slice(1, -1));
    artifacts = [];
    write('12345678'.repeat(webArtifactMaxBytes / 8));
    sampler(1, '12345678')();
    expect(artifacts).toEqual([]);
  });

  it.each(['incomplete', 'limit_reached', 'runtime_error'])('retains a parallel worker\'s last safe source when %s has no winner', status => {
    const key = 'sk-parallel-candidate-only';
    write(source);
    write(`-- ${key}\n${candidate}`, 1);
    sampler(2, key)();
    expect(artifacts.at(-1)?.workerId).toBe('engineer');
    const proof = readWebResultProof({ directory, workspace: path.join(directory, 'workspace'), status,
      winningWorker: undefined, state: { worktree: path.join(output + '.runtime', 'worktree') }, artifact: artifacts.at(-1) });
    expect(proof).toBe(`-- [REDACTED]\n${candidate}`);
    expect(proof).not.toContain('sorry');
    expect(proof).not.toContain(key);
  });

  it('uses the selected worker proof over an unrelated live candidate', () => {
    write('-- Lead\n' + source);
    write(candidate, 1);
    const state = { worktree: path.join(output + '.runtime', 'worktree'),
      workers: [{ id: 'engineer', worktree: path.join(output + '.runtime', 'worktree-2') }] };
    expect(readWebResultProof({ directory, workspace: path.join(directory, 'workspace'), status: 'runtime_error',
      winningWorker: 'engineer', state, artifact: { source, workerId: 'solver',
        capturedAt: new Date().toISOString(), status: 'candidate' } })).toBe(candidate);
  });

  it('keeps a single worker\'s selected proof even without a winningWorker field', () => {
    write(candidate);
    expect(readWebResultProof({ directory, workspace: path.join(directory, 'workspace'), status: 'limit_reached',
      winningWorker: undefined, state: { worktree: path.join(output + '.runtime', 'worktree'), check: { passed: true } },
      artifact: { source, workerId: 'solver', capturedAt: new Date().toISOString(), status: 'candidate' } })).toBe(candidate);
  });

  it('uses the integrated accepted proof over every unaccepted snapshot', () => {
    const workspace = path.join(directory, 'workspace');
    fs.mkdirSync(path.join(workspace, 'generated/problem'), { recursive: true });
    fs.writeFileSync(path.join(workspace, 'generated/problem/Submission.lean'), candidate + '-- Integrated\n');
    write(candidate);
    expect(readWebResultProof({ directory, workspace, status: 'evaluated_passed', winningWorker: undefined,
      state: { worktree: path.join(output + '.runtime', 'worktree') }, artifact: { source,
        workerId: 'engineer', capturedAt: new Date().toISOString(), status: 'candidate' } })).toBe(candidate + '-- Integrated\n');
  });

  it('still reads the worktree when no snapshot exists', () => {
    write(candidate);
    expect(readWebResultProof({ directory, workspace: path.join(directory, 'workspace'), status: 'incomplete',
      winningWorker: undefined, state: { worktree: path.join(output + '.runtime', 'worktree') } })).toBe(candidate);
  });
});
