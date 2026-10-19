import crypto from 'node:crypto';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import type { MathOfficialProblemManifest } from '../src/math/contracts';
import * as processes from '../src/math/mathProcess';
import { canonicalMathOfficialManifestPayload, checkManyFormalVerifications, runOfficialComparator,
  type MathematicsOfficialComparatorRequest } from '../src/math/verifier';

const git = (root: string, ...args: string[]) => {
  const result = spawnSync('git', ['-C', root, ...args], { encoding: 'utf8', timeout: 5000 });
  if (result.status !== 0) throw result.error ?? new Error(result.stderr);
  return result.stdout.trim();
};
const hash = (value: string) => crypto.createHash('sha256').update(value).digest('hex');
const seal = (input: MathOfficialProblemManifest) => ({ ...input, manifestHash: hash(canonicalMathOfficialManifestPayload(input)) });
const proofSource = 'theorem result : True := by trivial\n';

describe('official verifier identity and cleanup', () => {
  let directory: string;
  let root: string;
  let manifest: MathOfficialProblemManifest;
  let environment: NodeJS.ProcessEnv;
  let temporary: ReturnType<typeof vi.spyOn<typeof fs, 'mkdtempSync'>>;
  beforeEach(() => {
    directory = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'verifier-manifest-test-')));
    root = path.join(directory, 'repository');
    fs.mkdirSync(root);
    fs.writeFileSync(path.join(root, 'Support.lean'), proofSource);
    git(root, 'init', '--quiet');
    git(root, 'remote', 'add', 'origin', 'https://example.invalid/benchmark');
    git(root, 'add', '.');
    commit();
    manifest = seal({ schema: 'deepscientist.mathematics.official-manifest.v1', manifestId: 'fixture',
      manifestHash: '0'.repeat(64), problemId: 'fixture', informalStatement: 'True', formalStatement: 'theorem result : True',
      assumptions: [], statementHash: 'a'.repeat(64), leanStatementHash: 'b'.repeat(64),
      officialVerificationCommand: 'test -f Support.lean', repositoryUrl: 'https://example.invalid/benchmark',
      baselineCommit: git(root, 'rev-parse', 'HEAD'), benchmarkAdapterId: 'fixture', benchmarkAdapterVersion: '1',
      trackedFiles: [{ path: 'Support.lean', sha256: hash(proofSource) }] });
    const tools = path.join(directory, 'tools');
    fs.mkdirSync(path.join(tools, 'bin'), { recursive: true });
    fs.mkdirSync(path.join(tools, 'lib/lean'), { recursive: true });
    // A capturing backend completes locally without executing a compiler or model.
    for (const tool of ['bwrap', 'lean', 'lake'])
      fs.writeFileSync(path.join(tools, 'bin', tool), '#!/bin/sh\nexit 0\n', { mode: 0o700 });
    environment = { PATH: `${path.join(tools, 'bin')}:/usr/bin:/bin`, ELAN_HOME: tools,
      DEEPSCIENTIST_MATH_ENV_FILE: path.join(directory, 'absent.env'), DEEPSCIENTIST_MATH_SANDBOX_BACKEND: 'bwrap' };
    temporary = vi.spyOn(fs, 'mkdtempSync');
  });
  afterEach(() => {
    const directories = temporary.mock.results.filter(result => result.type === 'return').map(result => String(result.value));
    vi.restoreAllMocks();
    for (const owned of [...directories, directory]) fs.rmSync(owned, { recursive: true, force: true });
  });
  const commit = () => git(root, '-c', 'user.name=Fixture', '-c', 'user.email=fixture@localhost',
    'commit', '--quiet', '--allow-empty', '-m', 'fixture');
  const request = (source: 'committed' | 'supplied'): MathematicsOfficialComparatorRequest => {
    fs.writeFileSync(path.join(root, 'official.json'), JSON.stringify(manifest));
    git(root, 'add', '.');
    commit();
    environment.DEEPSCIENTIST_MATH_OFFICIAL_MANIFEST_HASH = manifest.manifestHash;
    return { projectRoot: root, targetCommit: git(root, 'rev-parse', 'HEAD'), command: manifest.officialVerificationCommand,
      problemId: manifest.problemId, statementHash: manifest.statementHash,
      ...(source === 'committed' ? { officialManifestPath: 'official.json' } : { officialManifest: manifest }) };
  };
  const expectClean = (before: string) => {
    expect(git(root, 'worktree', 'list', '--porcelain')).toBe(before);
    expect(temporary.mock.results.every(result => result.type !== 'return' || !fs.existsSync(String(result.value)))).toBe(true);
  };

  it.each(['committed', 'supplied'] as const)('rejects every %s manifest identity mismatch before execution', async source => {
    const cases = ['hash', 'target', 'command', 'problem', 'statement', 'contract'] as const;
    const valid = manifest;
    for (const failure of cases) {
      manifest = failure === 'target' ? seal({ ...valid, targetCommit: 'f'.repeat(40) }) : valid;
      if (failure === 'hash') manifest = { ...manifest, manifestHash: 'f'.repeat(64) };
      const input = request(source);
      if (failure === 'command') input.command = 'test -d Support.lean';
      if (failure === 'problem') input.problemId = 'other';
      if (failure === 'statement') input.statementHash = 'c'.repeat(64);
      if (failure === 'contract') input.expectedContract = { ...valid, knownTraps: [], acceptanceCriteria: ['Lean kernel'],
        leanStatementHash: 'c'.repeat(64) };
      const before = git(root, 'worktree', 'list', '--porcelain');
      const execution = vi.spyOn(processes, 'runLeanProcess');
      await expect(runOfficialComparator(input, { env: environment })).rejects.toThrow({
        hash: 'canonical contents', target: 'targetCommit does not match', command: source === 'committed'
          ? 'command frozen in the official problem manifest' : 'supplied official problem manifest',
        problem: 'problemId does not match', statement: 'statementHash does not match',
        contract: 'problem contract does not match the official problem manifest',
      }[failure]);
      expect(execution).not.toHaveBeenCalled();
      execution.mockRestore();
      expectClean(before);
    }
  });

  it.each(['committed', 'supplied'] as const)('preserves %s diagnostics when command and commit both differ', async source => {
    manifest = seal({ ...manifest, targetCommit: 'f'.repeat(40) });
    const input = request(source);
    input.command = 'test -d Support.lean';
    const before = git(root, 'worktree', 'list', '--porcelain');
    await expect(runOfficialComparator(input, { env: environment })).rejects.toThrow(source === 'committed'
      ? 'targetCommit does not match' : 'supplied official problem manifest');
    expectClean(before);
  });

  it('rejects a supplied manifest that differs from the committed bytes', async () => {
    const input = request('committed');
    input.officialManifest = seal({ ...manifest, informalStatement: 'different' });
    const before = git(root, 'worktree', 'list', '--porcelain');
    await expect(runOfficialComparator(input, { env: environment })).rejects.toThrow('differs from the committed manifest');
    expectClean(before);
  });

  it.each(['anchor', 'tracked-file'] as const)('still rejects a missing or inconsistent %s before execution', async failure => {
    if (failure === 'tracked-file') manifest = seal({ ...manifest, trackedFiles: [{ path: 'Support.lean', sha256: 'f'.repeat(64) }] });
    const input = request('committed');
    if (failure === 'anchor') delete environment.DEEPSCIENTIST_MATH_OFFICIAL_MANIFEST_HASH;
    const before = git(root, 'worktree', 'list', '--porcelain');
    const execution = vi.spyOn(processes, 'runLeanProcess');
    await expect(runOfficialComparator(input, { env: environment })).rejects.toThrow(failure === 'anchor'
      ? 'requires an external manifest anchor' : 'tracked file hash does not match');
    expect(execution).not.toHaveBeenCalled();
    expectClean(before);
  });

  it.runIf(process.platform === 'linux').each([
    ['none', 0], ['worktree', 0], ['temporary', 0], ['worktree', 3], ['temporary', 3],
  ] as const)('preserves official status and diagnostics with cleanup %s and exit %s', async (failure, exitCode) => {
    const input = request('committed');
    const execute = processes.runMathProcess;
    vi.spyOn(processes, 'runMathProcess').mockImplementation((command, args, settings) => {
      if (failure === 'worktree' && args[0] === 'worktree' && args[1] === 'remove')
        return Promise.resolve({ started: true, exitCode: 1, signal: null, stdout: '', stderr: 'fixture_remove',
          stdoutSha256: hash(''), stderrSha256: hash('fixture_remove'), timedOut: false, aborted: false, durationMs: 0 });
      return execute(command, args, settings);
    });
    const remove = fs.rmSync;
    vi.spyOn(fs, 'rmSync').mockImplementation((file, settings) => {
      if (failure === 'temporary' && path.basename(String(file)).startsWith('deepscientist-official-'))
        throw new Error('fixture_remove_directory');
      return remove(file, settings);
    });
    vi.spyOn(console, 'warn').mockImplementation(() => {});
    if (exitCode !== 0) vi.spyOn(processes, 'runLeanProcess').mockResolvedValue({
      started: true, exitCode, signal: null, stdout: '', stderr: '', stdoutSha256: hash(''), stderrSha256: hash(''),
      timedOut: false, aborted: false, durationMs: 0,
    });
    const result = await runOfficialComparator(input, { env: environment });
    expect(result.status).toBe(exitCode !== 0 ? 'failed' : failure === 'none' ? 'official_verified' : 'blocked');
    expect(Object.isFrozen(result)).toBe(true);
    expect(result).toMatchObject({ targetCommit: input.targetCommit, officialManifestHash: manifest.manifestHash,
      officialBaselineCommit: manifest.baselineCommit, stdoutSha256: hash(''), stderrSha256: hash(''), exitCode });
    if (failure !== 'none') {
      const reason = failure === 'worktree' ? 'git worktree remove failed: fixture_remove'
        : 'temporary directory cleanup failed: fixture_remove_directory';
      expect(result.cleanupError).toBe(reason);
      expect(result.error).toBe(exitCode === 0 ? `Official comparator cleanup failed: ${reason}`
        : `Official comparator exited with status ${exitCode}.`);
    }
  });

  it.runIf(process.platform === 'linux').each(['worktree', 'temporary'] as const)
  ('keeps local cleanup audit events and successful-receipt downgrade: %s', async failure => {
    const input = request('committed');
    const execute = processes.runMathProcess;
    vi.spyOn(processes, 'runMathProcess').mockImplementation((command, args, settings) => {
      if (failure === 'worktree' && args[0] === 'worktree' && args[1] === 'remove')
        return Promise.resolve({ started: true, exitCode: 1, signal: null, stdout: '', stderr: 'fixture_remove',
          stdoutSha256: hash(''), stderrSha256: hash('fixture_remove'), timedOut: false, aborted: false, durationMs: 0 });
      return execute(command, args, settings);
    });
    const remove = fs.rmSync;
    vi.spyOn(fs, 'rmSync').mockImplementation((file, settings) => {
      if (failure === 'temporary' && /^deepscientist-lean-[A-Za-z0-9]+$/u.test(path.basename(String(file))))
        throw new Error('fixture_remove_directory');
      return remove(file, settings);
    });
    vi.spyOn(console, 'warn').mockImplementation(() => {});
    const result = await checkManyFormalVerifications({ projectRoot: root, targetCommit: input.targetCommit,
      items: [{ proofPath: 'Support.lean', statementHash: manifest.statementHash },
        { id: 'mismatch', proofPath: 'Support.lean', theoremName: 'result', statementHash: manifest.statementHash,
          expectedSourceDeclarationHash: 'f'.repeat(64) }] }, { env: environment });
    const message = failure === 'worktree' ? 'Formal verification cleanup incomplete: git worktree remove failed: fixture_remove'
      : 'Formal verification temporary directory cleanup failed: fixture_remove_directory';
    expect(result.status).toBe('failed');
    expect(result.results).toHaveLength(2);
    expect(result.results[0]).toMatchObject({ status: 'blocked', cleanupError: message, error: message,
      proofHash: hash(proofSource), proofPath: 'Support.lean', targetCommit: input.targetCommit });
    expect(result.results[1]).toMatchObject({ status: 'failed', error: expect.stringContaining('immutable formal statement') });
    expect(result.results[1]).not.toHaveProperty('cleanupError');
    expect(result.events).toContainEqual(expect.objectContaining({ kind: 'diagnostic.emitted', payload: {
      source: failure === 'worktree' ? 'git' : 'process', severity: 'error', message,
    } }));
    expect(result.events.at(-1)).toMatchObject({ kind: 'session.closed', payload: { status: 'failed', resultCount: 2 } });
  });
});
