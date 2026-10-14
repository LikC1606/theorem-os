import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import { afterEach, describe, expect, it, vi } from 'vitest';
import { checkManyFormalVerifications } from '../src/math/verifier';
import { mathDigest } from '../src/math/mathRuntimeIo';

const roots: string[] = [];
const git = (root: string, args: string[]) => {
  const result = spawnSync('git', ['-C', root, ...args], { encoding: 'utf8', timeout: 5000 });
  if (result.status !== 0) throw result.error ?? new Error(result.stderr);
  return result.stdout.trim();
};
const fixture = () => {
  const root = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'math-batch-'))); roots.push(root);
  for (const name of ['First', 'Second']) fs.writeFileSync(path.join(root, `${name}.lean`), `theorem ${name.toLowerCase()} : True := by trivial\n`);
  git(root, ['init', '--quiet']); git(root, ['add', '.']);
  git(root, ['-c', 'user.name=Fixture', '-c', 'user.email=fixture@localhost', 'commit', '--quiet', '--no-gpg-sign', '-m', 'baseline']);
  return { root, commit: git(root, ['rev-parse', 'HEAD']), items: ['Second', 'First'].map(name => ({
    proofPath: `${name}.lean`, theoremName: name.toLowerCase(), statementHash: 'a'.repeat(64), claim: 'statement' as const })) };
};
afterEach(() => { vi.restoreAllMocks(); for (const root of roots.splice(0)) fs.rmSync(root, { recursive: true, force: true }); });

describe('formal batch source binding without model or compiler calls', () => {
  it('rejects mismatched declaration headers independently and removes its verifier checkout', async () => {
    const { root, commit, items } = fixture();
    const before = git(root, ['worktree', 'list', '--porcelain']);
    const result = await checkManyFormalVerifications({ projectRoot: root, targetCommit: commit,
      items: items.map(item => ({ ...item, expectedSourceDeclarationHash: 'b'.repeat(64) })) },
      { env: {}, verifierCommandPath: '/nonexistent/math-lean' });
    expect(result.status).toBe('failed');
    expect(result.results.map(receipt => receipt.proofPath)).toEqual(items.map(item => item.proofPath));
    expect(result.results.map(({ status, error }) => ({ status, error }))).toEqual(
      items.map(() => ({ status: 'failed', error: expect.stringContaining('immutable formal statement') })));
    expect(git(root, ['worktree', 'list', '--porcelain'])).toBe(before);
  }, 20_000);

  it('removes the verifier checkout when local dependency preparation throws', async () => {
    const { root, items } = fixture();
    fs.mkdirSync(path.join(root, '.lake/build'), { recursive: true });
    fs.writeFileSync(path.join(root, '.lake/build/stale.olean'), 'fixture');
    git(root, ['add', '-f', '.lake/build/stale.olean']);
    git(root, ['-c', 'user.name=Fixture', '-c', 'user.email=fixture@localhost', 'commit', '--quiet', '--no-gpg-sign', '-m', 'stale output']);
    const before = git(root, ['worktree', 'list', '--porcelain']);
    let checkout: string | undefined;
    const remove = fs.rmSync;
    vi.spyOn(fs, 'rmSync').mockImplementation((file, options) => {
      if (String(file).endsWith('/.lake/build')) {
        checkout = path.dirname(path.dirname(String(file)));
        throw new Error('fixture_batch_preparation_failed');
      }
      remove(file, options);
    });
    await expect(checkManyFormalVerifications({ projectRoot: root, targetCommit: git(root, ['rev-parse', 'HEAD']), items },
      { env: {}, verifierCommandPath: '/nonexistent/math-lean', prepareLocalDependencies: true })).rejects.toThrow('fixture_batch_preparation_failed');
    expect(checkout).toBeDefined();
    expect(fs.existsSync(checkout!)).toBe(false);
    expect(git(root, ['worktree', 'list', '--porcelain'])).toBe(before);
  }, 20_000);

  it('blocks proofs whose saved bytes differ from the pinned commit, preserving request order', async () => {
    const { root, commit, items } = fixture();
    for (const item of items) fs.writeFileSync(path.join(root, item.proofPath), `theorem ${item.theoremName} : True := by exact True.intro\n`);
    const result = await checkManyFormalVerifications({ projectRoot: root, targetCommit: commit, items },
      { env: {}, verifierCommandPath: '/nonexistent/math-lean' });
    expect(result.status).toBe('blocked');
    expect(result.results.map(receipt => receipt.proofPath)).toEqual(items.map(item => item.proofPath));
    expect(result.results.map(({ status, error }) => ({ status, error }))).toEqual(
      items.map(() => ({ status: 'blocked', error: expect.stringContaining('clean committed checkout') })));
  }, 20_000);

  it('shares one source snapshot across checks while preserving their identities and order', async () => {
    const { root, commit, items } = fixture();
    const requestItems = [...items, { ...items[0], id: 'repeated-check', statementHash: 'c'.repeat(64) }]
      .map(item => ({ ...item, expectedSourceDeclarationHash: 'b'.repeat(64) }));
    const reads = vi.spyOn(fs.promises, 'readFile');
    const result = await checkManyFormalVerifications({ projectRoot: root, targetCommit: commit, items: requestItems },
      { env: {}, verifierCommandPath: '/nonexistent/math-lean' });
    expect(result.results.map(item => [item.checkId, item.proofPath, item.statementHash])).toEqual(
      requestItems.map((item, index) => [item.id ?? `check-${index + 1}`, item.proofPath, item.statementHash]));
    expect(result.results.every(item => item.status === 'failed')).toBe(true);
    for (const item of items)
      expect(reads.mock.calls.filter(([file]) => String(file) === path.join(root, item.proofPath))).toHaveLength(1);
  }, 20_000);

  it.each(['rewrite', 'replace'])('discards stale source snapshots after a %s during preparation', async change => {
    const { root, commit, items } = fixture();
    const file = path.join(root, items[0].proofPath);
    const updated = `theorem ${items[0].theoremName} : True := by exact True.intro\n`;
    let changed = false;
    const mutate = (input: unknown) => {
      if (String(input) !== file || changed) return;
      changed = true;
      const stat = fs.statSync(file);
      if (change === 'replace') {
        fs.writeFileSync(`${file}.replacement`, updated);
        fs.renameSync(`${file}.replacement`, file);
      } else fs.writeFileSync(file, updated);
      fs.utimesSync(file, stat.atime, stat.mtime);
    };
    const readSync = fs.readFileSync;
    const readAsync = fs.promises.readFile;
    vi.spyOn(fs, 'readFileSync').mockImplementation((input, options) => {
      const value = readSync(input, options);
      mutate(input);
      return value;
    });
    vi.spyOn(fs.promises, 'readFile').mockImplementation(async (input, options) => {
      const value = await readAsync(input, options);
      mutate(input);
      return value;
    });
    const result = await checkManyFormalVerifications({ projectRoot: root, targetCommit: commit, items },
      { env: {}, verifierCommandPath: '/nonexistent/math-lean' });
    expect(changed).toBe(true);
    expect(result.status).toBe('blocked');
    expect(result.results[0]).toMatchObject({ proofPath: items[0].proofPath, proofHash: mathDigest(updated) });
    expect(result.results.map(item => item.proofPath)).toEqual(items.map(item => item.proofPath));
  }, 20_000);
});
