import crypto from 'node:crypto';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it } from 'vitest';
import { listLeanProbePackageInputs, readLeanProbeSnapshotFile } from '../src/math/leanProbeSnapshot';

describe('Lean dependency snapshots', () => {
  let directory: string;
  beforeEach(() => {
    directory = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'lean-snapshot-buffer-')));
  });
  afterEach(() => fs.rmSync(directory, { recursive: true, force: true }));

  it('copies and hashes binary files, partial chunks and empty files without retaining prior bytes', () => {
    const buffer = Buffer.alloc(1024, 0xff);
    for (const [index, length] of [2051, 0, 17, 1024].entries()) {
      const bytes = Buffer.from(Array.from({ length }, (_, i) => (i + index) % 256));
      const source = path.join(directory, `source-${index}`);
      const target = path.join(directory, `copy-${index}`);
      fs.writeFileSync(source, bytes, { mode: 0o700 });
      fs.utimesSync(source, 1_000_000 + index, 2_000_000 + index);
      const result = readLeanProbeSnapshotFile(source, () => {}, target, buffer);
      expect(result.digest).toBe(crypto.createHash('sha256').update(bytes).digest('hex'));
      expect(result.bytes).toBe(length);
      const copied = fs.statSync(target);
      const original = fs.statSync(source);
      expect(Math.abs(copied.atimeMs - original.atimeMs)).toBeLessThan(1);
      expect(Math.abs(copied.mtimeMs - original.mtimeMs)).toBeLessThan(1);
      expect(fs.readFileSync(target)).toEqual(bytes);
      expect(copied.mode & 0o777).toBe(0o500);
      expect(copied.ino).not.toBe(original.ino);
      expect(readLeanProbeSnapshotFile(source, () => {}, undefined, buffer)).toEqual(result);
    }
  });

  it('still rejects source changes during a buffered read', () => {
    const source = path.join(directory, 'changing');
    fs.writeFileSync(source, Buffer.alloc(2048));
    let checkpoints = 0;
    expect(() => readLeanProbeSnapshotFile(source, () => {
      if (++checkpoints === 2) fs.appendFileSync(source, 'changed');
    }, undefined, Buffer.alloc(1024))).toThrow('dependency changed during snapshot creation');
  });

  it('rejects an existing destination without modifying it', () => {
    const source = path.join(directory, 'source');
    const target = path.join(directory, 'existing');
    fs.writeFileSync(source, 'new bytes');
    fs.writeFileSync(target, 'keep these bytes');
    expect(() => readLeanProbeSnapshotFile(source, () => {}, target)).toThrow();
    expect(fs.readFileSync(target, 'utf8')).toBe('keep these bytes');
  });

  it('enumerates directory aliases independently in stable order and excludes Git metadata', () => {
    const dependency = path.join(directory, 'dependency');
    fs.mkdirSync(path.join(dependency, '.git'), { recursive: true });
    fs.writeFileSync(path.join(dependency, '.git', 'config'), 'excluded');
    for (const name of ['Z.lean', 'A.lean']) fs.writeFileSync(path.join(dependency, name), name);
    fs.symlinkSync(dependency, path.join(directory, 'absolute-alias'));
    fs.symlinkSync('dependency', path.join(directory, 'relative-alias'));

    const inputs = listLeanProbePackageInputs(directory, () => {});
    expect(inputs.map(input => input.relative)).toEqual([
      'absolute-alias/A.lean', 'absolute-alias/Z.lean',
      'dependency/A.lean', 'dependency/Z.lean',
      'relative-alias/A.lean', 'relative-alias/Z.lean',
    ]);
    for (const input of inputs) {
      expect(input.source).toBe(path.join(dependency, path.basename(input.relative)));
      expect(input.links).toHaveLength(input.relative.startsWith('dependency/') ? 0 : 1);
    }
  });

  it('excludes reference sources and artifacts without changing the source cache', () => {
    for (const file of ['Solution.lean', '.lake/build/lib/lean/Solution.olean', '.lake/build/ir/Solution.c', 'Public.lean']) {
      fs.mkdirSync(path.dirname(path.join(directory, file)), { recursive: true });
      fs.writeFileSync(path.join(directory, file), 'bytes');
    }
    expect(listLeanProbePackageInputs(directory, () => {}).map(input => input.relative)).toEqual(['Public.lean']);
    expect(fs.existsSync(path.join(directory, 'Solution.lean'))).toBe(true);
    fs.symlinkSync('Solution.lean', path.join(directory, 'Alias.lean'));
    expect(() => listLeanProbePackageInputs(directory, () => {})).toThrow('excluded reference module');
  });

  it('rejects a directory link to an ancestor', () => {
    const dependency = path.join(directory, 'dependency');
    fs.mkdirSync(dependency);
    fs.symlinkSync('..', path.join(dependency, 'back'));
    expect(() => listLeanProbePackageInputs(directory, () => {})).toThrow('directory link cycle');
  });

  it.each(['escape', 'git', 'cycle'])('rejects %s links inside an already resolved alias', kind => {
    const dependency = path.join(directory, 'dependency');
    fs.mkdirSync(dependency);
    fs.mkdirSync(path.join(dependency, '.git'));
    fs.symlinkSync('dependency', path.join(directory, 'alias'));
    const target = kind === 'escape' ? '../..' : kind === 'git' ? '.git' : '../alias/linked';
    fs.symlinkSync(target, path.join(dependency, 'linked'));
    expect(() => listLeanProbePackageInputs(directory, () => {})).toThrow(
      kind === 'escape' ? 'escapes the authorized package root' : kind === 'git' ? 'excluded Git metadata' : 'link cycle'
    );
  });

  it('rejects replacing a resolved parent with a link between visits', () => {
    const dependency = path.join(directory, 'dependency');
    const other = path.join(directory, 'other');
    for (const parent of [dependency, other]) {
      fs.mkdirSync(parent);
      fs.writeFileSync(path.join(parent, 'A.lean'), 'original');
    }
    let checkpoints = 0;
    expect(() => listLeanProbePackageInputs(directory, () => {
      if (++checkpoints === 3) {
        fs.rmSync(dependency, { recursive: true });
        fs.symlinkSync('other', dependency);
      }
    })).toThrow('math_path_invalid');
  });
});
