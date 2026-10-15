import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import { afterEach, describe, expect, it } from 'vitest';
import { createSearchComponent, checkReadyOrdering } from '../src/solver/componentTemplate';
import { goalsFirstResearchTasks, readyResearchTasks } from '../src/solver/modules/search';

const roots: string[] = [];
afterEach(() => { for (const root of roots.splice(0)) fs.rmSync(root, { recursive: true, force: true }); });
const temp = () => { const root = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'theoremos-component-'))); roots.push(root); return root; };

describe('search component starter', () => {
  it('generates an executable entry and a component that passes its ordering contract', () => {
    const root = temp(), files = createSearchComponent(root, 'my-search');
    fs.symlinkSync(path.resolve('src/solver'), path.join(root, 'src/solver'), 'dir');
    const probe = spawnSync('bun', ['-e',
      'const { modules } = await import(process.argv[1]); const { checkReadyOrdering } = await import(process.argv[2]); console.log(JSON.stringify(checkReadyOrdering(modules.M3.ready)));',
      files.source, path.resolve('src/solver/componentTemplate.ts')], { encoding: 'utf8', timeout: 20_000, maxBuffer: 8_000 });
    expect(probe.status, probe.stderr).toBe(0);
    expect(JSON.parse(probe.stdout).readyTasks).toEqual(['goal', 'research']);
    const help = spawnSync('bun', [files.entry, '--help'], { encoding: 'utf8', timeout: 20_000, maxBuffer: 8_000 });
    expect(help.status, help.stderr).toBe(0);
    expect(help.stdout).toContain('--workspace');
  });
  it('preserves an existing component or entry', () => {
    const root = temp(), files = createSearchComponent(root, 'my-search');
    fs.writeFileSync(files.source, 'user implementation');
    expect(() => createSearchComponent(root, 'my-search')).toThrow('already exists');
    expect(fs.readFileSync(files.source, 'utf8')).toBe('user implementation');
  });
  it('supports init and check from the CLI using a source checkout', () => {
    const root = temp(), directory = path.join(root, 'scripts/mathematics');
    fs.mkdirSync(directory, { recursive: true });
    fs.mkdirSync(path.join(root, 'src'));
    fs.symlinkSync(path.resolve('src/solver'), path.join(root, 'src/solver'), 'dir');
    const script = path.join(directory, 'component.ts');
    fs.copyFileSync(path.resolve('scripts/mathematics/component.ts'), script);
    for (const command of ['init', 'check']) {
      const result = spawnSync('bun', [script, command, '--name', 'my-search'], { cwd: root, encoding: 'utf8', timeout: 20_000, maxBuffer: 8_000 });
      expect(result.status, result.stderr).toBe(0);
      if (command === 'check') expect(JSON.parse(result.stdout).status).toBe('passed');
    }
  });
  it.each(['../escape', 'bad/name', 'NotLowercase', '', 'a'.repeat(65)])('rejects an unsafe name %s', name => {
    expect(() => createSearchComponent(temp(), name)).toThrow('component name');
  });
  it('detects ordering functions that bypass gates, duplicate tasks or mutate input', () => {
    expect(() => checkReadyOrdering(tasks => [...tasks])).toThrow('ready task exactly once');
    expect(() => checkReadyOrdering((tasks, groups) => { const ready = readyResearchTasks(tasks, groups); return [ready[0], ready[0]]; })).toThrow('ready task exactly once');
    expect(() => checkReadyOrdering(tasks => { tasks[0].status = 'completed'; return []; })).toThrow('mutated');
    expect(checkReadyOrdering(goalsFirstResearchTasks).readyTasks).toEqual(['goal', 'research']);
  });
});
