import fs from 'node:fs';
import path from 'node:path';
import { assertMathCanonicalPath } from '../math/paths';
import { readyResearchTasks } from './modules/search';
import type { SolverModules } from './modules';
import type { TaskRecord } from './tasks';

export function componentPaths(root: string, name: string) {
  if (!/^[a-z][a-z0-9]*(?:-[a-z0-9]+)*$/u.test(name) || name.length > 64)
    throw new Error('Use a component name such as my-search: lowercase letters, digits and hyphens, up to 64 characters.');
  return { source: path.join(root, 'src/components', `${name}.ts`), entry: path.join(root, 'scripts/components', `${name}.ts`) };
}

export function createSearchComponent(root: string, name: string) {
  const files = componentPaths(root, name);
  for (const file of Object.values(files)) {
    assertMathCanonicalPath(file);
    if (fs.existsSync(file)) throw new Error(`File already exists; choose a new component name: ${file}`);
  }
  const source = `import { directSolverModules, type SolverModules } from '../solver/modules';
import { readyResearchTasks } from '../solver/modules/search';

export const ready: SolverModules['M3']['ready'] = (tasks, groups) => {
  // Change the ordering here; keep dependency, pause and budget checks.
  const candidates = readyResearchTasks(tasks, groups);
  return candidates.toSorted((a, b) => Number(b.task.kind === 'goal') - Number(a.task.kind === 'goal'));
};

export const modules: SolverModules = {
  ...directSolverModules,
  id: '${name}-v1',
  M3: { ...directSolverModules.M3, version: '${name}-v1', ready },
};
`;
  const entry = `#!/usr/bin/env bun
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { runSolver } from '../../src/solver/run';
import { modules } from '../../src/components/${name}';

process.env.CODEX_HOME ||= path.join(os.homedir(), '.config/deepscientist/math-sol-codex');
const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '../..');
runSolver(process.argv.slice(2), root, modules).then(
  code => { process.exitCode = code; },
  error => { console.error(error instanceof Error ? error.message : 'Component run failed.'); process.exitCode = 1; },
);
`;
  for (const file of Object.values(files)) fs.mkdirSync(path.dirname(file), { recursive: true });
  fs.writeFileSync(files.source, source, { flag: 'wx', mode: 0o600 });
  try { fs.writeFileSync(files.entry, entry, { flag: 'wx', mode: 0o600 }); }
  catch (error) { fs.unlinkSync(files.source); throw error; }
  return files;
}

/** A small contract check for ordering templates, not a claim about strategy quality. */
export function checkReadyOrdering(ready: SolverModules['M3']['ready']) {
  const node = (id: string, kind: TaskRecord['task']['kind'], extra: Partial<TaskRecord['task']> = {}): TaskRecord => ({
    task: { id, kind, objective: id, revision: 0, dependsOn: [], ...extra }, status: 'pending', attempts: 0,
  });
  const tasks = [node('research', 'research'), node('goal', 'goal'), node('blocked', 'goal', { dependsOn: ['goal'] }),
    node('paused', 'goal', { status: 'paused' }), node('stopped', 'research', { groupId: 'stopped' })];
  const groups = [{ group: { id: 'main', objective: 'tutorial', revision: 0, status: 'active' as const }, turns: 0 },
    { group: { id: 'stopped', objective: 'stopped', revision: 0, status: 'stopped' as const }, turns: 0 }];
  const expected = readyResearchTasks(tasks, groups);
  const before = JSON.stringify([tasks, groups]);
  const actual = ready(tasks, groups);
  if (JSON.stringify([tasks, groups]) !== before) throw new Error('The ordering function mutated tasks or routes.');
  if (!Array.isArray(actual) || actual.length !== expected.length || new Set(actual).size !== actual.length ||
      actual.some(task => !expected.includes(task)))
    throw new Error('Return each ready task exactly once. Blocked, paused and stopped tasks must stay excluded.');
  const exhausted = groups.map(record => ({ ...record, group: { ...record.group, maxTurns: 0 } }));
  const exhaustedBefore = JSON.stringify([tasks, exhausted]);
  if (ready(tasks, exhausted).length !== 0 || JSON.stringify([tasks, exhausted]) !== exhaustedBefore)
    throw new Error('An exhausted route must not receive new tasks.');
  return { readyTasks: actual.map(node => node.task.id), checks: ['dependencies', 'paused tasks', 'stopped routes', 'route budgets', 'unchanged inputs'] };
}
