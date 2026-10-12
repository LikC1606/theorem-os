import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import { canonicalMathJson, mathDigest } from '../math/mathRuntimeIo';
import { checkManyFormalVerifications, hashMathFormalSourceDeclaration, inspectLeanDeclarationRegions } from '../math/verifier';
import { assertSolverSources, git, type SolverProblem } from './problem';
import type { ProofCheck } from './modules/evidence';
import type { CooperativeTask, TaskAssignment } from './cooperation';

export type DeclarationChange = { file: string; name: string; before?: string; after: string; beforeName?: string; tail?: string };
export type TaskProof = ProofCheck & { taskDigest: string; seedCommit: string; changes: DeclarationChange[] };
const local = (name: string) => name.split('.').at(-1)!;

export function committedSource(worktree: string, commit: string, file: string): string {
  const result = spawnSync('git', ['show', `${commit}:${file}`], { cwd: worktree, encoding: 'utf8', timeout: 30_000, maxBuffer: 1024 * 1024 });
  if (result.error || result.status !== 0) throw new Error('math_task_source_unavailable');
  return result.stdout;
}

export function ownedSourceDigest(problem: SolverProblem, worktree: string, commit: string): string {
  return mathDigest(canonicalMathJson(problem.ownedFiles.map(file =>
    [file, mathDigest(committedSource(worktree, commit, `${problem.projectRelative}/${file}`))])));
}

/** Omit helper artifacts outside a task's visible scope while preserving every original declaration. */
export function omitTaskHelpers(problem: SolverProblem, file: string, source: string, names: readonly string[]): string {
  const originals = new Set((problem.declarations[file] ?? []).map(item => item.name));
  const hidden = new Set(names.map(local));
  for (const region of inspectLeanDeclarationRegions(source).reverse()) if (hidden.has(local(region.name)) && !originals.has(region.name)) {
    const start = source.lastIndexOf('\n', region.startOffset - 1) + 1;
    source = source.slice(0, start) + source.slice(region.endOffset);
  }
  return source;
}

/** Freeze declaration changes while forbidding changes to another task's original goals or existing helpers. */
export function taskChanges(problem: SolverProblem, worktree: string, sourceCommit: string,
  task: CooperativeTask, assignment: TaskAssignment): DeclarationChange[] {
  const changes: DeclarationChange[] = [];
  for (const file of problem.ownedFiles) {
    const read = (commit: string) => committedSource(worktree, commit, `${problem.projectRelative}/${file}`);
    const before = read(assignment.seedCommit), after = read(sourceCommit);
    if (before === after) continue;
    if (task.kind === 'research' || file !== task.proofPath) throw new Error('math_task_source_outside_scope');
    const originals = inspectLeanDeclarationRegions(before), updated = inspectLeanDeclarationRegions(after);
    if (new Set(updated.map(region => local(region.name))).size !== updated.length)
      throw new Error('math_task_ambiguous_declaration');
    const text = (source: string, region: typeof originals[number]) => {
      const line = source.lastIndexOf('\n', region.startOffset - 1) + 1;
      return source.slice(line, region.endOffset).trimEnd() + '\n';
    };
    for (const region of originals) {
      const current = updated.find(item => item.name === region.name);
      if (!current) throw new Error('math_task_existing_declaration_removed');
      const oldText = text(before, region), newText = text(after, current);
      if (oldText === newText) continue;
      if (local(region.name) !== local(task.theoremName!))
        throw new Error('math_task_existing_declaration_changed');
      changes.push({ file, name: region.name, before: oldText, after: newText });
    }
    for (const region of updated.filter(item => !originals.some(original => original.name === item.name))) {
      const next = updated.find(item => item.startOffset > region.startOffset && originals.some(original => original.name === item.name));
      changes.push({ file, name: region.name, after: text(after, region), beforeName: next?.name,
        tail: next ? undefined : before.slice(originals.at(-1)?.endOffset ?? 0) });
    }
  }
  return changes;
}

/** Isolate one exact helper or original goal; incomplete unrelated original goals are removed. */
export async function checkTaskProof(problem: SolverProblem, worktree: string, sourceCommit: string,
  task: CooperativeTask, assignment: TaskAssignment, retainedGoals: readonly string[], env: NodeJS.ProcessEnv,
  signal: AbortSignal, timeoutMs = 180_000, excludedHelpers: readonly string[] = []): Promise<TaskProof> {
  signal.throwIfAborted();
  const directory = fs.mkdtempSync(path.join(os.tmpdir(), 'math-task-'));
  const checkout = path.join(directory, 'worktree');
  let added = false;
  try {
    git(worktree, ['worktree', 'add', '--quiet', '--detach', checkout, sourceCommit]); added = true;
    assertSolverSources(problem, checkout);
    const changes = taskChanges(problem, checkout, sourceCommit, task, assignment);
    const project = path.join(checkout, problem.projectRelative);
    const declaration = fs.readFileSync(path.join(project, task.proofPath!), 'utf8');
    const matches = inspectLeanDeclarationRegions(declaration).filter(region => local(region.name) === local(task.theoremName!));
    if (matches.length !== 1 || !/^(?:theorem|lemma)\s/u.test(declaration.slice(matches[0].startOffset, matches[0].bodyOffset)))
      throw new Error('math_task_requires_unambiguous_theorem');
    if (task.kind === 'lemma' && Object.values(problem.declarations).some(items => items.some(item => local(item.name) === local(task.theoremName!))))
      throw new Error('math_task_helper_is_original_declaration');
    const keep = new Set([task.theoremName!, ...retainedGoals].map(local));
    const excluded = new Set(excludedHelpers.map(local));
    for (const file of problem.ownedFiles.filter(file => file.endsWith('.lean'))) {
      const absolute = path.join(project, file);
      let source = fs.readFileSync(absolute, 'utf8');
      const targets = problem.targets.filter(target => target.proofPath === file);
      for (const region of inspectLeanDeclarationRegions(source).reverse()) {
        if ((targets.some(target => local(target.theoremName) === local(region.name)) || excluded.has(local(region.name))) && !keep.has(local(region.name)))
          source = source.slice(0, region.startOffset) + source.slice(region.endOffset);
      }
      fs.writeFileSync(absolute, source);
    }
    git(checkout, ['rm', '--quiet', '--force', '--ignore-unmatch', '--', 'RESEARCH.md']);
    git(checkout, ['add', '--', ...problem.ownedFiles.map(file => path.join(problem.projectRelative, file))]);
    git(checkout, ['-c', 'user.name=DeepScientist Math', '-c', 'user.email=math@localhost', 'commit', '--allow-empty',
      '--no-gpg-sign', '--quiet', '-m', `Check cooperative task ${task.id}`]);
    const commit = git(checkout, ['rev-parse', 'HEAD']);
    const source = fs.readFileSync(path.join(project, task.proofPath!), 'utf8');
    const declarationHash = hashMathFormalSourceDeclaration(source, task.theoremName!);
    if (!declarationHash) throw new Error('math_task_missing_declaration');
    const taskDigest = mathDigest(canonicalMathJson(task));
    const packages = path.join(worktree, problem.projectRelative, '.lake', 'packages');
    if (fs.existsSync(packages)) {
      fs.mkdirSync(path.join(project, '.lake'), { recursive: true });
      fs.symlinkSync(fs.realpathSync(packages), path.join(project, '.lake', 'packages'), 'dir');
    }
    const verification = await checkManyFormalVerifications({ projectRoot: project, targetCommit: commit,
      timeoutMs, batchTimeoutMs: timeoutMs === Infinity ? Infinity : undefined,
      items: [{ proofPath: task.proofPath!, theoremName: task.theoremName!, expectedSourceDeclarationHash: declarationHash,
        statementHash: taskDigest, leanStatementHash: taskDigest, claim: 'statement' }] },
    { env, signal, prepareLocalDependencies: problem.kind === 'lean-eval',
      trustedLakePackagesRoots: (env.DEEPSCIENTIST_MATH_TRUSTED_CACHE_ROOTS || '').split(path.delimiter).filter(Boolean),
      ...(task.kind === 'lemma' ? { expectedDeclarationType: task.type } : {}) });
    const result = verification.results[0];
    const passed = verification.status === 'kernel_verified' && verification.targetCommit === commit && verification.results.length === 1 &&
      result?.status === 'kernel_verified' && result.targetCommit === commit && result.theoremName === task.theoremName &&
      result.proofPath === task.proofPath && result.sourceDeclarationHash === declarationHash && result.statementHash === taskDigest &&
      result.leanStatementHash === taskDigest && result.claim === 'statement';
    return { commit: sourceCommit, sourceDigest: ownedSourceDigest(problem, checkout, sourceCommit), passed, verification,
      taskDigest, seedCommit: assignment.seedCommit, changes };
  } finally {
    if (added) git(worktree, ['worktree', 'remove', '--force', checkout]);
    fs.rmSync(directory, { recursive: true, force: true });
  }
}

/** Merge disjoint declaration edits, including helpers sharing a file, without overwriting peer work. */
export function applyTaskChanges(problem: SolverProblem, worktree: string, changes: readonly DeclarationChange[]): void {
  const files = new Map<string, string>();
  for (const change of changes) {
    if (!problem.ownedFiles.includes(change.file)) throw new Error('math_task_source_outside_scope');
    let source = files.get(change.file) ?? fs.readFileSync(path.join(worktree, problem.projectRelative, change.file), 'utf8');
    const regions = inspectLeanDeclarationRegions(source);
    const existing = regions.find(region => region.name === change.name);
    if (existing) {
      const start = source.lastIndexOf('\n', existing.startOffset - 1) + 1;
      const actual = source.slice(start, existing.endOffset).trimEnd() + '\n';
      if (actual === change.after) continue;
      if (!change.before || actual !== change.before) throw new Error('math_task_integration_conflict');
      source = source.slice(0, start) + change.after + source.slice(existing.endOffset);
    } else {
      if (change.before) throw new Error('math_task_integration_missing_declaration');
      const anchor = change.beforeName && regions.find(region => region.name === change.beforeName);
      const offset = anchor ? source.lastIndexOf('\n', anchor.startOffset - 1) + 1 :
        change.tail !== undefined && source.endsWith(change.tail) ? source.length - change.tail.length : -1;
      if (offset < 0) throw new Error('math_task_integration_missing_context');
      source = source.slice(0, offset) + change.after + source.slice(offset);
    }
    files.set(change.file, source);
  }
  for (const [file, source] of files) fs.writeFileSync(path.join(worktree, problem.projectRelative, file), source);
  assertSolverSources(problem, worktree);
}
