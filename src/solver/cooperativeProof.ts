import fs from 'node:fs';
import path from 'node:path';
import { canonicalMathJson, mathDigest } from '../math/mathRuntimeIo';
import { maskLeanCommentsAndStrings } from '../math/leanSyntax';
import { hashMathFormalSourceDeclaration, inspectLeanDeclarationRegions } from '../math/leanSource';
import { assertSolverSources, committedSource, commitSolverProjection, solverMathlibImports, withSolverWorktree, type SolverProblem } from './problem';
import { checkProjectedDeclaration, type ProofCheck } from './modules/evidence';
import { taskVersion, type CooperativeTask, type TaskAssignment } from './tasks';
import { captureProofReferences, type ProofReferences } from './proofReferences';

export type DeclarationChange = { file: string; name: string; before?: string; after: string; beforeName?: string; tail?: string };
export type TaskProof = ProofCheck & { taskDigest: string; seedCommit: string; changes: DeclarationChange[];
  imports?: { file: string; module: string }[];
  conditions?: NonNullable<TaskAssignment['dependencies']>; references?: ProofReferences };
const local = (name: string) => name.split('.').at(-1)!;

export { committedSource } from './problem';

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
  task: CooperativeTask | undefined, assignment: Pick<TaskAssignment, 'seedCommit'>): DeclarationChange[] {
  const changes: DeclarationChange[] = [];
  for (const file of problem.ownedFiles) {
    const read = (commit: string) => committedSource(worktree, commit, `${problem.projectRelative}/${file}`);
    const before = read(assignment.seedCommit), after = read(sourceCommit);
    if (before === after) continue;
    if (task && (['research', 'sketch'].includes(task.kind) || file !== task.proofPath)) throw new Error('math_task_source_outside_scope');
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
      if (task && local(region.name) !== local(task.theoremName!))
        throw new Error(`math_task_existing_declaration_changed\nFile: ${problem.projectRelative}/${file}\nDeclaration: ${region.name}\n` +
          `Restore this declaration's exact name, parameters, proof and namespace/section placement from git show ${assignment.seedCommit}:${problem.projectRelative}/${file}. ` +
          'Preserve new proof work; do not reset the worktree. Add a differently named helper if different parameters are needed.');
      changes.push({ file, name: region.name, before: oldText, after: newText });
    }
    for (const region of updated.filter(item => !originals.some(original => original.name === item.name))) {
      const next = updated.find(item => item.startOffset > region.startOffset && originals.some(original => original.name === item.name));
      changes.push({ file, name: region.name, after: text(after, region), beforeName: next?.name,
        tail: next ? undefined : originals.length ? before.slice(originals.at(-1)!.endOffset) : after.slice(updated.at(-1)!.endOffset) });
    }
  }
  return changes;
}

/** Deterministic proof projection shared by the checker and the host receipt boundary. */
export function projectTaskSources(problem: SolverProblem, worktree: string, sourceCommit: string,
  task: CooperativeTask, retainedGoals: readonly string[], excludedHelpers: readonly string[] = [],
  conditions: readonly CooperativeTask[] = []): Map<string, string> {
  const binders = conditions.map(dependency => `(${local(dependency.theoremName!)} : ${dependency.type})`).join(' ');
  const declaration = committedSource(worktree, sourceCommit, `${problem.projectRelative}/${task.proofPath}`);
  const matches = inspectLeanDeclarationRegions(declaration).filter(region => local(region.name) === local(task.theoremName!));
  const location = `\nFile: ${problem.projectRelative}/${task.proofPath}\nTarget: ${task.theoremName}\n`;
  if (!matches.length) throw new Error('math_task_missing_declaration' + location +
    'The assigned theorem is absent. Save it with the requested name and type, or report supporting results and the remaining gap as progress. No Lean proof check has started.');
  if (matches.length > 1) throw new Error('math_task_ambiguous_declaration' + location +
    'Multiple declarations share this target name. Give supporting helpers distinct names and preserve one exact assigned theorem.');
  if (!/^(?:theorem|lemma)\s/u.test(declaration.slice(matches[0].startOffset, matches[0].bodyOffset)))
    throw new Error('math_task_requires_theorem' + location + 'The target must be a theorem or lemma, not a definition or another declaration kind.');
  if (task.kind === 'lemma' && Object.values(problem.declarations).some(items => items.some(item => local(item.name) === local(task.theoremName!))))
    throw new Error('math_task_helper_is_original_declaration');
  const keep = new Set([task.theoremName!, ...retainedGoals].map(local));
  const excluded = new Set(excludedHelpers.map(local));
  const sources = new Map<string, string>();
  for (const file of problem.ownedFiles) {
    let source = committedSource(worktree, sourceCommit, `${problem.projectRelative}/${file}`);
    if (!file.endsWith('.lean')) { sources.set(file, source); continue; }
    const targets = problem.targets.filter(target => target.proofPath === file);
    for (const region of inspectLeanDeclarationRegions(source).reverse()) {
      if (conditions.length && file === task.proofPath && local(region.name) === local(task.theoremName!)) {
        const header = source.slice(region.startOffset, region.bodyOffset - 2);
        const name = /^(?:theorem|lemma)\s+[^\s(\[{:]+/u.exec(header);
        if (!name || source.slice(region.bodyOffset - 2, region.bodyOffset) !== ':=') throw new Error('math_task_conditional_header_unsupported');
        let body = source.slice(region.bodyOffset, region.endOffset);
        // Qualified references must also refer to the explicit assumptions in this projection.
        const references = [...maskLeanCommentsAndStrings(body).matchAll(/[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*/gu)];
        for (const reference of references.reverse()) {
          const dependency = conditions.find(item => item.theoremName === reference[0]);
          if (dependency) body = body.slice(0, reference.index) + local(dependency.theoremName!) + body.slice(reference.index + reference[0].length);
        }
        source = source.slice(0, region.startOffset) + name[0] + ' ' + binders + header.slice(name[0].length) + ':=' + body + source.slice(region.endOffset);
      } else if ((targets.some(target => local(target.theoremName) === local(region.name)) || excluded.has(local(region.name)) ||
          conditions.some(dependency => dependency.proofPath === file && local(dependency.theoremName!) === local(region.name))) && !keep.has(local(region.name)))
        source = source.slice(0, region.startOffset) + source.slice(region.endOffset);
    }
    sources.set(file, source);
  }
  return sources;
}

/** Isolate one exact helper or original goal; incomplete unrelated original goals are removed. */
export async function checkTaskProof(problem: SolverProblem, worktree: string, sourceCommit: string,
  task: CooperativeTask, assignment: TaskAssignment, retainedGoals: readonly string[], env: NodeJS.ProcessEnv,
  signal: AbortSignal, timeoutMs = 180_000, excludedHelpers: readonly string[] = [], conditions: readonly CooperativeTask[] = [],
  environmentDigest = mathDigest(canonicalMathJson(env))): Promise<TaskProof> {
  signal.throwIfAborted();
  if (conditions.some(dependency => !task.conditional || dependency.kind !== 'lemma' || !dependency.type ||
      !assignment.dependencies?.some(version => version.taskId === dependency.id && version.taskDigest === taskVersion(dependency))))
    throw new Error('math_task_condition_version_invalid');
  const binders = conditions.map(dependency => `(${local(dependency.theoremName!)} : ${dependency.type})`).join(' ');
  return withSolverWorktree(worktree, sourceCommit, async checkout => {
    assertSolverSources(problem, checkout);
    const changes = taskChanges(problem, checkout, sourceCommit, task, assignment);
    const imports = problem.ownedFiles.filter(file => file.endsWith('.lean')).flatMap(file => {
      const before = solverMathlibImports(committedSource(worktree, assignment.seedCommit, `${problem.projectRelative}/${file}`));
      return solverMathlibImports(committedSource(worktree, sourceCommit, `${problem.projectRelative}/${file}`))
        .filter(module => !before.includes(module)).map(module => ({ file, module }));
    });
    const project = path.join(checkout, problem.projectRelative);
    for (const [file, source] of projectTaskSources(problem, checkout, sourceCommit, task, retainedGoals, excludedHelpers, conditions))
      fs.writeFileSync(path.join(project, file), source);
    const commit = commitSolverProjection(problem, checkout, `Check cooperative task ${task.id}`);
    const taskDigest = taskVersion(task);
    const { passed, verification } = await checkProjectedDeclaration(problem, checkout, worktree, commit,
      { proofPath: task.proofPath!, theoremName: task.theoremName!, digest: taskDigest, missingError: 'math_task_missing_declaration' },
    { env, signal, timeoutMs, prepareLocalDependencies: problem.kind === 'lean-eval', collectDeclarationReferences: true,
      ...(task.kind === 'lemma' ? { expectedDeclarationType: conditions.length ? `∀ ${binders}, ${task.type}` : task.type } : {}) });
    const result = verification.results[0];
    const references = passed && !conditions.length && result.declarationReferences ? captureProofReferences(problem, checkout, sourceCommit,
      { name: task.theoremName!, file: task.proofPath! }, result.declarationReferences, environmentDigest) : undefined;
    return { commit: sourceCommit, sourceDigest: ownedSourceDigest(problem, checkout, sourceCommit), passed, verification,
      taskDigest, seedCommit: assignment.seedCommit, changes, ...(imports.length ? { imports } : {}),
      ...(references ? { references } : {}),
      ...(conditions.length ? { conditions: conditions.map(dependency => ({ taskId: dependency.id, taskDigest: taskVersion(dependency) })) } : {}) };
  });
}

/** Merge disjoint declaration edits, including helpers sharing a file, without overwriting peer work. */
export function applyTaskChanges(problem: SolverProblem, worktree: string, changes: readonly DeclarationChange[],
  imports: NonNullable<TaskProof['imports']> = []): void {
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
  for (const { file, module } of imports) {
    if (!problem.ownedFiles.includes(file) || !/^Mathlib(?:\.[A-Za-z_][A-Za-z0-9_']*)+$/u.test(module))
      throw new Error('math_task_source_outside_scope');
    const source = files.get(file) ?? fs.readFileSync(path.join(worktree, problem.projectRelative, file), 'utf8');
    if (!solverMathlibImports(source).includes(module)) files.set(file, `import ${module}\n` + source);
  }
  for (const [file, source] of files) fs.writeFileSync(path.join(worktree, problem.projectRelative, file), source);
  assertSolverSources(problem, worktree);
}
