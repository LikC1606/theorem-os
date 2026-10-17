import fs from 'node:fs';
import path from 'node:path';
import { canonicalMathJson, mathDigest } from '../math/mathRuntimeIo';
import { maskLeanComments, maskLeanCommentsAndStrings } from '../math/leanSyntax';
import { hashMathFormalSourceDeclaration, inspectLeanDeclarationRegions, inspectScopedLeanDeclarations,
  leanDeclarationContextCommands } from '../math/leanSource';
import { assertSolverSources, committedSource, commitSolverProjection, solverProofImports, withSolverWorktree, type SolverProblem } from './problem';
import { checkProjectedDeclarations, type ProofCheck } from './modules/evidence';
import { taskVersion, type CooperativeTask, type TaskAssignment } from './tasks';
import { captureProofReferences, type ProofReferences } from './proofReferences';

export type DeclarationChange = { file: string; name: string; before?: string; after: string; beforeName?: string; afterName?: string; tail?: string };
export type TaskProof = ProofCheck & { taskDigest: string; seedCommit: string; changes: DeclarationChange[];
  imports?: { file: string; module: string }[];
  conditions?: NonNullable<TaskAssignment['dependencies']>; references?: ProofReferences };
export type TaskProofRequest = { task: CooperativeTask; assignment: TaskAssignment; retainedGoals: readonly string[];
  conditions?: readonly CooperativeTask[] };
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

/** Freeze edits while preserving original goals, helper statements, and definition bodies. */
export function taskChanges(problem: SolverProblem, worktree: string, sourceCommit: string,
  task: CooperativeTask | undefined, assignment: Pick<TaskAssignment, 'seedCommit'>): DeclarationChange[] {
  const changes: DeclarationChange[] = [];
  for (const file of problem.ownedFiles) {
    const read = (commit: string) => committedSource(worktree, commit, `${problem.projectRelative}/${file}`);
    const before = read(assignment.seedCommit), after = read(sourceCommit);
    if (before === after) continue;
    if (task && (['research', 'sketch'].includes(task.kind) || !file.endsWith('.lean'))) throw new Error('math_task_source_outside_scope');
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
      const assigned = file === task?.proofPath && local(region.name) === local(task.theoremName!);
      const proofRepair = !problem.declarations[file]?.some(item => item.name === region.name) &&
        /^(?:theorem|lemma)\s/u.test(before.slice(region.startOffset, region.bodyOffset)) &&
        /^(?:theorem|lemma)\s/u.test(after.slice(current.startOffset, current.bodyOffset)) &&
        region.declarationType === current.declarationType;
      if (task && !assigned && !proofRepair)
        throw new Error(`math_task_existing_declaration_changed\nFile: ${problem.projectRelative}/${file}\nDeclaration: ${region.name}\n` +
          `Restore this declaration's exact name, parameters, proof and namespace/section placement from git show ${assignment.seedCommit}:${problem.projectRelative}/${file}. ` +
          'Proof-only repairs to solver-created lemmas are allowed; preserve their statements. Add a differently named helper if different parameters are needed. Do not reset the worktree.');
      changes.push({ file, name: region.name, before: oldText, after: newText });
    }
    const inherited = updated.filter(region => originals.some(original => original.name === region.name));
    if (inherited.some((region, index) => region.name !== originals[index].name)) {
      // Replay declaration order as well as proof edits; Lean cannot reference a later theorem.
      for (let index = 1; index < inherited.length; index++) {
        const region = inherited[index], previous = inherited[index - 1];
        if (canonicalMathJson(leanDeclarationContextCommands(after, region.name)) !==
            canonicalMathJson(leanDeclarationContextCommands(after, previous.name))) continue;
        changes.push({ file, name: region.name, before: text(before, originals.find(item => item.name === region.name)!),
          after: text(after, region), afterName: previous.name });
      }
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
  task: CooperativeTask, retainedGoals: readonly string[], conditions: readonly CooperativeTask[] = []): Map<string, string> {
  const binders = conditions.map(dependency => `(${local(dependency.theoremName!)} : ${dependency.type})`).join(' ');
  const declaration = committedSource(worktree, sourceCommit, `${problem.projectRelative}/${task.proofPath}`);
  const matches = inspectLeanDeclarationRegions(declaration).filter(region => local(region.name) === local(task.theoremName!));
  const location = `\nFile: ${problem.projectRelative}/${task.proofPath}\nTarget: ${task.theoremName}\n`;
  if (!matches.length) throw new Error('math_task_missing_declaration' + location +
    'The assigned theorem is absent. Save it with the requested name and type, or report supporting results and the remaining gap as progress. No Lean proof check has started.');
  if (matches.length > 1) throw new Error('math_task_ambiguous_declaration' + location +
    'Multiple declarations share this target name. Give supporting helpers distinct names and preserve one exact assigned theorem.');
  const originalTarget = task.kind === 'goal' ? problem.targets.find(target =>
    target.proofPath === task.proofPath && target.theoremName === task.theoremName) : undefined;
  const originalSource = originalTarget ? committedSource(worktree, problem.baseCommit, `${problem.projectRelative}/${task.proofPath}`) : undefined;
  const originalDeclaration = originalSource ? inspectScopedLeanDeclarations(originalSource)
    .find(item => item.qualifiedName === task.theoremName) : undefined;
  const originalDefinition = Boolean(originalSource && originalDeclaration && /^def\s/u.test(originalSource.slice(originalDeclaration.startOffset)));
  const header = declaration.slice(matches[0].startOffset, matches[0].bodyOffset);
  // Only an exact frozen original goal may deliver a definition body; helper targets remain propositions.
  const definitionMatches = originalTarget && originalDeclaration && originalDefinition && /^def\s/u.test(header) &&
    inspectScopedLeanDeclarations(declaration).some(item => item.startOffset === matches[0].startOffset &&
      item.qualifiedName === task.theoremName && item.declarationType === originalDeclaration.declarationType) &&
    hashMathFormalSourceDeclaration(declaration, task.theoremName!) === originalTarget.declarationHash;
  if (originalDefinition ? !definitionMatches : !/^(?:theorem|lemma)\s/u.test(header))
    throw new Error('math_task_requires_theorem' + location +
      'Helper targets must be theorems or lemmas. A goal may fill its exact frozen original def, preserving its declaration kind, name, parameters and type.');
  if (task.kind === 'lemma' && Object.values(problem.declarations).some(items => items.some(item => local(item.name) === local(task.theoremName!))))
    throw new Error('math_task_helper_is_original_declaration');
  const keep = new Set([task.theoremName!, ...retainedGoals].map(local));
  const sources = new Map(problem.ownedFiles.map(file => [file,
    committedSource(worktree, sourceCommit, `${problem.projectRelative}/${file}`)]));
  const removed = new Set([...problem.targets.map(target => target.theoremName),
    ...conditions.map(dependency => dependency.theoremName!)].map(local).filter(name => !keep.has(name)));
  const declarations = [...sources].filter(([file]) => file.endsWith('.lean')).flatMap(([, source]) =>
    inspectLeanDeclarationRegions(source).map(region => ({ name: local(region.name),
      theorem: /^(?:theorem|lemma)\s/u.test(source.slice(region.startOffset, region.bodyOffset)), references:
      [...maskLeanCommentsAndStrings(source.slice(region.startOffset, region.endOffset))
        .matchAll(/[\p{L}_][\p{L}\p{M}\p{N}_']*(?:\.[\p{L}_][\p{L}\p{M}\p{N}_']*)*/gu)].map(match => local(match[0])) })));
  for (const item of declarations) if (item.theorem && !keep.has(item.name) &&
      item.references.some(name => name === 'sorry' || name === 'admit')) removed.add(item.name);
  // Removing or parameterizing a theorem also invalidates unrelated saved wrappers that call it.
  const changed = new Set([...removed, ...(conditions.length ? [local(task.theoremName!)] : [])]);
  for (;;) {
    const affected = declarations.filter(item => !keep.has(item.name) && !removed.has(item.name) &&
      item.references.some(name => changed.has(name)));
    if (!affected.length) break;
    for (const item of affected) { removed.add(item.name); changed.add(item.name); }
  }
  for (const file of problem.ownedFiles) {
    let source = sources.get(file)!;
    if (!file.endsWith('.lean')) continue;
    // Doc comments require a following declaration, which this projection may remove.
    source = maskLeanComments(source);
    for (const region of inspectLeanDeclarationRegions(source).reverse()) {
      if (conditions.length && file === task.proofPath && local(region.name) === local(task.theoremName!)) {
        const header = source.slice(region.startOffset, region.bodyOffset - 2);
        const name = /^(?:theorem|lemma)\s+[^\s(\[{:]+/u.exec(header);
        if (!name || source.slice(region.bodyOffset - 2, region.bodyOffset) !== ':=') throw new Error('math_task_conditional_header_unsupported');
        let body = source.slice(region.bodyOffset, region.endOffset);
        // Qualified references must also refer to the explicit assumptions in this projection.
        const references = [...maskLeanCommentsAndStrings(body).matchAll(/[\p{L}_][\p{L}\p{M}\p{N}_']*(?:\.[\p{L}_][\p{L}\p{M}\p{N}_']*)*/gu)];
        for (const reference of references.reverse()) {
          const dependency = conditions.find(item => item.theoremName === reference[0]);
          if (dependency) body = body.slice(0, reference.index) + local(dependency.theoremName!) + body.slice(reference.index + reference[0].length);
        }
        source = source.slice(0, region.startOffset) + name[0] + ' ' + binders + header.slice(name[0].length) + ':=' + body + source.slice(region.endOffset);
      } else if (removed.has(local(region.name))) {
        const start = source.lastIndexOf('\n', region.startOffset - 1) + 1;
        source = source.slice(0, start) + source.slice(region.endOffset);
      }
    }
    sources.set(file, source);
  }
  return sources;
}

/** Isolate one exact helper or original goal; incomplete unrelated original goals are removed. */
export async function checkTaskProof(problem: SolverProblem, worktree: string, sourceCommit: string,
  task: CooperativeTask, assignment: TaskAssignment, retainedGoals: readonly string[], env: NodeJS.ProcessEnv,
  signal: AbortSignal, timeoutMs = 180_000, conditions: readonly CooperativeTask[] = [],
  environmentDigest = mathDigest(canonicalMathJson(env))): Promise<TaskProof> {
  return (await checkTaskProofs(problem, worktree, sourceCommit, [{ task, assignment, retainedGoals, conditions }],
    env, signal, timeoutMs, environmentDigest))[0]!;
}

/** Identical source projections share a kernel run, with a separate receipt for every target. */
export async function checkTaskProofs(problem: SolverProblem, worktree: string, sourceCommit: string,
  requests: readonly TaskProofRequest[], env: NodeJS.ProcessEnv, signal: AbortSignal, timeoutMs = 180_000,
  environmentDigest = mathDigest(canonicalMathJson(env))): Promise<TaskProof[]> {
  signal.throwIfAborted();
  if (!requests.length) return [];
  return withSolverWorktree(worktree, sourceCommit, async checkout => {
    assertSolverSources(problem, checkout);
    const prepared = requests.map(({ task, assignment, retainedGoals, conditions = [] }) => {
      if (conditions.some(dependency => !task.conditional || dependency.kind !== 'lemma' || !dependency.type ||
          !assignment.dependencies?.some(version => version.taskId === dependency.id && version.taskDigest === taskVersion(dependency))))
        throw new Error('math_task_condition_version_invalid');
      const binders = conditions.map(dependency => `(${local(dependency.theoremName!)} : ${dependency.type})`).join(' ');
      const imports = problem.ownedFiles.filter(file => file.endsWith('.lean')).flatMap(file => {
        const before = solverProofImports(problem, committedSource(worktree, assignment.seedCommit, `${problem.projectRelative}/${file}`));
        return solverProofImports(problem, committedSource(worktree, sourceCommit, `${problem.projectRelative}/${file}`))
          .filter(module => !before.includes(module)).map(module => ({ file, module }));
      });
      return { task, assignment, conditions, imports, changes: taskChanges(problem, checkout, sourceCommit, task, assignment),
        taskDigest: taskVersion(task), sources: projectTaskSources(problem, checkout, sourceCommit, task, retainedGoals, conditions),
        expectedType: task.kind === 'lemma' ? conditions.length ? `∀ ${binders}, ${task.type}` : task.type : undefined };
    });
    const sources = prepared[0]!.sources;
    if (prepared.some(item => canonicalMathJson([...item.sources]) !== canonicalMathJson([...sources])))
      throw new Error('math_task_batch_projection_mismatch');
    const project = path.join(checkout, problem.projectRelative);
    for (const [file, source] of sources) fs.writeFileSync(path.join(project, file), source);
    const commit = commitSolverProjection(problem, checkout, `Check cooperative tasks ${requests.map(item => item.task.id).join(', ')}`);
    const { passed, verification } = await checkProjectedDeclarations(problem, checkout, worktree, commit,
      prepared.map(({ task, taskDigest }) => ({ proofPath: task.proofPath!, theoremName: task.theoremName!, digest: taskDigest,
        missingError: 'math_task_missing_declaration' })),
    { env, signal, timeoutMs, prepareLocalDependencies: problem.kind === 'lean-eval', collectDeclarationReferences: true,
      ...(prepared.length === 1 ? { expectedDeclarationType: prepared[0]!.expectedType } : {
        expectedDeclarationTypes: Object.fromEntries(prepared.filter(item => item.expectedType !== undefined)
          .map(item => [item.task.theoremName!, item.expectedType!])) }) });
    const sourceDigest = ownedSourceDigest(problem, checkout, sourceCommit);
    return prepared.map(({ task, assignment, taskDigest, changes, imports, conditions }, index) => {
      const result = verification.results[index];
      const references = passed && !conditions.length && result?.declarationReferences ? captureProofReferences(problem, checkout, sourceCommit,
        { name: task.theoremName!, file: task.proofPath! }, result.declarationReferences, environmentDigest) : undefined;
      return { commit: sourceCommit, sourceDigest, passed,
        verification: { ...verification, results: result ? [result] : [] },
        taskDigest, seedCommit: assignment.seedCommit, changes, ...(imports.length ? { imports } : {}),
        ...(references ? { references } : {}),
        ...(conditions.length ? { conditions: conditions.map(dependency => ({ taskId: dependency.id, taskDigest: taskVersion(dependency) })) } : {}) };
    });
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
      if (actual !== change.after && (!change.before || actual !== change.before)) throw new Error('math_task_integration_conflict');
      if (change.afterName) {
        const anchor = regions.find(region => region.name === change.afterName);
        if (!anchor || canonicalMathJson(leanDeclarationContextCommands(source, change.name)) !==
            canonicalMathJson(leanDeclarationContextCommands(source, change.afterName)))
          throw new Error('math_task_integration_missing_context');
        if (actual === change.after && anchor.endOffset === start) continue;
        source = source.slice(0, start) + source.slice(existing.endOffset);
        const offset = inspectLeanDeclarationRegions(source).find(region => region.name === change.afterName)!.endOffset;
        source = source.slice(0, offset) + change.after + source.slice(offset);
      } else {
        if (actual === change.after) continue;
        source = source.slice(0, start) + change.after + source.slice(existing.endOffset);
      }
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
    if (!problem.ownedFiles.includes(file) || !solverProofImports(problem, `import ${module}\n`).includes(module))
      throw new Error('math_task_source_outside_scope');
    const source = files.get(file) ?? fs.readFileSync(path.join(worktree, problem.projectRelative, file), 'utf8');
    if (!solverProofImports(problem, source).includes(module)) files.set(file, `import ${module}\n` + source);
  }
  for (const [file, source] of files) fs.writeFileSync(path.join(worktree, problem.projectRelative, file), source);
  assertSolverSources(problem, worktree);
}
