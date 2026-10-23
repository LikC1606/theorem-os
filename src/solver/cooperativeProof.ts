import fs from 'node:fs';
import path from 'node:path';
import { canonicalMathJson, mathDigest } from '../math/mathRuntimeIo';
import { maskLeanComments, maskLeanCommentsAndStrings } from '../math/leanSyntax';
import { mathConstructionImports } from '../math/mathConstructionSources';
import { hashMathFormalSourceDeclaration, inspectLeanDeclarationRegions, inspectScopedLeanDeclarations,
  leanDeclarationContextCommands } from '../math/leanSource';
import { assertSolverSources, committedSource, commitSolverProjection, git, solverProofImports, withSolverWorktree, type SolverProblem } from './problem';
import { attributeProofEvidence, checkProjectedDeclarations, type ProofCheck } from './modules/evidence';
import { taskVersion, type CooperativeTask, type TaskAssignment } from './tasks';
import { captureProofReferences, type ProofReferences } from './proofReferences';
import { hasDeterministicLeanFailure, proofReuseEnvironment } from './proofReuse';
import { TaskProofCache, type TaskVerificationArtifact } from './taskProofCache';
import { formalVerificationToolIdentity, type MathematicsVerifierBatchItem } from '../math/verifier';
import { hasTaskConnectionCheck } from './taskConnections';

export { TaskProofCache } from './taskProofCache';

export type DeclarationChange = { file: string; name: string; before?: string; after: string; beforeName?: string; afterName?: string; tail?: string };
export type TaskProjectionReuse = Readonly<{ schema: 'theorem-os.task-projection-reuse.v1'; projectionCommit: string;
  checkedProjectionCommit: string; projectionTree: string; inputDigest: string }>;
export type TaskProof = ProofCheck & { taskDigest: string; seedCommit: string; changes: DeclarationChange[];
  imports?: { file: string; module: string }[];
  projectionReuse?: TaskProjectionReuse;
  /** Set by the host after checking the exact projection and its receipts. */
  projection?: Readonly<{ environmentDigest: string; problemReceiptDigest: string; sourceDigest: string }>;
  conditions?: NonNullable<TaskAssignment['dependencies']>; references?: ProofReferences };
export type TaskProofRequest = { task: CooperativeTask; assignment: TaskAssignment; retainedGoals: readonly string[];
  conditions?: readonly CooperativeTask[] };
const attributedProofs = new WeakMap<TaskProof, string>();
const reusedProjections = new WeakMap<TaskProof, string>();

/** Only unchanged task views attributed by this process may suppress a batch fallback. */
export const isAttributedTaskProof = (proof: TaskProof): boolean =>
  attributedProofs.get(proof) === mathDigest(canonicalMathJson(proof));

/** A restored, cloned or edited proof cannot authorize a receipt from another commit. */
export function trustedTaskProjectionReuse(proof: TaskProof): TaskProjectionReuse | undefined {
  try {
    if (proof.projectionReuse && reusedProjections.get(proof) === mathDigest(canonicalMathJson(proof))) return proof.projectionReuse;
  } catch { /* Invalid caller data cannot restore process-local trust. */ }
  return undefined;
}

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

/** Deterministic proof projection shared by the checker and the host receipt boundary. One immutable canonical snapshot
 * shares source reads and declaration indexes across its targets. */
export function createTaskSourceProjector(problem: SolverProblem, worktree: string, sourceCommit: string) {
  problem = structuredClone(problem);
  const sourceSnapshot = new Map(problem.ownedFiles.map(file => [file,
    committedSource(worktree, sourceCommit, `${problem.projectRelative}/${file}`)]));
  const regions = new Map([...sourceSnapshot].filter(([file]) => file.endsWith('.lean'))
    .map(([file, source]) => [file, inspectLeanDeclarationRegions(source)]));
  const key = (file: string, name: string) => `${file}\0${name}`;
  const identifiers = (source: string) => [...maskLeanCommentsAndStrings(source)
    .matchAll(/[\p{L}_][\p{L}\p{M}\p{N}_']*(?:\.[\p{L}_][\p{L}\p{M}\p{N}_']*)*/gu)].map(match => match[0]);
  const declarations = [...sourceSnapshot].filter(([file]) => file.endsWith('.lean')).flatMap(([file, source]) => {
    const scoped = inspectScopedLeanDeclarations(source);
    return regions.get(file)!.map(region => {
      const declaration = scoped.find(item => item.startOffset === region.startOffset)!;
      const header = source.slice(region.startOffset, region.bodyOffset);
      return { ...declaration, file, id: key(file, declaration.qualifiedName),
        theorem: /^(?:theorem|lemma)\s/u.test(header), header: identifiers(header),
        opened: leanDeclarationContextCommands(source, declaration.qualifiedName).before.some(command => /^open\b/u.test(command)),
        references: identifiers(source.slice(region.startOffset, region.endOffset)) };
    });
  });
  const byOffset = new Map(declarations.map(item => [`${item.file}\0${item.startOffset}`, item]));
  const masked = new Map([...sourceSnapshot].filter(([file]) => file.endsWith('.lean')).map(([file, source]) => {
    const text = maskLeanComments(source);
    return [file, { text, regions: inspectLeanDeclarationRegions(text) }] as const;
  }));
  const visible = new Map([...sourceSnapshot.keys()].map(file => {
    const files = new Set([file]);
    for (const current of files) for (const module of mathConstructionImports(sourceSnapshot.get(current)!)) {
      const imported = module.replaceAll('.', '/') + '.lean';
      if (sourceSnapshot.has(imported)) files.add(imported);
    }
    return [file, files] as const;
  }));
  const originals = new Map<string, string>();
  return (task: CooperativeTask, retainedGoals: readonly string[], conditions: readonly CooperativeTask[] = []): Map<string, string> => {
    const binders = conditions.map(dependency => `(${local(dependency.theoremName!)} : ${dependency.type})`).join(' ');
    const declaration = sourceSnapshot.get(task.proofPath!) ?? '';
    const matches = (regions.get(task.proofPath!) ?? []).filter(region => local(region.name) === local(task.theoremName!));
    const location = `\nFile: ${problem.projectRelative}/${task.proofPath}\nTarget: ${task.theoremName}\n`;
    if (!matches.length) throw new Error('math_task_missing_declaration' + location +
      'The assigned theorem is absent. Save it with the requested name and type, or report supporting results and the remaining gap as progress. No Lean proof check has started.');
    if (matches.length > 1) throw new Error('math_task_ambiguous_declaration' + location +
      'Multiple declarations share this target name. Give supporting helpers distinct names and preserve one exact assigned theorem.');
    const originalTarget = task.kind === 'goal' ? problem.targets.find(target =>
      target.proofPath === task.proofPath && target.theoremName === task.theoremName) : undefined;
    if (originalTarget && !originals.has(task.proofPath!)) originals.set(task.proofPath!,
      committedSource(worktree, problem.baseCommit, `${problem.projectRelative}/${task.proofPath}`));
    const originalSource = originalTarget ? originals.get(task.proofPath!) : undefined;
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
    const sources = new Map(sourceSnapshot);
    const targetKey = (file: string, name: string) => key(file, declarations.find(item => item.file === file &&
      (item.qualifiedName === name || !name.includes('.') && item.name === name))?.qualifiedName ?? name);
    const target = targetKey(task.proofPath!, task.theoremName!);
    const keep = new Set([target, ...problem.targets
      .filter(target => retainedGoals.includes(target.theoremName)).map(target => targetKey(target.proofPath, target.theoremName))]);
    const assumptions = new Map(conditions.map(dependency => [targetKey(dependency.proofPath!, dependency.theoremName!), dependency]));
    const removed = new Set([...problem.targets.map(target => targetKey(target.proofPath, target.theoremName)),
      ...assumptions.keys()].filter(id => !keep.has(id)));
    const bindings = new Map<string, { file: string; id: string }[]>();
    for (const binding of [...declarations.map(item => ({ file: item.file, name: item.qualifiedName, id: item.id })),
      ...[...assumptions].map(([id, dependency]) => ({ id, file: dependency.proofPath!, name: id.slice(id.indexOf('\0') + 1) }))]) {
      bindings.set(binding.name, [...(bindings.get(binding.name) ?? []), binding]);
    }
    // Only unambiguous source names guide projection cleanup; Lean owns actual dependency evidence.
    const referenceKey = (declaration: typeof declarations[number], name: string) => {
      if (!name.includes('.') && declaration.header.includes(name)) return;
      const namespace = declaration.namespace.split('.').filter(Boolean);
      const names = name.startsWith('_root_.') ? [name.slice(7)] :
        Array.from({ length: namespace.length + 1 }, (_, index) => [...namespace.slice(0, namespace.length - index), name].join('.'));
      for (const qualified of names) {
        const candidates = (bindings.get(qualified) ?? []).filter(item => visible.get(declaration.file)!.has(item.file));
        const own = candidates.filter(item => item.file === declaration.file);
        const ids = new Set((own.length ? own : candidates).map(item => item.id));
        if (!ids.size) continue;
        // An open command must not hide a known same-file binding. Relative imported
        // names still need Lean to resolve their open-namespace lookup context.
        if (declaration.opened && !name.startsWith('_root_.') && !bindings.has(name) && !own.length) return;
        return ids.size === 1 ? [...ids][0] : undefined;
      }
    };
    for (const item of declarations) if (item.theorem && !keep.has(item.id) &&
        item.references.some(name => name === 'sorry' || name === 'admit')) removed.add(item.id);
    // Removing or parameterizing a theorem also invalidates unrelated saved wrappers that call it.
    const changed = new Set([...removed, ...(conditions.length ? [target] : [])]);
    for (;;) {
      const affected = declarations.filter(item => !keep.has(item.id) && !removed.has(item.id) &&
        item.references.some(name => { const reference = referenceKey(item, name); return reference !== undefined && changed.has(reference); }));
      if (!affected.length) break;
      for (const item of affected) { removed.add(item.id); changed.add(item.id); }
    }
    for (const file of problem.ownedFiles) {
      let source = sources.get(file)!;
      if (!file.endsWith('.lean')) continue;
      // Doc comments require a following declaration, which this projection may remove.
      source = masked.get(file)!.text;
      for (const region of [...masked.get(file)!.regions].reverse()) {
        const declaration = byOffset.get(`${file}\0${region.startOffset}`)!;
        if (conditions.length && declaration.id === target) {
          const header = source.slice(region.startOffset, region.bodyOffset - 2);
          const name = (originalDefinition ? /^def\s+[^\s(\[{:]+/u : /^(?:theorem|lemma)\s+[^\s(\[{:]+/u).exec(header);
          if (!name || source.slice(region.bodyOffset - 2, region.bodyOffset) !== ':=') throw new Error('math_task_conditional_header_unsupported');
          let body = source.slice(region.bodyOffset, region.endOffset);
          // Qualified references must also refer to the explicit assumptions in this projection.
          const references = [...maskLeanCommentsAndStrings(body).matchAll(/[\p{L}_][\p{L}\p{M}\p{N}_']*(?:\.[\p{L}_][\p{L}\p{M}\p{N}_']*)*/gu)];
          for (const reference of references.reverse()) {
            const dependency = conditions.find(item => item.theoremName === reference[0]) ??
              assumptions.get(referenceKey(declaration, reference[0]) ?? '');
            if (dependency) body = body.slice(0, reference.index) + local(dependency.theoremName!) + body.slice(reference.index + reference[0].length);
          }
          source = source.slice(0, region.startOffset) + name[0] + ' ' + binders + header.slice(name[0].length) + ':=' + body + source.slice(region.endOffset);
        } else if (removed.has(declaration.id)) {
          const start = source.lastIndexOf('\n', region.startOffset - 1) + 1;
          source = source.slice(0, start) + source.slice(region.endOffset);
        }
      }
      sources.set(file, source);
    }
    return sources;
  };
}

/** Isolate one exact helper or original goal; incomplete unrelated original goals are removed. */
export async function checkTaskProof(problem: SolverProblem, worktree: string, sourceCommit: string,
  task: CooperativeTask, assignment: TaskAssignment, retainedGoals: readonly string[], env: NodeJS.ProcessEnv,
  signal: AbortSignal, timeoutMs = 180_000, conditions: readonly CooperativeTask[] = [],
  environmentDigest = mathDigest(canonicalMathJson(env)), cache?: TaskProofCache): Promise<TaskProof> {
  return (await checkTaskProofs(problem, worktree, sourceCommit, [{ task, assignment, retainedGoals, conditions }],
    env, signal, timeoutMs, environmentDigest, cache))[0]!;
}

/** Identical source projections share a kernel run, with a separate receipt for every target. */
export async function checkTaskProofs(problem: SolverProblem, worktree: string, sourceCommit: string,
  requests: readonly TaskProofRequest[], env: NodeJS.ProcessEnv, signal: AbortSignal, timeoutMs = 180_000,
  environmentDigest = mathDigest(canonicalMathJson(env)), cache?: TaskProofCache): Promise<TaskProof[]> {
  signal.throwIfAborted();
  if (!requests.length) return [];
  problem = structuredClone(problem);
  requests = structuredClone(requests);
  sourceCommit = git(worktree, ['rev-parse', `${sourceCommit}^{commit}`]);
  return withSolverWorktree(worktree, sourceCommit, async checkout => {
    assertSolverSources(problem, checkout);
    const projectSources = createTaskSourceProjector(problem, checkout, sourceCommit);
    const prepared = requests.map(({ task, assignment, retainedGoals, conditions = [] }) => {
      const connection = hasTaskConnectionCheck(task, assignment);
      if (assignment.connectionCheck && (!connection || assignment.connectionCheck.environmentDigest !== environmentDigest ||
          assignment.connectionCheck.problemReceiptDigest !== problem.receiptDigest))
        throw new Error('math_task_condition_version_invalid');
      if (conditions.some(dependency => !(task.conditional || connection) || dependency.kind !== 'lemma' || !dependency.type ||
          (connection && !(assignment.connectionCheck!.assumedInputs ?? assignment.connectionCheck!.inputs).some(input => input.taskId === dependency.id &&
            input.taskDigest === taskVersion(dependency))) ||
          !assignment.dependencies?.some(version => version.taskId === dependency.id && version.taskDigest === taskVersion(dependency))))
        throw new Error('math_task_condition_version_invalid');
      const binders = conditions.map(dependency => `(${local(dependency.theoremName!)} : ${dependency.type})`).join(' ');
      const imports = problem.ownedFiles.filter(file => file.endsWith('.lean')).flatMap(file => {
        const before = solverProofImports(problem, committedSource(worktree, assignment.seedCommit, `${problem.projectRelative}/${file}`));
        return solverProofImports(problem, committedSource(worktree, sourceCommit, `${problem.projectRelative}/${file}`))
          .filter(module => !before.includes(module)).map(module => ({ file, module }));
      });
      const changes = taskChanges(problem, checkout, sourceCommit, task, assignment);
      // Assumed children are supplied by their own checked deliveries, never by this parent's draft.
      const assumed = new Set(conditions.flatMap(dependency => inspectScopedLeanDeclarations(
        committedSource(worktree, sourceCommit, `${problem.projectRelative}/${dependency.proofPath}`))
        .filter(declaration => declaration.qualifiedName === dependency.theoremName ||
          !dependency.theoremName!.includes('.') && declaration.name === dependency.theoremName)
        .map(declaration => `${dependency.proofPath}\0${declaration.name}`)));
      return { task, assignment, retainedGoals, conditions, imports, changes: changes.filter(change => !assumed.has(`${change.file}\0${change.name}`)),
        taskDigest: taskVersion(task), sources: projectSources(task, retainedGoals, conditions),
        expectedType: task.kind === 'lemma' ? conditions.length ? `∀ ${binders}, ${task.type}` : task.type : undefined };
    });
    const sources = prepared[0]!.sources;
    if (prepared.some(item => canonicalMathJson([...item.sources]) !== canonicalMathJson([...sources])))
      throw new Error('math_task_batch_projection_mismatch');
    const project = path.join(checkout, problem.projectRelative);
    for (const [file, source] of sources) fs.writeFileSync(path.join(project, file), source);
    const commit = commitSolverProjection(problem, checkout, `Check cooperative tasks ${requests.map(item => item.task.id).join(', ')}`);
    const execution = { prepareLocalDependencies: problem.kind === 'lean-eval', collectDeclarationReferences: true,
      ...(prepared.length === 1 ? { expectedDeclarationType: prepared[0]!.expectedType } : {
        expectedDeclarationTypes: Object.fromEntries(prepared.filter(item => item.expectedType !== undefined)
          .map(item => [item.task.theoremName!, item.expectedType!])) }) };
    const targets = prepared.map(({ task, taskDigest }) => ({ proofPath: task.proofPath!, theoremName: task.theoremName!,
      digest: taskDigest, missingError: 'math_task_missing_declaration' }));
    const sourceProject = path.join(worktree, problem.projectRelative);
    const environment = cache ? proofReuseEnvironment(sourceProject, env) : undefined;
    const tools = environment && formalVerificationToolIdentity(project, environment.env);
    const assertStableEnvironment = () => {
      signal.throwIfAborted();
      if (!environment) return;
      const after = proofReuseEnvironment(sourceProject, env);
      if (after.reusable !== environment.reusable || after.digest !== environment.digest ||
          canonicalMathJson(after.env) !== canonicalMathJson(environment.env) ||
          formalVerificationToolIdentity(project, after.env) !== tools) throw new Error('math_verifier_unavailable');
    };
    const run = async () => {
      try {
        return await checkProjectedDeclarations(problem, checkout, worktree, commit, targets,
          { env: environment?.env ?? env, signal, timeoutMs, ...execution });
      } finally { assertStableEnvironment(); }
    };
    let attributions: Awaited<ReturnType<typeof checkProjectedDeclarations>>['attributions'];
    let projectionReuse: TaskProjectionReuse | undefined;
    if (cache && environment?.reusable && tools) {
      const projectionTree = git(checkout, ['rev-parse', `${commit}^{tree}`]);
      const items: MathematicsVerifierBatchItem[] = targets.map(target => ({ proofPath: target.proofPath,
        theoremName: target.theoremName, statementHash: target.digest, leanStatementHash: target.digest, claim: 'statement',
        expectedSourceDeclarationHash: hashMathFormalSourceDeclaration(sources.get(target.proofPath)!, target.theoremName) }));
      const inputDigest = mathDigest(canonicalMathJson({
        repository: git(worktree, ['rev-parse', '--path-format=absolute', '--git-common-dir']),
        projectionTree, problem, targets: items, environment: environment.digest, tools, environmentDigest,
        execution: { ...execution, timeoutMs: timeoutMs === Infinity ? 'unlimited' : timeoutMs,
          batchTimeoutMs: timeoutMs === Infinity ? 'unlimited' : 'default',
          trustedLakePackagesRoots: (environment.env.DEEPSCIENTIST_MATH_TRUSTED_CACHE_ROOTS || '').split(path.delimiter).filter(Boolean) },
        requests: prepared.map(({ taskDigest, assignment, retainedGoals, conditions }) => {
          const { seedCommit: _seed, basisDigest: _basis, ...connection } = assignment.connectionCheck ?? {};
          return { taskDigest, dependencies: assignment.dependencies ?? [], retainedGoals,
            connectionCheck: assignment.connectionCheck ? connection : undefined, conditions: conditions.map(taskVersion) };
        }),
      }));
      const valid = ({ projectionCommit, verification }: TaskVerificationArtifact) => {
        try {
          if (git(worktree, ['rev-parse', `${projectionCommit}^{tree}`]) !== projectionTree) return false;
          return attributeProofEvidence(verification, projectionCommit, items).every(attribution =>
            !attribution.verification.results.some(result => result.cleanupError) &&
            (attribution.passed || attribution.attributable && hasDeterministicLeanFailure(attribution.verification)));
        } catch { return false; }
      };
      let artifact: TaskVerificationArtifact;
      try {
        artifact = await cache.check(inputDigest, signal, valid, async () => {
          const checked = await run();
          return { projectionCommit: commit, verification: checked.verification };
        });
      } finally { assertStableEnvironment(); }
      attributions = attributeProofEvidence(artifact.verification, artifact.projectionCommit, items);
      if (artifact.projectionCommit !== commit) projectionReuse = {
        schema: 'theorem-os.task-projection-reuse.v1', projectionCommit: commit,
        checkedProjectionCommit: artifact.projectionCommit, projectionTree, inputDigest,
      };
    } else attributions = (await run()).attributions;
    const sourceDigest = ownedSourceDigest(problem, checkout, sourceCommit);
    return prepared.map(({ task, assignment, taskDigest, changes, imports, conditions }, index) => {
      const { passed, verification, attributable } = attributions[index]!;
      const result = verification.results[0];
      const references = passed && !conditions.length && result?.declarationReferences ? captureProofReferences(problem, checkout, sourceCommit,
        { name: task.theoremName!, file: task.proofPath! }, result.declarationReferences, environmentDigest) : undefined;
      const proof: TaskProof = { commit: sourceCommit, sourceDigest, passed, verification,
        taskDigest, seedCommit: assignment.seedCommit, changes, ...(imports.length ? { imports } : {}),
        ...(projectionReuse ? { projectionReuse: { ...projectionReuse } } : {}),
        ...(references ? { references } : {}),
        ...(conditions.length ? { conditions: conditions.map(dependency => ({ taskId: dependency.id, taskDigest: taskVersion(dependency) })) } : {}) };
      if (attributable) attributedProofs.set(proof, mathDigest(canonicalMathJson(proof)));
      if (projectionReuse) reusedProjections.set(proof, mathDigest(canonicalMathJson(proof)));
      return proof;
    });
  });
}

/** Move an attached document comment with its declaration without changing archived patch text. */
function declarationStartWithDoc(source: string, startOffset: number): number {
  const lineStart = source.lastIndexOf('\n', startOffset - 1) + 1;
  let cursor = lineStart;
  while (cursor > 0 && /\s/u.test(source[cursor - 1])) cursor--;
  if (source.slice(cursor - 2, cursor) !== '-/') return lineStart;
  cursor -= 2;
  let depth = 1;
  while (cursor > 0) {
    const pair = source.slice(cursor - 2, cursor);
    if (pair === '-/') { depth++; cursor -= 2; }
    else if (pair === '/-') {
      cursor -= 2;
      if (--depth === 0) {
        const commentLine = source.lastIndexOf('\n', cursor - 1) + 1;
        return source.startsWith('/--', cursor) && !source.slice(commentLine, cursor).trim() ? commentLine : lineStart;
      }
    } else cursor--;
  }
  return lineStart;
}

/** Discharge saved assumptions against declarations that may have arrived after the old insertion anchor. */
function orderConditionalChanges(source: string, file: string, changes: readonly DeclarationChange[],
  conditions: readonly CooperativeTask[]): string {
  const names = new Set(changes.filter(change => change.file === file).map(change => change.name));
  const ordered = inspectScopedLeanDeclarations(source).filter(declaration => names.has(declaration.name));
  const previous = new Map<string, string>();
  for (const original of ordered) {
    const declarations = inspectScopedLeanDeclarations(source), regions = inspectLeanDeclarationRegions(source);
    const declaration = declarations.find(item => item.qualifiedName === original.qualifiedName)!;
    const region = regions.find(item => item.startOffset === declaration.startOffset)!;
    const context = canonicalMathJson(leanDeclarationContextCommands(source, declaration.qualifiedName));
    const text = source.slice(region.startOffset, region.endOffset);
    const references = new Set([...maskLeanCommentsAndStrings(text).matchAll(/[\p{L}_][\p{L}\p{M}\p{N}_']*(?:\.[\p{L}_][\p{L}\p{M}\p{N}_']*)*/gu)]
      .map(match => match[0].replace(/^_root_\./u, '')));
    const inputs = conditions.filter(input => input.proofPath === file &&
      (references.has(input.theoremName!) || references.has(local(input.theoremName!))));
    const candidates = declarations.filter(item => item.qualifiedName === previous.get(context) || inputs.some(input =>
      item.qualifiedName === input.theoremName || !input.theoremName!.includes('.') && item.name === input.theoremName));
    const anchor = candidates.filter(item => item.startOffset > declaration.startOffset)
      .toSorted((a, b) => b.startOffset - a.startOffset)[0];
    previous.set(context, declaration.qualifiedName);
    if (!anchor) continue;
    const anchorRegion = regions.find(item => item.startOffset === anchor.startOffset)!;
    // Scope equality alone omits variable/notation/attribute commands. Only cross declarations
    // and comments; other context changes require an explicit source repair from the worker.
    let between = source.slice(region.endOffset, anchorRegion.endOffset);
    for (const crossed of regions.filter(item => item.startOffset >= region.endOffset && item.endOffset <= anchorRegion.endOffset).reverse()) {
      const start = crossed.startOffset - region.endOffset, end = crossed.endOffset - region.endOffset;
      between = between.slice(0, start) + between.slice(end);
    }
    if (canonicalMathJson(leanDeclarationContextCommands(source, anchor.qualifiedName)) !== context || maskLeanComments(between).trim())
      throw new Error('math_task_integration_missing_context\nA conditional consumer precedes its checked input across context commands. ' +
        'Move the consumer and its supporting helpers after that input while preserving the frozen source context.');
    const start = declarationStartWithDoc(source, region.startOffset);
    const moved = source.slice(start, region.endOffset);
    source = source.slice(0, start) + source.slice(region.endOffset, anchorRegion.endOffset) + moved + source.slice(anchorRegion.endOffset);
  }
  return source;
}

/** Merge disjoint declaration edits, including helpers sharing a file, without overwriting peer work. */
export function applyTaskChanges(problem: SolverProblem, worktree: string, changes: readonly DeclarationChange[],
  imports: NonNullable<TaskProof['imports']> = [], conditions: readonly CooperativeTask[] = []): void {
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
        const moveStart = declarationStartWithDoc(source, existing.startOffset);
        const documentation = source.slice(moveStart, start);
        if (actual === change.after && anchor.endOffset === moveStart) continue;
        source = source.slice(0, moveStart) + source.slice(existing.endOffset);
        const offset = inspectLeanDeclarationRegions(source).find(region => region.name === change.afterName)!.endOffset;
        source = source.slice(0, offset) + documentation + change.after + source.slice(offset);
      } else {
        if (actual === change.after) continue;
        source = source.slice(0, start) + change.after + source.slice(existing.endOffset);
      }
    } else {
      if (change.before) throw new Error('math_task_integration_missing_declaration');
      const anchor = change.beforeName && regions.find(region => region.name === change.beforeName);
      const offset = anchor ? declarationStartWithDoc(source, anchor.startOffset) :
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
  for (const [file, source] of files) fs.writeFileSync(path.join(worktree, problem.projectRelative, file),
    conditions.length && file.endsWith('.lean') ? orderConditionalChanges(source, file, changes, conditions) : source);
  assertSolverSources(problem, worktree);
}
