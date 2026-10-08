import { mathDigest } from "./mathRuntimeIo";
import fs from 'node:fs';
import path from 'node:path';
import { inspectLeanDeclarations } from "./verifier";
import { MAX_INSTALLED_SOURCE_FILE_BYTES } from "./installedPackageSearch";
import { isAllowedMathProofSource } from "./mathProofSourcePolicy";
import type { MathResearchWorkflowState } from "./mathResearchWorkflow";

/** Conservative textual identity: formatting is ignored, mathematical symbols and case are preserved. */
export const mathResearchStatementIdentity = (value: string): string =>
  mathDigest(value.normalize('NFC').replace(/\s+/gu, ' ').trim());

/** Explicit references disambiguate a cross-assignment reference from a local key containing colons. */
export const mathResearchNoteReference = (assignmentId: string, key: string): string =>
  `math-note:${JSON.stringify([assignmentId, key])}`;

type MathResearchArtifact = { digest: string; declarations: Set<string> };
type MathResearchArtifactCacheEntry = { stamp: string; artifact: MathResearchArtifact };
const researchArtifactCache = new Map<string, MathResearchArtifactCacheEntry>();

function rememberResearchArtifact(file: string, stamp: string, artifact: MathResearchArtifact): MathResearchArtifact {
  if (researchArtifactCache.size >= 256) researchArtifactCache.delete(researchArtifactCache.keys().next().value!);
  researchArtifactCache.set(file, { stamp, artifact });
  return artifact;
}

function readCurrentResearchArtifact(file: string): MathResearchArtifact {
  if (fs.realpathSync(file) !== file) throw new Error('symlink');
  const stat = fs.statSync(file, { bigint: true });
  if (!stat.isFile() || stat.size > BigInt(MAX_INSTALLED_SOURCE_FILE_BYTES)) throw new Error('unsupported artifact');
  const stamp = [stat.dev, stat.ino, stat.size, stat.mtimeNs, stat.ctimeNs].join(':');
  const cached = researchArtifactCache.get(file);
  if (cached?.stamp === stamp) return cached.artifact;
  const source = fs.readFileSync(file, 'utf8');
  return rememberResearchArtifact(file, stamp, {
    digest: mathDigest(source),
    declarations: new Set(file.endsWith('.lean') ? inspectLeanDeclarations(source).map((entry) => entry.name) : []),
  });
}

/** Research dependencies are organizational evidence, distinct from kernel-verified proof plans. */
export function buildMathResearchGraph(
  states: readonly Pick<MathResearchWorkflowState, 'assignmentId' | 'notebook'>[],
  options: { projectRoot?: string; assignmentRoots?: Readonly<Record<string, string>> } = {}
) {
  const localKeys = new Map(
    states.map((state) => [state.assignmentId, new Set(state.notebook.map((note) => note.key))])
  );
  const resolveReference = (assignmentId: string, key: string): string => {
    if (key.startsWith('math-note:')) {
      try {
        const value: unknown = JSON.parse(key.slice('math-note:'.length));
        if (Array.isArray(value) && value.length === 2 && value.every((item) => typeof item === 'string'))
          return `${value[0]}:${value[1]}`;
      } catch {
        /* Legacy keys may share the explicit-reference prefix. */
      }
    }
    if (localKeys.get(assignmentId)?.has(key) || !key.includes(':')) return `${assignmentId}:${key}`;
    return key;
  };
  const artifacts = new Map<string, MathResearchArtifact | undefined>();
  const inspectBinding = (
    binding: NonNullable<MathResearchWorkflowState['notebook'][number]['artifactBindings']>[number],
    assignmentId: string
  ) => {
    const projectRoot = options.assignmentRoots?.[assignmentId] ?? options.projectRoot;
    if (!projectRoot || path.isAbsolute(binding.path) || binding.path.includes('\\')) return 'unknown' as const;
    const parts = binding.path.split('/');
    if (
      parts.some((part) => !part || part === '.' || part === '..') ||
      !isAllowedMathProofSource(binding.path.endsWith('.lean') ? binding.path : `${binding.path}.lean`)
    )
      return 'unknown' as const;
    let root: string;
    try {
      root = fs.realpathSync(projectRoot);
    } catch {
      return 'unknown' as const;
    }
    const file = path.resolve(root, binding.path);
    if (!artifacts.has(file)) {
      try {
        artifacts.set(file, readCurrentResearchArtifact(file));
      } catch {
        artifacts.set(file, undefined);
      }
    }
    const artifact = artifacts.get(file);
    if (!artifact) return 'unknown' as const;
    if (artifact.digest !== binding.sha256) return 'changed' as const;
    if (
      binding.kind === 'lean_declaration' &&
      (!binding.declarationName || !artifact.declarations.has(binding.declarationName))
    )
      return 'unknown' as const;
    return 'current' as const;
  };
  const nodes = states.flatMap((state) =>
    state.notebook.map((note) => {
      const statuses = (note.artifactBindings ?? []).map((binding) => inspectBinding(binding, state.assignmentId));
      return {
        ...note,
        id: `${state.assignmentId}:${note.key}`,
        assignmentId: state.assignmentId,
        statementIdentity: mathResearchStatementIdentity(note.statement ?? note.summary),
        dependencies: [...new Set((note.dependsOn ?? []).map((key) => resolveReference(state.assignmentId, key)))],
        supersededId: note.supersedes ? resolveReference(state.assignmentId, note.supersedes) : undefined,
        authority: 'organization' as const,
        artifactStatus: statuses.includes('changed')
          ? ('changed' as const)
          : statuses.includes('unknown')
            ? ('unknown' as const)
            : statuses.length
              ? ('current' as const)
              : ('unbound' as const),
      };
    })
  );
  const byId = new Map(nodes.map((node) => [node.id, node]));
  const dependents = new Map<string, string[]>();
  const indegree = new Map<string, number>();
  for (const node of nodes) {
    indegree.set(node.id, node.dependencies.filter((dependency) => byId.has(dependency)).length);
    for (const dependency of node.dependencies) {
      const downstream = dependents.get(dependency);
      if (downstream) downstream.push(node.id);
      else dependents.set(dependency, [node.id]);
    }
  }
  const invalidated = new Set(
    nodes
      .filter(
        (node) =>
          node.assessment === 'refuted' || node.artifactStatus === 'changed' || node.artifactStatus === 'unknown'
      )
      .map((node) => node.id)
  );
  const unresolved = new Set(
    nodes
      .filter((node) => node.dependencies.some((id) => !byId.has(id) || byId.get(id)!.assessment !== 'supported'))
      .map((node) => node.id)
  );
  const unresolvedQueue = [...unresolved];
  for (let index = 0; index < unresolvedQueue.length; index += 1) {
    for (const id of dependents.get(unresolvedQueue[index]!) ?? []) {
      if (!unresolved.has(id)) {
        unresolved.add(id);
        unresolvedQueue.push(id);
      }
    }
  }
  const superseded = new Set(
    nodes.flatMap((node) => (node.supersededId && byId.has(node.supersededId) ? [node.supersededId] : []))
  );
  for (const id of superseded) invalidated.add(id);
  const invalidationQueue = [...invalidated];
  for (let index = 0; index < invalidationQueue.length; index += 1) {
    for (const id of dependents.get(invalidationQueue[index]!) ?? []) {
      if (!invalidated.has(id)) {
        invalidated.add(id);
        invalidationQueue.push(id);
      }
    }
  }
  // Kahn's remaining vertices include each dependency cycle and every node relying on it.
  const acyclicQueue = nodes.filter((node) => indegree.get(node.id) === 0).map((node) => node.id);
  for (let index = 0; index < acyclicQueue.length; index += 1) {
    for (const id of dependents.get(acyclicQueue[index]!) ?? []) {
      const remaining = indegree.get(id)! - 1;
      indegree.set(id, remaining);
      if (remaining === 0) acyclicQueue.push(id);
    }
  }
  const projected = nodes.map((node) => {
    const unresolvedDependencies = node.dependencies.filter((id) => {
      const dependency = byId.get(id);
      return !dependency || dependency.assessment !== 'supported' || invalidated.has(id) || unresolved.has(id);
    });
    return {
      ...node,
      unresolvedDependencies,
      cyclic: indegree.get(node.id)! > 0,
      needsRecheck: invalidated.has(node.id) || unresolved.has(node.id),
      experimentStatus: node.experiment ? (node.experiment.outcome ? 'observed' : 'planned') : undefined,
    };
  });
  const statementGroups = new Map<string, string[]>();
  for (const node of nodes) {
    const group = statementGroups.get(node.statementIdentity);
    if (group) group.push(node.id);
    else statementGroups.set(node.statementIdentity, [node.id]);
  }
  return {
    nodes: projected,
    repeatedStatements: [...statementGroups.values()].filter((ids) => ids.length > 1),
    nextQuestions: projected
      .filter(
        (node) =>
          !superseded.has(node.id) &&
          (node.needsRecheck ||
            node.cyclic ||
            node.unresolvedDependencies.length > 0 ||
            node.experimentStatus === 'planned' ||
            node.assessment !== 'supported')
      )
      .map((node) => ({
        id: node.id,
        question: node.experiment?.question ?? node.statement ?? node.summary,
        reason: node.cyclic
          ? 'circular_dependency'
          : node.artifactStatus === 'changed'
            ? 'artifact_changed'
            : node.artifactStatus === 'unknown'
              ? 'artifact_unavailable'
              : unresolved.has(node.id)
                ? 'unresolved_dependencies'
                : node.needsRecheck
                  ? 'dependency_changed'
                  : node.unresolvedDependencies.length
                    ? 'unresolved_dependencies'
                    : node.experimentStatus === 'planned'
                      ? 'run_experiment'
                      : 'needs_evidence',
        targetConnection: node.targetConnection,
        dependencies: node.unresolvedDependencies,
      })),
    authority: 'organization',
    solverReady: false,
  };
}
