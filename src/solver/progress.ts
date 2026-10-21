import { isAdvisoryTask, taskGroup, taskVersion, type RouteRecord, type TaskRecord } from './tasks';
import { describeProofRoutes, type ProofRoute } from './proofRoutes';
import type { ResearchHandoff } from './researchHandoffs';

/** Stored receipts describe a checkpoint; this function never replays or authorizes a proof. */
export function recordedTaskProofStatus(node: TaskRecord, environmentDigest?: string) {
  const proof = node.integratedCheck ?? node.proof;
  if (!proof) return 'none' as const;
  const stale = proof.taskDigest !== taskVersion(node.task) || Boolean(environmentDigest && proof.references &&
    proof.references.environmentDigest !== environmentDigest);
  const receipts = proof.verification;
  const checked = receipts.status === 'kernel_verified' && Boolean(receipts.targetCommit) && receipts.results.length > 0 &&
    receipts.results.every(result => result.status === 'kernel_verified' && result.targetCommit === receipts.targetCommit && result.receiptId);
  return stale ? 'stale' as const : !proof.passed ? 'failed' as const : !checked ? 'unverified' as const :
    proof.conditions?.length ? 'conditional' as const : 'checked' as const;
}

/** Completed investigations cannot encapsulate open premises; checked formal interfaces can. */
export function createRecordedTaskSettlement(tasks: readonly TaskRecord[], options: {
  environmentDigest?: string; proofRoutes?: readonly ProofRoute[]; includeParkedRoutes?: boolean;
} = {}) {
  const nodes = new Map(tasks.map(node => [node.task.id, node]));
  const versions = new Map(tasks.map(node => [node.task.id, taskVersion(node.task)]));
  const status = new Map(tasks.map(node => [node.task.id, recordedTaskProofStatus(node, options.environmentDigest)]));
  const currentReferences = (node: TaskRecord) => {
    const references = (node.integratedCheck ?? node.proof)?.references;
    // A scoped worker view may omit a private implementation prerequisite of a shared lemma.
    return references?.tasks?.every(reference => !versions.has(reference.taskId) ||
      versions.get(reference.taskId) === reference.taskDigest) ?? true;
  };
  const completed = new Map<string, boolean>();
  const settled = (node: TaskRecord | undefined): boolean => {
    if (!node) return false;
    if (!isAdvisoryTask(node.task)) return node.status === 'integrated' &&
      status.get(node.task.id) === 'checked' && currentReferences(node);
    if (completed.has(node.task.id)) return completed.get(node.task.id)!;
    completed.set(node.task.id, false);
    const alternatives = options.proofRoutes?.filter(route => route.targetTaskId === node.task.id) ?? node.alternativeRoutes ?? [];
    const eligible = options.includeParkedRoutes === false
      ? alternatives.filter(route => !node.parkedRoutes?.[route.id]?.length) : alternatives;
    const ready = node.status === 'completed' && node.task.dependsOn.every(id => settled(nodes.get(id))) &&
      (!alternatives.length || eligible.some(route =>
        [...route.prerequisiteTaskIds, route.closingTaskId].every(id => settled(nodes.get(id)))));
    completed.set(node.task.id, ready);
    return ready;
  };
  return { settled, currentReferences, status };
}

/** Planned use and recorded Lean use are separate facts, never a proof-completion percentage. */
export function buildProofContinuation(tasks: readonly TaskRecord[], options: {
  groups?: readonly RouteRecord[]; environmentDigest?: string; proofRoutes?: readonly ProofRoute[];
  /** Callers resolve these against the same scoped state before constructing the report. */
  researchHandoffs?: readonly ResearchHandoff[];
} = {}) {
  const nodes = new Map(tasks.map(node => [node.task.id, node]));
  const versions = new Map(tasks.map(node => [node.task.id, taskVersion(node.task)]));
  const active = (node: TaskRecord) => (node.task.status ?? 'active') === 'active' && (!options.groups ||
    options.groups.some(route => route.group.id === taskGroup(node.task) && route.group.status === 'active'));
  const { settled, currentReferences, status } = createRecordedTaskSettlement(tasks, options);
  const consumers = new Map<string, string[]>();
  const routes = options.proofRoutes ?? tasks.flatMap(node => node.alternativeRoutes ?? []);
  const alternatives = (id: string) => routes.filter(route => route.targetTaskId === id);
  const plannedInputs = (node: TaskRecord) => [...new Set([...node.task.dependsOn,
    ...alternatives(node.task.id).flatMap(route => [...route.prerequisiteTaskIds, route.closingTaskId])])];
  for (const node of tasks) for (const id of plannedInputs(node)) {
    const list = consumers.get(id) ?? []; list.push(node.task.id); consumers.set(id, list);
  }
  const goalPaths = new Map<string, Set<string>>();
  const frontierGoals = new Map<string, string[]>();
  const goals = tasks.filter(node => node.task.kind === 'goal' && active(node)).map(goal => {
    const seen = new Set<string>(), frontier = new Set<string>(), missing = new Set<string>();
    const visitPath = (id: string) => {
      if (seen.has(id)) return;
      seen.add(id);
      const paths = goalPaths.get(id) ?? new Set<string>(); paths.add(goal.task.id); goalPaths.set(id, paths);
      const node = nodes.get(id); if (node) plannedInputs(node).forEach(visitPath);
    };
    visitPath(goal.task.id);
    const visited = new Set<string>();
    const visitOpen = (id: string, result = frontier, absent = missing, walked = visited) => {
      if (walked.has(id)) return;
      walked.add(id);
      const node = nodes.get(id);
      if (!node) { absent.add(id); return; }
      if (settled(node)) return;
      const open = node.task.dependsOn.filter(dependency => !settled(nodes.get(dependency)));
      if (!open.length) result.add(id);
      else open.forEach(input => visitOpen(input, result, absent, walked));
    };
    visitOpen(goal.task.id);
    const routeFrontiers = alternatives(goal.task.id).map(route => {
      const open = new Set<string>(), absent = new Set<string>(), walked = new Set<string>();
      if (!settled(goal)) for (const id of [...route.prerequisiteTaskIds, route.closingTaskId]) visitOpen(id, open, absent, walked);
      return { routeId: route.id, frontier: [...open], missingDependencies: [...absent],
        parkedBy: [...(goal.parkedRoutes?.[route.id] ?? [])] };
    });
    if (!settled(goal) && routeFrontiers.length && !routeFrontiers.some(route => !route.frontier.length && !route.missingDependencies.length)) {
      frontier.delete(goal.task.id);
      for (const route of routeFrontiers) {
        route.frontier.forEach(id => frontier.add(id)); route.missingDependencies.forEach(id => missing.add(id));
      }
    }
    for (const id of frontier) {
      const list = frontierGoals.get(id) ?? []; list.push(goal.task.id); frontierGoals.set(id, list);
    }
    return { taskId: goal.task.id, status: goal.status, recordedProof: status.get(goal.task.id)!,
      frontier: [...frontier], missingDependencies: [...missing],
      checkedDependencies: [...seen].filter(id => id !== goal.task.id && nodes.get(id)?.task.kind === 'lemma' && settled(nodes.get(id))),
      advisoryDependencies: [...seen].filter(id => nodes.get(id)?.status === 'completed' &&
        ['research', 'sketch'].includes(nodes.get(id)!.task.kind)),
      ...(routeFrontiers.length ? { routeCombination: 'any' as const, alternatives: routeFrontiers } : {}) };
  });
  const checkedInputs = (node: TaskRecord) => plannedInputs(node).filter(id =>
    nodes.get(id)?.task.kind === 'lemma' && settled(nodes.get(id)));
  const frontier = [...frontierGoals].map(([id, goalIds]) => {
    const node = nodes.get(id)!;
    return { taskId: id, kind: node.task.kind, status: node.status, control: node.task.status ?? 'active',
      goalIds, attempts: node.attempts, checkedInputs: checkedInputs(node),
      ...(node.routeParking?.length ? { parkedBy: [...node.routeParking] } : {}) };
  });
  const reuse = tasks.filter(node => node.task.kind === 'lemma' && settled(node)).map(producer => {
    const proofConsumers: string[] = [], statementConsumers: string[] = [], conditionalConsumers: string[] = [];
    const declarations = [{ file: producer.task.proofPath, name: producer.task.theoremName },
      ...((producer.integratedCheck ?? producer.proof)?.changes ?? [])];
    const matches = (reference: { file: string; name: string }) => declarations.some(declaration =>
      declaration.file === reference.file && declaration.name &&
      (reference.name === declaration.name || reference.name.endsWith('.' + declaration.name)));
    for (const consumer of tasks) {
      if (consumer === producer || !currentReferences(consumer)) continue;
      const proof = consumer.integratedCheck ?? consumer.proof, references = proof?.references;
      if (!Array.isArray(references?.tasks) || !references.tasks.some(reference => reference.taskId === producer.task.id &&
          reference.taskDigest === versions.get(producer.task.id))) continue;
      const proofUse = Array.isArray(references.proof) && references.proof.some(matches);
      const statementUse = Array.isArray(references.statement) && references.statement.some(matches);
      if (!proofUse && !statementUse) continue;
      if (status.get(consumer.task.id) === 'conditional' && consumer.status === 'conditional') {
        conditionalConsumers.push(consumer.task.id);
      } else if (settled(consumer) && status.get(consumer.task.id) === 'checked') {
        if (proofUse) proofConsumers.push(consumer.task.id);
        if (statementUse) statementConsumers.push(consumer.task.id);
      }
    }
    return { taskId: producer.task.id, plannedConsumers: consumers.get(producer.task.id) ?? [],
      plannedGoalIds: [...(goalPaths.get(producer.task.id) ?? [])], proofConsumers, statementConsumers, conditionalConsumers };
  });
  const reuseById = new Map(reuse.map(item => [item.taskId, item]));
  const missingReferences = tasks.filter(node => {
    if (isAdvisoryTask(node.task)) return false;
    const proof = node.integratedCheck ?? node.proof;
    if (!proof) return false;
    const references = proof.references, recorded = status.get(node.task.id);
    return !['checked', 'conditional'].includes(recorded!) || !currentReferences(node) ||
      !Array.isArray(references?.tasks) || !Array.isArray(references?.proof) || !Array.isArray(references?.statement);
  }).map(node => node.task.id);
  const adoptedResearch = (options.researchHandoffs ?? []).flatMap(handoff => {
    const decision = handoff.decision, source = nodes.get(handoff.sourceTaskId);
    const adopted = decision?.taskId ? nodes.get(decision.taskId) : undefined;
    if (handoff.status !== 'adopted' || decision?.status !== 'adopted' || !source ||
        versions.get(source.task.id) !== handoff.sourceTaskDigest || !adopted || adopted.task.kind !== 'lemma' ||
        versions.get(adopted.task.id) !== decision.taskDigest) return [];
    const use = reuseById.get(adopted.task.id);
    const missingReferenceTaskIds = [...new Set([...(!use ? [adopted.task.id] : []), ...missingReferences])];
    return [{ adoption: 'adopted' as const, handoffId: handoff.id, sourceTaskId: source.task.id,
      taskId: adopted.task.id, taskDigest: versions.get(adopted.task.id)!, recordedProof: status.get(adopted.task.id)!,
      plannedConsumers: consumers.get(adopted.task.id) ?? [], plannedGoalIds: [...(goalPaths.get(adopted.task.id) ?? [])],
      proofConsumers: use?.proofConsumers ?? [], statementConsumers: use?.statementConsumers ?? [],
      conditionalConsumers: use?.conditionalConsumers ?? [],
      // Empty consumer arrays describe only recorded use; missing coverage never establishes non-use.
      referenceCoverage: missingReferenceTaskIds.length ? 'unknown' as const : 'recorded' as const,
      missingReferenceTaskIds }];
  });
  return { evidence: 'recorded-not-replayed' as const, goals, frontier, reuse, adoptedResearch,
    continuationCandidates: tasks.filter(node => active(node) && node.status === 'pending' &&
      ['lemma', 'goal'].includes(node.task.kind) && goalPaths.has(node.task.id) && checkedInputs(node).length > 0 &&
      node.task.dependsOn.every(id => settled(nodes.get(id))) && !node.routeParking?.length &&
      (!alternatives(node.task.id).length || alternatives(node.task.id).some(route =>
        !node.parkedRoutes?.[route.id]?.length &&
        [...route.prerequisiteTaskIds, route.closingTaskId].every(id => settled(nodes.get(id)))))).map(node => node.task.id),
    unconnectedTasks: tasks.filter(node => active(node) && node.task.kind !== 'goal' && !goalPaths.has(node.task.id)).map(node => node.task.id),
    referenceCoverageMissing: tasks.filter(node => settled(node) && ['lemma', 'goal'].includes(node.task.kind) &&
      !(node.integratedCheck ?? node.proof)?.references?.tasks).map(node => node.task.id),
    ...(routes.length ? { proofRoutes: describeProofRoutes(routes, tasks, options.environmentDigest) } : {}) };
}
