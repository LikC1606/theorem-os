import { taskGroup, taskVersion, type RouteRecord, type TaskRecord } from './tasks';

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

/** Planned use and recorded Lean use are separate facts, never a proof-completion percentage. */
export function buildProofContinuation(tasks: readonly TaskRecord[], options: {
  groups?: readonly RouteRecord[]; environmentDigest?: string;
} = {}) {
  const nodes = new Map(tasks.map(node => [node.task.id, node]));
  const versions = new Map(tasks.map(node => [node.task.id, taskVersion(node.task)]));
  const active = (node: TaskRecord) => (node.task.status ?? 'active') === 'active' && (!options.groups ||
    options.groups.some(route => route.group.id === taskGroup(node.task) && route.group.status === 'active'));
  const status = new Map(tasks.map(node => [node.task.id, recordedTaskProofStatus(node, options.environmentDigest)]));
  const currentReferences = (node: TaskRecord) => {
    const references = (node.integratedCheck ?? node.proof)?.references;
    // A scoped worker view may omit a private implementation prerequisite of a shared lemma.
    return references?.tasks?.every(reference => !versions.has(reference.taskId) ||
      versions.get(reference.taskId) === reference.taskDigest) ?? true;
  };
  const settled = (node: TaskRecord | undefined) => Boolean(node && (['research', 'sketch'].includes(node.task.kind)
    ? node.status === 'completed' : node.status === 'integrated' && status.get(node.task.id) === 'checked' && currentReferences(node)));
  const consumers = new Map<string, string[]>();
  for (const node of tasks) for (const id of node.task.dependsOn) {
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
      nodes.get(id)?.task.dependsOn.forEach(visitPath);
    };
    visitPath(goal.task.id);
    const visited = new Set<string>();
    const visitOpen = (id: string) => {
      if (visited.has(id)) return;
      visited.add(id);
      const node = nodes.get(id);
      if (!node) { missing.add(id); return; }
      if (settled(node)) return;
      const open = node.task.dependsOn.filter(dependency => !settled(nodes.get(dependency)));
      if (!open.length) frontier.add(id);
      else open.forEach(visitOpen);
    };
    visitOpen(goal.task.id);
    for (const id of frontier) {
      const list = frontierGoals.get(id) ?? []; list.push(goal.task.id); frontierGoals.set(id, list);
    }
    return { taskId: goal.task.id, status: goal.status, recordedProof: status.get(goal.task.id)!,
      frontier: [...frontier], missingDependencies: [...missing],
      checkedDependencies: [...seen].filter(id => id !== goal.task.id && nodes.get(id)?.task.kind === 'lemma' && settled(nodes.get(id))),
      advisoryDependencies: [...seen].filter(id => nodes.get(id)?.status === 'completed' &&
        ['research', 'sketch'].includes(nodes.get(id)!.task.kind)) };
  });
  const checkedInputs = (node: TaskRecord) => node.task.dependsOn.filter(id =>
    nodes.get(id)?.task.kind === 'lemma' && settled(nodes.get(id)));
  const frontier = [...frontierGoals].map(([id, goalIds]) => {
    const node = nodes.get(id)!;
    return { taskId: id, kind: node.task.kind, status: node.status, control: node.task.status ?? 'active',
      goalIds, attempts: node.attempts, checkedInputs: checkedInputs(node) };
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
      if (!references?.tasks?.some(reference => reference.taskId === producer.task.id &&
          reference.taskDigest === versions.get(producer.task.id))) continue;
      const proofUse = references.proof.some(matches), statementUse = references.statement.some(matches);
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
  return { evidence: 'recorded-not-replayed' as const, goals, frontier, reuse,
    continuationCandidates: tasks.filter(node => active(node) && node.status === 'pending' &&
      ['lemma', 'goal'].includes(node.task.kind) && goalPaths.has(node.task.id) && checkedInputs(node).length > 0 &&
      node.task.dependsOn.every(id => settled(nodes.get(id)))).map(node => node.task.id),
    unconnectedTasks: tasks.filter(node => active(node) && node.task.kind !== 'goal' && !goalPaths.has(node.task.id)).map(node => node.task.id),
    referenceCoverageMissing: tasks.filter(node => settled(node) && ['lemma', 'goal'].includes(node.task.kind) &&
      !(node.integratedCheck ?? node.proof)?.references?.tasks).map(node => node.task.id) };
}
