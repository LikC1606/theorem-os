import type { SolverProblem } from './problem';
import { hasTaskReferences, taskGroup, taskVersion, type CooperativeTask, type TaskRecord } from './tasks';

export type TaskVersionReference = Readonly<{ taskId: string; taskDigest: string }>;
export type TaskApplicationContract = Readonly<{
  id: string; consumer: TaskVersionReference; type: string; proofTask?: TaskVersionReference;
}>;
export type TaskPremiseSource = Readonly<
  { kind: 'original-context'; file: string; declaration: string } |
  ({ kind: 'task' | 'local' } & TaskVersionReference) | { kind: 'unassigned' }
>;
export type TaskPremiseObligation = Readonly<{ id: string; type: string; source: TaskPremiseSource }>;

const object = (value: unknown): value is Record<string, unknown> =>
  Boolean(value && typeof value === 'object' && !Array.isArray(value));
const id = (value: unknown): value is string => typeof value === 'string' && /^[a-zA-Z0-9_-]{1,64}$/u.test(value);
const digest = (value: unknown): value is string => typeof value === 'string' && /^[a-f0-9]{64}$/u.test(value);
const fail = (reason: string): never => { throw new Error(`math_plan_obligation_${reason}`); };
const keys = (value: Record<string, unknown>, allowed: readonly string[]) => {
  if (Object.keys(value).some(key => !allowed.includes(key))) fail('invalid_fields');
};
const reference = (value: unknown): TaskVersionReference => {
  if (!object(value) || !id(value.taskId) || !digest(value.taskDigest)) return fail('invalid_reference');
  keys(value, ['taskId', 'taskDigest']);
  return { taskId: value.taskId, taskDigest: value.taskDigest };
};
const leanType = (value: unknown): string => {
  if (typeof value !== 'string' || !value.trim() || value.includes('\0') ||
      Buffer.byteLength(value) > 32_000 || value.trim() === 'FULL_CLOSED_LEAN_TYPE') return fail('invalid_type');
  return value;
};
const entries = (value: unknown): Record<string, unknown>[] => {
  if (!Array.isArray(value) || value.length > 32 || value.some(item => !object(item) || !id(item.id)))
    return fail('invalid_entries');
  if (new Set(value.map(item => item.id)).size !== value.length) return fail('duplicate_id');
  return value;
};

/** These are declared closed types, not an elaborated telescope or proof evidence. */
export function parseTaskObligationMetadata(value: { applications?: unknown; obligations?: unknown }) {
  const applications = value.applications === undefined ? undefined : entries(value.applications).map(item => {
    keys(item, ['id', 'consumer', 'type', 'proofTask']);
    return { id: item.id as string, consumer: reference(item.consumer), type: leanType(item.type),
      ...(item.proofTask === undefined ? {} : { proofTask: reference(item.proofTask) }) };
  });
  const obligations = value.obligations === undefined ? undefined : entries(value.obligations).map(item => {
    keys(item, ['id', 'type', 'source']);
    const source = item.source;
    if (!object(source)) return fail('invalid_source');
    let parsed: TaskPremiseSource;
    if (source.kind === 'original-context') {
      keys(source, ['kind', 'file', 'declaration']);
      if (typeof source.file !== 'string' || typeof source.declaration !== 'string' || !source.declaration.trim())
        return fail('invalid_source');
      parsed = { kind: source.kind, file: source.file, declaration: source.declaration };
    } else if (source.kind === 'task' || source.kind === 'local') {
      keys(source, ['kind', 'taskId', 'taskDigest']);
      parsed = { kind: source.kind, ...reference({ taskId: source.taskId, taskDigest: source.taskDigest }) };
    } else if (source.kind === 'unassigned') {
      keys(source, ['kind']); parsed = { kind: source.kind };
    } else return fail('invalid_source');
    return { id: item.id as string, type: leanType(item.type), source: parsed };
  });
  return { ...(applications === undefined ? {} : { applications }), ...(obligations === undefined ? {} : { obligations }) };
}

/** Metadata edges describe provenance only; they never become scheduling dependencies. */
export function validateTaskObligations(problem: SolverProblem, tasks: readonly CooperativeTask[]): void {
  const nodes = new Map(tasks.map(task => [task.id, task]));
  const edges = new Map(tasks.map(task => [task.id, new Set(task.dependsOn)]));
  const typed = (task: CooperativeTask) => task.kind === 'lemma' && Boolean(task.type?.trim());
  const resolve = (ref: TaskVersionReference) => {
    const task = nodes.get(ref.taskId);
    if (!task) return fail('missing_task');
    if (taskVersion(task) !== ref.taskDigest) return fail('stale_reference');
    return task;
  };
  const visible = (viewer: CooperativeTask, target: CooperativeTask) => {
    if (taskGroup(viewer) !== taskGroup(target) && target.sharing === 'group') fail('not_shared');
  };
  const edge = (consumer: CooperativeTask, producer: CooperativeTask) => {
    visible(consumer, producer);
    edges.get(consumer.id)!.add(producer.id);
  };
  for (const task of tasks) {
    if (task.applications?.length && !typed(task)) fail('application_requires_helper');
    for (const app of task.applications ?? []) {
      const consumer = resolve(app.consumer);
      if (!['lemma', 'goal'].includes(consumer.kind)) fail('invalid_consumer');
      visible(task, consumer);
      edge(consumer, task);
      if (app.proofTask) {
        const proof = resolve(app.proofTask);
        if (!typed(proof) || proof.id === task.id || proof.id === consumer.id || proof.type!.trim() !== app.type.trim())
          fail('invalid_application_task');
        visible(task, proof);
        edge(consumer, proof); edge(proof, task);
      }
    }
    for (const premise of task.obligations ?? []) {
      const source = premise.source;
      if (source.kind === 'original-context') {
        if (!problem.declarations[source.file]?.some(declaration => declaration.name === source.declaration))
          fail('unknown_original_context');
      } else if (source.kind === 'task' || source.kind === 'local') {
        const producer = resolve(source);
        if (!typed(producer) || producer.type!.trim() !== premise.type.trim()) fail('producer_type_mismatch');
        edge(task, producer);
      }
    }
  }
  const visiting = new Set<string>(), visited = new Set<string>();
  const visit = (taskId: string) => {
    if (visiting.has(taskId)) fail('cycle');
    if (visited.has(taskId)) return;
    visiting.add(taskId);
    for (const producer of edges.get(taskId) ?? []) visit(producer);
    visiting.delete(taskId); visited.add(taskId);
  };
  for (const task of tasks) visit(task.id);
}

function proofSummary(node: TaskRecord | undefined, environmentDigest: string,
  visibleTasks: ReadonlyMap<string, TaskRecord>) {
  const proof = node?.integratedCheck ?? node?.proof;
  if (!node || !proof) return { status: 'unchecked' as const };
  const identity = { commit: proof.commit, sourceDigest: proof.sourceDigest,
    receiptIds: proof.verification.results.flatMap(result => result.receiptId ? [result.receiptId] : []) };
  if (proof.taskDigest !== taskVersion(node.task) || (proof.references && proof.references.environmentDigest !== environmentDigest))
    return { ...identity, status: 'stale' as const };
  if (proof.conditions?.length) return { ...identity, status: 'conditional' as const,
    conditions: proof.conditions.filter(condition => visibleTasks.has(condition.taskId)) };
  const results = proof.verification.results;
  const checked = node.status === 'integrated' && proof === node.integratedCheck && proof.passed && hasTaskReferences(proof) && proof.references &&
    proof.references.scope !== 'statement' && proof.references.sourceCommit === proof.commit &&
    proof.references.root.name === node.task.theoremName && proof.references.root.file === node.task.proofPath &&
    proof.verification.status === 'kernel_verified' && Boolean(proof.verification.targetCommit) && results.length === 1 &&
    results.every(result => result.status === 'kernel_verified' && Boolean(result.receiptId) &&
      result.targetCommit === proof.verification.targetCommit && result.theoremName === node.task.theoremName &&
      result.proofPath === node.task.proofPath && result.statementHash === proof.taskDigest &&
      result.leanStatementHash === proof.taskDigest && result.claim === 'statement' &&
      result.sorryCount === 0 && result.admitCount === 0 && result.goalsRemaining === 0);
  return { ...identity, status: checked ? 'checked-at-source' as const : 'recorded-unverified' as const };
}

/** Advisory display only. Formal application lemmas and actual consumer references stay distinct. */
export function buildTaskObligationSummary(records: readonly TaskRecord[], options: { environmentDigest: string }) {
  const nodes = new Map(records.map(node => [node.task.id, node]));
  const current = (ref: TaskVersionReference) => {
    const node = nodes.get(ref.taskId);
    return node && taskVersion(node.task) === ref.taskDigest ? node : undefined;
  };
  const uses = (consumer: TaskRecord | undefined, producer: TaskRecord) => {
    const references = consumer?.integratedCheck?.references;
    return Boolean(references?.tasks?.some(ref => ref.taskId === producer.task.id && ref.taskDigest === taskVersion(producer.task)) &&
      references.proof.some(ref => ref.name === producer.task.theoremName && ref.file === producer.task.proofPath));
  };
  return { evidence: 'advisory-contracts' as const, tasks: records.filter(node =>
    node.task.applications?.length || node.task.obligations?.length).map(node => {
    const producerProof = proofSummary(node, options.environmentDigest, nodes);
    return { taskId: node.task.id, taskDigest: taskVersion(node.task),
      applications: (node.task.applications ?? []).filter(app => nodes.has(app.consumer.taskId) &&
        (!app.proofTask || nodes.has(app.proofTask.taskId))).map(app => {
        const consumer = current(app.consumer), application = app.proofTask && current(app.proofTask);
        const consumerProof = proofSummary(consumer, options.environmentDigest, nodes);
        const applicationProof = proofSummary(application, options.environmentDigest, nodes);
        const observed = producerProof.status === 'checked-at-source' && consumerProof.status === 'checked-at-source' &&
          uses(consumer, node);
        const applicationChecked = application?.task.kind === 'lemma' && application.task.type?.trim() === app.type.trim() &&
          producerProof.status === 'checked-at-source' && applicationProof.status === 'checked-at-source' && uses(application, node);
        return { ...app, producer: { taskId: node.task.id, taskDigest: taskVersion(node.task) },
          typeEvidence: applicationChecked ? 'checked-application-task' as const : 'declared-not-elaborated' as const,
          status: !consumer || (app.proofTask && !application) ? 'stale-or-unavailable' as const :
            observed ? 'checked-reference' as const : applicationChecked ? 'checked-application-task' as const : 'declared' as const,
          producerProof, consumerProof, ...(app.proofTask ? { applicationProof } : {}) };
      }),
      obligations: (node.task.obligations ?? []).filter(premise =>
        (premise.source.kind !== 'task' && premise.source.kind !== 'local') || nodes.has(premise.source.taskId)).map(premise => {
        const source = premise.source;
        if (source.kind === 'original-context' || source.kind === 'unassigned')
          return { ...premise, status: source.kind === 'original-context' ? 'declared-original-context' as const : 'unassigned' as const };
        const producer = current(source), evidence = proofSummary(producer, options.environmentDigest, nodes);
        return { ...premise, status: !producer || producer.task.type?.trim() !== premise.type.trim() ? 'stale-or-unavailable' as const :
          evidence.status === 'checked-at-source' ? 'checked-producer' as const : 'awaiting-proof' as const, producerProof: evidence };
      }) };
  }) };
}
