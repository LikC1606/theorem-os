import path from 'node:path';
import { canonicalMathJson, mathDigest } from '../math/mathRuntimeIo';
import { inspectLeanDeclarations, inspectLeanDeclarationRegions } from '../math/leanSource';
import type { CooperationState } from './cooperation';
import { deliveryFinding, type DeliveryRecord } from './deliveries';
import type { SolverProblem } from './problem';
import { hasTaskAcceptance, taskGroup, taskVersion, type CooperativeAction, type TaskRecord } from './tasks';
import { buildProofContinuation } from './progress';
import { pendingResearchHandoffs, researchHandoffContext, selectResearchHandoffBatch } from './researchHandoffs';
import { COORDINATION_INLINE_FINDING_BYTES, pendingResearchChallenges, researchChallengeContext, selectResearchChallengeBatch } from './researchChallenges';
import { contextTaskConsumers } from './taskConsumers';
import { mathematicalGapContext } from './mathematicalGaps';

export const DEFAULT_TASK_CONTEXT_BYTES = 512 * 1024;
export const DEFAULT_OPTIONAL_TASK_CONTEXT_BYTES = 64 * 1024;
export type ContextItemKind = 'problem' | 'assignment' | 'interfaces' | 'sources' | 'feedback' | 'delivery' |
  'finding' | 'history' | 'blocker' | 'routes' | 'continuation' | 'statement-review' | 'checkpoint' | 'groups';
export type ContextOmissionReason = 'budget' | 'superseded' | 'stale-version' | 'duplicate' | 'selection-limit' |
  'advisory-summary-limit' | 'advisory-details-by-reference' | 'optional-budget' |
  'encapsulated-private-dependency' | 'outside-task-scope';
export type ContextManifest = Readonly<{
  schema: 'theorem-os.task-context.v1';
  evidence: 'recorded-not-replayed';
  maxBytes: number; usedBytes: number; mandatoryBytes: number; maxOptionalBytes: number; optionalBytes: number; contentDigest: string;
  requiredTaskIds: readonly string[];
  included: readonly { id: string; kind: ContextItemKind; required: boolean; bytes: number }[];
  omitted: readonly { id: string; kind: ContextItemKind; reason: ContextOmissionReason }[];
}>;
export type ContextSection = Readonly<{ id: string; kind: ContextItemKind; text: string; priority?: number }>;
export type TaskContextInput = Readonly<{
  problem: SolverProblem; cooperation?: CooperationState; action?: CooperativeAction;
  instructions: string; taskText: string; feedback?: string; checkpoint?: string;
  /** Frozen source projection containing complete context and fixed definitions, with proof bodies omitted. */
  frozenContexts?: Readonly<Record<string, string>>;
  maxContextBytes?: number; environmentDigest?: string;
  /** Optional hints have their own allowance; exact mathematical contracts never use it. */
  maxOptionalContextBytes?: number;
  mandatory?: readonly ContextSection[];
  optional?: readonly ContextSection[];
}>;
export class TaskContextError extends Error {
  constructor(readonly code: 'math_context_missing_required' | 'math_context_stale_required' |
    'math_context_mandatory_overflow' | 'math_context_invalid_budget', readonly itemId: string) {
    super(`${code}:${itemId}`);
  }
}

const json = (value: unknown) => JSON.stringify(value);
const section = (id: string, kind: ContextItemKind, title: string, value: unknown): ContextSection =>
  ({ id, kind, text: `${title}\n${typeof value === 'string' ? value : json(value)}` });
const missing = (id: string): never => { throw new TaskContextError('math_context_missing_required', id); };
const stale = (id: string): never => { throw new TaskContextError('math_context_stale_required', id); };
const present = (value: unknown): value is string => typeof value === 'string' && !!value.trim();
const localName = (name: string) => name.split('.').at(-1);
const sourcePath = (problem: SolverProblem, file: string) => path.posix.join(problem.projectRelative.replaceAll('\\', '/'), file);

/** Preserve source-level variables, scopes, instances and fixed definitions; never copy an existing proof body. */
export function frozenSourceContext(problem: SolverProblem, file: string, source: string): string {
  const regions = inspectLeanDeclarationRegions(source), originals = problem.declarations[file] ?? [];
  if (originals.some(original => {
    const found = regions.filter(region => region.name === original.name);
    return found.length !== 1 || found[0].declarationType !== original.header || (original.body &&
      mathDigest(source.slice(found[0].bodyOffset, found[0].endOffset).trim()) !== original.body);
  })) return stale(`frozen-source:${file}`);
  const kinds = new Map(inspectLeanDeclarations(source).map(item => [item.startOffset, item.kind]));
  for (const region of [...regions].reverse()) {
    const isTarget = problem.targets.some(target => target.proofPath === file &&
      localName(target.theoremName) === localName(region.name));
    if (kinds.get(region.startOffset) === 'theorem' || isTarget)
      source = source.slice(0, region.bodyOffset) + '\n/- Proof body omitted by the host context compiler. -/\n' + source.slice(region.endOffset);
  }
  return source;
}

function frozenHeader(problem: SolverProblem, node: Pick<TaskRecord, 'task'>): string | undefined {
  if (node.task.kind !== 'goal') return node.task.type;
  const exact = problem.declarations[node.task.proofPath!]?.filter(item =>
    item.name === node.task.theoremName || localName(item.name) === localName(node.task.theoremName!)) ?? [];
  if (exact.length !== 1) return missing(`interface:${node.task.id}`);
  return exact[0].header;
}

/** Kernel-verified at one target commit, with at least one receipt and every receipt at that commit. */
const receiptsComplete = ({ verification }: NonNullable<TaskRecord['proof']>) => verification.status === 'kernel_verified' &&
  present(verification.targetCommit) && verification.results.length > 0 && verification.results.every(result =>
    result.status === 'kernel_verified' && result.targetCommit === verification.targetCommit && present(result.receiptId));

function evidence(node: TaskRecord, environmentDigest?: string) {
  const proof = node.integratedCheck ?? node.proof;
  if (!proof) return undefined;
  if (proof.taskDigest !== taskVersion(node.task) || (environmentDigest && proof.references &&
      proof.references.environmentDigest !== environmentDigest) || (proof.passed && !receiptsComplete(proof)))
    return stale(`evidence:${node.task.id}`);
  return { evidence: 'recorded-not-replayed', passed: proof.passed, commit: proof.commit,
    sourceDigest: proof.sourceDigest, taskDigest: proof.taskDigest, conditions: proof.conditions ?? [],
    verification: { status: proof.verification.status, targetCommit: proof.verification.targetCommit,
      receipts: proof.verification.results.map(result => ({ receiptId: result.receiptId, status: result.status,
        targetCommit: result.targetCommit })) },
    references: proof.references && { sourceCommit: proof.references.sourceCommit,
      environmentDigest: proof.references.environmentDigest, contextDigest: proof.references.contextDigest,
      root: proof.references.root, inputs: proof.references.inputs, tasks: proof.references.tasks,
      statement: proof.references.statement, proof: proof.references.proof }, imports: proof.imports };
}

type EvidenceReferenceEntry = NonNullable<ReturnType<typeof evidence>>['references']['inputs'][number] |
  NonNullable<ReturnType<typeof evidence>>['references']['proof'][number] |
  NonNullable<ReturnType<typeof evidence>>['references']['tasks'][number];

/** First-seen index of each distinct key. */
function interner<T>(key: (value: T) => string) {
  const values: T[] = [], indices = new Map<string, number>();
  return { values, index: (value: T) => {
    const id = key(value), previous = indices.get(id);
    if (previous !== undefined) return previous;
    indices.set(id, values.length); values.push(value); return values.length - 1;
  } };
}

/** Intern exact metadata only; each proof retains its own source and verifier identities. */
function evidenceReferenceDictionary() {
  const { values: entries, index } = interner<EvidenceReferenceEntry>(canonicalMathJson);
  const { values: digests, index: digestIndex } = interner<string>(digest => digest);
  return { entries, digests, encode: (record: ReturnType<typeof sharedEvidence>) => record?.references ? {
    ...record, references: { ...record.references,
      environmentDigest: digestIndex(record.references.environmentDigest),
      contextDigest: digestIndex(record.references.contextDigest),
      inputs: record.references.inputs.map(index), proof: record.references.proof.map(index), tasks: record.references.tasks?.map(index),
      statement: record.references.statement.map(index) },
  } : record };
}

/** Null marks only exact field equality; absent or distinct receipt targets stay distinct. */
function sharedEvidence(record: ReturnType<typeof evidence>) {
  return record && { ...record, taskDigest: null, verification: { ...record.verification,
    receipts: record.verification.receipts.map(receipt => ({ ...receipt,
      targetCommit: receipt.targetCommit !== undefined && receipt.targetCommit === record.verification.targetCommit
        ? null : receipt.targetCommit })),
  } };
}

function closedLeadHelper(node: TaskRecord): boolean {
  const proof = node.integratedCheck;
  return node.task.kind === 'lemma' && node.status === 'integrated' && !!proof?.passed &&
    !proof.conditions?.length && hasTaskAcceptance(proof) && present(proof.commit) &&
    present(proof.sourceDigest) && present(node.task.proofPath) && present(node.task.theoremName);
}

function leadTaskInterface(node: TaskRecord, action: CooperativeAction | undefined,
  omitted: ContextManifest['omitted'][number][]) {
  if (action?.kind === 'task' && node.task.id === action.task.id) return { id: node.task.id };
  const finishedAdvisory = node.status === 'completed' && ['research', 'sketch'].includes(node.task.kind);
  if (action?.kind !== 'lead' || !(closedLeadHelper(node) || finishedAdvisory) ||
      Buffer.byteLength(node.task.objective) <= 1024) return node.task;
  // The full typed interface remains inline; only settled planning prose moves to the live peer index.
  const { objective, ...task } = node.task;
  omitted.push({ id: `objective:${task.id}`, kind: 'interfaces', reason: 'advisory-details-by-reference' });
  return { ...task, objectiveDigest: mathDigest(objective) };
}

/** Closed shared interfaces encapsulate private implementation prerequisites, never unresolved assumptions. */
function requiredTasks(input: TaskContextInput, omitted: ContextManifest['omitted'][number][]) {
  const tasks = input.cooperation?.tasks ?? [], byId = new Map(tasks.map(node => [node.task.id, node]));
  if (byId.size !== tasks.length) return missing('duplicate-task-id');
  const required = new Set<string>(), visiting = new Set<string>();
  const action = input.action;
  const scopedLead = action?.kind === 'lead' && tasks.some(node => node.task.kind === 'goal');
  const coordination = action?.kind === 'lead' && action.coordination;
  if (action?.kind === 'task') {
    if (action.assignment.taskId !== action.task.id || action.assignment.taskDigest !== taskVersion(action.task))
      return stale(`assignment:${action.task.id}`);
    const current = byId.get(action.task.id);
    if (!current) return missing(`task:${action.task.id}`);
    if (taskVersion(current.task) !== action.assignment.taskDigest) return stale(`task:${action.task.id}`);
  }
  const visit = (id: string, consumer?: TaskRecord) => {
    const node = byId.get(id);
    if (!node) {
      const proof = consumer?.integratedCheck;
      if (consumer?.status === 'integrated' && proof?.passed && !proof.conditions?.length &&
          proof.taskDigest === taskVersion(consumer.task) && receiptsComplete(proof)) {
        omitted.push({ id: `interface:${id}`, kind: 'interfaces', reason: 'encapsulated-private-dependency' });
        return;
      }
      return missing(`dependency:${id}`);
    }
    if (visiting.has(id)) return missing(`dependency-cycle:${id}`);
    if (required.has(id)) return;
    visiting.add(id);
    // A typed interface must be supplied exactly; advisory tasks have no admitted proposition.
    if (['lemma', 'goal'].includes(node.task.kind) && !present(frozenHeader(input.problem, node)))
      return missing(`interface:${id}`);
    evidence(node, input.environmentDigest);
    required.add(id);
    const proof = node.integratedCheck ?? node.proof;
    for (const condition of proof?.conditions ?? []) {
      const dependency = byId.get(condition.taskId);
      if (!dependency) return missing(`condition:${condition.taskId}`);
      if (taskVersion(dependency.task) !== condition.taskDigest) return stale(`condition:${condition.taskId}`);
      visit(condition.taskId);
    }
    if ((!scopedLead || !closedLeadHelper(node)) && !(coordination && node.task.kind === 'goal')) {
      for (const dependency of node.task.dependsOn) visit(dependency, node);
      if (action?.kind === 'lead' && !coordination) for (const route of [
        ...(input.cooperation?.proofRoutes ?? []), ...(node.alternativeRoutes ?? []),
      ]) if (route.targetTaskId === id) [...route.prerequisiteTaskIds, route.closingTaskId].forEach(dependency => visit(dependency));
    }
    visiting.delete(id);
  };
  if (action?.kind === 'task') visit(action.task.id);
  else if (coordination) {
    // Coordination consumes a fixed inbox, not every open mathematical investigation.
    // The complete archive remains available for an explicit full-plan replacement.
    tasks.filter(node => node.task.kind === 'goal').forEach(node => visit(node.task.id));
    const visitDeliveryInputs = (deliveryId: string) => {
      const delivery = input.cooperation?.deliveries?.find(item => item.id === deliveryId);
      if (!delivery) return missing(`delivery:${deliveryId}`);
      for (const dependency of delivery.dependencies) {
        const node = byId.get(dependency.taskId);
        if (!node) return missing(`dependency:${dependency.taskId}`);
        if (taskVersion(node.task) !== dependency.taskDigest) return stale(`dependency:${dependency.taskId}`);
        visit(dependency.taskId);
      }
    };
    action.stagnationRecovery?.taskIds.forEach(id => visit(id));
    action.capacityRefill?.ownershipCandidates?.forEach(item => visit(item.taskId));
    const handoffIds = new Set(action.handoffIds ?? []);
    for (const item of pendingResearchHandoffs(input.cooperation!)) if (handoffIds.has(item.id) ||
        item.sources.some(source => handoffIds.has(source.handoffId))) {
      visit(item.sourceTaskId);
      item.sources.forEach(source => visitDeliveryInputs(source.deliveryId));
      item.proposal.dependsOn.filter(id => byId.has(id)).forEach(id => visit(id));
    }
    const challengeIds = new Set(action.challengeIds ?? []);
    for (const item of pendingResearchChallenges(input.cooperation!))
      if (challengeIds.has(item.id)) { visit(item.sourceTaskId); visitDeliveryInputs(item.deliveryId); }
    if (!handoffIds.size && !challengeIds.size) {
      const continuation = buildProofContinuation(tasks, { groups: input.cooperation?.groups,
        environmentDigest: input.environmentDigest, proofRoutes: input.cooperation?.proofRoutes });
      continuation.frontier.forEach(item => visit(item.taskId));
    }
    for (const node of tasks) if (!required.has(node.task.id))
      omitted.push({ id: `interface:${node.task.id}`, kind: 'interfaces', reason: 'outside-task-scope' });
  }
  else if (scopedLead) {
    for (const node of tasks) if (node.task.kind === 'goal' || !closedLeadHelper(node)) visit(node.task.id);
  }
  else tasks.forEach(node => visit(node.task.id));
  const route = action?.kind === 'task' && action.assignment.routeId ?
    input.cooperation?.proofRoutes?.find(route => route.id === action.assignment.routeId) ??
      byId.get(action.task.id)?.alternativeRoutes?.find(route => route.id === action.assignment.routeId) : undefined;
  if (action?.kind === 'task' && action.assignment.routeId) {
    if (!route || route.targetTaskId !== action.task.id) return missing(`route:${action.assignment.routeId}`);
    [...route.prerequisiteTaskIds, route.closingTaskId].forEach(id => visit(id));
  }
  if (action?.kind === 'task') for (const dependency of action.assignment.dependencies ?? []) {
    const current = byId.get(dependency.taskId);
    if (!current) {
      if (!omitted.some(item => item.id === `interface:${dependency.taskId}` && item.reason === 'encapsulated-private-dependency'))
        return missing(`dependency:${dependency.taskId}`);
    } else {
      if (taskVersion(current.task) !== dependency.taskDigest) return stale(`dependency:${dependency.taskId}`);
      visit(dependency.taskId);
    }
  }
  return { tasks: tasks.filter(node => required.has(node.task.id)),
    deferred: scopedLead && !coordination ? tasks.filter(node => !required.has(node.task.id) && closedLeadHelper(node)) : [], byId, required, route };
}

function checkedHelperReference(input: TaskContextInput, node: TaskRecord) {
  const proof = evidence(node, input.environmentDigest)!;
  return { id: node.task.id, taskDigest: taskVersion(node.task), status: node.status,
    theoremName: node.task.theoremName, proofPath: node.task.proofPath, groupId: taskGroup(node.task),
    sharing: node.task.sharing ?? 'problem', objectiveDigest: mathDigest(node.task.objective),
    source: { commit: proof.commit, path: sourcePath(input.problem, node.task.proofPath!), sourceDigest: proof.sourceDigest },
    verification: proof.verification, referenceSource: proof.references && { sourceCommit: proof.references.sourceCommit,
      environmentDigest: proof.references.environmentDigest, contextDigest: proof.references.contextDigest },
    evidence: 'recorded-not-replayed' };
}

function sourceReferences(input: TaskContextInput) {
  const problem = input.problem;
  if (!present(problem.baseCommit)) return missing('frozen-source-commit');
  if (!problem.declarations || !Array.isArray(problem.ownedFiles)) return missing('frozen-declarations');
  for (const file of problem.ownedFiles.filter(file => file.endsWith('.lean')))
    if (typeof input.frozenContexts?.[file] !== 'string') return missing(`frozen-context:${file}`);
  return { baseCommit: problem.baseCommit,
    retrieval: 'Read full proofs and namespace/section/instance context with git show COMMIT:PATH in this isolated worktree. Source references identify immutable content; they grant no proof acceptance.',
    files: problem.ownedFiles.filter(file => file.endsWith('.lean')).map(file => ({
      commit: problem.baseCommit, path: sourcePath(problem, file),
      contextDigest: problem.sourceStructure?.[file], imports: problem.sourceImports?.[file],
      declarations: problem.declarations[file] ?? [], context: input.frozenContexts![file] })),
    trustedFiles: Object.entries(problem.trustedFiles ?? {}).map(([file, digest]) =>
      ({ commit: problem.baseCommit, path: sourcePath(problem, file), digest })) };
}

function proofSources(problem: SolverProblem, node: TaskRecord) {
  const proof = node.integratedCheck ?? node.proof;
  return proof && { path: node.task.proofPath && sourcePath(problem, node.task.proofPath), evidenceFrom: 'evidence' };
}

function deliveryMatchesFinding(record: DeliveryRecord, node?: TaskRecord): boolean {
  if (record.kind !== 'research' || !node || !present(node.finding)) return false;
  return record.findingDigest === undefined ? record.summary === node.finding : record.findingDigest === mathDigest(node.finding);
}

/** 0 for the active task, 1 for its required closure, 2 for its group, 3 otherwise. */
const scopeRank = (active: TaskRecord['task'] | undefined, required: ReadonlySet<string>) => (taskId?: string, groupId?: string) =>
  active && taskId === active.id ? 0 : required.has(taskId ?? '') ? 1 : active && groupId === taskGroup(active) ? 2 : 3;

function optionalDeliveries(input: TaskContextInput, required: ReadonlySet<string>,
  byId: ReadonlyMap<string, TaskRecord>, omitted: ContextManifest['omitted'][number][]) {
  const action = input.action, active = action?.kind === 'task' ? action.task : undefined;
  const rank = scopeRank(active, required), priority = (record: DeliveryRecord) => rank(record.taskId, record.groupId);
  const seen = new Set<string>(), selected: DeliveryRecord[] = [];
  const findingSources = new Map<string, { deliveryId: string; commit: string; notesPath: 'RESEARCH.md'; sourceDigest?: string }>();
  for (const record of [...(input.cooperation?.deliveries ?? [])].reverse().sort((a, b) => priority(a) - priority(b))) {
    const id = `delivery:${record.id}`, current = record.taskId ? byId.get(record.taskId) : undefined;
    let reason: ContextOmissionReason | undefined;
    if (record.status === 'superseded') reason = 'superseded';
    else if ((current && record.taskDigest !== taskVersion(current.task)) || record.dependencies?.some(dependency =>
      byId.has(dependency.taskId) && taskVersion(byId.get(dependency.taskId)!.task) !== dependency.taskDigest)) reason = 'stale-version';
    if (!reason && current && deliveryMatchesFinding(record, current) && record.commit &&
        !findingSources.has(current.task.id)) findingSources.set(current.task.id, {
      deliveryId: record.id, commit: record.commit, notesPath: 'RESEARCH.md', sourceDigest: record.sourceDigest,
    });
    const key = json([record.taskId ?? record.id, record.taskDigest, record.kind, record.producer, record.findingDigest]);
    if (!reason && seen.has(key)) reason = 'duplicate';
    if (!reason && selected.length >= 8) reason = 'selection-limit';
    if (reason) { omitted.push({ id, kind: 'delivery', reason }); continue; }
    seen.add(key); selected.push(record);
  }
  const sections = selected.flatMap(record => {
    // Interfaces and receipts live in mandatory sections. A delivery summary is advisory prose.
    const current = record.taskId ? byId.get(record.taskId) : undefined;
    // Keep a shared mathematical finding independently selectable from its delivery metadata.
    const sharedFinding = deliveryMatchesFinding(record, current);
    const ownFinding = sharedFinding ? undefined : deliveryFinding(record);
    const findingId = sharedFinding ? `finding:${record.taskId}` : ownFinding ? `finding:delivery:${record.id}` : undefined;
    if (record.actualReferences || record.artifacts?.artifacts.some(artifact => artifact.declarations.length))
      omitted.push({ id: `delivery:${record.id}:details`, kind: 'delivery', reason: 'advisory-details-by-reference' });
    const visible = {
      id: record.id, submissionId: record.submissionId, statementReviewId: record.statementReviewId,
      producer: record.producer, taskId: record.taskId, taskDigest: record.taskDigest, groupId: record.groupId,
      kind: record.kind, status: record.status, statement: record.statement, premises: record.premises, findingDigest: record.findingDigest,
      dependencies: record.dependencies, remainingObligations: record.remainingObligations,
      evidenceRefs: record.evidenceRefs, createdAt: record.createdAt, commit: record.commit, sourceDigest: record.sourceDigest,
      savedSource: record.commit && { commit: record.commit, notesPath: 'RESEARCH.md',
        proofPath: current && current.task.proofPath && sourcePath(input.problem, current.task.proofPath) },
      actualReferenceSource: record.actualReferences && { sourceCommit: record.actualReferences.sourceCommit,
        root: record.actualReferences.root, environmentDigest: record.actualReferences.environmentDigest,
        contextDigest: record.actualReferences.contextDigest, tasks: record.actualReferences.tasks },
      artifacts: record.artifacts && { ...record.artifacts, artifacts: record.artifacts.artifacts.map(artifact => ({
        ...artifact, declarations: artifact.declarations.map(({ name, sha256, draft }) => ({ name, sha256, draft })),
      })) },
      artifactWarning: record.artifactWarning, lemmaRequests: record.lemmaRequests,
    };
    return [{ ...section(`delivery:${record.id}`, 'delivery', 'Current-version delivery selected for this task (advisory; retain unproved obligations):',
      { ...visible, ...(findingId ? { summarySource: findingId } : { summary: record.summary }) }),
      priority: priority(record) * 10 + 2 }, ...(ownFinding ? [{ ...section(findingId!, 'finding', 'Immutable advisory research publication:', {
        taskId: record.taskId, taskDigest: record.taskDigest, finding: ownFinding, findingDigest: record.findingDigest,
        savedSource: { commit: record.commit, notesPath: 'RESEARCH.md' },
      }), priority: priority(record) * 10 + 1 }] : [])];
  });
  return { sections, findingSources };
}

/** Unshown queue items counted per source task, in first-seen order. */
function backlogSources(items: readonly { id: string; sourceTaskId: string; sourceTaskDigest: string }[], shown: ReadonlySet<string>) {
  const sources = new Map<string, { taskId: string; taskDigest: string; remaining: number }>();
  for (const item of items) if (!shown.has(item.id)) {
    const source = sources.get(item.sourceTaskId) ?? { taskId: item.sourceTaskId, taskDigest: item.sourceTaskDigest, remaining: 0 };
    source.remaining++; sources.set(item.sourceTaskId, source);
  }
  return [...sources.values()];
}

/** Compile a task's mathematical interface before dispatch. A budget can omit hints, never hypotheses. */
export function compileTaskContext(input: TaskContextInput): { message: string; manifest: ContextManifest } {
  const { problem, action } = input;
  const maxBytes = input.maxContextBytes ?? DEFAULT_TASK_CONTEXT_BYTES;
  const maxOptionalBytes = input.maxOptionalContextBytes ?? DEFAULT_OPTIONAL_TASK_CONTEXT_BYTES;
  if (!Number.isSafeInteger(maxBytes) || maxBytes <= 0) throw new TaskContextError('math_context_invalid_budget', 'maxContextBytes');
  if (!Number.isSafeInteger(maxOptionalBytes) || maxOptionalBytes < 0)
    throw new TaskContextError('math_context_invalid_budget', 'maxOptionalContextBytes');
  if (!present(problem.receiptDigest) || !present(problem.contract?.formalStatement) || !Array.isArray(problem.contract?.assumptions))
    return missing('frozen-problem');
  const omitted: ContextManifest['omitted'][number][] = [];
  const { tasks, deferred, byId, required, route: selectedRoute } = requiredTasks(input, omitted);
  const consumers = action?.kind === 'task' ? contextTaskConsumers(action.task, input.cooperation?.tasks ?? [], input.cooperation) : [];
  const consumerIds = new Set(consumers.map(consumer => consumer.task.id));
  if (consumerIds.size !== consumers.length) return missing('duplicate-consumer-id');
  for (const consumer of consumers) {
    const current = byId.get(consumer.task.id);
    if (consumer.taskDigest !== taskVersion(consumer.task) || (current && taskVersion(current.task) !== consumer.taskDigest))
      return stale(`consumer:${consumer.task.id}`);
    if (['lemma', 'goal'].includes(consumer.task.kind) && !present(frozenHeader(problem, consumer)))
      return missing(`interface:${consumer.task.id}`);
  }
  const references = evidenceReferenceDictionary();
  const graph = tasks.map(node => ({ ...leadTaskInterface(node, action, omitted), taskDigest: taskVersion(node.task),
    status: node.status, attempts: node.attempts, groupId: taskGroup(node.task), producer: node.assignment?.workerId,
    sharing: node.task.sharing ?? 'problem',
    integratedCommit: node.integratedCheck ? null : undefined, checkedSourceDigest: node.integratedCheck ? null : undefined,
    ...(node.task.kind === 'goal' ? { exactFrozenHeader: frozenHeader(problem, node) } : {}),
    evidence: references.encode(sharedEvidence(evidence(node, input.environmentDigest))), source: proofSources(problem, node) }));
  const mandatory: ContextSection[] = [
    section('original-problem', 'problem', `${input.taskText}\n\nOriginal problem:`, problem.contract.formalStatement),
    section('original-assumptions', 'problem', 'Frozen assumptions and problem identity:', { problemReceiptDigest: problem.receiptDigest,
      statementHash: problem.contract.statementHash, leanStatementHash: problem.contract.leanStatementHash,
      informalStatement: problem.contract.informalStatement, assumptions: problem.contract.assumptions }),
    section('frozen-sources', 'sources', 'Frozen source context and immutable retrieval references:', sourceReferences(input)),
  ];
  if (action) mandatory.push(section('assignment', 'assignment', 'Cooperative assignment:', action));
  if (consumers.length) mandatory.push(section('consumer-interfaces', 'interfaces',
    'Planned consumer interfaces (read-only mathematical purpose; not premises, proof evidence or permission to edit consumers):',
    consumers.map(consumer => ({ ...consumer.task, taskDigest: consumer.taskDigest, status: consumer.status, uses: consumer.uses,
      ...(consumer.task.kind === 'goal' ? { exactFrozenHeader: frozenHeader(problem, consumer) } : {}) }))));
  if (input.feedback) mandatory.push(section('current-feedback', 'feedback',
    'Current host feedback (preserve the frozen original problem):', input.feedback));
  const assigned = action?.kind === 'task' ? byId.get(action.task.id) : undefined;
  if (assigned?.feedback) mandatory.push(section(`feedback:${assigned.task.id}`, 'feedback',
    `Host feedback for ${assigned.task.id}:`, assigned.feedback));
  if (selectedRoute) mandatory.push(section(`route:${selectedRoute.id}`, 'routes', 'Selected alternative route and exact closing obligation (planned, not accepted):', selectedRoute));
  if (input.cooperation) {
    if (input.cooperation.mathematicalGaps?.length) mandatory.push(section('mathematical-gaps', 'finding',
      'Persistent mathematical gaps (advisory; historical-scope reports require review of changed inputs; complete records remain in COOPERATION.json):',
      mathematicalGapContext(input.cooperation.mathematicalGaps)));
    if (action?.kind === 'lead') {
      if (action.stagnationRecovery) mandatory.push(section('stagnation-recovery', 'assignment',
        'Host stagnation recovery request (advisory scheduling evidence; not proof failure or acceptance):',
        action.stagnationRecovery));
      const challenges = pendingResearchChallenges(input.cooperation);
      const challengeContextOptions = action.coordination ? { maxFindingBytes: COORDINATION_INLINE_FINDING_BYTES } : {};
      const challengeIds = new Set(action.challengeIds ?? selectResearchChallengeBatch(input.cooperation, challengeContextOptions).map(item => item.id));
      const shownChallenges = challenges.filter(item => challengeIds.has(item.id));
      if (shownChallenges.length) mandatory.push(section('research-challenges', 'assignment',
        'Research challenges requiring a route decision (advisory, not proof acceptance):',
        shownChallenges.map(item => researchChallengeContext(item, challengeContextOptions))));
      if (challenges.length > shownChallenges.length) mandatory.push(section('research-challenge-backlog', 'assignment',
        'Queued challenges for later dispatches; preserve their source tasks and inputs. Full records are in COOPERATION.json researchChallenges:', {
          pending: challenges.length, shown: shownChallenges.length, remaining: challenges.length - shownChallenges.length,
          sources: backlogSources(challenges, challengeIds),
        }));
      const pending = pendingResearchHandoffs(input.cooperation);
      const aliases = new Map(pending.flatMap(item => item.sources.map(source => [source.handoffId, item.id] as const)));
      const shown = new Set((action.handoffIds ?? selectResearchHandoffBatch(input.cooperation).map(item => item.id))
        .map(id => aliases.get(id) ?? id));
      const handoffs = pending.filter(item => shown.has(item.id));
      if (handoffs.length) mandatory.push(section('research-handoffs', 'assignment',
        'Pending research proposals requiring a Lead decision (advisory; not checked lemmas). Duplicate provenance is in ' +
        'COOPERATION.json researchHandoffs: match sourceSet.reference.handoffId and contextDigest, then verify ' +
        'sourceSet.digest against SHA-256 of canonical JSON of sources before using the full source list. ' +
        'A missing or mismatched source list is unavailable and grants no proof acceptance:', handoffs.map(researchHandoffContext)));
      if (pending.length > handoffs.length) mandatory.push(section('research-handoff-backlog', 'assignment',
        'Queued research proposals (not required in this response; preserve their sources and prerequisites for subsequent batches):', {
          pending: pending.length, shown: handoffs.length, remaining: pending.length - handoffs.length, sources: backlogSources(pending, shown),
        }));
    }
    mandatory.push(section('task-interfaces', 'interfaces', 'Lead task graph and host feedback:', graph));
    if (graph.some(node => 'objectiveDigest' in node)) mandatory.push(section('task-objective-reference-encoding', 'sources',
      'Finished task objective references (advisory prose by reference; exact interfaces remain mandatory):', {
        encoding: 'finished-task-objectives-v1',
        retrieval: 'Retrieve omitted finished objectives from worktree-root COOPERATION.json peers by id. Require peer.taskDigest = row.taskDigest ' +
          'and UTF-8 SHA-256(peer.objective) = row.objectiveDigest. Missing or mismatched descriptions are unavailable. ' +
          'This live file is not an immutable proof source and grants no proof acceptance. Exact Lean types, premises, dependencies, ' +
          'unresolved conditions and evidence stay inline; completed research/sketch tasks remain advisory.',
      }));
    if (deferred.length) mandatory.push(section('checked-helper-catalog', 'sources',
      'Checked helpers outside the current open-task closure (retrieve before using; recorded, not replayed):', {
        retrieval: 'Each source commit/path identifies the complete immutable Lean declaration and proof. Read it with git show COMMIT:PATH. ' +
          'The exact original goals, all unfinished task descriptions and interfaces, and unresolved conditions remain in the task graph. ' +
          'Only freshly checked unconditional helpers are encapsulated here; this catalog grants no proof acceptance. ' +
          'Their earlier objective is advisory planning material, not their Lean interface. Its UTF-8 SHA-256 is objectiveDigest. ' +
          'A current description may be read from COOPERATION.json peers by id only if its taskDigest matches this row and its objective hash matches objectiveDigest; ' +
          'that live file is not an immutable proof source. A missing or mismatched description is unavailable, never a new mathematical premise.',
        helpers: deferred.map(node => checkedHelperReference(input, node)),
      }));
    if (action?.kind === 'lead') {
      const continuation = buildProofContinuation(action.coordination ? input.cooperation.tasks : tasks, { groups: input.cooperation.groups,
        environmentDigest: input.environmentDigest, proofRoutes: input.cooperation.proofRoutes });
      const goals = continuation.goals.filter(goal => goal.status !== 'integrated' || goal.recordedProof !== 'checked');
      const frontierIds = new Set(goals.flatMap(goal => goal.frontier));
      const relevant = new Set<string>();
      const visit = (id: string) => {
        if (relevant.has(id) || !required.has(id)) return;
        relevant.add(id); byId.get(id)!.task.dependsOn.forEach(visit);
        for (const route of input.cooperation!.proofRoutes ?? byId.get(id)!.alternativeRoutes ?? [])
          if (route.targetTaskId === id) [...route.prerequisiteTaskIds, route.closingTaskId].forEach(visit);
      };
      goals.forEach(goal => visit(goal.taskId));
      if (goals.length) mandatory.push(section('original-goal-frontier', 'continuation',
        'Unfinished original goals and their current frontier (recorded, not proof acceptance):', {
          goals: goals.map(({ taskId, frontier, missingDependencies, alternatives }) => ({ taskId, frontier, missingDependencies, alternatives })),
          frontier: continuation.frontier.filter(item => frontierIds.has(item.taskId)).map(item => ({ ...item,
            feedback: byId.get(item.taskId)?.feedback })),
          blockers: (input.cooperation.blockers ?? []).filter(blocker => relevant.has(blocker.taskId) &&
            blocker.status !== 'superseded' && blocker.taskDigest === taskVersion(byId.get(blocker.taskId)!.task))
            .map(({ id, taskId, routeId, status, mechanism, scope, evidenceStatus, reopenOn }) =>
              ({ id, taskId, routeId, status, mechanism, scope, evidenceStatus, reopenOn })),
        }));
    }
    if (action?.kind === 'lead' && input.cooperation.error) mandatory.push(section('plan-rejection', 'feedback',
      'Host rejected the proposed plan. Repair this error while preserving every exact original target:', {
        error: input.cooperation.error, rejection: input.cooperation.planRejection,
        originalTargets: problem.targets.map(({ proofPath, theoremName }) => ({ proofPath, theoremName })),
      }));
    const visibleGroups = new Set(tasks.map(node => taskGroup(node.task)));
    mandatory.push(section('groups', 'groups', 'Route groups and budgets:',
      input.cooperation.groups?.filter(route => action?.kind !== 'task' || visibleGroups.has(route.group.id)) ?? []));
    if (references.entries.length || references.digests.length) mandatory.push(section('evidence-reference-dictionary', 'sources',
      'Complete evidence reference dictionary (mandatory, recorded-not-replayed):', {
        encoding: 'evidence-reference-indices-v3', projectRelative: problem.projectRelative.replaceAll('\\', '/'),
        expansion: 'Each numeric element in a task evidence.references.inputs, proof, statement or tasks array indexes entries below. ' +
          'Expand every index in its original array order. A task source.inputsFrom names its evidence.references.inputs; ' +
          'each expanded input retains all fields and uses that task evidence.references.sourceCommit as commit and path.posix.join(projectRelative, input.file) as path. ' +
          'Source commits, verifier target commits and evidence remain distinct. Indexing grants no proof acceptance.',
        entries: references.entries,
        digestExpansion: 'Each numeric task evidence.references.environmentDigest or contextDigest indexes digests below. ' +
          'Replace that number with the exact original digest string. Digest sharing changes representation only; ' +
          'retain each source commit, verifier target commit, condition and reference inventory separately.',
        digests: references.digests,
      }));
    if (graph.some(node => node.source)) mandatory.push(section('proof-source-reference-encoding', 'sources',
      'Complete proof source reference encoding (mandatory, recorded-not-replayed):', {
        encoding: 'proof-source-evidence-v2',
        expansion: 'A task row.source with evidenceFrom="evidence" expands to {commit: row.evidence.commit, path: row.source.path, ' +
          'sourceDigest: row.evidence.sourceDigest}. If row.evidence.references exists, add inputsFrom="evidence.references.inputs"; ' +
          'otherwise omit inputsFrom. Preserve the actual source path and all values exactly. The source commit is row.evidence.commit, ' +
          'distinct from row.evidence.verification.targetCommit and row.evidence.references.sourceCommit. ' +
          'This encoding shares metadata only and grants no proof acceptance.',
        fieldExpansion: 'A null row.evidence.taskDigest expands to row.taskDigest. A null row.integratedCommit expands to row.evidence.commit; ' +
          'a null row.checkedSourceDigest expands to row.evidence.sourceDigest. A null receipt.targetCommit expands to its enclosing ' +
          'row.evidence.verification.targetCommit. Only null has this meaning; absent fields remain absent, and every distinct explicit value is retained.',
      }));
  }
  mandatory.push(section('declaration-order', 'sources', 'Frozen declaration order by file:', Object.fromEntries(
    Object.entries(problem.declarations).map(([file, declarations]) => [file, declarations.map(declaration => declaration.name)]))),
  section('original-targets', 'problem', 'Original targets:', problem.targets));
  mandatory.push(...(input.mandatory ?? []));
  const { sections: deliveries, findingSources } = optionalDeliveries(input, required, byId, omitted);
  const active = action?.kind === 'task' ? action.task : undefined;
  const checkpoint = active && input.cooperation?.researchCheckpoints?.[active.id];
  if (active && checkpoint?.taskDigest === taskVersion(active) && checkpoint.unchangedEvidenceCount !== undefined)
    mandatory.push(section('checkpoint-evidence', 'checkpoint', 'Host checkpoint observations (advisory, no solving deadline):', {
      taskId: active.id, savedCheckpointCountWithoutCandidateChange: checkpoint.unchangedEvidenceCount,
      candidateStatus: checkpoint.candidateStatus,
      interpretation: 'Notes and drafts remain saved. Candidate identity covers retained code and structured references or proposals; ' +
        'unclassified prose can contain useful mathematics and has not been assessed. A changed file is not proof progress. ' +
        'Use the saved argument and identify a concrete new check, missing input or consumer application before repeating an attempt. ' +
        'This observation neither accepts a theorem nor stops continued reasoning.',
    }));
  const seenAttempts = new Set<string>();
  const repeatedAttempts = active ? (input.cooperation?.failedTaskInputs ?? []).toReversed().filter(record => {
    if (record.taskId !== active.id || record.taskDigest !== taskVersion(active) || !record.relatedFailureIds?.length ||
        !record.attemptFingerprint || seenAttempts.has(record.attemptFingerprint)) return false;
    seenAttempts.add(record.attemptFingerprint); return true;
  }) : [];
  const attemptHint = (record: typeof repeatedAttempts[number]) => ({ failureId: record.id,
      attemptFingerprint: record.attemptFingerprint, relatedFailureIds: record.relatedFailureIds,
      interpretation: 'The saved target text and local mathematical inputs match an earlier failure. Full source or declaration placement changed, ' +
        'so this is a search hint, not mathematical equivalence or permission to reuse a verification result.' });
  if (repeatedAttempts.length) mandatory.push(section('repeated-attempts', 'feedback',
    'Latest related failed attempt (advisory; full-source checks remain independent). Older search hints use the optional budget:',
    { relatedAttemptFingerprints: repeatedAttempts.length, latest: attemptHint(repeatedAttempts[0]) }));
  const rank = scopeRank(active, required);
  const optional: ContextSection[] = [];
  if (repeatedAttempts.length > 1) optional.push({ ...section('repeated-attempt-history', 'feedback',
    'Earlier related failed attempts (advisory; not permission to reuse verification):',
    repeatedAttempts.slice(1).map(attemptHint)), priority: 0 });
  for (const blocker of [...(input.cooperation?.blockers ?? [])].sort((a, b) => rank(a.taskId, a.groupId) - rank(b.taskId, b.groupId))) {
    const id = `blocker:${blocker.id}`;
    if (!byId.has(blocker.taskId) || (active && blocker.groupId !== taskGroup(active) && !required.has(blocker.taskId))) {
      omitted.push({ id, kind: 'blocker', reason: 'outside-task-scope' }); continue;
    }
    if (blocker.status === 'superseded' || blocker.taskDigest !== taskVersion(byId.get(blocker.taskId)!.task)) {
      omitted.push({ id, kind: 'blocker', reason: blocker.status === 'superseded' ? 'superseded' : 'stale-version' }); continue;
    }
    // The complete recurrence basis can contain private prerequisite identities; the public interface does not need it.
    const { basis: _basis, ...publicBlocker } = blocker;
    optional.push({ ...section(id, 'blocker', 'Local route blocker and reopening conditions (advisory):', publicBlocker), priority: rank(blocker.taskId, blocker.groupId) * 10 + 1 });
  }
  optional.push(...deliveries);
  for (const node of [...(input.cooperation?.tasks ?? [])].sort((a, b) =>
    rank(a.task.id, taskGroup(a.task)) - rank(b.task.id, taskGroup(b.task)))) {
    const priority = rank(node.task.id, taskGroup(node.task)) * 10;
    if (node.feedback && node.task.id !== active?.id) optional.push({ ...section(`feedback:${node.task.id}`, 'feedback', `Host feedback for ${node.task.id}:`, node.feedback), priority: priority + 3 });
    if (present(node.finding)) optional.push({ ...section(`finding:${node.task.id}`, 'finding', `Advisory finding for ${node.task.id}:`, {
      taskId: node.task.id, taskDigest: taskVersion(node.task), finding: node.finding,
      savedSource: findingSources.get(node.task.id),
    }), priority: priority + 1 });
    if (!required.has(node.task.id) && !consumerIds.has(node.task.id)) optional.push({ ...section(`interface:${node.task.id}`, 'interfaces', 'Other visible task (advisory planning context):',
      { ...node.task, taskDigest: taskVersion(node.task), status: node.status }), priority: priority + 8 });
  }
  for (const route of input.cooperation?.proofRoutes ?? []) {
    if (route.id === selectedRoute?.id) continue;
    if ([route.targetTaskId, route.closingTaskId, ...route.prerequisiteTaskIds].every(id => byId.has(id)))
      optional.push(section(`route:${route.id}`, 'routes', 'Alternative route and closing obligation (planned, not accepted):', route));
    else omitted.push({ id: `route:${route.id}`, kind: 'routes', reason: 'outside-task-scope' });
  }
  for (const [index, entry] of [...(input.cooperation?.history ?? [])].reverse().entries()) {
    const id = `history:${entry.task.id}:${taskVersion(entry.task)}:${index}`;
    if (active && !required.has(entry.task.id) && taskGroup(entry.task) !== taskGroup(active)) {
      omitted.push({ id, kind: 'history', reason: 'outside-task-scope' }); continue;
    }
    const proof = entry.integratedCheck ?? entry.proof;
    optional.push({ ...section(id, 'history', 'Earlier route finding (historical and advisory; not a current premise):', {
      taskId: entry.task.id, taskDigest: taskVersion(entry.task), objective: entry.task.objective,
      producer: entry.producer, finding: entry.finding, commit: proof?.commit, sourceDigest: proof?.sourceDigest,
      evidenceRefs: proof?.verification.results.map(result => result.receiptId),
      source: proof && entry.task.proofPath ? { commit: proof.commit, path: sourcePath(problem, entry.task.proofPath) } : undefined,
      evidence: 'historical-not-current' }), priority: rank(entry.task.id, taskGroup(entry.task)) * 10 + 5 });
  }
  if (input.checkpoint) {
    mandatory.push(section('checkpoint-source', 'sources', 'Complete current research checkpoint source (advisory, not proof acceptance):', {
      path: 'RESEARCH.md', bytes: Buffer.byteLength(input.checkpoint), digest: mathDigest(input.checkpoint),
      retrieval: 'If the checkpoint section is omitted for budget, read worktree-root RESEARCH.md before continuing the argument. ' +
        'Require the recorded byte length and UTF-8 SHA-256 to match; otherwise report that the saved checkpoint is unavailable. Resume from its attempted methods, exact results and evidence locations, scoped negative searches, and precise unresolved next inference; retain these before the next checkpoint or context rotation. Recheck claims in Lean and reopen a negatively searched scope only with a relevant changed input or genuinely different mathematical method.',
    }));
    optional.push({ ...section('checkpoint', 'checkpoint', 'Current research checkpoint (advisory; recheck claims in Lean):', input.checkpoint), priority: 5 });
  }
  optional.push(...(input.optional ?? []));
  return compileSections(input.instructions, mandatory, optional.sort((a, b) => (a.priority ?? 20) - (b.priority ?? 20)),
    omitted, [...required], maxBytes, maxOptionalBytes);
}

function compileSections(instructions: string, mandatory: readonly ContextSection[], optional: readonly ContextSection[],
  initialOmissions: ContextManifest['omitted'][number][], requiredTaskIds: readonly string[], maxBytes: number, maxOptionalBytes: number) {
  const selected: ContextSection[] = [];
  const omissionReasons = new Map<string, ContextOmissionReason>();
  const optionalBytes = (items: readonly ContextSection[]) => items.reduce((total, item) => total + Buffer.byteLength(item.text) + 2, 0);
  const render = (selected: readonly ContextSection[], mandatoryBytes?: number) => {
    const included = [...mandatory.map(item => ({ ...item, required: true })), ...selected.map(item => ({ ...item, required: false }))];
    const content = included.map(item => item.text).join('\n\n');
    const includedIds = new Set(selected.map(item => item.id));
    const manifest: { -readonly [K in keyof ContextManifest]: ContextManifest[K] } = {
      schema: 'theorem-os.task-context.v1', evidence: 'recorded-not-replayed', maxBytes, usedBytes: 0, mandatoryBytes: mandatoryBytes ?? 0,
      maxOptionalBytes, optionalBytes: optionalBytes(selected),
      contentDigest: mathDigest(json({ instructions, message: content })), requiredTaskIds,
      included: included.map(item => ({ id: item.id, kind: item.kind, required: item.required, bytes: Buffer.byteLength(item.text) })),
      omitted: [...initialOmissions, ...optional.filter(item => !includedIds.has(item.id))
        .map(item => ({ id: item.id, kind: item.kind, reason: omissionReasons.get(item.id) ?? 'budget' as const }))],
    };
    const omissionPreview = manifest.omitted.length <= 16 ? undefined : {
      omitted: manifest.omitted.slice(0, 16),
      omissionSet: { selection: 'bounded-preview', count: manifest.omitted.length,
        digest: mathDigest(canonicalMathJson(manifest.omitted)),
        reference: { path: 'CONTEXT-MANIFEST.json', field: 'omitted' },
        retrieval: 'Read the full manifest file; require matching contentDigest, omitted count and canonical JSON SHA-256. ' +
          'Inline omissions are a preview.' } };
    let message: string;
    do {
      // Large audit inventories already live in the durable worker manifest. Keep the
      // byte accounting and omission preview inline without repeating section metadata.
      const { included: _included, requiredTaskIds: _requiredTaskIds, ...summary } = manifest;
      const inlineManifest = omissionPreview ? { ...summary, manifestRef: 'CONTEXT-MANIFEST.json', ...omissionPreview } : manifest;
      message = content + '\n\nContext compilation manifest:\n' + json(inlineManifest);
      const usedBytes = Buffer.byteLength(instructions) + Buffer.byteLength(message);
      if (usedBytes === manifest.usedBytes) break;
      manifest.usedBytes = usedBytes;
      if (mandatoryBytes === undefined) manifest.mandatoryBytes = usedBytes;
    } while (true);
    return { message, manifest };
  };
  const mandatoryResult = () => {
    const result = render([]);
    if (result.manifest.usedBytes > maxBytes)
      throw new TaskContextError('math_context_mandatory_overflow', `${result.manifest.usedBytes}>${maxBytes}`);
    return result;
  };
  let mandatoryBytes = mandatoryResult().manifest.usedBytes;
  for (const item of optional) {
    const candidate = render([...selected, item], mandatoryBytes);
    if (candidate.manifest.usedBytes > maxBytes) omissionReasons.set(item.id, 'budget');
    else if (candidate.manifest.optionalBytes > maxOptionalBytes) omissionReasons.set(item.id, 'optional-budget');
    else selected.push(item);
  }
  // Final omission reasons can enlarge the manifest; retain the hard byte boundary after recording them.
  mandatoryBytes = mandatoryResult().manifest.usedBytes;
  let result = render(selected, mandatoryBytes);
  while (result.manifest.usedBytes > maxBytes && selected.length) {
    omissionReasons.set(selected.pop()!.id, 'budget');
    mandatoryBytes = mandatoryResult().manifest.usedBytes;
    result = render(selected, mandatoryBytes);
  }
  return result;
}
