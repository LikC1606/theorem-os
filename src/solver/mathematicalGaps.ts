import { z } from 'zod';
import { canonicalMathJson, mathDigest } from '../math/mathRuntimeIo';
import type { DeliveryRecord } from './deliveries';
import { plannedTaskDependencyIds } from './modules/search';
import { taskGroup, taskReferenceDependencies, taskVersion, type CooperativeTask, type TaskRecord } from './tasks';

const text = z.string().trim().min(1).max(12000);
/** A mathematical report, never an inferred equivalence, difficulty score or acceptance. */
export const mathematicalGapSchema = z.object({
  consumer: z.object({ taskId: z.string().min(1), taskDigest: z.string().regex(/^[a-f0-9]{64}$/u) }).strict(),
  previousDeliveryId: z.string().min(1).optional(),
  previousGap: text, reduced: text, remaining: text, evidenceScope: text,
  reconsiderWhen: z.array(text).max(32),
}).strict();
export type MathematicalGap = z.infer<typeof mathematicalGapSchema>;
export type MathematicalGapScope = Readonly<{
  problemReceiptDigest: string; environmentDigest: string;
  source: CooperativeTask; consumer: CooperativeTask;
  dependencies: DeliveryRecord['dependencies'];
}>;
type GapState = { tasks: readonly TaskRecord[]; deliveries?: readonly DeliveryRecord[] };

/** A public source does not publish a private consumer's contract or its earlier scope. */
export function mathematicalGapVisible(delivery: DeliveryRecord, state: GapState, viewer?: CooperativeTask): boolean {
  if (!delivery.mathematicalGap && !delivery.mathematicalGapScope) return true;
  const scope = delivery.mathematicalGapScope;
  if (!scope || !delivery.mathematicalGap) return false;
  const visible = (task: CooperativeTask) => !viewer || taskGroup(task) === taskGroup(viewer) || task.sharing !== 'group';
  return [scope.source, scope.consumer].every(task => visible(task) &&
    state.tasks.filter(node => node.task.id === task.id).every(node => visible(node.task)));
}

export function bindMathematicalGap(gap: MathematicalGap, source: CooperativeTask, state: GapState,
  identity: { problemReceiptDigest: string; environmentDigest: string }): MathematicalGapScope {
  const consumer = state.tasks.find(node => node.task.kind === 'goal' && node.task.id === gap.consumer.taskId &&
    taskVersion(node.task) === gap.consumer.taskDigest)?.task;
  if (!consumer || taskGroup(source) !== taskGroup(consumer) && consumer.sharing === 'group')
    throw new Error('math_delivery_invalid:gap_consumer');
  if (gap.previousDeliveryId) {
    const prior = state.deliveries?.find(item => item.id === gap.previousDeliveryId);
    if (!prior?.mathematicalGapScope || prior.mathematicalGapScope.consumer.id !== consumer.id ||
        prior.mathematicalGapScope.problemReceiptDigest !== identity.problemReceiptDigest ||
        !mathematicalGapVisible(prior, state, source))
      throw new Error('math_delivery_invalid:gap_previous');
  }
  const nodes = new Map(state.tasks.map(node => [node.task.id, node]));
  const ids = (node: TaskRecord) => taskReferenceDependencies(node)?.map(reference => reference.taskId) ??
    plannedTaskDependencyIds(node, state.tasks);
  const sourceNode = nodes.get(source.id), visited = new Set([source.id]);
  const pending = [...(sourceNode?.task === source ? ids(sourceNode) : source.dependsOn)].reverse();
  const dependencies: DeliveryRecord['dependencies'] = [];
  while (pending.length) {
    const id = pending.pop()!;
    if (visited.has(id)) continue;
    visited.add(id);
    const input = nodes.get(id);
    if (!input) throw new Error('math_delivery_invalid:gap_dependency');
    dependencies.push({ taskId: id, taskDigest: taskVersion(input.task) });
    pending.push(...[...ids(input)].reverse());
  }
  return { ...identity, source: structuredClone(source), consumer: structuredClone(consumer), dependencies };
}

/** Retain immutable evidence across revisions; changed inputs make it history, never a current result. */
export function mathematicalGaps(state: GapState, identity: { problemReceiptDigest: string; environmentDigest: string },
  viewer?: CooperativeTask) {
  const nodes = new Map(state.tasks.map(node => [node.task.id, node.task]));
  return (state.deliveries ?? []).flatMap(delivery => {
    const gap = delivery.mathematicalGap, scope = delivery.mathematicalGapScope;
    if (!gap || !scope || !mathematicalGapVisible(delivery, state, viewer) ||
        scope.problemReceiptDigest !== identity.problemReceiptDigest ||
        delivery.taskDigest !== taskVersion(scope.source) || gap.consumer.taskDigest !== taskVersion(scope.consumer)) return [];
    const current = scope.environmentDigest === identity.environmentDigest && delivery.status !== 'superseded' &&
      [scope.source, scope.consumer].every(task => nodes.has(task.id) && taskVersion(nodes.get(task.id)!) === taskVersion(task)) &&
      scope.dependencies.every(input => nodes.has(input.taskId) && taskVersion(nodes.get(input.taskId)!) === input.taskDigest);
    return [{ deliveryId: delivery.id, ...gap, scope, scopeStatus: current ? 'current-contracts' as const : 'historical-scope' as const,
      evidence: 'model-reported-advisory' as const, evidenceRefs: delivery.evidenceRefs,
      findingDigest: delivery.findingDigest, commit: delivery.commit, createdAt: delivery.createdAt }];
  });
}

export const MATHEMATICAL_GAP_ENTRY_MAX_BYTES = 8 * 1024;
export const MATHEMATICAL_GAP_CONTEXT_MAX_BYTES = 32 * 1024;
const jsonBytes = (value: unknown) => Buffer.byteLength(JSON.stringify(value));
function preview(value: string, maxBytes: number) {
  if (jsonBytes(value) <= maxBytes) return value;
  let lower = 0, upper = Math.min(value.length, maxBytes), end = 0;
  while (lower <= upper) {
    const middle = Math.floor((lower + upper) / 2);
    if (jsonBytes(value.slice(0, middle)) <= maxBytes) { end = middle; lower = middle + 1; }
    else upper = middle - 1;
  }
  if (end && /[\uD800-\uDBFF]/u.test(value[end - 1]!)) end--;
  return { preview: value.slice(0, end), complete: false as const, bytes: Buffer.byteLength(value),
    sha256: mathDigest(value) };
}
function gapEntry(item: ReturnType<typeof mathematicalGaps>[number], textBytes: number) {
  const { scope } = item;
  const descriptions = { previousGap: preview(item.previousGap, textBytes), reduced: preview(item.reduced, textBytes),
    remaining: preview(item.remaining, textBytes), evidenceScope: preview(item.evidenceScope, textBytes) };
  const reconsiderWhen = item.reconsiderWhen.slice(0, 4).map(value => preview(value, 256));
  const evidenceRefs = item.evidenceRefs.slice(0, 4).map(value => preview(value, 256));
  const dependencies = scope.dependencies.slice(0, 4);
  const complete = Object.values(descriptions).every(value => typeof value === 'string') &&
    reconsiderWhen.every(value => typeof value === 'string') && item.reconsiderWhen.length === reconsiderWhen.length &&
    evidenceRefs.every(value => typeof value === 'string') && item.evidenceRefs.length === evidenceRefs.length &&
    scope.dependencies.length === dependencies.length;
  return { deliveryId: item.deliveryId, consumer: item.consumer, previousDeliveryId: item.previousDeliveryId,
    ...descriptions, reconsiderWhen, evidenceRefs, dependencies, complete,
    omittedRetryConditions: item.reconsiderWhen.length - reconsiderWhen.length,
    omittedEvidenceRefs: item.evidenceRefs.length - evidenceRefs.length,
    omittedDependencies: scope.dependencies.length - dependencies.length,
    evidenceRefsDigest: mathDigest(canonicalMathJson(item.evidenceRefs)),
    dependenciesDigest: mathDigest(canonicalMathJson(scope.dependencies)),
    scopeStatus: item.scopeStatus, evidence: item.evidence, findingDigest: item.findingDigest,
    commit: item.commit, createdAt: item.createdAt, scopeDigest: mathDigest(canonicalMathJson(scope)),
    source: { taskId: scope.source.id, taskDigest: taskVersion(scope.source) }, environmentDigest: scope.environmentDigest,
    read: { file: 'COOPERATION.json', collection: 'mathematicalGaps', deliveryId: item.deliveryId } };
}

/** Keep the latest gap per original and route in mandatory context, with full immutable retrieval handles. */
export function mathematicalGapContext(entries: ReturnType<typeof mathematicalGaps>) {
  const latest = new Map<string, (typeof entries)[number]>();
  for (const item of entries) latest.set(canonicalMathJson([item.consumer.taskId, taskGroup(item.scope.source)]), item);
  const selected = [...latest.values()].sort((a, b) => b.createdAt - a.createdAt || a.deliveryId.localeCompare(b.deliveryId)).slice(0, 8);
  const shown: ReturnType<typeof gapEntry>[] = [];
  const packet = (items: typeof shown) => ({ total: entries.length, shown: items.length,
    complete: latest.size === items.length && items.every(item => item.complete), omittedRoutes: latest.size - items.length,
    omittedForBudget: selected.length - items.length, maxBytes: MATHEMATICAL_GAP_CONTEXT_MAX_BYTES, entries: items });
  for (const item of selected) {
    let display = gapEntry(item, 1024);
    if (jsonBytes(display) > MATHEMATICAL_GAP_ENTRY_MAX_BYTES) display = gapEntry(item, 512);
    if (jsonBytes(display) <= MATHEMATICAL_GAP_ENTRY_MAX_BYTES &&
        jsonBytes(packet([...shown, display])) <= MATHEMATICAL_GAP_CONTEXT_MAX_BYTES) shown.push(display);
  }
  return packet(shown);
}
