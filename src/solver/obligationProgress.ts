import { canonicalMathJson, mathDigest } from '../math/mathRuntimeIo';
import { buildProofContinuation } from './progress';
import { describeProofRoutes, routeEvidence, type ProofRoute, type RecordedRouteProofStatus } from './proofRoutes';
import type { RouteBlocker } from './routeControl';
import { taskGroup, taskVersion, type RouteRecord, type TaskRecord } from './tasks';

type TaskReference = { taskId: string; taskDigest: string };
export type RecordedObligation = {
  taskId: string; taskDigest: string; kind: 'lemma' | 'goal'; groupId: string;
  recordedProof: RecordedRouteProofStatus;
  /** A recursively settled integrated checkpoint; this is never official acceptance. */
  closed: boolean;
  conditions: TaskReference[]; referenceCoverage: 'available' | 'missing'; evidenceDigest?: string;
};
export type GoalObligationFrontier = {
  taskId: string; taskDigest: string; closed: boolean;
  frontier: { taskId: string; taskDigest: string | null }[]; missingDependencies: string[];
  routeCombination?: 'any'; alternatives?: { routeId: string;
    frontier: { taskId: string; taskDigest: string | null }[]; missingDependencies: string[]; parkedBy: string[] }[];
};
export type RecordedAdvisory = { taskId: string; taskDigest: string; kind: 'research' | 'sketch';
  completed: boolean; findingDigest?: string };
export type RecordedBlocker = Pick<RouteBlocker, 'id' | 'taskId' | 'taskDigest' | 'groupId' | 'mechanism' | 'scope' |
  'routeId' | 'evidenceStatus' | 'evidenceRefs' | 'reopenOn' | 'basis' | 'status' | 'reopenedReason'>;
export type RecordedProofRoute = ReturnType<typeof describeProofRoutes>['routes'][number] & { parkedBy: string[] };
export type ObligationSnapshot = {
  schema: 'theoremos.obligation-snapshot.v1'; evidence: 'recorded-not-replayed'; acceptance: 'not-assessed';
  digest: string; environmentDigest?: string; obligations: RecordedObligation[]; goals: GoalObligationFrontier[];
  blockers: RecordedBlocker[]; routes: RecordedProofRoute[]; advisory: RecordedAdvisory[];
};
type Change<T> = { before: T; after: T };
export type ObligationProgressReceipt = {
  schema: 'theoremos.obligation-progress.v1'; evidence: 'recorded-not-replayed'; acceptance: 'not-assessed';
  kind: 'baseline' | 'transition'; at: number; beforeDigest?: string; afterDigest: string; environmentChanged: boolean;
  obligations: { new: RecordedObligation[]; closed: Change<RecordedObligation>[]; reopened: Change<RecordedObligation>[];
    removed: RecordedObligation[]; changed: Change<RecordedObligation>[] };
  goalFrontiers: { goalId: string; before?: GoalObligationFrontier; after?: GoalObligationFrontier }[];
  blockers: { new: RecordedBlocker[]; parked: Change<RecordedBlocker>[]; reopened: Change<RecordedBlocker>[];
    superseded: Change<RecordedBlocker>[]; removed: RecordedBlocker[]; changed: Change<RecordedBlocker>[] };
  routes: { routeId: string; before?: RecordedProofRoute; after?: RecordedProofRoute }[];
  advisory: { proposed: RecordedAdvisory[]; completed: Change<RecordedAdvisory>[]; reopened: Change<RecordedAdvisory>[];
    removed: RecordedAdvisory[]; changed: Change<RecordedAdvisory>[] };
};

const hash = (value: unknown) => mathDigest(canonicalMathJson(value));
const same = (left: unknown, right: unknown) => canonicalMathJson(left) === canonicalMathJson(right);
const sorted = (items: readonly string[]) => [...new Set(items)].sort();
const compareText = (left: string, right: string) => left < right ? -1 : left > right ? 1 : 0;
const byTask = <T extends { taskId: string }>(items: readonly T[]) => [...items].sort((a, b) => compareText(a.taskId, b.taskId));
const references = (items: readonly TaskReference[]) => byTask(items.map(item => ({ taskId: item.taskId, taskDigest: item.taskDigest })));
const typed = (node: TaskRecord) => node.task.kind === 'lemma' || node.task.kind === 'goal';

/** Reading this state never marks a receipt as freshly checked or authorizes dispatch. */
export function captureObligationSnapshot(tasks: readonly TaskRecord[], options: {
  groups?: readonly RouteRecord[]; environmentDigest?: string; blockers?: readonly RouteBlocker[]; proofRoutes?: readonly ProofRoute[];
} = {}): ObligationSnapshot {
  // Host capacity work is advisory scheduling, never a proposed or closed proof obligation.
  const capacityIds = new Set(tasks.filter(node => node.capacityExploration).map(node => node.task.id));
  tasks = tasks.filter(node => !capacityIds.has(node.task.id));
  if (capacityIds.size) options = { ...options,
    blockers: options.blockers?.filter(blocker => !capacityIds.has(blocker.taskId)) };
  const nodes = new Map(tasks.map(node => [node.task.id, node]));
  const versions = new Map(tasks.map(node => [node.task.id, taskVersion(node.task)]));
  const recorded = routeEvidence(tasks, options.environmentDigest);
  const obligations = byTask(tasks.filter(typed).map((node): RecordedObligation => {
    const proof = node.integratedCheck ?? node.proof, refs = proof?.references, recordedProof = recorded.status(node.task.id);
    // Receipt IDs, projection commits and whole-source hashes describe a replay,
    // whereas conditions and referenced declarations describe mathematical inputs.
    const evidence = proof && { recordedProof, conditions: references(proof.conditions ?? []),
      ...(refs ? { root: refs.root, scope: refs.scope, tasks: references(refs.tasks ?? []),
        inputs: [...refs.inputs].sort((a, b) => compareText(canonicalMathJson(a), canonicalMathJson(b))) } : {}) };
    return { taskId: node.task.id, taskDigest: versions.get(node.task.id)!, kind: node.task.kind as 'lemma' | 'goal',
      groupId: taskGroup(node.task), recordedProof, closed: recorded.settled(node.task.id, false),
      conditions: references(proof?.conditions ?? []), referenceCoverage: refs?.tasks ? 'available' : 'missing',
      ...(evidence ? { evidenceDigest: hash(evidence) } : {}) };
  }));
  const obligationById = new Map(obligations.map(item => [item.taskId, item]));
  const routes = options.proofRoutes ?? tasks.flatMap(node => node.alternativeRoutes ?? []);
  const parents = new Map<string, Set<string>>();
  const inputs = (node: TaskRecord) => [...node.task.dependsOn, ...routes.filter(route => route.targetTaskId === node.task.id)
    .flatMap(route => [...route.prerequisiteTaskIds, route.closingTaskId])];
  for (const node of tasks) for (const input of inputs(node)) {
    const owners = parents.get(input) ?? new Set<string>(); owners.add(node.task.id); parents.set(input, owners);
  }
  // Keep every original goal in the mathematical report, including paused routes.
  // Invalid recorded evidence cannot settle a frontier merely through its status label.
  const mathematicalView = tasks.map(node => ({ ...node,
    task: node.task.kind === 'goal' ? { ...node.task, status: 'active' as const } : node.task,
    status: typed(node) && node.status === 'integrated' && !obligationById.get(node.task.id)?.closed ? 'pending' as const : node.status }));
  const continuation = buildProofContinuation(mathematicalView, { environmentDigest: options.environmentDigest, proofRoutes: routes });
  const goals = byTask(continuation.goals.map(goal => {
    const reachable = new Set<string>();
    const visit = (id: string) => { if (reachable.has(id)) return; reachable.add(id); const node = nodes.get(id); if (node) inputs(node).forEach(visit); };
    visit(goal.taskId);
    const frontier = (ids: readonly string[]) => {
      const result = new Set<string>(), seen = new Set<string>();
      const nearestMathematical = (id: string) => {
        if (seen.has(id) || !reachable.has(id)) return; seen.add(id);
        const node = nodes.get(id);
        if (!node || typed(node)) { result.add(id); return; }
        // Completing an advisory note does not close a mathematical obligation.
        for (const owner of parents.get(id) ?? []) nearestMathematical(owner);
      };
      ids.forEach(nearestMathematical);
      return sorted([...result]).map(taskId => ({ taskId, taskDigest: versions.get(taskId) ?? null }));
    };
    return { taskId: goal.taskId, taskDigest: versions.get(goal.taskId)!, closed: obligationById.get(goal.taskId)?.closed ?? false,
      frontier: frontier(goal.frontier), missingDependencies: sorted(goal.missingDependencies),
      ...(goal.alternatives ? { routeCombination: 'any' as const, alternatives: goal.alternatives.map(route => ({ routeId: route.routeId,
        frontier: frontier(route.frontier), missingDependencies: sorted(route.missingDependencies), parkedBy: sorted(route.parkedBy),
      })).sort((a, b) => compareText(a.routeId, b.routeId)) } : {}) };
  }));
  const body = {
    schema: 'theoremos.obligation-snapshot.v1' as const, evidence: 'recorded-not-replayed' as const, acceptance: 'not-assessed' as const,
    ...(options.environmentDigest ? { environmentDigest: options.environmentDigest } : {}), obligations, goals,
    blockers: [...(options.blockers ?? [])].map(({ id, taskId, taskDigest, groupId, routeId, mechanism, scope, evidenceStatus, evidenceRefs,
      reopenOn, basis, status, reopenedReason }): RecordedBlocker => ({ id, taskId, taskDigest, groupId, mechanism, scope, evidenceStatus,
      ...(routeId ? { routeId } : {}),
      evidenceRefs: sorted(evidenceRefs), reopenOn: [...reopenOn].sort((a, b) => compareText(canonicalMathJson(a), canonicalMathJson(b))),
      basis, status, ...(reopenedReason ? { reopenedReason } : {}) })).sort((a, b) => compareText(a.id, b.id)),
    routes: describeProofRoutes(routes, mathematicalView, options.environmentDigest).routes.map(route => ({ ...route,
      prerequisiteTaskIds: sorted(route.prerequisiteTaskIds), prerequisiteStatuses: byTask(route.prerequisiteStatuses),
      remainingPrerequisiteTaskIds: sorted(route.remainingPrerequisiteTaskIds), referenceCoverageMissing: sorted(route.referenceCoverageMissing),
      parkedBy: sorted(nodes.get(route.targetTaskId)?.parkedRoutes?.[route.routeId] ?? []),
    })).sort((a, b) => compareText(a.routeId, b.routeId)),
    advisory: byTask(tasks.filter(node => !typed(node)).map((node): RecordedAdvisory => ({ taskId: node.task.id,
      taskDigest: versions.get(node.task.id)!, kind: node.task.kind as 'research' | 'sketch', completed: node.status === 'completed',
      ...(node.finding ? { findingDigest: hash(node.finding) } : {}) }))),
  };
  // Detach the checkpoint from mutable task records before it is kept as "before".
  return JSON.parse(canonicalMathJson({ ...body, digest: hash(body) })) as ObligationSnapshot;
}

/** Describe observed changes; no transition, including a goal check, is platform acceptance. */
export function diffObligationProgress(before: ObligationSnapshot | undefined, after: ObligationSnapshot,
  at = Date.now()): ObligationProgressReceipt | undefined {
  if (before?.digest === after.digest) return;
  const receipt: ObligationProgressReceipt = {
    schema: 'theoremos.obligation-progress.v1', evidence: 'recorded-not-replayed', acceptance: 'not-assessed',
    kind: before ? 'transition' : 'baseline', at, ...(before ? { beforeDigest: before.digest } : {}), afterDigest: after.digest,
    environmentChanged: Boolean(before && before.environmentDigest !== after.environmentDigest),
    obligations: { new: [], closed: [], reopened: [], removed: [], changed: [] }, goalFrontiers: [],
    blockers: { new: [], parked: [], reopened: [], superseded: [], removed: [], changed: [] }, routes: [],
    advisory: { proposed: [], completed: [], reopened: [], removed: [], changed: [] },
  };
  if (!before) return receipt;
  const compare = <T>(previous: readonly T[], current: readonly T[], key: (item: T) => string,
    change: (before: T | undefined, after: T | undefined) => void) => {
    const oldItems = new Map(previous.map(item => [key(item), item])), newItems = new Map(current.map(item => [key(item), item]));
    for (const id of sorted([...oldItems.keys(), ...newItems.keys()])) {
      const oldItem = oldItems.get(id), newItem = newItems.get(id);
      if (!oldItem || !newItem || !same(oldItem, newItem)) change(oldItem, newItem);
    }
  };
  compare(before.obligations, after.obligations, item => item.taskId, (oldItem, newItem) => {
    if (!oldItem) receipt.obligations.new.push(newItem!);
    else if (!newItem) receipt.obligations.removed.push(oldItem);
    else if (!oldItem.closed && newItem.closed) receipt.obligations.closed.push({ before: oldItem, after: newItem });
    else if (oldItem.closed && !newItem.closed) receipt.obligations.reopened.push({ before: oldItem, after: newItem });
    else receipt.obligations.changed.push({ before: oldItem, after: newItem });
  });
  const mathematicalFrontier = (goal: GoalObligationFrontier) => ({ ...goal,
    ...(goal.alternatives ? { alternatives: goal.alternatives.map(({ parkedBy: _parking, ...route }) => route) } : {}) });
  compare(before.goals, after.goals, item => item.taskId, (oldItem, newItem) => {
    // Parking changes scheduling; it does not change an unmet mathematical statement.
    if (oldItem && newItem && same(mathematicalFrontier(oldItem), mathematicalFrontier(newItem))) return;
    receipt.goalFrontiers.push({ goalId: (newItem ?? oldItem)!.taskId,
      ...(oldItem ? { before: oldItem } : {}), ...(newItem ? { after: newItem } : {}) });
  });
  compare(before.blockers, after.blockers, item => item.id, (oldItem, newItem) => {
    if (!oldItem) receipt.blockers.new.push(newItem!);
    else if (!newItem) receipt.blockers.removed.push(oldItem);
    else {
      const change = { before: oldItem, after: newItem };
      if (oldItem.status !== newItem.status && newItem.status === 'parked') receipt.blockers.parked.push(change);
      else if (oldItem.status !== newItem.status && newItem.status === 'reopened') receipt.blockers.reopened.push(change);
      else if (oldItem.status !== newItem.status && newItem.status === 'superseded') receipt.blockers.superseded.push(change);
      else receipt.blockers.changed.push(change);
    }
  });
  compare(before.routes, after.routes, item => item.routeId, (oldItem, newItem) => receipt.routes.push({
    routeId: (newItem ?? oldItem)!.routeId, ...(oldItem ? { before: oldItem } : {}), ...(newItem ? { after: newItem } : {}) }));
  compare(before.advisory, after.advisory, item => item.taskId, (oldItem, newItem) => {
    if (!oldItem) receipt.advisory.proposed.push(newItem!);
    else if (!newItem) receipt.advisory.removed.push(oldItem);
    else if (!oldItem.completed && newItem.completed) receipt.advisory.completed.push({ before: oldItem, after: newItem });
    else if (oldItem.completed && !newItem.completed) receipt.advisory.reopened.push({ before: oldItem, after: newItem });
    else receipt.advisory.changed.push({ before: oldItem, after: newItem });
  });
  return receipt;
}
