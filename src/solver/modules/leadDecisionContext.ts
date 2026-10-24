import { compileTaskContext, type TaskContextInput } from '../contextCompiler';
import type { CooperationState } from '../cooperation';
import type { SolverProblem } from '../problem';
import { pendingResearchHandoffs } from '../researchHandoffs';
import { pendingResearchChallenges } from '../researchChallenges';
import { leadPlanDeliveryFile, taskVersion, type CooperativeAction } from '../tasks';
import { cooperativeWorkContract } from './contracts';
import type { ContextBundle } from './context';
import type { ResearchWorker } from './organization';

/** The decision uses the same intake protocol as full planning, with a smaller work product. */
export function buildLeadDecisionContext(problem: SolverProblem, cooperation: CooperationState, context: ContextBundle,
  action: Extract<CooperativeAction, { kind: 'lead' | 'assemble' }>, compilation: Omit<TaskContextInput, 'instructions'>,
  workers: readonly Pick<ResearchWorker, 'id' | 'role'>[]): ContextBundle {
  const workContract = cooperativeWorkContract(action, cooperation.tasks, cooperation);
  const handoffs = pendingResearchHandoffs(cooperation), challenges = pendingResearchChallenges(cooperation);
  const handoffIds = new Set(action.handoffIds ?? []), challengeIds = new Set(action.challengeIds ?? []);
  const shownHandoffs = handoffs.filter(item => handoffIds.has(item.id) || item.sources.some(source => handoffIds.has(source.handoffId)));
  const shownChallenges = challenges.filter(item => challengeIds.has(item.id));
  const hasInbox = Boolean(handoffs.length || challenges.length);
  const file = leadPlanDeliveryFile(action)!;
  const envelope = { baseVersion: action.planVersion, dispatchNonce: action.planNonce };
  const assessments = [
    ...(action.capacityRefill ? [{ kind: 'capacity', requestId: action.capacityRefill.requestId,
      inputDigest: action.capacityRefill.inputDigest, outcome: 'no-independent-work', reason: 'EXACT_MISSING_INPUT_AND_REOPEN_TRIGGER' }] : []),
    ...(action.stagnationRecovery ? [{ kind: 'stagnation', requestId: action.stagnationRecovery.requestId,
      inputDigest: action.stagnationRecovery.inputDigest, outcome: 'no-independent-work', reason: 'EXACT_MISSING_INPUT_AND_REOPEN_TRIGGER' }] : []),
  ];
  const response = hasInbox ? {
    kind: 'handoff', ...envelope,
    ...(shownHandoffs.length ? { handoffDecisions: shownHandoffs.map(item => ({ id: item.id,
      status: 'deferred', reason: 'EXACT_MISSING_MATHEMATICAL_INPUT' })) } : {}),
    ...(shownChallenges.length ? { challengeDecisions: shownChallenges.map(item => ({ id: item.id,
      status: 'deferred', reason: 'SPECIFIC_RESPONSE_TO_THIS_FINDING', reopenOn: 'SPECIFIC_NEW_INPUT' })) } : {}),
  } : { kind: 'assessment', ...envelope, assessments };
  const packet = {
    schema: 'theorem-os.lead-decision.v1', problemReceiptDigest: problem.receiptDigest,
    planVersion: action.planVersion, dispatchNonce: action.planNonce, deliveryFile: file,
    pending: { handoffs: handoffs.length, challenges: challenges.length },
    shown: { handoffIds: shownHandoffs.map(item => item.id), challengeIds: shownChallenges.map(item => item.id) },
    queuedForLater: handoffs.length + challenges.length - shownHandoffs.length - shownChallenges.length,
    capacity: action.capacityRefill, stagnation: action.stagnationRecovery,
    peers: workers.map(worker => ({ id: worker.id, role: worker.role, assignments: cooperation.tasks.filter(node =>
      ['running', 'delivered'].includes(node.status) && node.assignment?.workerId === worker.id).map(node => ({
        taskId: node.task.id, taskDigest: taskVersion(node.task), kind: node.task.kind })) })),
    inFlightQuestions: cooperation.parallelQuestions ?? [],
    blockers: (cooperation.blockers ?? []).filter(item => item.status !== 'superseded' && cooperation.tasks.some(node =>
      node.task.id === item.taskId && taskVersion(node.task) === item.taskDigest)).map(({ id, taskId, mechanism, scope, evidenceStatus, reopenOn }) =>
      ({ id, taskId, mechanism, scope, evidenceStatus, reopenOn })),
    archive: { path: 'COOPERATION.json', taskCount: cooperation.tasks.length,
      retrieval: 'The full graph and older findings remain here. Retrieve only the exact referenced record needed for this decision; do not print or rescan the complete archive.' },
  };
  const decisionRules = [
    'You are the Lead handling one bounded coordination decision. Resolve this dispatch before further mathematical investigation. A decision does not require proving the missing theorem.',
    'Use the fixed shown inbox, exact task interfaces and cited evidence below. Decide each shown item; do not wait for every other research task to finish. Preserve unshown items for subsequent dispatches.',
    'First inspect the capacity request, eligible ownership candidates and shown evidence for executable new work or an ownership repair. If supported, publish the complete plan now with decisions for every shown inbox id; queuedForLater need not be zero. Otherwise resolve the shown inbox with a short decision. Only a no-independent-work assessment must wait for all pending inbox input.',
    'Large finding bodies use exact digest-bound references to COOPERATION.json researchChallenges. The inline summary is advisory; retrieve and verify the complete referenced finding before relying on details absent from the summary. A reference is not a decision or permission to acknowledge an unshown id.',
    'Leave Lean sources unchanged and do not run Lean diagnostics during coordination. Keep existing RESEARCH.md and saved source drafts. A short publication does not require rewriting the complete plan or reproducing old research notes.',
    'Append one complete JSON line to worktree-root ' + file + ' and return promptly. Current response envelope (a schema example, not a recommendation to defer; replace statuses and placeholders with your supported decisions):\n' + JSON.stringify(response),
    ...(hasInbox ? [
      'For handoffs, choose status adopted, rejected or deferred. Adoption copies the exact immutable proposal and its actual typed inputs into a separate proof assignment; it never accepts a proof. For adopted use only id, status and optional ownerId; omit reason and waitsOn. Rejected/deferred decisions require a precise reason. Optional ownerId applies only to a newly adopted task; omit it for shared work. Optional waitsOn lists actual proof task ids.',
      'For challenges, choose status revised, disputed or deferred with a concrete response. A disputed decision requires nonempty evidenceRefs. A deferred decision requires actual waitsOn inputs or a nonempty, specific reopenOn condition. Resolve exactly the shown ids, using their supplied activation identities; do not acknowledge unseen input.',
      'Do not attach no-independent-work assessments to this inbox publication. Capacity/stagnation requests remain pending while the host presents subsequent inbox batches, including concurrent arrivals.',
    ] : [
      'Use the assessment envelope only if no independent executable work is supported by the saved evidence. Replace each reason with the exact missing input and a concrete reopening condition. This is an explicit scheduling assessment, never a proof verdict or proof of impossibility. New pending inbox input prevents its acceptance and must be handled first.',
    ]),
    'When the evidence supports new independent work or an ownership repair, publish kind plan with this same envelope and the complete current tasks/groups/proofRoutes instead. Retrieve the graph selectively before editing it; preserve checked contracts, running assignments and all queued source tasks. Reassign only an unstarted, unassigned task to an eligible worker, preserving its mathematical contract, owner gates, route/group restrictions and reviewer independence. For a new task, give its distinct scope, first method, exact interface, actual dependencies and intended consumer. Do not keep the original goal and restatements running as substitute methods or manufacture work to fill slots.',
    'Only the first valid publication is accepted. Keep the exact current baseVersion and dispatchNonce; old dispatch files and nonces are stale. Full host validation, hidden-inbox checks and independent Lean acceptance remain in force. A saved checkpoint or unchanged plan is not a decision.',
    'Scheduling checkpoints preserve the thread and drafts. Coordination gets bounded additional decision time after unchanged checkpoints; the solving budget remains shared and unchanged.',
  ].join('\n\n');
  const instructions = context.instructions + '\n' + decisionRules;
  const mandatory = [
    { id: 'work-contract', kind: 'assignment' as const, text: 'Host work contract:\n' + JSON.stringify(workContract) },
    { id: 'coordination-decision', kind: 'assignment' as const, text: 'Current bounded Lead decision (advisory; no proof acceptance):\n' + JSON.stringify(packet) },
  ];
  const compiled = compileTaskContext({ ...compilation, instructions, checkpoint: undefined,
    // Continuation history is already preserved in the previous thread and the full archive.
    // This work product needs exact current interfaces and the shown immutable inbox.
    mandatory, optional: [], maxOptionalContextBytes: 0 });
  const continuationMessage = [
    'Continue the current coordination responsibility. This dispatch replaces every previous dispatch nonce and receipt. Prior notes and threads remain saved; do not resume the long mathematical investigation before deciding the shown items.',
    decisionRules, compiled.message,
  ].join('\n\n');
  return { ...context, assignment: action, workContract, instructions, ...compiled, continuationMessage };
}
