import { z } from 'zod';
import type { MathSolverReadyReceipt } from "../common/types/team/mathematicsTeam";
import type { ProjectGitResearchTeamAssignmentReceipt } from "../project-git/ProjectGitService";
import { normalizeRuntimeMathAssignment } from "./mathAssignmentJournal";
import { verifyMathSolverReadyReceipt } from "./receiptAttestation";

const identity = z.string().min(1);
const counter = z.number().int().nonnegative().safe();
const slot = z.object({
  slot_id: identity,
  role: z.enum(['lead', 'teammate']),
  state: z.enum(['idle', 'queued', 'starting', 'running', 'paused', 'blocked']),
  queued_foreground_count: counter,
  queued_background_count: counter,
  active_turn_id: identity.nullable(),
  team_run_id: identity.nullable(),
  blocked_reason: z.enum(['runtime_starting', 'runtime_failed', 'removing', 'session_stopped']).nullable(),
});
const snapshotSchema = z.object({
  session_generation: identity.nullable(),
  active_run: z
    .object({
      team_id: identity,
      team_run_id: identity,
      status: z.enum(['accepted', 'running', 'cancelling', 'completed', 'cancelled', 'failed']),
      queued_intent_count: counter,
      starting_batch_count: counter,
      running_batch_count: counter,
      active_enqueue_lease_count: counter,
      slot_work: z.array(slot),
    })
    .nullable(),
  slot_work: z.array(slot),
});
type MathRunSlot = z.infer<typeof slot>;
type MathAssignmentLineageNode = Readonly<{
  receipt: ProjectGitResearchTeamAssignmentReceipt;
  assignment: ReturnType<typeof normalizeRuntimeMathAssignment>;
}>;

const slotHasNoWork = (item: MathRunSlot): boolean =>
  item.queued_foreground_count === 0 &&
  item.queued_background_count === 0 &&
  item.active_turn_id === null &&
  item.team_run_id === null;

const slotQuiescent = (item: MathRunSlot): boolean =>
  item.state === 'idle' && slotHasNoWork(item) && item.blocked_reason === null;

const solverReadyAncestors = (
  candidate: ProjectGitResearchTeamAssignmentReceipt,
  nodes: ReadonlyMap<string, MathAssignmentLineageNode>,
  successors: ReadonlyMap<string, string>
): ReadonlySet<string> | undefined => {
  if (candidate.schema === 'deepscientist.research_team_assignment.v1') return new Set();
  const leaf = nodes.get(candidate.assignmentId);
  if (!leaf || leaf.assignment.request.kind !== 'formalize' || successors.has(candidate.assignmentId)) return undefined;
  const ancestors = new Set<string>();
  let current = leaf;
  while (current.assignment.request.predecessorAssignmentId) {
    const predecessorId = current.assignment.request.predecessorAssignmentId;
    if (ancestors.has(predecessorId)) return undefined;
    const predecessor = nodes.get(predecessorId);
    if (
      !predecessor ||
      predecessor.assignment.runId !== current.assignment.runId ||
      predecessor.assignment.bindingDigest !== current.assignment.bindingDigest ||
      predecessor.assignment.scopeId !== current.assignment.scopeId ||
      predecessor.assignment.request.kind !== 'formalize' ||
      predecessor.receipt.state !== 'superseded' ||
      predecessor.receipt.supersession?.winnerAssignmentId !== current.receipt.assignmentId
    )
      return undefined;
    ancestors.add(predecessorId);
    current = predecessor;
  }
  return ancestors;
};

export type MathRunObservation = Readonly<{
  state: 'waiting' | 'solver_ready' | 'incomplete' | 'runtime_error';
  reason?: string;
  teamRunId?: string;
  quiescent: boolean;
  /** The assigned Worker is idle even when an unrelated reusable slot is starting. */
  pendingAssignmentQuiescent: boolean;
  workerDispatched: boolean;
  assignmentCounts: Readonly<{ pending: number; integrated: number; superseded: number }>;
  solverReady?: MathSolverReadyReceipt;
}>;

/** Events are only wakeups. The durable Core snapshot decides the outcome. */
export function observeMathRun(
  input: Readonly<{
    teamId: string;
    statementHash: string;
    core: unknown;
    assignments: readonly ProjectGitResearchTeamAssignmentReceipt[];
    workspaceHead: string;
    receiptSecret?: string;
  }>
): MathRunObservation {
  const parsed = snapshotSchema.safeParse(input.core);
  if (!parsed.success) throw new Error('math_core_snapshot_invalid');
  const core = parsed.data;
  const run = core.active_run;
  if (run && run.team_id !== input.teamId) throw new Error('math_core_snapshot_identity');
  const sessionStopped = core.session_generation === null;
  const slots = [...core.slot_work, ...(run?.slot_work ?? [])];
  for (const projection of [core.slot_work, run?.slot_work ?? []]) {
    if (new Set(projection.map((item) => item.slot_id)).size !== projection.length)
      throw new Error('math_core_snapshot_identity');
  }
  const assignments = input.assignments;
  if (
    new Set(assignments.map((item) => item.assignmentId)).size !== assignments.length ||
    assignments.some((item) => item.teamId !== input.teamId)
  )
    throw new Error('math_assignment_wal_integrity');
  const lineageNodes = new Map<string, MathAssignmentLineageNode>();
  const successors = new Map<string, string>();
  for (const receipt of assignments) {
    if (receipt.schema !== 'deepscientist.research_team_assignment.v2') continue;
    try {
      const assignment = normalizeRuntimeMathAssignment(receipt.assignment);
      if (assignment.assignmentId !== receipt.assignmentId || assignment.request.targetSlotId !== receipt.slotId)
        throw new Error('identity');
      lineageNodes.set(receipt.assignmentId, { receipt, assignment });
      const predecessorId = assignment.request.predecessorAssignmentId;
      if (predecessorId) {
        if (successors.has(predecessorId)) throw new Error('duplicate successor');
        successors.set(predecessorId, receipt.assignmentId);
      }
    } catch {
      throw new Error('math_assignment_wal_integrity');
    }
  }
  // A successor pointer is not a retirement receipt. Count every durable owner
  // until the producer has actually superseded it, including during recovery.
  const pending = assignments.filter((item) => item.state === 'prepared' || item.state === 'accepted');
  const noActiveRunQuiescent =
    !run &&
    !sessionStopped &&
    core.slot_work.every(
      (item) =>
        (item.state === 'idle' && item.blocked_reason === null && slotHasNoWork(item)) ||
        (item.state === 'blocked' &&
          item.blocked_reason === 'runtime_starting' &&
          slotHasNoWork(item) &&
          !assignments.some((assignment) => assignment.slotId === item.slot_id))
    );
  const assignmentSnapshotInconsistent =
    new Set(pending.map((item) => item.slotId)).size !== pending.length ||
    (!noActiveRunQuiescent &&
      pending.some(
        (item) =>
          !core.slot_work.some((target) => target.slot_id === item.slotId) &&
          !run?.slot_work.some((target) => target.slot_id === item.slotId)
      ));
  const quiescent =
    slots.every(
      (item) =>
        (item.state === 'idle' ||
          (item.role === 'teammate' &&
            item.state === 'blocked' &&
            item.blocked_reason === 'runtime_starting' &&
            !assignments.some((assignment) => assignment.slotId === item.slot_id) &&
            !run?.slot_work.some((active) => active.slot_id === item.slot_id))) &&
        item.queued_foreground_count === 0 &&
        item.queued_background_count === 0 &&
        item.active_turn_id === null &&
        item.team_run_id === null &&
        (item.blocked_reason === null || item.blocked_reason === 'runtime_starting')
    ) &&
    Boolean(
      run &&
      run.queued_intent_count === 0 &&
      run.starting_batch_count === 0 &&
      run.running_batch_count === 0 &&
      run.active_enqueue_lease_count === 0
    );
  const pendingAssignmentQuiescent =
    !assignmentSnapshotInconsistent &&
    pending.length > 0 &&
    (Boolean(
      run &&
      run.status === 'completed' &&
      run.queued_intent_count === 0 &&
      run.starting_batch_count === 0 &&
      run.running_batch_count === 0 &&
      run.active_enqueue_lease_count === 0 &&
      pending.every((assignment) =>
        core.slot_work.some((item) => item.slot_id === assignment.slotId && slotQuiescent(item))
      )
    ) ||
      // Core may retire a completed control turn before publishing the next
      // run event. An accepted assignment whose own slot is idle is still
      // durable evidence that the proof episode needs recovery. Keep a
      // stopped session distinct: it cannot safely accept a replay.
      (!run && !sessionStopped && noActiveRunQuiescent));
  const base = {
    quiescent,
    pendingAssignmentQuiescent,
    ...(run ? { teamRunId: run.team_run_id } : {}),
    workerDispatched: assignments.length > 0 || slots.some((item) => item.role === 'teammate' && item.state !== 'idle'),
    assignmentCounts: {
      pending: pending.length,
      integrated: assignments.filter((item) => item.state === 'integrated').length,
      superseded: assignments.filter((item) => item.state === 'superseded').length,
    },
  };
  if (run?.status === 'failed' || slots.some((item) => item.blocked_reason === 'runtime_failed'))
    return { ...base, state: 'runtime_error', reason: 'math_core_run_failed' };
  if (run?.status === 'cancelled') return { ...base, state: 'runtime_error', reason: 'math_core_run_cancelled' };
  if (assignmentSnapshotInconsistent)
    return { ...base, state: quiescent ? 'incomplete' : 'waiting', reason: 'math_assignment_snapshot_inconsistent' };
  const solverReadyCandidates: { receipt: MathSolverReadyReceipt; ancestors: ReadonlySet<string> }[] = [];
  for (const assignment of assignments) {
    const candidate = assignment.integration?.solverReadyReceipt;
    if (!candidate) continue;
    const verified = input.receiptSecret ? verifyMathSolverReadyReceipt(candidate, input.receiptSecret) : undefined;
    if (
      !verified ||
      assignment.state !== 'integrated' ||
      verified.teamId !== input.teamId ||
      verified.assignmentId !== assignment.assignmentId ||
      verified.slotId !== assignment.slotId ||
      verified.deliveryId !== assignment.delivery?.deliveryId ||
      verified.statementHash !== input.statementHash
    )
      throw new Error('math_solver_ready_receipt_invalid');
    if (verified.targetCommit !== input.workspaceHead) continue;
    const ancestors = solverReadyAncestors(assignment, lineageNodes, successors);
    if (ancestors) solverReadyCandidates.push({ receipt: verified, ancestors });
  }
  if (solverReadyCandidates.length > 1) throw new Error('math_solver_ready_receipt_ambiguous');
  const solverReady = solverReadyCandidates[0]?.receipt;
  const resolvedAncestors = solverReadyCandidates[0]?.ancestors ?? new Set<string>();
  const unresolved =
    // Advisory research cannot invalidate an integrated original-target proof.
    // Unknown/legacy work and all proof owners remain conservative blockers.
    pending.some((item) => lineageNodes.get(item.assignmentId)?.assignment.request.kind !== 'research') ||
    assignments.some(
      (item) =>
        item.supersessionPending ||
        item.budgetCancellation?.status === 'pending' ||
        item.budgetCancellation?.status === 'failed' ||
        (item.integration?.reverificationRequired && !resolvedAncestors.has(item.assignmentId))
    );
  // A signed, integrated current-HEAD receipt is the host's trigger for the
  // independent evaluator, not a claim that evaluation already succeeded.
  // Lead narration and unrelated research must not hold that boundary open.
  // Preserve real cancellation/session stop. A completed, drained run may
  // already have retired the receipt's slot from the Core snapshot.
  if (
    run &&
    ['accepted', 'running', 'completed'].includes(run.status) &&
    !sessionStopped &&
    solverReady &&
    !unresolved &&
    (run.status === 'completed' ? quiescent : slots.some((item) => item.slot_id === solverReady.slotId))
  ) {
    return { ...base, state: 'solver_ready', solverReady };
  }
  if (run?.status === 'completed') return { ...base, state: 'incomplete' };
  // Core can retire its run after integration or session recovery. Completion
  // still requires the signed current-HEAD receipt and an observed idle Worker.
  if (
    !run &&
    !sessionStopped &&
    solverReady &&
    !unresolved &&
    core.slot_work.some((item) => item.slot_id === solverReady.slotId) &&
    core.slot_work.every(slotQuiescent)
  ) {
    return { ...base, quiescent: true, state: 'solver_ready', solverReady };
  }
  return { ...base, state: quiescent || pendingAssignmentQuiescent ? 'incomplete' : 'waiting' };
}
