import { describe, expect, it } from 'vitest';
import { observeMathRun } from '../src/math/mathRunObservation';
import { canonicalMathJson, mathDigest } from '../src/math/mathRuntimeIo';
import { signMathSolverReadyReceipt } from '../src/math/receiptAttestation';
import type { ProjectGitResearchTeamAssignmentReceipt } from '../src/project-git/ProjectGitService';

const idle = {
  slot_id: 'worker',
  role: 'teammate',
  state: 'idle',
  queued_foreground_count: 0,
  queued_background_count: 0,
  active_turn_id: null,
  team_run_id: null,
  blocked_reason: null,
};
const core = () => ({
  session_generation: 'generation',
  active_run: {
    team_id: 'team',
    team_run_id: 'run',
    status: 'completed',
    queued_intent_count: 0,
    starting_batch_count: 0,
    running_batch_count: 0,
    active_enqueue_lease_count: 0,
    slot_work: [idle],
  },
  slot_work: [idle],
});
const input = () => ({
  teamId: 'team',
  statementHash: 'a'.repeat(64),
  core: core(),
  assignments: [] as ProjectGitResearchTeamAssignmentReceipt[],
  workspaceHead: 'b'.repeat(40),
  receiptSecret: 'secret',
});
const wal = (state: ProjectGitResearchTeamAssignmentReceipt['state']): ProjectGitResearchTeamAssignmentReceipt => ({
  schema: 'deepscientist.research_team_assignment.v1',
  teamId: 'team',
  slotId: 'worker',
  assignmentId: 'assignment',
  assignment: {},
  state,
  updatedAt: new Date(100).toISOString(),
});
const solved = (): ProjectGitResearchTeamAssignmentReceipt => ({
  ...wal('integrated'),
  delivery: {
    deliveryId: 'delivery',
    result: {},
    deliveredAt: new Date(100).toISOString(),
    resultPayloadBytes: 2,
    leadPayloadBytes: 2,
  },
  integration: {
    executionMode: 'artifact',
    solverReadyReceipt: signMathSolverReadyReceipt(
      {
        teamId: 'team',
        slotId: 'worker',
        assignmentId: 'assignment',
        deliveryId: 'delivery',
        targetCommit: 'b'.repeat(40),
        statementHash: 'a'.repeat(64),
        routeFingerprint: 'route',
        checkedAt: 100,
      },
      'secret'
    ),
  },
});
const v2Assignment = (assignmentId: string, predecessorAssignmentId?: string) => {
  const request = {
    idempotencyKey: `key-${assignmentId}`,
    targetSlotId: 'worker',
    ...(predecessorAssignmentId ? { predecessorAssignmentId } : {}),
    kind: 'formalize' as const,
    objective: `Repair ${assignmentId}`,
    acceptance: ['Prove the original theorem.'],
  };
  return {
    schema: 'deepscientist.math.assignment.v2' as const,
    runId: 'run',
    bindingDigest: 'd'.repeat(64),
    assignmentId,
    scopeId: 'proof-scope',
    baseCommit: 'a'.repeat(40),
    request,
    payloadHash: mathDigest(canonicalMathJson(request)),
    sourceRootRelative: `.deepscientist/assignments/${assignmentId}`,
    draftRoot: `/tmp/math-run/drafts/${assignmentId}`,
    artifactGrants: [],
  };
};
const supersededV2 = (
  assignmentId: string,
  winnerAssignmentId: string,
  predecessorAssignmentId?: string
): ProjectGitResearchTeamAssignmentReceipt => ({
  schema: 'deepscientist.research_team_assignment.v2',
  teamId: 'team',
  slotId: 'worker',
  assignmentId,
  assignment: v2Assignment(assignmentId, predecessorAssignmentId),
  state: 'superseded',
  supersession: { winnerAssignmentId, reason: 'A verified rejection authorized the repair successor.' },
  integration: {
    executionMode: 'artifact',
    branch: `branch-${assignmentId}`,
    headCommit: '8'.repeat(40),
    mergedCommit: '9'.repeat(40),
    reverificationRequired: true,
    verification: {
      schema: 'deepscientist.math.source-verification-evidence.v1',
      disposition: 'candidate_rejected',
      targetCommit: '9'.repeat(40),
      checkedAt: 100,
      itemIds: ['proof'],
      sourceHashes: ['e'.repeat(64)],
    },
  },
  updatedAt: new Date(100).toISOString(),
});
const solvedV2 = (assignmentId: string, predecessorAssignmentId?: string): ProjectGitResearchTeamAssignmentReceipt => ({
  schema: 'deepscientist.research_team_assignment.v2',
  teamId: 'team',
  slotId: 'worker',
  assignmentId,
  assignment: v2Assignment(assignmentId, predecessorAssignmentId),
  state: 'integrated',
  delivery: {
    deliveryId: `team:worker:${assignmentId}`,
    result: {},
    deliveredAt: new Date(100).toISOString(),
    resultPayloadBytes: 2,
    leadPayloadBytes: 2,
  },
  integration: {
    executionMode: 'artifact',
    branch: `branch-${assignmentId}`,
    headCommit: 'b'.repeat(40),
    mergedCommit: 'b'.repeat(40),
    solverReadyReceipt: signMathSolverReadyReceipt(
      {
        teamId: 'team',
        slotId: 'worker',
        assignmentId,
        deliveryId: `team:worker:${assignmentId}`,
        targetCommit: 'b'.repeat(40),
        statementHash: 'a'.repeat(64),
        routeFingerprint: 'route',
        checkedAt: 100,
      },
      'secret'
    ),
  },
  updatedAt: new Date(100).toISOString(),
});

describe('Authoritative mathematics completion', () => {
  const activeProof = () => {
    const value = input();
    const research = v2Assignment('research');
    const request = { ...research.request, kind: 'research' as const, targetSlotId: 'researcher' };
    const advisory: ProjectGitResearchTeamAssignmentReceipt = {
      ...wal('accepted'),
      schema: 'deepscientist.research_team_assignment.v2',
      assignmentId: 'research',
      slotId: 'researcher',
      assignment: { ...research, request, payloadHash: mathDigest(canonicalMathJson(request)) },
    };
    value.assignments = [solvedV2('proof'), advisory];
    value.core.active_run.status = 'running';
    value.core.active_run.running_batch_count = 2;
    value.core.active_run.queued_intent_count = 3;
    value.core.slot_work = [
      idle,
      { ...idle, slot_id: 'lead', role: 'lead', state: 'running', active_turn_id: 'lead-turn' },
      { ...idle, slot_id: 'researcher', state: 'running', active_turn_id: 'research-turn' },
    ];
    return value;
  };

  it('enters independent evaluation from a signed integration while Lead and research are still busy', () => {
    expect(observeMathRun(activeProof())).toMatchObject({
      state: 'solver_ready',
      quiescent: false,
      assignmentCounts: { pending: 1 },
      solverReady: { assignmentId: 'proof', targetCommit: 'b'.repeat(40) },
    });
  });

  it.each(['cancelled', 'cancelling', 'failed'])('does not start final evaluation during Core %s', (status) => {
    const value = activeProof();
    value.core.active_run.status = status;
    expect(observeMathRun(value).state).not.toBe('solver_ready');
  });

  it.each(['stopped', 'changed-head', 'missing-receipt', 'pending-proof', 'reverification'])(
    'keeps live finalization blocked for %s',
    (fault) => {
      const value = activeProof();
      if (fault === 'stopped') value.core.session_generation = null;
      if (fault === 'changed-head') value.workspaceHead = 'c'.repeat(40);
      if (fault === 'missing-receipt') value.assignments[0].integration = undefined;
      if (fault === 'reverification') value.assignments[0].integration!.reverificationRequired = true;
      if (fault === 'pending-proof') {
        const assignment = v2Assignment('other-proof');
        const request = { ...assignment.request, targetSlotId: 'researcher' };
        value.assignments[1] = {
          ...value.assignments[1],
          assignmentId: 'other-proof',
          assignment: { ...assignment, request, payloadHash: mathDigest(canonicalMathJson(request)) },
        };
      }
      expect(observeMathRun(value).state).not.toBe('solver_ready');
    }
  );

  it('finalizes when the second proof owner was superseded by the winning integration', () => {
    // Second proof owner: the other Lean Engineer's attempt blocks solver_ready
    // while pending and releases it once superseded by the winner.
    const value = activeProof();
    const other = v2Assignment('second-owner');
    const request = { ...other.request, targetSlotId: 'lean-2' };
    const pendingOther: ProjectGitResearchTeamAssignmentReceipt = {
      ...wal('accepted'),
      schema: 'deepscientist.research_team_assignment.v2',
      assignmentId: 'second-owner',
      slotId: 'lean-2',
      assignment: { ...other, request, payloadHash: mathDigest(canonicalMathJson(request)) },
    };
    value.assignments.push(pendingOther);
    expect(observeMathRun(value).state).not.toBe('solver_ready');
    value.assignments[value.assignments.length - 1] = {
      ...pendingOther,
      state: 'superseded',
      supersession: { winnerAssignmentId: 'proof', reason: 'first verified integration won' },
    };
    expect(observeMathRun(value)).toMatchObject({
      state: 'solver_ready',
      solverReady: { assignmentId: 'proof' },
    });
  });

  it('rejects a forged success even when only advisory work remains', () => {
    const value = activeProof();
    value.receiptSecret = 'different-secret';
    expect(() => observeMathRun(value)).toThrow('math_solver_ready_receipt_invalid');
  });

  it('requires a signed exact-HEAD WAL receipt for solver-ready', () => {
    expect(observeMathRun({ ...input(), assignments: [solved()] })).toMatchObject({ state: 'solver_ready' });
    expect(observeMathRun(input())).toMatchObject({ state: 'incomplete' });
  });
  it.each(['prepared', 'accepted'] as const)('finishes a completed Core as incomplete with a %s WAL entry', (state) => {
    expect(observeMathRun({ ...input(), assignments: [wal(state)] })).toMatchObject({
      state: 'incomplete',
      quiescent: true,
    });
  });
  it('keeps a pending assignment resumable when an unrelated slot is starting', () => {
    const value = input();
    value.core.slot_work = [
      idle,
      { ...idle, slot_id: 'unrelated', state: 'blocked', blocked_reason: 'runtime_starting' },
    ];
    value.core.active_run.slot_work = [idle];
    expect(observeMathRun({ ...value, assignments: [wal('accepted')] })).toMatchObject({
      state: 'incomplete',
      quiescent: true,
      pendingAssignmentQuiescent: true,
    });
  });
  it.each(['assigned', 'queued', 'active-run'] as const)('does not ignore a %s blocked slot', (kind) => {
    const value = input();
    const blocked = { ...idle, slot_id: 'other', state: 'blocked', blocked_reason: 'runtime_starting' };
    value.core.slot_work.push(blocked);
    if (kind === 'assigned') value.assignments.push({ ...wal('accepted'), slotId: 'other' });
    if (kind === 'queued') blocked.queued_foreground_count = 1;
    if (kind === 'active-run') value.core.active_run.slot_work.push(blocked);
    expect(observeMathRun(value).quiescent).toBe(false);
  });
  it('accepts an assigned slot represented only in the active run projection', () => {
    const value = input();
    value.core.slot_work = [];
    value.core.active_run.slot_work = [{ ...idle, slot_id: 'worker' }];
    expect(observeMathRun({ ...value, assignments: [wal('accepted')] })).toMatchObject({
      state: 'incomplete',
      quiescent: true,
    });
  });
  it('finishes a completed Core with an unintegrated blocked delivery as incomplete', () => {
    expect(
      observeMathRun({
        ...input(),
        assignments: [
          {
            ...wal('accepted'),
            delivery: {
              deliveryId: 'delivery',
              result: { status: 'blocked' },
              deliveredAt: 'now',
              resultPayloadBytes: 2,
              leadPayloadBytes: 2,
            },
          },
        ],
      })
    ).toMatchObject({ state: 'incomplete' });
  });
  it.each([
    'queued_intent_count',
    'starting_batch_count',
    'running_batch_count',
    'active_enqueue_lease_count',
  ] as const)('finishes a completed Core as incomplete with outstanding %s', (key) => {
    const value = input();
    value.core.active_run[key] = 1;
    expect(observeMathRun(value)).toMatchObject({ state: 'incomplete', quiescent: false });
  });
  it.each(['queued', 'starting', 'running', 'paused', 'blocked'])(
    'finishes a completed Core with a %s slot',
    (state) => {
      const value = input();
      value.core.slot_work = [{ ...idle, state }];
      expect(observeMathRun(value)).toMatchObject({ state: 'incomplete', quiescent: false });
    }
  );
  it('does not use an absent run or a terminal event as durable completion', () => {
    expect(observeMathRun({ ...input(), core: { ...core(), active_run: null } }).state).toBe('waiting');
  });
  it('recovers an exact-HEAD signed integration after Core retires the run in a live idle session', () => {
    expect(
      observeMathRun({
        ...input(),
        core: { ...core(), active_run: null },
        assignments: [supersededV2('first', 'second'), solvedV2('second', 'first')],
      })
    ).toMatchObject({ state: 'solver_ready', quiescent: true, assignmentCounts: { pending: 0 } });
  });
  it.each([
    { name: 'stopped session', corePatch: { session_generation: null } },
    { name: 'missing slots', corePatch: { slot_work: [] } },
    { name: 'missing receipt Worker', corePatch: { slot_work: [{ ...idle, slot_id: 'other' }] } },
    { name: 'queued work', corePatch: { slot_work: [{ ...idle, queued_foreground_count: 1 }] } },
    { name: 'background work', corePatch: { slot_work: [{ ...idle, queued_background_count: 1 }] } },
    { name: 'active turn', corePatch: { slot_work: [{ ...idle, active_turn_id: 'turn' }] } },
    { name: 'active run reference', corePatch: { slot_work: [{ ...idle, team_run_id: 'old-run' }] } },
    { name: 'paused slot', corePatch: { slot_work: [{ ...idle, state: 'paused' }] } },
    {
      name: 'starting slot',
      corePatch: { slot_work: [{ ...idle, state: 'blocked', blocked_reason: 'runtime_starting' }] },
    },
  ])('does not recover retired-run success with $name', ({ corePatch }) => {
    expect(
      observeMathRun({
        ...input(),
        core: { ...core(), active_run: null, ...corePatch },
        assignments: [solvedV2('solved')],
      }).state
    ).not.toBe('solver_ready');
  });
  it.each(['pending', 'reverification', 'supersession', 'changed-head'] as const)(
    'keeps retired-run completion blocked by %s',
    (kind) => {
      const receipt = solvedV2('solved');
      if (kind === 'reverification') receipt.integration!.reverificationRequired = true;
      if (kind === 'supersession') receipt.supersessionPending = { winnerAssignmentId: 'next', reason: 'pending' };
      expect(
        observeMathRun({
          ...input(),
          core: { ...core(), active_run: null },
          workspaceHead: (kind === 'changed-head' ? 'c' : 'b').repeat(40),
          assignments: [receipt, ...(kind === 'pending' ? [{ ...wal('accepted'), assignmentId: 'pending' }] : [])],
        }).state
      ).not.toBe('solver_ready');
    }
  );
  it('marks an accepted assignment incomplete when Core retires the run but leaves its slot idle', () => {
    const value = input();
    value.core.active_run = null;
    expect(observeMathRun({ ...value, assignments: [wal('accepted')] })).toMatchObject({
      state: 'incomplete',
      quiescent: false,
      pendingAssignmentQuiescent: true,
    });
  });
  it('recovers an accepted assignment when a live session omits both the run and slot projection', () => {
    const value = input();
    value.core.active_run = null;
    value.core.slot_work = [];
    expect(observeMathRun({ ...value, assignments: [wal('accepted')] })).toMatchObject({
      state: 'incomplete',
      quiescent: false,
      pendingAssignmentQuiescent: true,
    });
  });
  it.each(['failed', 'cancelled'])('keeps Core %s separate from mathematical failure', (status) => {
    const value = input();
    value.core.active_run.status = status;
    expect(observeMathRun(value).state).toBe('runtime_error');
  });
  it.each([undefined, '0', -1, NaN])('rejects malformed/missing counters: %s', (active_enqueue_lease_count) => {
    const value = input();
    expect(() =>
      observeMathRun({
        ...value,
        core: {
          ...value.core,
          active_run: {
            ...value.core.active_run,
            active_enqueue_lease_count,
          },
        },
      })
    ).toThrow('math_core_snapshot_invalid');
  });
  it('rejects foreign WAL identity and requests recovery for duplicate ownership and missing slots', () => {
    expect(() => observeMathRun({ ...input(), assignments: [{ ...wal('accepted'), teamId: 'other' }] })).toThrow(
      'math_assignment_wal_integrity'
    );
    expect(
      observeMathRun({ ...input(), assignments: [wal('accepted'), { ...wal('accepted'), assignmentId: 'second' }] })
    ).toMatchObject({ state: 'incomplete', reason: 'math_assignment_snapshot_inconsistent' });
    expect(observeMathRun({ ...input(), assignments: [{ ...wal('prepared'), slotId: 'absent' }] })).toMatchObject({
      state: 'incomplete',
      reason: 'math_assignment_snapshot_inconsistent',
    });
  });
  it.each([false, true])('does not hide accepted predecessor ownership when Core run is absent: %s', (retiredRun) => {
    const value = input();
    if (retiredRun) value.core.active_run = null;
    const predecessor = { ...supersededV2('first', 'second'), state: 'accepted' as const, supersession: undefined };
    const successor = { ...solvedV2('second', 'first'), state: 'accepted' as const, integration: undefined };
    expect(observeMathRun({ ...value, assignments: [predecessor, successor] })).toMatchObject({
      reason: 'math_assignment_snapshot_inconsistent',
      pendingAssignmentQuiescent: false,
      assignmentCounts: { pending: 2 },
    });
  });
  it('counts only the successor after durable predecessor retirement', () => {
    const successor = { ...solvedV2('second', 'first'), state: 'accepted' as const, integration: undefined };
    expect(observeMathRun({ ...input(), assignments: [supersededV2('first', 'second'), successor] })).toMatchObject({
      state: 'incomplete',
      pendingAssignmentQuiescent: true,
      assignmentCounts: { pending: 1, superseded: 1 },
    });
  });
  it('rejects a signed receipt replayed into a different task or assignment', () => {
    expect(() => observeMathRun({ ...input(), statementHash: 'c'.repeat(64), assignments: [solved()] })).toThrow(
      'math_solver_ready_receipt_invalid'
    );
    expect(() => observeMathRun({ ...input(), assignments: [{ ...solved(), assignmentId: 'other' }] })).toThrow(
      'math_solver_ready_receipt_invalid'
    );
    expect(() => observeMathRun({ ...input(), receiptSecret: undefined, assignments: [solved()] })).toThrow(
      'math_solver_ready_receipt_invalid'
    );
  });
  it('does not reuse a historical receipt for a modified HEAD', () => {
    expect(observeMathRun({ ...input(), workspaceHead: 'c'.repeat(40), assignments: [solved()] })).toMatchObject({
      state: 'incomplete',
    });
  });
  it('keeps a supersession intent pending even with a valid solver receipt', () => {
    expect(
      observeMathRun({
        ...input(),
        assignments: [
          {
            ...solved(),
            supersessionPending: {
              winnerAssignmentId: 'other',
              reason: 'pending cancellation',
            },
          },
        ],
      })
    ).toMatchObject({ state: 'incomplete' });
  });
  it('LITE-RELIABILITY T47: accepts a successful chain leaf without erasing rejected ancestor evidence', () => {
    const first = supersededV2('first', 'second');
    const second = supersededV2('second', 'final', 'first');
    const final = solvedV2('final', 'second');
    expect(observeMathRun({ ...input(), assignments: [first, second, final] })).toMatchObject({
      state: 'solver_ready',
      solverReady: { assignmentId: 'final', targetCommit: 'b'.repeat(40) },
    });
    expect(first.integration).toMatchObject({
      reverificationRequired: true,
      verification: { disposition: 'candidate_rejected' },
    });
  });
  it('LITE-RELIABILITY T48: keeps an unfinished predecessor active despite a later signed receipt', () => {
    const predecessor: ProjectGitResearchTeamAssignmentReceipt = {
      ...supersededV2('first', 'final'),
      state: 'accepted',
      supersession: undefined,
    };
    expect(observeMathRun({ ...input(), assignments: [predecessor, solvedV2('final', 'first')] })).toMatchObject({
      state: 'incomplete',
    });
  });
  it('LITE-RELIABILITY T49: rejects a signed success whose claimed predecessor chain is missing', () => {
    expect(observeMathRun({ ...input(), assignments: [solvedV2('final', 'missing')] })).toMatchObject({
      state: 'incomplete',
    });
  });
  it.each(['runId', 'bindingDigest', 'scopeId'] as const)(
    'does not resolve rejected history across a different %s',
    (field) => {
      const predecessor = supersededV2('first', 'final');
      predecessor.assignment = {
        ...v2Assignment('first'),
        [field]: field === 'bindingDigest' ? 'f'.repeat(64) : 'foreign',
      };
      expect(observeMathRun({ ...input(), assignments: [predecessor, solvedV2('final', 'first')] })).toMatchObject({
        state: 'incomplete',
      });
    }
  );
  it('does not resolve rejected history when retirement names a different winner', () => {
    expect(
      observeMathRun({ ...input(), assignments: [supersededV2('first', 'other'), solvedV2('final', 'first')] })
    ).toMatchObject({ state: 'incomplete' });
  });
  it('LITE-RELIABILITY T50: selects the exact current canonical commit instead of a historical success', () => {
    const current = solvedV2('current');
    const historical = {
      ...solved(),
      integration: {
        ...solved().integration!,
        solverReadyReceipt: signMathSolverReadyReceipt(
          {
            teamId: 'team',
            slotId: 'worker',
            assignmentId: 'assignment',
            deliveryId: 'delivery',
            targetCommit: 'c'.repeat(40),
            statementHash: 'a'.repeat(64),
            routeFingerprint: 'route',
            checkedAt: 90,
          },
          'secret'
        ),
      },
    };
    expect(observeMathRun({ ...input(), assignments: [current, historical] })).toMatchObject({
      state: 'solver_ready',
      solverReady: { assignmentId: 'current', targetCommit: 'b'.repeat(40) },
    });
  });
});
