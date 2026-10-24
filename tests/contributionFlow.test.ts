import { describe, expect, it } from 'vitest';
import type { SolverRunState } from '../src/solver/archive';
import type { TaskProof } from '../src/solver/cooperativeProof';
import type { DeliveryRecord } from '../src/solver/deliveries';
import { buildResearchContributionFlow, contributionExecutionAttempts, type ContributionJournal } from '../src/solver/contributionFlow';
import { researchHandoffs } from '../src/solver/researchHandoffs';
import { assignmentDeliveryFile, freshlyAccepted, hasTaskAcceptance, taskVersion, type CooperativeTask } from '../src/solver/tasks';
import { buildRunInspection, renderRunInspection } from '../src/solver/inspection';

const seed = 'a'.repeat(40), snapshot = 'b'.repeat(40), merged = 'c'.repeat(40);
const research: CooperativeTask = { id: 'investigate', kind: 'research', objective: 'Find a bridge', dependsOn: [], revision: 0 };
const helper: CooperativeTask = { id: 'bridge', kind: 'lemma', objective: 'Prove the bridge', dependsOn: [], revision: 0,
  proofPath: 'Submission.lean', theoremName: 'Original.bridge', type: 'True' };
const goal: CooperativeTask = { id: 'goal', kind: 'goal', objective: 'Prove the goal', dependsOn: ['bridge'], revision: 0,
  proofPath: 'Submission.lean', theoremName: 'Original.goal' };

function proof(task = helper, commit = snapshot, receiptId = 'lean-receipt'): TaskProof {
  return { taskDigest: taskVersion(task), seedCommit: seed, commit, sourceDigest: 'source-' + commit,
    passed: true, changes: [], verification: { status: 'kernel_verified', targetCommit: 'projection-' + commit,
      startedAt: 160, checkedAt: 180, durationMs: 20,
      results: [{ status: 'kernel_verified', targetCommit: 'projection-' + commit, receiptId }] },
    references: { environmentDigest: 'environment', sourceCommit: commit, tasks: [], proof: [], statement: [], inputs: [] },
  } as TaskProof;
}

function fixture() {
  const assignment = { taskId: helper.id, taskDigest: taskVersion(helper), workerId: 'prover', seedCommit: seed, assignmentId: 'first' };
  const assignmentKey = assignmentDeliveryFile(assignment), check = proof();
  const delivery: DeliveryRecord = { id: 'finding-1', producer: 'researcher', taskId: research.id, taskDigest: taskVersion(research),
    kind: 'research', status: 'advisory', summary: 'A bridge', statement: '', premises: [], dependencies: [],
    remainingObligations: [], evidenceRefs: [], createdAt: 10, commit: seed, lemmaRequests: [helper] };
  const state: SolverRunState = { schema: 'deepscientist.math.solver.v1', runId: 'run', taskDigest: 'task', buildDigest: 'build',
    environmentDigest: 'environment', evaluatorDigest: 'evaluator', model: 'fixture', effort: 'max', worktree: '/unused',
    phase: 'running', turns: 2, problem: { kind: 'imo2026', workspace: '/unused', projectRelative: 'project', baseCommit: seed,
      receiptDigest: 'problem', activeProblemPath: '/unused/problem.json',
      contract: { problemId: 'example', informalStatement: 'The goal', formalStatement: 'theorem goal : True := by sorry',
        assumptions: [], knownTraps: [], acceptanceCriteria: [], statementHash: 'statement', leanStatementHash: 'lean',
        officialVerificationCommand: 'lean' },
      targets: [{ theoremName: 'Original.goal', proofPath: 'Submission.lean', declarationHash: 'declaration' }],
      ownedFiles: ['Submission.lean'], trustedFiles: {}, declarations: {}, sourceStructure: {} },
    cooperation: { planVersion: 'plan-1', canonicalCommit: snapshot,
      tasks: [{ task: research, status: 'completed', attempts: 1 }, {
        task: helper, status: 'integrated', attempts: 1, assignment, proof: check, integratedCheck: check,
      }, { task: goal, status: 'pending', attempts: 0 }],
      deliveries: [delivery, { ...delivery, id: 'finding-2', createdAt: 20 }],
      proofReadyRecords: [{ id: 'ready-record', submissionId: 'submission', assignmentKey, workerId: 'prover',
        taskId: helper.id, taskDigest: taskVersion(helper), seedCommit: seed, problemReceiptDigest: 'problem',
        environmentDigest: 'environment', requestedAt: 120, frozenAt: 140, status: 'checked',
        snapshotCommit: snapshot, sourceDigest: check.sourceDigest, evidence: 'unconditional', receiptIds: ['lean-receipt'] }] } };
  const handoff = researchHandoffs(state.cooperation!)[0];
  const decision = { id: handoff.id, deliveryId: handoff.deliveryId, status: 'adopted' as const,
    taskId: helper.id, taskDigest: taskVersion(helper), contextDigest: handoff.contextDigest };
  state.cooperation!.researchDecisions = [decision];
  const taskIdentity = { taskId: helper.id, taskDigest: taskVersion(helper), assignmentKey, workerId: 'prover', seedCommit: seed };
  const log: Record<string, unknown>[] = [
    { event: 'ready', at: 1 },
    { event: 'delivery_published', deliveryId: delivery.id, taskId: research.id, taskDigest: taskVersion(research), commit: seed, at: 50 },
    { event: 'research_handoff_decided', ...decision, activationDigest: handoff.activationDigest, planVersion: 'plan-1', at: 100 },
    { event: 'task_assigned', ...taskIdentity, kind: 'lemma', planVersion: 'plan-1', at: 110 },
    { event: 'turn_started', ...taskIdentity, turnId: 'turn-1', threadId: 'thread-1', at: 115 },
    { event: 'proof_ready_frozen', ...taskIdentity, readyId: 'ready-record', snapshotCommit: snapshot,
      sourceDigest: check.sourceDigest, frozenAt: 140, at: 141 },
    { event: 'proof_ready_checked', ...taskIdentity, receiptId: 'ready-record', readyId: 'ready-record',
      commit: snapshot, sourceDigest: check.sourceDigest, receiptIds: ['lean-receipt'], at: 190 },
    { event: 'task_integrated', ...taskIdentity, commit: snapshot, sourceDigest: check.sourceDigest, receiptIds: ['lean-receipt'], at: 200 },
  ];
  const journal = (): ContributionJournal => ({ runBinding: 'matched', digest: 'journal-digest',
    events: log.map((data, index) => ({ line: index + 1, data: { runId: state.runId,
      problemReceiptDigest: state.problem.receiptDigest, environmentDigest: state.environmentDigest, ...data } })) });
  return { state, log, journal, assignment, assignmentKey, check, handoff };
}

function failedReadyFixture() {
  const f = fixture(), node = f.state.cooperation!.tasks[1], ready = f.state.cooperation!.proofReadyRecords![0];
  const check: TaskProof = { ...f.check, passed: false, verification: { ...f.check.verification, status: 'failed',
    results: f.check.verification.results.map(result => ({ ...result, status: 'failed' })) } };
  node.status = 'blocked'; node.proof = check; delete node.integratedCheck;
  ready.status = 'failed'; delete ready.evidence; delete ready.receiptIds;
  f.log[6].passed = false; f.log.pop();
  return { ...f, check };
}

function sourceAttemptsFixture() {
  const f = fixture(), deliveries = f.state.cooperation!.deliveries!;
  const first = { taskId: research.id, taskDigest: taskVersion(research), workerId: 'researcher-1',
    seedCommit: seed, assignmentId: 'research-first' };
  const second = { ...first, workerId: 'researcher-2', assignmentId: 'research-second' };
  const firstKey = assignmentDeliveryFile(first), secondKey = assignmentDeliveryFile(second);
  for (const delivery of deliveries) { delivery.producer = first.workerId; delivery.assignmentKey = firstKey; }
  deliveries.push({ ...deliveries[0], id: 'finding-3', producer: second.workerId, assignmentKey: secondKey });
  // Execution order differs from source order; the report keeps obligations first, then source associations.
  for (const [index, assignment] of [second, first].entries()) f.log.push({ event: 'task_assigned',
    ...assignment, assignmentKey: assignmentDeliveryFile(assignment), at: 250 + index });
  return { ...f, firstKey, secondKey };
}

describe('research contribution flow', () => {
  it('projects multiple sources through one handoff, exact execution and a deduplicated recorded check', () => {
    const f = fixture(), before = structuredClone(f.state), report = buildResearchContributionFlow(f.state, f.journal());
    expect(report).toMatchObject({ evidence: 'recorded-not-replayed', runId: 'run', journalDigest: 'journal-digest' });
    expect(report.sources).toHaveLength(2);
    expect(report.handoffs).toHaveLength(1);
    expect(report.handoffs[0].sources).toHaveLength(2);
    expect(report.sources.every(source => source.handoffAliases[0].currentHandoffId === f.handoff.id)).toBe(true);
    expect(report.decisionOccurrences[0]).toMatchObject({
      publicationToDecisionMs: { status: 'recorded', value: 50 },
      decisionToFirstObservedStartMs: { status: 'recorded', value: 15 }, executionAssignmentKey: f.assignmentKey,
    });
    const obligation = report.obligations.find(item => item.taskId === helper.id)!;
    expect(obligation.attempts[0]).toMatchObject({ identity: { status: 'recorded' },
      assignedToFirstObservedStartMs: { status: 'recorded', value: 5 },
      ready: [{ readyToCheckMs: { status: 'recorded', value: 40 }, frozenToCheckMs: { status: 'recorded', value: 20 } }] });
    expect(report.checks).toHaveLength(1);
    expect(report.checks[0]).toMatchObject({ readyIds: ['ready-record'], receiptIds: ['lean-receipt'],
      checkDurationMs: { status: 'recorded', value: 20 }, checkedToIntegratedMs: { status: 'recorded', value: 20 } });
    expect(report.checks[0].storedAs.map(item => item.kind)).toEqual(['task-check', 'integrated-check']);
    expect(report.checks[0].storedAs.every(item => item.recordedProof === 'checked')).toBe(true);
    expect(report.unresolved).toEqual([]);
    expect(f.state).toEqual(before);
    expect(hasTaskAcceptance(f.check)).toBe(false);
    expect(freshlyAccepted(f.state.cooperation!.tasks[1], taskVersion(helper))).toBe(false);
  });

  it('keeps durable decisions without inventing their time, and does not use imported creation time as current publication', () => {
    const f = fixture(), report = buildResearchContributionFlow(f.state);
    expect(report.coverage.journal).toBe('absent');
    expect(report.storedDecisions[0].at).toMatchObject({ status: 'unknown' });
    expect(report.decisionOccurrences).toEqual([]);
    expect(report.sources[0]).toMatchObject({ created: { status: 'recorded', value: 10 },
      publication: { status: 'unknown' }, publicationInThisRun: false });
    expect(report.obligations.find(item => item.taskId === helper.id)!.attempts[0]).toMatchObject({
      assigned: { status: 'unknown' }, firstObservedStart: { status: 'unknown' }, assignedToFirstObservedStartMs: { status: 'unknown' },
    });
    const journal = f.journal();
    const noPublication = { ...journal, events: journal.events.filter(item => item.data.event !== 'delivery_published') };
    expect(buildResearchContributionFlow(f.state, noPublication).decisionOccurrences[0].publicationToDecisionMs.status).toBe('unknown');
  });

  it.each(['unknown', 'mismatched'] as const)('does not attribute an %s journal to saved assignments', runBinding => {
    const f = fixture(), report = buildResearchContributionFlow(f.state, { ...f.journal(), runBinding });
    expect(report.decisionOccurrences).toEqual([]);
    expect(report.obligations.find(item => item.taskId === helper.id)!.attempts[0].starts).toEqual([]);
    expect(report.coverage.journal).toBe(runBinding);
  });

  it('retains deferred and re-decided occurrences, including sources no longer in the current inbox', () => {
    const f = fixture();
    f.log.splice(2, 0, { ...f.log[2], status: 'deferred', taskId: undefined, taskDigest: undefined,
      waitsOn: [{ taskId: 'input', taskDigest: 'input-v1' }], at: 80 });
    f.state.cooperation!.deliveries![0].status = 'superseded';
    f.state.cooperation!.deliveries![1].status = 'superseded';
    const report = buildResearchContributionFlow(f.state, f.journal());
    expect(report.handoffs).toEqual([]);
    expect(report.decisionOccurrences.map(item => item.status)).toEqual(['deferred', 'adopted']);
    expect(report.decisionOccurrences[0]).toMatchObject({ waitsOn: [{ taskId: 'input', taskDigest: 'input-v1' }] });
    expect(report.sources[0]).toMatchObject({ status: 'superseded', handoffAliases: [{ handoffId: f.handoff.id }] });
    expect(report.sources[0].proposals[0]).toMatchObject({ task: helper, taskDigest: taskVersion(helper) });
    expect(report.storedDecisions[0].id).toBe(f.handoff.id);
    expect(report.unresolved.some(item => item.event === 'research_handoff_decided')).toBe(false);
  });

  it('retains a stale check version even when its task definition and assignment are no longer current', () => {
    const f = fixture();
    f.state.cooperation!.tasks[1].task = { ...helper, revision: 1, type: 'False' };
    const report = buildResearchContributionFlow(f.state, f.journal());
    expect(report.obligations.filter(item => item.taskId === helper.id)).toHaveLength(2);
    expect(report.obligations.find(item => item.taskDigest === taskVersion(helper))).toMatchObject({ currentTaskVersion: false,
      checkIds: [report.checks[0].id], uses: undefined });
    expect(report.checks[0]).toMatchObject({ currentTaskVersion: false, storedAs: [{ recordedProof: 'stale' }, { recordedProof: 'stale' }] });
    expect(report.obligations.find(item => item.currentTaskVersion && item.taskId === helper.id)!.checkIds).toEqual([]);
  });

  it('keeps an adopted historical obligation without a remaining task definition and does not turn old research execution into a lemma', () => {
    const f = fixture();
    const historical = { ...f.log[2], taskId: 'old-lemma', taskDigest: 'old-version', planVersion: 'old-plan', at: 90 };
    f.log.splice(2, 0, historical);
    f.state.cooperation!.deliveries![0].assignmentKey = 'research-assignment';
    f.log.push({ event: 'task_assigned', taskId: research.id, taskDigest: taskVersion(research), workerId: 'researcher',
      seedCommit: seed, assignmentKey: 'research-assignment', at: 250 });
    f.state.cooperation!.tasks.shift();
    const report = buildResearchContributionFlow(f.state, f.journal());
    expect(report.obligations.find(item => item.taskId === 'old-lemma')).toMatchObject({
      taskDigest: 'old-version', currentTaskVersion: false, task: undefined, checkIds: [],
    });
    expect(report.sources[0].attempts).toHaveLength(1);
    expect(report.obligations.some(item => item.taskId === research.id)).toBe(false);
  });

  it('attributes research sources only to their own saved assignment', () => {
    const f = fixture(), deliveries = f.state.cooperation!.deliveries!;
    for (const [index, delivery] of deliveries.entries()) {
      const assignment = { taskId: research.id, taskDigest: taskVersion(research), workerId: 'researcher-' + index,
        seedCommit: seed, assignmentId: 'research-attempt-' + index };
      delivery.producer = assignment.workerId; delivery.assignmentKey = assignmentDeliveryFile(assignment);
      f.log.push({ event: 'task_assigned', ...assignment, assignmentKey: delivery.assignmentKey, at: 250 + index });
    }
    const report = buildResearchContributionFlow(f.state, f.journal());
    for (const source of report.sources) {
      expect(source.attempts).toHaveLength(1);
      expect(source.attempts[0]).toMatchObject({ assignmentKey: source.assignmentKey, workerId: source.producer });
    }

    delete deliveries[0].assignmentKey;
    expect(buildResearchContributionFlow(f.state, f.journal()).sources[0].attempts).toEqual([]);
  });

  it('reads each reachable execution once in obligation and source order without changing v1 JSON', () => {
    const f = sourceAttemptsFixture(), flow = buildResearchContributionFlow(f.state, f.journal());
    const before = JSON.stringify(flow), attempts = contributionExecutionAttempts(flow);
    expect(flow.sources.map(source => source.attempts.map(attempt => attempt.assignmentKey)))
      .toEqual([[f.firstKey], [f.firstKey], [f.secondKey]]);
    expect(attempts.map(attempt => [attempt.taskId, attempt.taskDigest, attempt.assignmentKey])).toEqual([
      [helper.id, taskVersion(helper), f.assignmentKey],
      [research.id, taskVersion(research), f.firstKey],
      [research.id, taskVersion(research), f.secondKey],
    ]);
    expect(contributionExecutionAttempts(flow)).toEqual(attempts);
    expect(flow.schema).toBe('theoremos.contribution-flow.v1');
    expect(flow).not.toHaveProperty('attempts');
    expect(JSON.stringify(flow)).toBe(before);
  });

  it('renders repeated source execution once and keeps journal-only research attempts out of execution rows', () => {
    const f = sourceAttemptsFixture(), orphanKey = 'research-without-delivery';
    f.log.push({ event: 'task_assigned', taskId: research.id, taskDigest: taskVersion(research),
      workerId: 'researcher-3', seedCommit: seed, assignmentKey: orphanKey, at: 300 });
    const flow = buildResearchContributionFlow(f.state, f.journal());
    expect(contributionExecutionAttempts(flow).map(attempt => attempt.assignmentKey))
      .toEqual([f.assignmentKey, f.firstKey, f.secondKey]);
    const text = renderRunInspection({ ...buildRunInspection(f.state), contributionFlow: flow });
    const execution = text.split('## Contribution execution observations\n')[1].split('\n## ')[0];
    const rows = execution.split('\n').filter(line => line.startsWith('|')).slice(2);
    expect(rows.map(row => row.split('|')[2].trim())).toEqual([f.assignmentKey, f.firstKey, f.secondKey]);
    expect(execution).not.toContain(orphanKey);
  });

  it('shows bare legacy history checks without manufacturing a task version', () => {
    const f = fixture();
    f.state.cooperation!.tasks[1].proof = undefined; f.state.cooperation!.tasks[1].integratedCheck = undefined;
    f.state.cooperation!.history = [{ task: helper, proof: { commit: snapshot, sourceDigest: 'legacy', passed: true,
      verification: f.check.verification } }];
    const report = buildResearchContributionFlow(f.state, f.journal());
    expect(report.checks).toHaveLength(1);
    expect(report.checks[0]).toMatchObject({ taskDigest: undefined, readyIds: [], storedAs: [{ recordedProof: 'unknown' }] });
    expect(report.obligations.find(item => item.taskId === helper.id)!.checkIds).toEqual([]);
  });

  it('preserves repeated starts and treats repeated dispatch of one saved assignment as ambiguous', () => {
    const f = fixture();
    f.log.splice(4, 0, { ...f.log[3], at: 112 });
    f.log.push({ ...f.log[5], turnId: 'turn-2', at: 250 });
    const report = buildResearchContributionFlow(f.state, f.journal()), attempt = report.obligations.find(item => item.taskId === helper.id)!.attempts[0];
    expect(attempt.assignments).toHaveLength(2);
    expect(attempt.starts.map(item => item.turnId)).toEqual(['turn-1', 'turn-2']);
    expect(attempt.assigned.status).toBe('ambiguous');
    expect(attempt.assignedToFirstObservedStartMs.status).toBe('ambiguous');
    expect(report.decisionOccurrences[0].decisionToFirstObservedStartMs.status).toBe('ambiguous');
  });

  it.each(['reversed-clock', 'missing-first-time'] as const)('does not hide %s with a later start', mode => {
    const f = fixture();
    f.log[4].at = mode === 'reversed-clock' ? 105 : undefined;
    f.log.push({ ...f.log[4], at: 130, turnId: 'turn-2' });
    const report = buildResearchContributionFlow(f.state, f.journal()), attempt = report.obligations.find(item => item.taskId === helper.id)!.attempts[0];
    expect(attempt.assignedToFirstObservedStartMs).toMatchObject({ status: 'unknown',
      reason: mode === 'reversed-clock' ? 'time-order-conflict' : 'endpoint-unavailable' });
    expect(report.decisionOccurrences[0].decisionToFirstObservedStartMs.status).toBe('unknown');
  });

  it.each(['planVersion', 'activationDigest', 'contextDigest'] as const)('leaves decision-to-start unknown without %s', field => {
    const f = fixture(); delete f.log[2][field];
    expect(buildResearchContributionFlow(f.state, f.journal()).decisionOccurrences[0].decisionToFirstObservedStartMs.status).toBe('unknown');
  });

  it('does not join a decision to a different accepted plan or choose among repeated adoption occurrences', () => {
    const f = fixture(); f.log[3].planVersion = 'other-plan';
    expect(buildResearchContributionFlow(f.state, f.journal()).decisionOccurrences[0].decisionToFirstObservedStartMs.status).toBe('unknown');
    f.log[3].planVersion = 'plan-1'; f.log.splice(3, 0, { ...f.log[2], at: 101 });
    expect(buildResearchContributionFlow(f.state, f.journal()).decisionOccurrences.every(
      item => item.decisionToFirstObservedStartMs.status === 'ambiguous')).toBe(true);
  });

  it('leaves reverse event order and a decision-to-assignment clock conflict unknown', () => {
    const f = fixture(), started = f.log.splice(4, 1)[0];
    started.at = 150; f.log.splice(3, 0, started);
    let report = buildResearchContributionFlow(f.state, f.journal());
    expect(report.obligations.find(item => item.taskId === helper.id)!.attempts[0].assignedToFirstObservedStartMs)
      .toMatchObject({ status: 'unknown', reason: 'event-order-conflict' });
    f.log.splice(3, 1); f.log.splice(4, 0, started); f.log[2].at = 120;
    report = buildResearchContributionFlow(f.state, f.journal());
    expect(report.decisionOccurrences[0].decisionToFirstObservedStartMs.status).toBe('unknown');
  });

  it('does not report publication-to-decision latency from a publication logged after the decision', () => {
    const f = fixture(), publication = f.log.splice(1, 1)[0];
    f.log.push(publication);
    expect(buildResearchContributionFlow(f.state, f.journal()).decisionOccurrences[0].publicationToDecisionMs)
      .toMatchObject({ status: 'unknown', reason: 'event-order-conflict' });
  });

  it('reports an assignment worker conflict rather than binding its ready receipt', () => {
    const f = fixture(); f.log[4].workerId = 'other-prover';
    const report = buildResearchContributionFlow(f.state, f.journal()), attempt = report.obligations.find(item => item.taskId === helper.id)!.attempts[0];
    expect(attempt.identity).toMatchObject({ status: 'ambiguous', reason: 'assignment-identity-conflict' });
    expect(attempt.assignedToFirstObservedStartMs.status).toBe('ambiguous');
    expect(report.checks[0].readyIds).toEqual([]);
  });

  it.each(['problemReceiptDigest', 'environmentDigest', 'runId'] as const)('rejects an explicit %s mismatch inside a bound journal', field => {
    const f = fixture(); f.log[4][field] = 'other';
    const report = buildResearchContributionFlow(f.state, f.journal());
    expect(report.obligations.find(item => item.taskId === helper.id)!.attempts[0].starts).toEqual([]);
    expect(report.unresolved).toContainEqual({ event: 'turn_started', evidence: { kind: 'journal', line: 5 },
      reason: 'run-problem-or-environment-mismatch' });
  });

  it('does not guess missing assignment identities from worker or nearby time', () => {
    const f = fixture(); delete f.log[3].assignmentKey; delete f.log[4].assignmentKey;
    const report = buildResearchContributionFlow(f.state, f.journal());
    expect(report.obligations.find(item => item.taskId === helper.id)!.attempts[0].starts).toEqual([]);
    expect(report.unresolved.filter(item => item.reason === 'assignment-identity-missing')).toHaveLength(2);
  });

  it('does not confuse a legacy ready receiptId with Lean receiptIds', () => {
    const f = fixture(); delete f.log[6].readyId; delete f.log[6].receiptIds;
    const report = buildResearchContributionFlow(f.state, f.journal());
    expect(report.checks[0]).toMatchObject({ readyIds: ['ready-record'], receiptIds: ['lean-receipt'],
      checkObserved: { status: 'recorded', value: 190 } });
  });

  it('links a failed ready check through its exact journal receipt without granting acceptance', () => {
    const f = failedReadyFixture(), before = structuredClone(f.state);
    const report = buildResearchContributionFlow(f.state, f.journal()), check = report.checks[0];
    expect(check).toMatchObject({ readyIds: ['ready-record'], receiptIds: ['lean-receipt'],
      storedAs: [{ recordedProof: 'failed' }], checkEvents: [{ kind: 'journal', line: 7 }],
      checkObserved: { status: 'recorded', value: 190 } });
    expect(report.obligations.find(item => item.taskId === helper.id)!.attempts[0].ready[0]).toMatchObject({
      status: 'failed', checkIds: [check.id],
      readyToCheckMs: { status: 'recorded', value: 40 }, frozenToCheckMs: { status: 'recorded', value: 20 },
    });
    expect(report.unresolved).toEqual([]);
    expect(f.state).toEqual(before);
    expect(hasTaskAcceptance(f.check)).toBe(false);
    expect(freshlyAccepted(f.state.cooperation!.tasks[1], taskVersion(helper))).toBe(false);
  });

  it('leaves a failed ready check unbound without an exact journal observation or with conflicting stored receipts', () => {
    const f = failedReadyFixture();
    expect(buildResearchContributionFlow(f.state).checks[0].readyIds).toEqual([]);
    f.state.cooperation!.proofReadyRecords![0].receiptIds = ['other-receipt'];
    expect(buildResearchContributionFlow(f.state, f.journal()).checks[0].readyIds).toEqual([]);
  });

  it.each(['assignmentKey', 'workerId', 'seedCommit', 'sourceDigest', 'receiptIds', 'passed'] as const)(
    'does not infer a failed check link from a journal observation missing %s', field => {
      const f = failedReadyFixture(); delete f.log[6][field];
      const report = buildResearchContributionFlow(f.state, f.journal());
      expect(report.checks[0].readyIds).toEqual([]);
      expect(report.obligations.find(item => item.taskId === helper.id)!.attempts[0].ready[0].readyToCheckMs.status).toBe('unknown');
    });

  it.each(['assignmentKey', 'workerId', 'seedCommit', 'sourceDigest', 'receiptIds', 'passed', 'passed:true'] as const)(
    'keeps a later failed-check observation with invalid %s unresolved after an exact association', field => {
      const f = failedReadyFixture(), later: Record<string, unknown> = { ...f.log[6], at: 195 };
      if (field === 'passed:true') later.passed = true;
      else delete later[field];
      f.log.push(later);
      const report = buildResearchContributionFlow(f.state, f.journal());
      expect(report.checks[0]).toMatchObject({ checkEvents: [{ kind: 'journal', line: 7 }],
        checkObserved: { status: 'recorded', value: 190 } });
      expect(report.checks[0].checkEvents).toHaveLength(1);
      expect(report.unresolved).toContainEqual({ event: 'proof_ready_checked', evidence: { kind: 'journal', line: 8 },
        reason: 'exact-record-match-unavailable' });
    });

  it('keeps conflicting complete failed-check observations ambiguous', () => {
    const f = failedReadyFixture(); f.log.push({ ...f.log[6], at: 195 });
    const report = buildResearchContributionFlow(f.state, f.journal());
    expect(report.checks[0]).toMatchObject({ checkEvents: [{ kind: 'journal', line: 7 }, { kind: 'journal', line: 8 }],
      checkObserved: { status: 'ambiguous', reason: 'conflicting-records' } });
    expect(report.checks[0].checkEvents).toHaveLength(2);
    expect(report.unresolved).toEqual([]);
  });

  it('keeps worker-snapshot checking separate from checking and integrating a merged commit', () => {
    const f = fixture(), integrated = proof(helper, merged, 'merged-receipt');
    // Canonical integration checks use a different seed from the producer assignment in the event.
    integrated.seedCommit = merged;
    integrated.verification.startedAt = 210; integrated.verification.checkedAt = 230;
    f.state.cooperation!.tasks[1].integratedCheck = integrated;
    f.log[7] = { ...f.log[7], commit: merged, sourceDigest: integrated.sourceDigest, receiptIds: ['merged-receipt'], at: 240 };
    const report = buildResearchContributionFlow(f.state, f.journal());
    expect(report.checks).toHaveLength(2);
    expect(report.checks.find(check => check.commit === snapshot)).toMatchObject({ readyIds: ['ready-record'],
      integrated: { status: 'unknown' }, checkedToIntegratedMs: { status: 'unknown' } });
    expect(report.checks.find(check => check.commit === merged)).toMatchObject({ readyIds: [],
      integrated: { status: 'recorded', value: 240 }, checkedToIntegratedMs: { status: 'recorded', value: 10 } });
    expect(report.obligations.find(item => item.taskId === helper.id)!.attempts[0].ready[0].checkIds).toEqual([
      report.checks.find(check => check.commit === snapshot)!.id,
    ]);
  });

  it.each(['source', 'receipt', 'environment'] as const)('does not bind ready to a %s mismatch', field => {
    const f = fixture();
    if (field === 'source') f.state.cooperation!.proofReadyRecords![0].sourceDigest = 'other';
    else if (field === 'receipt') f.state.cooperation!.proofReadyRecords![0].receiptIds = ['other'];
    else f.check.references!.environmentDigest = 'other';
    expect(buildResearchContributionFlow(f.state, f.journal()).checks[0].readyIds).toEqual([]);
  });

  it('leaves missing freeze time and cached verification before readiness unknown', () => {
    const f = fixture(); delete f.state.cooperation!.proofReadyRecords![0].frozenAt; delete f.log[5].frozenAt;
    f.check.verification.startedAt = 100; f.check.verification.checkedAt = 105;
    const ready = buildResearchContributionFlow(f.state, f.journal()).obligations.find(item => item.taskId === helper.id)!.attempts[0].ready[0];
    expect(ready.frozen.status).toBe('unknown');
    expect(ready.frozenToCheckMs.status).toBe('unknown');
    expect(ready.readyToCheckMs).toMatchObject({ status: 'unknown', reason: 'time-order-conflict' });
  });

  it('keeps conditional ready/check records conditional and conflicting first-freeze times ambiguous', () => {
    const f = fixture(), ready = f.state.cooperation!.proofReadyRecords![0];
    ready.evidence = 'conditional'; ready.conditions = [{ taskId: 'input', taskDigest: 'input-v1' }];
    f.check.conditions = [...ready.conditions]; f.state.cooperation!.tasks[1].status = 'conditional';
    f.log[5].frozenAt = 145;
    const report = buildResearchContributionFlow(f.state, f.journal()), entry = report.obligations.find(item => item.taskId === helper.id)!.attempts[0].ready[0];
    expect(entry).toMatchObject({ evidenceKind: 'conditional', frozen: { status: 'ambiguous' },
      frozenToCheckMs: { status: 'ambiguous' } });
    expect(report.checks[0]).toMatchObject({ evidenceKind: 'conditional',
      storedAs: [{ recordedProof: 'conditional' }, { recordedProof: 'conditional' }] });
    expect(report.obligations.find(item => item.taskId === helper.id)!.uses?.proofConsumers ?? []).toEqual([]);
    expect(freshlyAccepted(f.state.cooperation!.tasks[1], taskVersion(helper))).toBe(false);
  });

  it.each(['proof', 'statement', 'conditional'] as const)('keeps planned and %s consumer use distinct via existing continuation semantics', use => {
    const f = fixture(), consumer = f.state.cooperation!.tasks[2], consumerProof = proof(goal, merged, 'consumer-receipt');
    const references = consumerProof.references!;
    references.tasks = [{ taskId: helper.id, taskDigest: taskVersion(helper) }];
    references[use === 'statement' ? 'statement' : 'proof'] = [{ file: 'Submission.lean', name: 'Original.bridge' }];
    if (use === 'conditional') {
      consumer.status = 'conditional'; consumerProof.conditions = [{ taskId: helper.id, taskDigest: taskVersion(helper) }];
      consumer.proof = consumerProof;
    } else { consumer.status = 'integrated'; consumer.integratedCheck = consumerProof; }
    const obligation = buildResearchContributionFlow(f.state, f.journal()).obligations.find(item => item.taskId === helper.id)!;
    expect(obligation.uses).toMatchObject({ plannedConsumers: ['goal'],
      proofConsumers: use === 'proof' ? ['goal'] : [], statementConsumers: use === 'statement' ? ['goal'] : [],
      conditionalConsumers: use === 'conditional' ? ['goal'] : [] });
  });

  it('keeps missing reference coverage unknown and model-reported origins separate from checked use', () => {
    const f = fixture(); delete f.check.references;
    f.state.cooperation!.deliveries![0].knowledgeUses = [{ id: 'external-hint', catalogDigest: 'catalog',
      consumer: { taskId: helper.id, taskDigest: taskVersion(helper) },
      declaration: { name: 'Original.bridge', file: 'Submission.lean' },
      status: 'reported-attempt', attribution: 'model-reported-origin' }];
    const report = buildResearchContributionFlow(f.state, f.journal()), obligation = report.obligations.find(item => item.taskId === helper.id)!;
    expect(obligation.referenceCoverage).toBe('unknown');
    expect(obligation.uses!.proofConsumers).toEqual([]);
    expect(report.modelReportedUses[0]).toMatchObject({ attribution: 'model-reported-origin', origin: 'delivery', deliveryId: 'finding-1' });
    f.state.cooperation!.deliveries = []; f.state.cooperation!.researchDecisions = [];
    expect(buildResearchContributionFlow(f.state).obligations.find(item => item.taskId === helper.id)!.referenceCoverage).toBe('unknown');
  });

  it('renders precise observations and missing evidence without rendering unknown durations as zero', () => {
    const f = fixture(), flow = buildResearchContributionFlow(f.state, f.journal());
    const text = renderRunInspection({ ...buildRunInspection(f.state), contributionFlow: flow });
    expect(text).toContain('## Contribution flow');
    expect(text).toContain('recorded-not-replayed');
    expect(text).toContain('50 ms');
    expect(text).toContain('15 ms');
    const legacy = renderRunInspection({ ...buildRunInspection(f.state), contributionFlow: buildResearchContributionFlow(f.state) });
    expect(legacy).toContain('unknown');
    expect(legacy).not.toMatch(/\| 0 ms \|/u);
  });

  it('renders frozen source attribution and journal diagnostics independently from current execution', () => {
    const f = fixture();
    const text = renderRunInspection({ ...buildRunInspection(f.state), artifacts: { stateFile: '/current/state.json',
      journal: { source: 'log', status: 'read', runBinding: 'unknown', coverage: 'partial', file: '/log',
        bytesRead: 32, ignoredLines: 1, truncated: false, incompleteTailBytes: 3, diagnostics: ['math_inspect_log_run_unknown'] },
      continuation: { status: 'recorded', file: '/current/continuation.json', snapshotDigest: 'snapshot-digest',
        evidence: 'recorded-not-replayed', attachment: { id: 'seed-history', sha256: 'blob-digest', bytes: 64 },
        source: { runId: 'old-run', stateFile: '/old/state.json', stateDigest: 'old-state-digest',
          buildDigest: 'old-build', canonicalCommit: seed }, capturedAt: 100, capture: 'frozen' },
    } });
    expect(text).toContain('math_inspect_log_run_unknown');
    expect(text).toContain('## Frozen continuation source');
    expect(text).toContain('old-state-digest');
    expect(text).toContain('historical execution is not merged');
  });
});
