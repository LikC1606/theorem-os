import fs from 'node:fs';
import path from 'node:path';
import { readSolverRunState, type DispatchWaitObservation, type SolverRunState } from './archive';
import { canonicalMathJson, mathDigest, readMathJson } from '../math/mathRuntimeIo';
import { taskGroup, taskVersion, type TaskRecord } from './tasks';
import { researchFailureCategory } from './modules/search';
import { buildProofContinuation, recordedTaskProofStatus } from './progress';
import { researchHandoffs } from './researchHandoffs';
import { buildTokenBudget } from './usageBudget';
import { captureObligationSnapshot } from './obligationProgress';
import type { ContributionObservation, ResearchContributionFlow } from './contributionFlow';
import type { StoredRunInspectionArtifacts } from './storedRunInspection';

/** Binds a report to the stored observation; this does not replay or accept its proof evidence. */
export function runInspectionSnapshot(state: SolverRunState, result?: Record<string, unknown>) {
  return { schema: 'theoremos.run-observation.v1' as const, runId: state.runId,
    stateDigest: mathDigest(canonicalMathJson(state)),
    resultDigest: result ? mathDigest(canonicalMathJson(result)) : null };
}

/** Reading a checkpoint does not revalidate its stored Lean evidence. */
export function readRunInspection(run: string) {
  const input = path.resolve(run);
  const stateFile = path.basename(input) === 'state.json' ? input : `${input}.runtime/state.json`;
  const state = readSolverRunState(stateFile);
  const resultFile = stateFile === input ? undefined : input;
  const result = resultFile && fs.existsSync(resultFile) ? readMathJson(resultFile) as Record<string, unknown> : undefined;
  if (result && (result.schema !== 'deepscientist.math.run.v2' || result.runId !== state.runId ||
      path.resolve(String(result.stateFile)) !== stateFile)) throw new Error('math_inspect_result_identity_mismatch');
  return { stateFile, state, result, snapshot: runInspectionSnapshot(state, result) };
}

function proofRecord(node: TaskRecord, state: SolverRunState) {
  const proof = node.integratedCheck ?? node.proof;
  if (!proof) return { status: 'none' as const };
  return {
    status: recordedTaskProofStatus(node, state.environmentDigest),
    failureCategory: proof.passed ? undefined : ['blocked', 'unavailable'].includes(proof.verification.status) ? 'environment' : 'proof',
    commit: proof.commit, sourceDigest: proof.sourceDigest,
    conditions: proof.conditions ?? [],
    receiptIds: proof.verification.results.map(result => result.receiptId).filter(Boolean),
    actualReferences: proof.references,
  };
}

function dispatchWaitRecord(state: SolverRunState, observation?: DispatchWaitObservation) {
  if (!observation) return { status: 'unknown' as const };
  const stale = observation.planVersion !== undefined && observation.planVersion !== state.cooperation?.planVersion ||
    observation.candidates.some(candidate => !state.cooperation?.tasks.some(node =>
      node.task.id === candidate.taskId && taskVersion(node.task) === candidate.taskDigest));
  return { status: stale ? 'stale' as const : 'recorded' as const, observation };
}

export function buildRunInspection(state: SolverRunState, result?: Record<string, unknown>) {
  const cooperative = state.cooperation;
  const resultMatches = state.phase === 'finished' && result?.runId === state.runId &&
    (result.solution_commit === null || result.solution_commit === state.check?.commit) &&
    (result.status !== 'evaluated_passed' || Boolean(state.check?.passed && result.solution_commit === state.check.commit));
  const evaluator = resultMatches && result?.evaluator && typeof result.evaluator === 'object'
    ? result.evaluator as Record<string, unknown> : undefined;
  const tasks = cooperative?.tasks ?? [];
  const checked = tasks.filter(node => proofRecord(node, state).status === 'checked');
  const scheduled = (state.workers ?? []).filter(worker => worker.scheduling);
  const working = scheduled.filter(worker => worker.scheduling!.status === 'working');
  return {
    schema: 'deepscientist.math.inspection.v1', runId: state.runId,
    snapshot: runInspectionSnapshot(state, result),
    evidence: 'recorded-not-replayed', phase: state.phase,
    recordedOutcome: resultMatches ? result?.status : undefined,
    evaluator: evaluator ? { status: evaluator.status, method: evaluator.method, official: evaluator.official } : undefined,
    problem: { id: state.problem.contract.problemId, statement: state.problem.contract.informalStatement,
      formalStatement: state.problem.contract.formalStatement, assumptions: state.problem.contract.assumptions,
      targets: state.problem.targets },
    configuration: { model: state.model, effort: state.effort, workers: state.workerCount ?? 1,
      coordination: state.coordination ?? 'cooperative', modules: state.moduleConfiguration,
      buildDigest: state.buildDigest, environmentDigest: state.environmentDigest, methodDigest: state.methodDigest,
      knowledgeDigest: state.knowledgeDigest },
    turns: state.turns, usage: state.usage, planVersion: cooperative?.planVersion,
    scheduling: { evidence: 'recorded-dispatch-state', observedWorkers: scheduled.length,
      working: working.length,
      proofAssignments: working.filter(worker => tasks.some(node => node.task.id === worker.scheduling!.taskId &&
        ['lemma', 'goal'].includes(node.task.kind))).length,
      preparing: scheduled.filter(worker => worker.scheduling!.status === 'preparing').length,
      stopping: scheduled.filter(worker => worker.scheduling!.status === 'stopping').length,
      idle: scheduled.filter(worker => worker.scheduling!.status === 'idle').length,
      stopped: scheduled.filter(worker => worker.scheduling!.status === 'stopped').length,
      capacityRefill: cooperative?.lastCapacityRefill },
    knowledge: { status: state.knowledgeDigest ? 'enabled' : 'disabled', catalogDigest: state.knowledgeDigest,
      evidence: 'recorded-not-replayed', attribution: 'model-reported-origin',
      retrievalCoverage: state.knowledgeRetrievals ? 'recorded' : 'unknown',
      droppedRetrievals: state.knowledgeRetrievals?.dropped ?? 0, retrievals: state.knowledgeRetrievals?.observations ?? [],
      originalUses: state.knowledgeUses ?? [],
      uses: (cooperative?.deliveries ?? []).filter(delivery => delivery.status !== 'superseded').flatMap(delivery =>
        (delivery.knowledgeUses ?? []).map(use => ({ ...use, deliveryId: delivery.id, commit: delivery.commit,
          currentTaskVersion: tasks.some(node => node.task.id === use.consumer.taskId && taskVersion(node.task) === use.consumer.taskDigest) }))) },
    tokenBudget: buildTokenBudget(state.tokenBudget?.maxTotalTokens ?? 0, state.workers ?? [state], state.tokenBudget?.enforcement),
    continuation: buildProofContinuation(tasks, { groups: cooperative?.groups, environmentDigest: state.environmentDigest,
      proofRoutes: cooperative?.proofRoutes, researchHandoffs: cooperative ? researchHandoffs(cooperative) : [] }),
    mathematics: { snapshot: captureObligationSnapshot(tasks, { groups: cooperative?.groups, environmentDigest: state.environmentDigest,
      blockers: cooperative?.blockers, proofRoutes: cooperative?.proofRoutes }),
      recentChanges: cooperative?.progressReceipts ?? [], retainedChangeLimit: 64 },
    progress: { checkedProofTasks: checked.length,
      conditionalProofTasks: tasks.filter(node => proofRecord(node, state).status === 'conditional').length,
      completedResearchTasks: tasks.filter(node => ['research', 'sketch'].includes(node.task.kind) && node.status === 'completed').length,
      openProofTasks: tasks.filter(node => ['lemma', 'goal'].includes(node.task.kind) && !checked.includes(node)).map(node => node.task.id) },
    waiting: cooperative?.frontierWaiting ? { ...cooperative.frontierWaiting } : undefined,
    groups: cooperative?.groups ?? [],
    tasks: (cooperative?.tasks ?? []).map(node => ({
      id: node.task.id, kind: node.task.kind, objective: node.task.objective,
      group: taskGroup(node.task), status: node.status, control: node.task.status ?? 'active',
      ...(node.capacityExploration ? { capacityExploration: node.capacityExploration } : {}),
      owner: node.task.ownerId ?? node.assignment?.workerId,
      version: taskVersion(node.task), theorem: node.task.theoremName, type: node.task.type,
      informalStatement: node.task.informalStatement, premises: node.task.premises ?? [],
      plannedDependencies: node.task.dependsOn, attempts: node.attempts,
      proof: proofRecord(node, state), feedback: node.feedback, feedbackCategory: researchFailureCategory(node.feedback), finding: node.finding,
      parkedBy: node.routeParking ?? [],
      parkedRoutes: node.parkedRoutes ?? {},
    })),
    workers: (state.workers ?? [{ id: 'solver', role: 'lead', ...state }]).map(worker => ({
      id: worker.id, role: worker.role, sessionRole: 'sessionRole' in worker ? worker.sessionRole : undefined,
      phase: worker.phase, turns: worker.turns,
      scheduling: 'scheduling' in worker ? worker.scheduling : undefined,
      dispatchWait: dispatchWaitRecord(state, 'scheduling' in worker ? worker.scheduling?.wait : undefined),
      usage: worker.usage,
      lastActivity: worker.lastActivity,
      lastFailure: worker.lastFailure && { ...worker.lastFailure, category: researchFailureCategory(worker.lastFailure.reason) },
      recovery: worker.recovery && { ...worker.recovery, category: researchFailureCategory(worker.recovery.reason) },
      task: 'scheduling' in worker && worker.scheduling ? worker.scheduling.taskId :
        'sessionTaskId' in worker ? worker.sessionTaskId : undefined,
      context: worker.lastContextManifest,
      failures: worker.failures, error: 'error' in worker ? worker.error : undefined,
      failureCategory: researchFailureCategory(worker.error),
    })),
    statementReviews: (cooperative?.statementReviews ?? []).map(review => ({
      taskId: review.taskId, version: review.taskDigest, status: review.status,
      intendedStatement: review.intendedStatement, leanStatement: review.leanStatement,
      translation: review.translation, summary: review.summary,
    })),
    review: cooperative?.review, edits: cooperative?.edits ?? [], error: cooperative?.error ?? state.error,
    failureCategory: researchFailureCategory(cooperative?.error ?? state.error),
  };
}

export function exportRunPlan(state: SolverRunState) {
  if (!state.cooperation?.planVersion || !state.cooperation.tasks.length) throw new Error('math_edit_plan_unavailable');
  return { schema: 'deepscientist.math.plan-edit.v1', baseVersion: state.cooperation.planVersion,
    tasks: state.cooperation.tasks.map(node => node.task), groups: state.cooperation.groups?.map(record => record.group),
    ...(state.cooperation.proofRoutes?.length ? { proofRoutes: state.cooperation.proofRoutes } : {}) };
}

type Inspection = ReturnType<typeof buildRunInspection> & {
  artifacts?: StoredRunInspectionArtifacts;
  contributionFlow?: ResearchContributionFlow;
};
const cell = (value: unknown) => String(value ?? '—').replaceAll('|', '\\|').replace(/[\r\n]+/gu, ' ').replaceAll('`', "'");
const table = (headers: string[], rows: unknown[][]) => [headers, headers.map(() => '---'), ...rows]
  .map(row => `| ${row.map(cell).join(' | ')} |`).join('\n');
const section = (title: string, text: string) => `\n## ${title}\n\n${text}\n`;

function observation(value: ContributionObservation<number>, suffix = ''): string {
  return value.status === 'recorded' ? String(value.value) + suffix : value.status + ' (' + value.reason + ')';
}

function renderStoredArtifacts(artifacts: StoredRunInspectionArtifacts): string {
  const journal = artifacts.journal;
  let text = section('Stored artifacts', table(['State', 'Result', 'Journal source', 'Read status', 'Run binding', 'Coverage'], [[
    artifacts.stateFile, artifacts.resultFile ?? 'absent', journal.source, journal.status, journal.runBinding, journal.coverage,
  ]]));
  if (journal.file) text += '\nJournal: ' + cell(journal.file) + '; prefix digest: ' + (journal.digest ?? 'unknown') +
    '; bytes: ' + journal.bytesRead + '; ignored lines: ' + journal.ignoredLines +
    '; prefix limited: ' + journal.truncated + '; incomplete tail bytes: ' + journal.incompleteTailBytes + '.\n';
  if (journal.batchFile) text += '\nBatch mapping: ' + cell(journal.batchFile) + '.\n';
  if (journal.diagnostics.length) text += '\nJournal diagnostics: ' + journal.diagnostics.map(cell).join(', ') + '.\n';
  text += '\nState and journal are separate observations; the captured prefix does not establish complete event coverage.\n';
  const continuation = artifacts.continuation;
  if (continuation.status === 'recorded') {
    text += section('Frozen continuation source', table(['Source run', 'Frozen state digest', 'Source build', 'Source method', 'Source commit', 'Source plan'], [[
      continuation.source.runId, continuation.source.stateDigest, continuation.source.buildDigest, continuation.source.methodDigest,
      continuation.source.canonicalCommit, continuation.source.planVersion,
    ]]));
    text += '\nSnapshot: ' + continuation.snapshotDigest + '; seed-history: ' + continuation.attachment.sha256 +
      '; captured at: ' + continuation.capturedAt + '; evidence: ' + continuation.evidence + '.\n';
    text += '\nSource state attribution: ' + cell(continuation.source.stateFile) +
      '. Only frozen provenance is shown; historical execution is not merged into this run.\n';
  } else if (continuation.status === 'unknown') text += section('Frozen continuation source',
    'unknown (' + cell(continuation.reason) + '); snapshot: ' + continuation.snapshotDigest + '.');
  return text;
}

function renderContributionFlow(flow: ResearchContributionFlow): string {
  let text = section('Contribution flow', 'Evidence: ' + flow.evidence + '; journal binding: ' + flow.coverage.journal +
    '; decision history: ' + flow.coverage.decisionHistory + '; execution history: ' + flow.coverage.executionHistory + '.');
  text += '\nTimes are recorded Unix milliseconds; elapsed values require exact identities and both endpoints. ' +
    'The first observed start belongs to the supplied journal prefix. Missing evidence and clock/order conflicts remain unknown or ambiguous.\n';
  text += section('Research sources', flow.sources.length ? table([
    'Delivery', 'Source task / version', 'Status', 'Current version', 'Created', 'Published in this run', 'Handoff aliases', 'Proposals',
  ], flow.sources.map(source => [source.deliveryId, source.taskId + '@' + source.taskDigest, source.status, source.currentTaskVersion,
    observation(source.created), observation(source.publication), source.handoffAliases.map(item => item.handoffId).join(', ') || 'none recorded',
    source.proposals.map(item => item.task.id + '@' + item.taskDigest).join(', ') || 'none recorded',
  ])) : 'No research deliveries recorded.');
  if (flow.handoffs.length) text += section('Current handoffs', table([
    'Handoff', 'Proposal', 'Status', 'Context', 'Activation', 'Source deliveries',
  ], flow.handoffs.map(item => [item.id, item.proposal.id, item.status, item.contextDigest, item.activationDigest,
    item.sources.map(source => source.deliveryId).join(', ')])));
  text += section('Handoff decision observations', flow.decisionOccurrences.length || flow.storedDecisions.length ? table([
    'Evidence', 'Handoff', 'Delivery', 'Decision', 'Context', 'Activation', 'Plan', 'Task / version', 'At',
    'Publication to decision', 'Decision to first observed start',
  ], [
    ...flow.decisionOccurrences.map(item => ['journal line ' + item.evidence.line, item.id, item.deliveryId, item.status,
      item.contextDigest, item.activationDigest, item.planVersion,
      item.taskId ? item.taskId + '@' + item.taskDigest : 'none recorded', observation(item.at),
      observation(item.publicationToDecisionMs, ' ms'), observation(item.decisionToFirstObservedStartMs, ' ms')]),
    ...flow.storedDecisions.map(item => [item.evidence.path + ' (stored latest)', item.id, item.deliveryId, item.status,
      item.contextDigest, 'unknown', 'unknown', item.taskId ? item.taskId + '@' + item.taskDigest : 'none recorded',
      observation(item.at), 'unknown', 'unknown']),
  ]) : 'No decision records available.');
  text += '\nStored latest decisions are separate from journal occurrences. Deferred and repeated decisions remain separate; adoption creates a proof obligation.\n';
  text += section('Versioned contribution obligations', flow.obligations.length ? table([
    'Task / version', 'Current version', 'Execution', 'Assignments', 'Check IDs', 'Planned consumers',
    'Proof consumers', 'Statement consumers', 'Conditional consumers', 'Reference coverage',
  ], flow.obligations.map(item => [item.taskId + '@' + item.taskDigest, item.currentTaskVersion, item.status,
    item.attempts.length, item.checkIds.join(', ') || 'none recorded', item.uses?.plannedConsumers.join(', ') || 'none recorded',
    item.uses?.proofConsumers.join(', ') || 'none recorded', item.uses?.statementConsumers.join(', ') || 'none recorded',
    item.uses?.conditionalConsumers.join(', ') || 'none recorded', item.referenceCoverage,
  ])) : 'No typed contribution obligations recorded.');
  const attempts = [...new Map([
    ...flow.obligations.flatMap(item => item.attempts), ...flow.sources.flatMap(item => item.attempts),
  ].map(attempt => [JSON.stringify([attempt.assignmentKey, attempt.taskId, attempt.taskDigest]), attempt])).values()];
  if (attempts.length) {
    text += section('Contribution execution observations', table([
      'Task / version', 'Assignment', 'Worker', 'Identity', 'Assignment occurrences', 'Assigned',
      'Observed starts', 'First observed start', 'Assignment to start',
    ], attempts.map(item => [item.taskId + '@' + item.taskDigest, item.assignmentKey, item.workerId,
      item.identity.status, item.assignments.length, observation(item.assigned), item.starts.length,
      observation(item.firstObservedStart), observation(item.assignedToFirstObservedStartMs, ' ms')])));
    const starts = attempts.flatMap(item => item.starts.map(start => [item.assignmentKey, start.turnId, start.threadId, observation(start.at),
      start.evidence.kind === 'journal' ? 'journal line ' + start.evidence.line : start.evidence.path]));
    if (starts.length) text += section('Recorded task starts', table(['Assignment', 'Turn', 'Thread', 'At', 'Evidence'], starts));
    const readiness = attempts.flatMap(item => item.ready.map(ready => [ready.id, item.taskId + '@' + item.taskDigest,
      item.assignmentKey, ready.status, ready.evidenceKind, JSON.stringify(ready.conditions), ready.snapshotCommit,
      observation(ready.requested), observation(ready.frozen), ready.checkIds.join(', ') || 'none recorded',
      observation(ready.readyToCheckMs, ' ms'), observation(ready.frozenToCheckMs, ' ms')]));
    if (readiness.length) text += section('Readiness and frozen checks', table([
      'Ready ID', 'Task / version', 'Assignment', 'Status', 'Evidence kind', 'Conditions', 'Snapshot',
      'Requested', 'First frozen', 'Check IDs', 'Ready to verification start', 'Frozen to verification start',
    ], readiness));
  }
  if (flow.checks.length) text += section('Contribution check observations', table([
    'Check ID', 'Task / version', 'Source commit', 'Lean receipts', 'Stored as / proof status', 'Ready IDs',
    'Evidence kind', 'Conditions', 'Verification start', 'Verification end', 'Integrated', 'Check duration', 'Check end to integration',
  ], flow.checks.map(item => [item.id, item.taskId + '@' + (item.taskDigest ?? 'unknown'), item.commit,
    item.receiptIds.join(', ') || 'unknown', item.storedAs.map(record => record.kind + ': ' + record.recordedProof).join('; '),
    item.readyIds.join(', ') || 'none recorded', item.evidenceKind, JSON.stringify(item.conditions),
    observation(item.started), observation(item.checked), observation(item.integrated),
    observation(item.checkDurationMs, ' ms'), observation(item.checkedToIntegratedMs, ' ms')]))) +
    '\nA stored check can appear at multiple paths under one Check ID. Ready IDs identify submissions; Lean receipts identify checks. ' +
    'Worker snapshots and merged commits are connected only by their exact recorded check identities. Cached verification can predate readiness; no waiting time is inferred in that case.\n';
  if (flow.modelReportedUses.length) text += section('Model-reported contribution origins', table([
    'Entry', 'Consumer', 'Declaration', 'Status', 'Origin', 'Delivery',
  ], flow.modelReportedUses.map(item => [item.id, item.consumer?.taskId, item.declaration?.name, item.status, item.attribution,
    'deliveryId' in item ? item.deliveryId : 'run-original']))) +
    '\nReported origins do not establish historical authorship. Recorded proof, statement and conditional consumers are shown separately above.\n';
  if (flow.unresolved.length) text += section('Unresolved contribution records', table(['Event', 'Evidence', 'Reason'],
    flow.unresolved.map(item => [item.event, item.evidence.kind === 'journal' ? 'journal line ' + item.evidence.line : item.evidence.path, item.reason])));
  return text;
}

export function renderRunInspection(report: Inspection): string {
  let text = '# Mathematics research run\n\nStored evidence only; this report does not rerun Lean or grant proof acceptance.\n';
  text += section('Run', table(['Problem', 'Phase', 'Recorded outcome', 'Model', 'Agents', 'Turns'], [[
    report.problem.id, report.phase, report.recordedOutcome, report.configuration.model, report.configuration.workers, report.turns]]));
  text += `\nObservation: ${report.snapshot.stateDigest}; result: ${report.snapshot.resultDigest ?? 'absent'}.\n`;
  text += `\n${report.problem.statement}\n\nRun: ${report.runId}\n\nPlan version: ${report.planVersion ?? 'not yet planned'}\n`;
  text += section('Model usage', table(['Shared token allowance', 'Reported tokens', 'Complete usage', 'Observed overrun', 'Dispatch status'], [[
    report.tokenBudget.maxTotalTokens || 'unlimited', report.tokenBudget.reportedTotalTokens,
    report.tokenBudget.usageComplete, report.tokenBudget.overrunTokens, report.tokenBudget.status]]));
  text += '\nThe allowance stops new model turns using provider reports. In-flight turns may exceed it; missing reports leave consumption incomplete. No monetary cost is inferred.\n';
  if (report.artifacts) text += renderStoredArtifacts(report.artifacts);
  if (report.contributionFlow) text += renderContributionFlow(report.contributionFlow);
  const knowledgeUses = [...report.knowledge.originalUses, ...report.knowledge.uses];
  text += section('Knowledge observations', table(['Catalog', 'Retrieval coverage', 'Included sections', 'Omitted sections', 'Reported attempts', 'Checked references'], [[
    report.knowledge.status, report.knowledge.retrievalCoverage,
    report.knowledge.retrievals.filter(item => item.included).length,
    report.knowledge.retrievals.filter(item => !item.included).length,
    knowledgeUses.filter(item => item.status === 'reported-attempt').length,
    knowledgeUses.filter(item => item.status === 'checked-reference').length]]));
  if (report.knowledge.catalogDigest) text += `\nPinned catalog: ${report.knowledge.catalogDigest}. ` +
    `Dropped retrieval observations: ${report.knowledge.droppedRetrievals}. ` +
    'Usage origins are model-reported; checked references confirm a declaration in a recorded proof, not historical authorship or current acceptance.\n';
  text += section('Original targets', table(['Declaration', 'File'], report.problem.targets.map(target => [target.theoremName, target.proofPath])));
  text += section('Recorded progress', `${report.progress.checkedProofTasks} checked proof tasks; ${report.progress.conditionalProofTasks} conditional; ${report.progress.completedResearchTasks} completed research tasks.\n\nOpen proof tasks: ${report.progress.openProofTasks.join(', ') || 'none'}. Dispatch counts include retries and do not measure mathematical progress.`);
  if (report.waiting) text += section('Waiting for input', `${report.waiting.reason}${report.waiting.investigation
    ? `; investigation ${report.waiting.investigation.state}${report.waiting.investigation.reason ? ` (${report.waiting.investigation.reason})` : ''}` : ''}
Waiting is a scheduling state, not a mathematical failure. An abandoned or rejected advisory investigation produced no accepted finding.`);
  text += section('Proof continuation', table(['Original goal', 'Recorded proof', 'Open dependency frontier', 'Missing tasks'],
    report.continuation.goals.map(goal => [goal.taskId, goal.recordedProof, goal.frontier.join(', ') || 'none', goal.missingDependencies.join(', ') || 'none'])));
  const transitions = report.mathematics.recentChanges.filter(receipt => receipt.kind === 'transition').slice(-12);
  text += section('Mathematical changes', transitions.length ? table([
    'At', 'Locally checked obligations', 'Reopened obligations', 'Goal frontiers changed', 'Blockers parked / reopened', 'Advisory completed',
  ], transitions.map(receipt => [new Date(receipt.at).toISOString(), receipt.obligations.closed.map(change => change.after.taskId).join(', ') || 'none',
    receipt.obligations.reopened.map(change => change.after.taskId).join(', ') || 'none',
    receipt.goalFrontiers.map(change => `${change.goalId}: ${change.before?.frontier.map(item => item.taskId).join(', ') || 'none'} → ${change.after?.frontier.map(item => item.taskId).join(', ') || 'none'}`).join('; ') || 'none',
    `${receipt.blockers.parked.map(change => change.after.id).join(', ') || 'none'} / ${receipt.blockers.reopened.map(change => change.after.id).join(', ') || 'none'}`,
    receipt.advisory.completed.map(change => change.after.taskId).join(', ') || 'none',
  ])) : 'No mathematical transitions recorded in this checkpoint.');
  text += '\nLocal obligation checks, advisory findings and original-goal frontiers are separate. The retained window contains at most 64 changes; the event journal retains emitted transitions. Official acceptance is shown only under Evaluation.\n';
  if (report.mathematics.snapshot.routes.length) text += section('Alternative proof routes', table([
    'Route', 'Original goal', 'All prerequisites', 'Still open', 'Closing declaration', 'Closing evidence', 'Evidence ready', 'Branch control', 'Parked by', 'Original connection',
  ], report.mathematics.snapshot.routes.map(route => [route.routeId, route.targetTaskId, route.prerequisiteTaskIds.join(', ') || 'none',
    route.remainingPrerequisiteTaskIds.join(', ') || 'none', route.closingTaskId, route.closingStatus, route.ready,
    route.parkedBy.length ? 'parked' : 'active', route.parkedBy.join(', ') || 'none', route.connection]))) +
    '\nRoutes are alternatives (OR); prerequisites within each route are required together (AND). Checked helpers enable an original-goal attempt; the goal still needs its own check.\n';
  if (report.mathematics.snapshot.blockers.length) text += section('Local route blockers', table([
    'Blocker', 'Task', 'Alternative branch', 'Mechanism', 'Affected inference', 'Scheduling state', 'Evidence', 'Reopen conditions',
  ], report.mathematics.snapshot.blockers.map(blocker => [blocker.id, blocker.taskId, blocker.routeId ?? 'whole task', blocker.mechanism, blocker.scope,
    blocker.status, blocker.evidenceStatus, JSON.stringify(blocker.reopenOn)]))) +
    '\nParking applies to the recorded alternative branch or whole task shown above. Other branches can continue. An advisory obstruction does not refute the original theorem.\n';
  text += '\nConsumers with checked inputs and completed planned dependencies: ' +
    (report.continuation.continuationCandidates.join(', ') || 'none') + '.\n';
  text += section('Recorded lemma reuse', report.continuation.reuse.length ?
    table(['Lemma', 'Planned consumers', 'Verified proof consumers', 'Statement references', 'Conditional consumers'],
      report.continuation.reuse.map(item => [item.taskId, item.plannedConsumers.join(', ') || 'none',
        item.proofConsumers.join(', ') || 'none recorded', item.statementConsumers.join(', ') || 'none recorded',
        item.conditionalConsumers.join(', ') || 'none recorded'])) : 'No integrated lemmas with current recorded receipts.');
  if (report.continuation.adoptedResearch.length) text += section('Adopted research', table([
    'Source task', 'Adopted lemma', 'Recorded proof', 'Planned original goals', 'Proof consumers', 'Statement references', 'Conditional consumers', 'Reference coverage',
  ], report.continuation.adoptedResearch.map(item => [item.sourceTaskId, item.taskId, item.recordedProof,
    item.plannedGoalIds.join(', ') || 'none', item.proofConsumers.join(', ') || 'none recorded',
    item.statementConsumers.join(', ') || 'none recorded', item.conditionalConsumers.join(', ') || 'none recorded',
    item.referenceCoverage]))) + '\nAdoption schedules a proof obligation. Missing reference coverage leaves actual use unknown.\n';
  text += '\nTasks without a planned path to an active original goal: ' +
    (report.continuation.unconnectedTasks.join(', ') || 'none') + '. This does not establish that a result is mathematically unhelpful.\n';
  if (report.continuation.referenceCoverageMissing.length) text += '\nActual-reference evidence unavailable for: ' +
    report.continuation.referenceCoverageMissing.join(', ') + '.\n';
  text += section('Scheduling', `Recorded active dispatches: ${report.scheduling.working}; proof assignments: ${report.scheduling.proofAssignments}; ` +
    `preparing: ${report.scheduling.preparing}; stopping: ${report.scheduling.stopping}; idle: ${report.scheduling.idle}. ` +
    'These checkpoint observations do not establish current process liveness or mathematical progress.');
  text += section('Workers', table(['Worker', 'Role', 'Session role', 'Scheduling', 'Phase', 'Task', 'Last activity', 'At'], report.workers.map(worker => [
    worker.id, worker.role, worker.sessionRole, worker.scheduling?.status ?? 'unknown', worker.phase, worker.task, worker.lastActivity?.event,
    worker.lastActivity ? new Date(worker.lastActivity.at).toISOString() : undefined])));
  text += section('Recorded dispatch waits', table([
    'Worker', 'Observation', 'Stage / gate', 'Observed at', 'Ended at', 'Plan version', 'Candidates shown / total', 'Recorded exclusions',
  ], report.workers.map(worker => {
    const wait = worker.dispatchWait.observation;
    return [worker.id, worker.dispatchWait.status, wait && `${wait.stage}${wait.gate ? ` / ${wait.gate}` : ''}`,
      wait && new Date(wait.observedAt).toISOString(), wait?.endedAt !== undefined ? new Date(wait.endedAt).toISOString() : undefined,
      wait && (wait.planVersion ?? 'unrecorded'),
      wait && `${wait.candidates.length} / ${wait.candidateCount}${wait.omittedCandidates ? ` (${wait.omittedCandidates} omitted)` : ''}`,
      wait ? wait.candidates.map(candidate => `${candidate.taskId}@${candidate.taskDigest}: ${candidate.reason}`).join('; ') || 'none recorded'
        : 'not recorded'];
  }))) + '\nThese are stored dispatch observations; scheduling is not replayed. Stale means a recorded plan or task identity differs from this checkpoint. ' +
    'An Ended at timestamp marks a completed historical observation. Observed at is an observation time, not the start of a cause or a waiting duration. ' +
    'No reason is inferred from scheduling.since; absent observations remain unknown.\n';
  const recoveries = report.workers.filter(worker => worker.recovery);
  if (recoveries.length) text += section('Session recovery', table([
    'Worker', 'Recovery', 'Category', 'Reason', 'Cycles', 'Next retry', 'Waited ms',
  ], recoveries.map(worker => {
    const recovery = worker.recovery!;
    return [worker.id, recovery.phase === 'recovered' ? 'recovered (history)' : recovery.phase,
      recovery.category, recovery.reason, recovery.cycles,
      recovery.phase === 'cooling-down' ? new Date(recovery.nextRetryAt).toISOString() : undefined, recovery.waitedMs];
  })));
  const failures = report.workers.filter(worker => worker.lastFailure || worker.error);
  if (failures.length) text += section('Execution failures', table(['Worker', 'Category', 'Last failure', 'At'], failures.map(worker => [
    worker.id, worker.failureCategory ?? worker.lastFailure?.category, worker.error ?? worker.lastFailure?.reason,
    worker.lastFailure ? new Date(worker.lastFailure.at).toISOString() : undefined])));
  text += section('Routes', report.groups.length ? table(['Route', 'Objective', 'Control', 'Engineer', 'Turns'],
    report.groups.map(({ group, turns }) => [group.id, group.objective, group.status, group.engineerId, turns])) : 'No cooperative routes recorded.');
  text += section('Tasks', report.tasks.length ? table(['Task', 'Kind', 'Owner', 'Execution', 'Proof record', 'Planned dependencies'],
    report.tasks.map(task => [task.id, task.kind, task.owner, task.status,
      task.proof.status + ('failureCategory' in task.proof && task.proof.failureCategory ? ` (${task.proof.failureCategory})` : ''),
      task.plannedDependencies.join(', ')])) : 'No cooperative tasks recorded.');
  for (const task of report.tasks) {
    text += section(`Task: ${cell(task.id)}`, task.objective);
    text += `\nControl: ${task.control}; dispatches (including retries): ${task.attempts}; version: ${task.version}\n`;
    if (task.theorem) text += `\nDeclaration: ${task.theorem}\n`;
    if (task.type) text += `\nLean type: ${task.type}\n`;
    if (task.informalStatement) text += `\nMathematical intent: ${task.informalStatement}\n`;
    if (task.premises.length) text += `\nPremises: ${task.premises.join('; ')}\n`;
    if (task.feedback) text += `\nCurrent feedback (${task.feedbackCategory}): ${task.feedback}\n`;
    if (task.parkedBy.length) text += `\nParked by local blockers: ${task.parkedBy.join(', ')}\n`;
    for (const [routeId, blockers] of Object.entries(task.parkedRoutes)) if (blockers.length)
      text += `\nAlternative branch ${cell(routeId)} parked by local blockers: ${blockers.map(cell).join(', ')}\n`;
    if (task.finding) text += `\nResearch finding: ${task.finding}\n`;
    if ('commit' in task.proof) {
      text += `\nRecorded commit: ${task.proof.commit}\n\nReceipt IDs: ${task.proof.receiptIds.join(', ') || 'none'}\n`;
      if (task.proof.conditions.length) text += `\nOpen conditions: ${task.proof.conditions.map(item => item.taskId).join(', ')}\n`;
      const references = task.proof.actualReferences;
      text += '\nActual Lean references: ' + (references ? JSON.stringify(references) : 'not recorded') + '\n';
    }
  }
  text += section('Statement reviews', report.statementReviews.length ? report.statementReviews.map(review =>
    `Task: ${review.taskId}; recorded status: ${review.status}\n\nIntent: ${review.intendedStatement}\n\nLean: ${review.leanStatement}\n\nBacktranslation: ${review.translation?.mathematics ?? 'pending'}\n\n${review.summary ?? ''}`).join('\n\n---\n\n') : 'No statement reviews recorded.');
  text += section('Candidate review', report.review ? `${report.review.status}; commit: ${report.review.commit}\n\n${report.review.summary ?? ''}` : 'No candidate review recorded.');
  text += section('Human edits', report.edits.length ? table(['Edit', 'Application', 'Proof recheck', 'Affected tasks', 'Reason'],
    report.edits.map(edit => [edit.id, edit.status, edit.recheck?.status, edit.affectedTasks?.join(', '), edit.reason])) : 'No human edits recorded.');
  if (report.error) text += section('Current blocker', report.error);
  text += section('Evaluation', report.evaluator ? JSON.stringify(report.evaluator, null, 2) : 'No matching final evaluation recorded.');
  return text;
}
