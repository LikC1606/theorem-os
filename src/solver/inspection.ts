import fs from 'node:fs';
import path from 'node:path';
import { readSolverRunState, type SolverRunState } from './archive';
import { readMathJson } from '../math/mathRuntimeIo';
import { taskGroup, taskVersion, type TaskRecord } from './tasks';

/** Reading a checkpoint does not revalidate its stored Lean evidence. */
export function readRunInspection(run: string) {
  const input = path.resolve(run);
  const stateFile = path.basename(input) === 'state.json' ? input : `${input}.runtime/state.json`;
  const state = readSolverRunState(stateFile);
  const resultFile = stateFile === input ? undefined : input;
  const result = resultFile && fs.existsSync(resultFile) ? readMathJson(resultFile) as Record<string, unknown> : undefined;
  if (result && (result.schema !== 'deepscientist.math.run.v2' || result.runId !== state.runId ||
      path.resolve(String(result.stateFile)) !== stateFile)) throw new Error('math_inspect_result_identity_mismatch');
  return { stateFile, state, result };
}

function proofRecord(node: TaskRecord, state: SolverRunState) {
  const proof = node.integratedCheck ?? node.proof;
  if (!proof) return { status: 'none' as const };
  const stale = proof.taskDigest !== taskVersion(node.task) ||
    Boolean(proof.references && proof.references.environmentDigest !== state.environmentDigest);
  const hasReceipts = proof.verification.status === 'kernel_verified' && proof.verification.targetCommit === proof.commit &&
    proof.verification.results.length > 0 && proof.verification.results.every(result =>
      result.status === 'kernel_verified' && result.targetCommit === proof.commit && result.receiptId);
  return {
    status: stale ? 'stale' : !proof.passed ? 'failed' : !hasReceipts ? 'unverified' : proof.conditions?.length ? 'conditional' : 'checked',
    commit: proof.commit, sourceDigest: proof.sourceDigest,
    conditions: proof.conditions ?? [],
    receiptIds: proof.verification.results.map(result => result.receiptId).filter(Boolean),
    actualReferences: proof.references,
  };
}

export function buildRunInspection(state: SolverRunState, result?: Record<string, unknown>) {
  const cooperative = state.cooperation;
  const resultMatches = state.phase === 'finished' && result?.runId === state.runId &&
    (result.solution_commit === null || result.solution_commit === state.check?.commit) &&
    (result.status !== 'evaluated_passed' || Boolean(state.check?.passed && result.solution_commit === state.check.commit));
  const evaluator = resultMatches && result?.evaluator && typeof result.evaluator === 'object'
    ? result.evaluator as Record<string, unknown> : undefined;
  return {
    schema: 'deepscientist.math.inspection.v1', runId: state.runId,
    evidence: 'recorded-not-replayed', phase: state.phase,
    recordedOutcome: resultMatches ? result?.status : undefined,
    evaluator: evaluator ? { status: evaluator.status, method: evaluator.method, official: evaluator.official } : undefined,
    problem: { id: state.problem.contract.problemId, statement: state.problem.contract.informalStatement,
      formalStatement: state.problem.contract.formalStatement, assumptions: state.problem.contract.assumptions,
      targets: state.problem.targets },
    configuration: { model: state.model, effort: state.effort, workers: state.workerCount ?? 1,
      coordination: state.coordination ?? 'cooperative', modules: state.moduleConfiguration,
      buildDigest: state.buildDigest, environmentDigest: state.environmentDigest, methodDigest: state.methodDigest },
    turns: state.turns, usage: state.usage, planVersion: cooperative?.planVersion,
    groups: cooperative?.groups ?? [],
    tasks: (cooperative?.tasks ?? []).map(node => ({
      id: node.task.id, kind: node.task.kind, objective: node.task.objective,
      group: taskGroup(node.task), status: node.status, control: node.task.status ?? 'active',
      owner: node.task.ownerId ?? node.assignment?.workerId,
      version: taskVersion(node.task), theorem: node.task.theoremName, type: node.task.type,
      informalStatement: node.task.informalStatement, premises: node.task.premises ?? [],
      plannedDependencies: node.task.dependsOn, attempts: node.attempts,
      proof: proofRecord(node, state), feedback: node.feedback, finding: node.finding,
    })),
    workers: (state.workers ?? [{ id: 'solver', role: 'lead', ...state }]).map(worker => ({
      id: worker.id, role: worker.role, phase: worker.phase, turns: worker.turns,
      lastActivity: worker.lastActivity,
      task: 'sessionTaskId' in worker ? worker.sessionTaskId : undefined,
      failures: worker.failures, error: 'error' in worker ? worker.error : undefined,
    })),
    statementReviews: (cooperative?.statementReviews ?? []).map(review => ({
      taskId: review.taskId, version: review.taskDigest, status: review.status,
      intendedStatement: review.intendedStatement, leanStatement: review.leanStatement,
      translation: review.translation, summary: review.summary,
    })),
    review: cooperative?.review, edits: cooperative?.edits ?? [], error: cooperative?.error,
  };
}

export function exportRunPlan(state: SolverRunState) {
  if (!state.cooperation?.planVersion || !state.cooperation.tasks.length) throw new Error('math_edit_plan_unavailable');
  return { schema: 'deepscientist.math.plan-edit.v1', baseVersion: state.cooperation.planVersion,
    tasks: state.cooperation.tasks.map(node => node.task), groups: state.cooperation.groups?.map(record => record.group) };
}

type Inspection = ReturnType<typeof buildRunInspection>;
const cell = (value: unknown) => String(value ?? '—').replaceAll('|', '\\|').replace(/[\r\n]+/gu, ' ').replaceAll('`', "'");
const table = (headers: string[], rows: unknown[][]) => [headers, headers.map(() => '---'), ...rows]
  .map(row => `| ${row.map(cell).join(' | ')} |`).join('\n');
const section = (title: string, text: string) => `\n## ${title}\n\n${text}\n`;

export function renderRunInspection(report: Inspection): string {
  let text = '# Mathematics research run\n\nStored evidence only; this report does not rerun Lean or grant proof acceptance.\n';
  text += section('Run', table(['Problem', 'Phase', 'Recorded outcome', 'Model', 'Agents', 'Turns'], [[
    report.problem.id, report.phase, report.recordedOutcome, report.configuration.model, report.configuration.workers, report.turns]]));
  text += `\n${report.problem.statement}\n\nRun: ${report.runId}\n\nPlan version: ${report.planVersion ?? 'not yet planned'}\n`;
  text += section('Original targets', table(['Declaration', 'File'], report.problem.targets.map(target => [target.theoremName, target.proofPath])));
  text += section('Workers', table(['Worker', 'Phase', 'Task', 'Last activity', 'At'], report.workers.map(worker => [
    worker.id, worker.phase, worker.task, worker.lastActivity?.event,
    worker.lastActivity ? new Date(worker.lastActivity.at).toISOString() : undefined])));
  text += section('Routes', report.groups.length ? table(['Route', 'Objective', 'Control', 'Engineer', 'Turns'],
    report.groups.map(({ group, turns }) => [group.id, group.objective, group.status, group.engineerId, turns])) : 'No cooperative routes recorded.');
  text += section('Tasks', report.tasks.length ? table(['Task', 'Kind', 'Owner', 'Execution', 'Proof record', 'Planned dependencies'],
    report.tasks.map(task => [task.id, task.kind, task.owner, task.status, task.proof.status, task.plannedDependencies.join(', ')])) : 'No cooperative tasks recorded.');
  for (const task of report.tasks) {
    text += section(`Task: ${cell(task.id)}`, task.objective);
    text += `\nControl: ${task.control}; attempts: ${task.attempts}; version: ${task.version}\n`;
    if (task.theorem) text += `\nDeclaration: ${task.theorem}\n`;
    if (task.type) text += `\nLean type: ${task.type}\n`;
    if (task.informalStatement) text += `\nMathematical intent: ${task.informalStatement}\n`;
    if (task.premises.length) text += `\nPremises: ${task.premises.join('; ')}\n`;
    if (task.feedback) text += `\nCurrent feedback: ${task.feedback}\n`;
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
