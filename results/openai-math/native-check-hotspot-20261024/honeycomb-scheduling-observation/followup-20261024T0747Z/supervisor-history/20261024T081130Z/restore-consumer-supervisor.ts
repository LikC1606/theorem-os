import fs from 'node:fs';
import path from 'node:path';
import assert from 'node:assert/strict';
import { queueRunEdit } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/honeycomb-new-build-continuation-20261024/runtime/src/solver/humanEdit';
import { canonicalMathJson, mathDigest } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/honeycomb-new-build-continuation-20261024/runtime/src/math/mathRuntimeIo';
import { parseCooperationPlan, taskVersion, taskProofContractVersion } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/honeycomb-new-build-continuation-20261024/runtime/src/solver/tasks';

const stage = import.meta.dir;
const pause = JSON.parse(fs.readFileSync(path.join(stage, 'consumer-pause-preparation.json'), 'utf8'));
const run = pause.run as string;
const stateFile = run + '.runtime/state.json';
const editLog = run + '.runtime/edits.jsonl';
const statusFile = path.join(stage, 'supervisor-status.json');
const exitFile = path.join(stage, 'supervisor-exit.json');
const expectedRunId = '8bd4a613-c70e-4e96-b298-c9d22cfafaf3';
const expectedBuild = '7e2c42e897361d27b0aa6bf216f74ed7ba71aa32987771ade075193bed54c19f';
const expectedSums = pause.proposal.tasks.find((task: any) => task.id === 'sums_reduction');
const originalGoal = pause.originalGoalTask;
const prefix = 'honeycomb-consumer-resume-';
const startedAt = new Date().toISOString();
let exitReason = 'unexpected-exit';
let latest: any = { phase: 'starting' };
let lastObservation = '';
let lastError = '';

const log = (event: string, details: any = {}) => console.log(JSON.stringify({
  at: new Date().toISOString(), event, pid: process.pid, runId: expectedRunId, ...details,
}));
const saveStatus = () => {
  const temporary = statusFile + '.tmp-' + process.pid;
  fs.writeFileSync(temporary, JSON.stringify({ startedAt, observedAt: new Date().toISOString(),
    pid: process.pid, runId: expectedRunId, run, stateFile,
    noTotalTimeLimit: true, pollSeconds: 15, ...latest }, null, 2) + '\n');
  fs.renameSync(temporary, statusFile);
};
const finish = (reason: string, code = 0): never => {
  exitReason = reason;
  log('supervisor_exit', { reason, code, latest });
  process.exit(code);
};
process.on('exit', code => {
  fs.writeFileSync(exitFile, JSON.stringify({ startedAt, exitedAt: new Date().toISOString(),
    pid: process.pid, runId: expectedRunId, run, reason: exitReason, exitCode: code, latest }, null, 2) + '\n');
});
process.on('SIGTERM', () => finish('received-SIGTERM', 143));
process.on('SIGINT', () => finish('received-SIGINT', 130));
process.on('uncaughtException', error => {
  log('uncaught_exception', { error: String(error?.stack ?? error) });
  finish('uncaught-exception', 1);
});
process.on('unhandledRejection', error => {
  log('unhandled_rejection', { error: String(error) });
  finish('unhandled-rejection', 1);
});

function inspect() {
  const state = JSON.parse(fs.readFileSync(stateFile, 'utf8'));
  assert.equal(state.runId, expectedRunId);
  assert.equal(state.buildDigest, expectedBuild);
  assert.equal(mathDigest(canonicalMathJson(state.problem)), pause.problemSHA256);
  const cooperation = state.cooperation;
  const sums = cooperation.tasks.find((node: any) => node.task.id === expectedSums.id);
  const goal = cooperation.tasks.find((node: any) => node.task.id === originalGoal.id);
  assert(sums && goal, 'The monitored tasks must remain in the original graph.');
  assert.equal(taskProofContractVersion(sums.task), taskProofContractVersion(expectedSums));
  assert.equal(taskProofContractVersion(goal.task), taskProofContractVersion(originalGoal));
  const proof = sums.integratedCheck?.passed ? sums.integratedCheck : sums.proof;
  const accepted = proof?.passed === true && proof.taskDigest === taskVersion(sums.task) &&
    proof.verification?.status === 'kernel_verified' && !(proof.conditions?.length);
  const delivery = accepted && cooperation.deliveries.find((record: any) => record.kind === 'proof' &&
    record.taskId === sums.task.id && record.taskDigest === taskVersion(sums.task) &&
    record.commit === proof.commit && record.status !== 'superseded');
  const typedProof = delivery ? { taskDigest: proof.taskDigest, commit: proof.commit,
    deliveryId: delivery.id, deliveryStatus: delivery.status,
    verificationStatus: proof.verification.status,
    receipts: proof.verification.results?.map((result: any) => ({ receiptId: result.receiptId,
      status: result.status, targetCommit: result.targetCommit })) } : undefined;
  const engineer = state.workers.find((worker: any) => worker.id === 'engineer');
  return { state, cooperation, sums, goal, typedProof, engineer };
}

log('supervisor_started', { run, buildDigest: expectedBuild, noTotalTimeLimit: true,
  restorationCondition: 'Current exact sums task: native passed, kernel_verified, no extra task conditions, matching non-superseded proof delivery.',
  queueInterface: 'queueRunEdit, with full current graph and fresh baseVersion; validate before queue.',
  standaloneLeanOrModelsStarted: false });
saveStatus();

while (true) {
  try {
    const { state, cooperation, sums, goal, typedProof, engineer } = inspect();
    latest = { phase: typedProof ? 'native-typed-proof-observed' : 'waiting-for-native-typed-proof',
      runPhase: state.phase, turns: state.turns, planVersion: cooperation.planVersion,
      sumsStatus: sums.status, sumsTaskDigest: taskVersion(sums.task),
      sumsAssignmentId: sums.assignment?.assignmentId, engineerSessionTaskId: engineer?.sessionTaskId,
      goalSchedulingStatus: goal.task.status ?? 'active',
      typedProof: typedProof ?? null,
      failure: sums.proof?.passed === false || sums.status === 'blocked'
        ? { status: sums.status, verificationStatus: sums.proof?.verification?.status, feedback: sums.feedback } : null,
    };
    const observation = canonicalMathJson({ sumsStatus: latest.sumsStatus,
      sumsTaskDigest: latest.sumsTaskDigest, sumsAssignmentId: latest.sumsAssignmentId ?? null,
      engineerSessionTaskId: latest.engineerSessionTaskId ?? null,
      goalSchedulingStatus: latest.goalSchedulingStatus, typedProof: latest.typedProof, failure: latest.failure });
    if (observation !== lastObservation) {
      log('monitored_task_changed', latest);
      lastObservation = observation;
    }
    saveStatus();
    if (state.phase === 'finished') finish('known-run-finished');
    if (goal.task.status !== 'paused') finish('consumer-already-restored-or-scheduled-externally');
    if (typedProof) {
      const rows = fs.existsSync(editLog)
        ? fs.readFileSync(editLog, 'utf8').split('\n').filter(Boolean).map(line => JSON.parse(line)) : [];
      const previous = rows.filter((edit: any) => typeof edit.id === 'string' && edit.id.startsWith(prefix));
      const applied = previous.find((edit: any) => cooperation.edits?.some((record: any) => record.id === edit.id && record.status === 'applied'));
      if (applied) finish('normal-resume-edit-already-applied');
      const pending = previous.find((edit: any) => {
        const record = cooperation.edits?.find((item: any) => item.id === edit.id);
        return !record || record.status === 'received';
      });
      if (pending) {
        latest = { ...latest, phase: 'waiting-for-queued-resume-edit', editId: pending.id };
        saveStatus();
      } else {
        const id = prefix + cooperation.planVersion.slice(0, 12);
        const priorRecord = cooperation.edits?.find((record: any) => record.id === id);
        if (priorRecord?.status === 'rejected') {
          latest = { ...latest, phase: 'resume-edit-rejected-waiting-for-new-plan', editId: id, rejectionReason: priorRecord.reason };
          saveStatus();
        } else {
          const restored = { ...goal.task };
          if (Object.hasOwn(originalGoal, 'status')) restored.status = originalGoal.status;
          else delete restored.status;
          assert.equal(taskVersion(restored), taskVersion(goal.task));
          const proposal = { id, baseVersion: cooperation.planVersion,
            tasks: cooperation.tasks.map((node: any) => node.task.id === goal.task.id ? restored : node.task),
            groups: cooperation.groups.map((record: any) => record.group),
            ...(cooperation.proofRoutes ? { proofRoutes: cooperation.proofRoutes } : {}) };
          const normalized = parseCooperationPlan(state.problem, proposal);
          assert.deepEqual(normalized.tasks.map(task => task.id), cooperation.tasks.map((node: any) => node.task.id));
          for (const task of normalized.tasks) {
            const old = cooperation.tasks.find((node: any) => node.task.id === task.id).task;
            if (task.id === goal.task.id) {
              const omitStatus = ({ status: _status, ...rest }: any) => rest;
              assert.equal(canonicalMathJson(omitStatus(task)), canonicalMathJson(omitStatus(old)));
            } else assert.equal(canonicalMathJson(task), canonicalMathJson(old));
          }
          const validation = await queueRunEdit(run, proposal, true);
          log('normal_resume_dry_run', { editId: id, typedProof, validation });
          // Re-read the exact receipt immediately before mutation; a later task revision cannot authorize this edit.
          const fresh = inspect();
          assert(fresh.typedProof && fresh.typedProof.taskDigest === typedProof.taskDigest &&
            fresh.typedProof.commit === typedProof.commit);
          const result = await queueRunEdit(run, proposal);
          const receipt = { observedAt: new Date().toISOString(), runId: expectedRunId, run,
            editId: id, typedProof, proposal, validation, result,
            originalGoalPreserved: true, fullCurrentTaskGraphPreserved: true,
            allMathematicalTaskContractsPreserved: true,
            directStateWrites: false, directActiveSourceWrites: false, leanStarted: false, modelsStarted: false };
          const receiptPath = path.join(stage, 'supervisor-resume-' + id + '.json');
          if (!fs.existsSync(receiptPath)) fs.writeFileSync(receiptPath, JSON.stringify(receipt, null, 2) + '\n', { flag: 'wx' });
          latest = { ...latest, phase: 'normal-resume-queued', editId: id, receiptPath };
          log('normal_resume_queued', { editId: id, result, receiptPath });
          saveStatus();
        }
      }
    }
    lastError = '';
  } catch (error) {
    const message = String(error instanceof Error ? error.stack : error);
    latest = { ...latest, phase: 'inspection-or-queue-error-waiting', error: message };
    if (message !== lastError) log('inspection_or_queue_error', { error: message });
    lastError = message;
    saveStatus();
  }
  await Bun.sleep(15_000);
}
