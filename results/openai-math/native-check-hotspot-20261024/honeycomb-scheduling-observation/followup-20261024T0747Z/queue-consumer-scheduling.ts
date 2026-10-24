import fs from 'node:fs';
import path from 'node:path';
import assert from 'node:assert/strict';
import { queueRunEdit } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/honeycomb-new-build-continuation-20261024/runtime/src/solver/humanEdit';
import { canonicalMathJson, mathDigest } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/honeycomb-new-build-continuation-20261024/runtime/src/math/mathRuntimeIo';
import { parseCooperationPlan, taskVersion, taskProofContractVersion, assignmentDeliveryFile } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/honeycomb-new-build-continuation-20261024/runtime/src/solver/tasks';
import { readyResearchTasks } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/honeycomb-new-build-continuation-20261024/runtime/src/solver/modules/search';
import { assignSharedResearchTask } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/honeycomb-new-build-continuation-20261024/runtime/src/solver/modules/organization';
import { MAX_DELIVERY_LINE_BYTES, readDeliveryLines } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/honeycomb-new-build-continuation-20261024/runtime/src/solver/deliveries';

const stage = import.meta.dir;
const run = '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/tasks/HoneycombBridgeFiniteness/attempts/workflow-20261024/result.json';
const stateFile = run + '.runtime/state.json';
const mode = process.argv[2];
assert(['pause', 'resume'].includes(mode), 'Use pause or resume; add --queue only after dry-run.');
const stateBytes = fs.readFileSync(stateFile);
const state = JSON.parse(stateBytes.toString('utf8'));
const cooperation = state.cooperation;
assert.equal(state.runId, '8bd4a613-c70e-4e96-b298-c9d22cfafaf3');
assert.equal(state.buildDigest, '7e2c42e897361d27b0aa6bf216f74ed7ba71aa32987771ade075193bed54c19f');
assert.equal(state.problem.receiptDigest, '288f5d5aa511a456e7c9b4e2b2bed14521b39e76f27c1fbf51c9ac980cc0d37c');
assert.equal(state.problem.targets[0].theoremName, 'OAI.PolynomialVacuumBridge.Corridor.finite_bridge_sums');
assert.notEqual(state.phase, 'finished');
const goal = cooperation.tasks.find((node: any) => node.task.id === 'initial_goal_1');
const sums = cooperation.tasks.find((node: any) => node.task.id === 'sums_reduction');
const engineer = state.workers.find((worker: any) => worker.id === 'engineer');
const preparationFile = path.join(stage, 'consumer-' + mode + '-preparation.json');
const receiptFile = path.join(stage, 'consumer-' + mode + '-queue-receipt.json');
const pausePreparationFile = path.join(stage, 'consumer-pause-preparation.json');
const restoreGate = () => {
  // Integration has its own checked commit; match each proof to its own delivery.
  const matched = [sums.proof, sums.integratedCheck].flatMap(proof => {
    const accepted = proof?.passed === true && proof.taskDigest === taskVersion(sums.task) &&
      proof.verification?.status === 'kernel_verified' && !(proof.conditions?.length);
    if (!accepted) return [];
    const delivery = cooperation.deliveries.find((record: any) => record.kind === 'proof' &&
      record.taskId === sums.task.id && record.taskDigest === taskVersion(sums.task) &&
      record.commit === proof.commit && record.status !== 'superseded');
    return delivery ? [{ proof, delivery }] : [];
  })[0];
  const proof = matched?.proof, delivery = matched?.delivery;
  return matched ? { commit: proof.commit, taskDigest: proof.taskDigest,
    verificationStatus: proof.verification.status, deliveryId: delivery.id, taskStatus: sums.status } : undefined;
};

if (fs.existsSync(receiptFile)) {
  const prior = JSON.parse(fs.readFileSync(receiptFile, 'utf8'));
  console.log(JSON.stringify({ phase: 'already-recorded', receiptFile, result: prior.result }));
} else if (mode === 'resume' && !restoreGate()) {
  console.log(JSON.stringify({ phase: 'waiting-for-native-typed-proof', taskId: sums.task.id,
    taskStatus: sums.status, mathematicalAcceptance: false, queued: false }));
} else {
  let preparation: any;
  if (fs.existsSync(preparationFile)) {
    preparation = JSON.parse(fs.readFileSync(preparationFile, 'utf8'));
    assert.equal(preparation.runId, state.runId);
  } else {
    assert(cooperation.tasks.every((node: any) => !node.capacityExploration));
    let updated: any;
    let nativeSchedulingPreview: any;
    if (mode === 'pause') {
      assert.equal(goal.status, 'running');
      assert.equal(goal.assignment?.workerId, 'engineer');
      assert.equal(engineer.sessionTaskId, goal.task.id);
      assert(!goal.proof && !goal.integratedCheck && !goal.pendingValidation,
        'Reinspect an original-goal proof already submitted or under verification.');
      assert.equal(sums.status, 'pending');
      assert.equal(sums.task.ownerId, 'engineer');
      assert(!sums.proof && !sums.assignment);
      const source = fs.readFileSync(path.join(engineer.worktree, 'generated/problem/Submission.lean'));
      assert.equal(mathDigest(source), '6acaeab1940555d1df29856e504deae4f9edf7777231969b9b7d13515731d830',
        'Reinspect new original-goal source progress before pausing.');
      const deliveryFile = path.join(engineer.worktree, assignmentDeliveryFile(goal.assignment));
      if (fs.existsSync(deliveryFile)) {
        const events = fs.readFileSync(deliveryFile, 'utf8').split('\n').filter(Boolean).map(line => JSON.parse(line));
        assert(!events.some(event => ['ready', 'proof'].includes(event.kind)), 'Do not interrupt a newly submitted proof.');
      }
      updated = { ...goal.task, status: 'paused' };
      const simulate = (paused: boolean) => {
        const tasks = structuredClone(cooperation.tasks);
        const consumer = tasks.find((node: any) => node.task.id === goal.task.id);
        consumer.status = 'pending';
        if (paused) consumer.task = updated;
        const groups = structuredClone(cooperation.groups).map((record: any) => ({ ...record,
          busy: new Set(tasks.filter((node: any) => node.status === 'running' && node.assignment &&
            (node.task.groupId ?? 'main') === record.group.id).map((node: any) => node.assignment.workerId)).size }));
        const ranked = readyResearchTasks(tasks, groups);
        const selected = assignSharedResearchTask(ranked, engineer, state.workers, groups, tasks);
        return { rankedTaskIds: ranked.map(node => node.task.id), selectedTaskId: selected?.task.id };
      };
      nativeSchedulingPreview = { beforePauseOnNextFreeSlot: simulate(false), afterPauseOnNextFreeSlot: simulate(true) };
      assert.equal(nativeSchedulingPreview.afterPauseOnNextFreeSlot.selectedTaskId, sums.task.id);
    } else {
      assert(restoreGate());
      assert.equal(goal.task.status, 'paused');
      const pause = JSON.parse(fs.readFileSync(pausePreparationFile, 'utf8'));
      updated = { ...goal.task };
      if (Object.hasOwn(pause.originalGoalTask, 'status')) updated.status = pause.originalGoalTask.status;
      else delete updated.status;
    }
    assert.equal(taskVersion(updated), taskVersion(goal.task));
    assert.equal(taskProofContractVersion(updated), taskProofContractVersion(goal.task));
    const proposal = {
      id: 'honeycomb-consumer-' + mode + '-' + cooperation.planVersion.slice(0, 12),
      baseVersion: cooperation.planVersion,
      tasks: cooperation.tasks.map((node: any) => node.task.id === goal.task.id ? updated : node.task),
      groups: cooperation.groups.map((record: any) => record.group),
      ...(cooperation.proofRoutes ? { proofRoutes: cooperation.proofRoutes } : {}),
    };
    const normalized = { id: proposal.id, baseVersion: proposal.baseVersion, ...parseCooperationPlan(state.problem, proposal) };
    assert.deepEqual(normalized.tasks.map(task => task.id), cooperation.tasks.map((node: any) => node.task.id));
    for (const task of normalized.tasks) {
      const old = cooperation.tasks.find((node: any) => node.task.id === task.id).task;
      if (task.id === goal.task.id) {
        const omitStatus = ({ status: _status, ...other }: any) => other;
        assert.equal(canonicalMathJson(omitStatus(task)), canonicalMathJson(omitStatus(old)));
      } else assert.equal(canonicalMathJson(task), canonicalMathJson(old));
    }
    const line = JSON.stringify(normalized) + '\n';
    assert(Buffer.byteLength(line) <= MAX_DELIVERY_LINE_BYTES);
    const fixture = path.join(stage, 'consumer-' + mode + '-edit-fixture.jsonl');
    fs.writeFileSync(fixture, line, { flag: 'wx' });
    const consumed = readDeliveryLines(fixture, 0);
    assert.equal(consumed.entries!.length, 1);
    assert.equal(canonicalMathJson(JSON.parse(consumed.entries![0].line!)), canonicalMathJson(normalized));
    const validation = await queueRunEdit(run, proposal, true);
    assert.equal(validation.status, 'validated');
    preparation = {
      observedAt: new Date().toISOString(), mode, runId: state.runId, run,
      stateFileSHA256: mathDigest(stateBytes), problemSHA256: mathDigest(canonicalMathJson(state.problem)),
      originalGoalTask: goal.task, originalGoalAssignment: goal.assignment,
      originalEngineerSessionTaskId: engineer.sessionTaskId, nativeSchedulingPreview,
      proposal, validation, normalizedEditLineBytes: Buffer.byteLength(line),
      fullTaskGraphPreserved: true, allMathematicalTaskContractsPreserved: true,
      changedTaskId: goal.task.id, changedField: 'status',
      restorationCondition: 'Current sums_reduction has a passing, unconditional native kernel TaskProof and a non-superseded proof delivery for its exact current task digest.',
      restorationEntry: '/home/lzh/.venvs/deepscientist-finance/.bun/bin/bun queue-consumer-scheduling.ts resume --queue',
      restoreGate: mode === 'resume' ? restoreGate() : null,
      directStateWrites: false, directActiveSourceWrites: false, leanStarted: false, modelsStarted: false,
      mathematicalAcceptance: false,
    };
    fs.writeFileSync(preparationFile, JSON.stringify(preparation, null, 2) + '\n', { flag: 'wx' });
  }
  if (process.argv.includes('--queue')) {
    assert.equal(mathDigest(canonicalMathJson(state.problem)), preparation.problemSHA256);
    if (mode === 'resume') assert(restoreGate());
    if (mode === 'pause') {
      assert(!goal.proof && !goal.integratedCheck && !goal.pendingValidation);
      assert.equal(goal.status, 'running');
      assert.equal(goal.assignment?.workerId, 'engineer');
      assert.equal(mathDigest(fs.readFileSync(path.join(engineer.worktree, 'generated/problem/Submission.lean'))),
        '6acaeab1940555d1df29856e504deae4f9edf7777231969b9b7d13515731d830');
      const currentDelivery = path.join(engineer.worktree, assignmentDeliveryFile(goal.assignment));
      if (fs.existsSync(currentDelivery)) assert(!fs.readFileSync(currentDelivery, 'utf8').split('\n').filter(Boolean)
        .map(line => JSON.parse(line)).some(event => ['ready', 'proof'].includes(event.kind)));
    }
    const result = await queueRunEdit(run, preparation.proposal);
    const receipt = { observedAt: new Date().toISOString(), mode, runId: state.runId,
      editId: preparation.proposal.id, preparationFile, preparationSHA256: mathDigest(fs.readFileSync(preparationFile)), result,
      originalGoalPreserved: true, fullTaskGraphPreserved: true, allMathematicalTaskContractsPreserved: true,
      directStateWrites: false, directActiveSourceWrites: false, leanStarted: false, modelsStarted: false,
      mathematicalAcceptance: false };
    fs.writeFileSync(receiptFile, JSON.stringify(receipt, null, 2) + '\n', { flag: 'wx' });
    console.log(JSON.stringify({ phase: 'queued', receiptFile, result }));
  } else console.log(JSON.stringify({ phase: 'prepared', preparationFile, validation: preparation.validation,
    normalizedEditLineBytes: preparation.normalizedEditLineBytes, nativeSchedulingPreview: preparation.nativeSchedulingPreview }));
}
