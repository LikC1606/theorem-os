import fs from 'node:fs';
import path from 'node:path';
import assert from 'node:assert/strict';
import { queueRunEdit } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/honeycomb-new-build-continuation-20261024/runtime/src/solver/humanEdit';
import { canonicalMathJson, mathDigest } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/honeycomb-new-build-continuation-20261024/runtime/src/math/mathRuntimeIo';
import { parseCooperationPlan, invalidatedTaskIds, taskGroup } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/honeycomb-new-build-continuation-20261024/runtime/src/solver/tasks';
import { taskConnectionCheckCurrent } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/honeycomb-new-build-continuation-20261024/runtime/src/solver/taskConnections';
import { MAX_DELIVERY_LINE_BYTES } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/honeycomb-new-build-continuation-20261024/runtime/src/solver/deliveries';

const stage = import.meta.dir;
const run = '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/tasks/HoneycombBridgeFiniteness/attempts/workflow-20261024/result.json';
const stateBytes = fs.readFileSync(run + '.runtime/state.json');
const state = JSON.parse(stateBytes.toString('utf8'));
assert.equal(state.runId, '8bd4a613-c70e-4e96-b298-c9d22cfafaf3');
assert.equal(state.buildDigest, '7e2c42e897361d27b0aa6bf216f74ed7ba71aa32987771ade075193bed54c19f');
assert.equal(state.problem.receiptDigest, '288f5d5aa511a456e7c9b4e2b2bed14521b39e76f27c1fbf51c9ac980cc0d37c');
assert.notEqual(state.phase, 'finished');
const taskId = 'finite_box_zero_mass_reference';
const preparationFile = path.join(stage, 'native-advisory-preparation.json');
const receiptFile = path.join(stage, 'native-advisory-queue-receipt.json');
const handoff = fs.readFileSync(path.join(stage, 'native-advisory-handoff.md'), 'utf8');
const resultBytes = fs.readFileSync(path.join(stage, 'validation-no-budget-result.json'));
const result = JSON.parse(resultBytes.toString('utf8'));
assert.equal(result.actualExitCode, 0);
assert.equal(result.sourceSHA256, mathDigest(fs.readFileSync(path.join(stage, 'Submission.lean'))));
assert.equal(result.resourceLimits.maxHeartbeats, 0);
for (const field of ['wallSeconds', 'cpuSoftSeconds', 'cpuHardSeconds']) assert.equal(result.resourceLimits[field], null);
assert(!('invocationLimit' in result));

if (fs.existsSync(receiptFile)) {
  const prior = JSON.parse(fs.readFileSync(receiptFile, 'utf8'));
  console.log(JSON.stringify({ phase: 'already-recorded', receiptFile, result: prior.result }));
} else {
  let preparation: any;
  if (fs.existsSync(preparationFile)) {
    preparation = JSON.parse(fs.readFileSync(preparationFile, 'utf8'));
    assert.equal(preparation.runId, state.runId);
    assert.equal(preparation.handoffSHA256, mathDigest(handoff));
    assert.equal(preparation.validationResultSHA256, mathDigest(resultBytes));
  } else {
    const cooperation = state.cooperation;
    const nodes = cooperation.tasks;
    assert(nodes.every((node: any) => !node.capacityExploration));
    assert(!nodes.some((node: any) => node.task.id === taskId));
    const newTask = {
      id: taskId,
      kind: 'research',
      objective: handoff,
      dependsOn: [],
      revision: 0,
      ownerId: 'researcher-2',
      groupId: 'main',
      sharing: 'problem',
    };
    const groups = cooperation.groups.map((record: any) => record.group);
    const proposal = {
      id: 'honeycomb-finite-box-' + mathDigest(handoff).slice(0, 12),
      baseVersion: cooperation.planVersion,
      tasks: [...nodes.map((node: any) => node.task), newTask],
      groups,
      ...(cooperation.proofRoutes ? { proofRoutes: cooperation.proofRoutes } : {}),
    };
    const normalized = parseCooperationPlan(state.problem, proposal);
    assert.deepEqual(normalized.tasks.map(task => task.id), [...nodes.map((node: any) => node.task.id), taskId]);
    assert.equal(canonicalMathJson(normalized.groups), canonicalMathJson(groups));
    assert.equal(canonicalMathJson(normalized.proofRoutes ?? null), canonicalMathJson(cooperation.proofRoutes ?? null));
    for (const node of nodes) assert.equal(canonicalMathJson(normalized.tasks.find(task => task.id === node.task.id)), canonicalMathJson(node.task));
    const dependencies = new Map(nodes.map((node: any) => [node.task.id,
      [...node.task.dependsOn, ...(node.alternativeRoutes?.flatMap((route: any) => [...route.prerequisiteTaskIds, route.closingTaskId]) ?? []),
        ...(node.assignment?.dependencies?.map((item: any) => item.taskId) ?? [])]]));
    const projected = normalized.tasks.map(task => ({ task, status: 'pending' as const, attempts: 0,
      alternativeRoutes: normalized.proofRoutes?.filter(route => route.targetTaskId === task.id) }));
    const routeChanges = new Set<string>(nodes.filter((node: any) => node.status !== 'integrated' &&
      (canonicalMathJson(node.alternativeRoutes ?? []) !== canonicalMathJson(normalized.proofRoutes?.filter(route => route.targetTaskId === node.task.id) ?? []) ||
        node.assignment?.connectionCheck && !taskConnectionCheckCurrent(node.task, node.assignment, projected)))
      .map((node: any) => node.task.id));
    const invalidated = [...invalidatedTaskIds(nodes, normalized.tasks, new Set(), dependencies, routeChanges)];
    assert.deepEqual(invalidated, [], 'The shared reference must not invalidate any existing task or assignment.');
    const viewers = ['initial_goal_1', 'initial_research_2'].map(id => {
      const viewer = nodes.find((node: any) => node.task.id === id);
      assert(viewer?.assignment);
      assert.equal(taskGroup(viewer.task), taskGroup(newTask as any));
      return { taskId: id, workerId: viewer.assignment.workerId, assignmentId: viewer.assignment.assignmentId,
        groupId: taskGroup(viewer.task), sameGroupVisibility: true };
    });
    const lineBytes = Buffer.byteLength(JSON.stringify(proposal) + '\n');
    assert(lineBytes <= MAX_DELIVERY_LINE_BYTES);
    const validation = await queueRunEdit(run, proposal, true);
    assert.equal(validation.status, 'validated');
    preparation = {
      observedAt: new Date().toISOString(), runId: state.runId, run,
      stateSHA256AtPreparation: mathDigest(stateBytes), problemSHA256: mathDigest(canonicalMathJson(state.problem)),
      handoffSHA256: mathDigest(handoff), validationResultSHA256: mathDigest(resultBytes),
      existingTaskSnapshots: nodes.map((node: any) => ({ task: node.task, status: node.status,
        assignment: node.assignment ?? null, pendingValidation: node.pendingValidation ?? null })),
      proposal, validation, expectedInvalidatedTaskIds: invalidated, expectedAddedTaskIds: [taskId], lineBytes,
      groupsPreserved: true, proofRoutesPreserved: true, existingTasksPreserved: true, existingAssignmentsPreserved: true,
      visibility: { viewers, basis: 'CooperationCore.visible includes all tasks in the same group, even pending. CooperationCore.changed writes each visible task objective to that worker COOPERATION.json. sharing=problem also permits subsequent cross-group completed-reference visibility.',
        source: 'runtime/src/solver/cooperationCore.ts:638 and :294; runtime/src/solver/cooperation.ts:798' },
      directCheckpointWrites: false, directActiveSourceWrites: false, mathematicalAcceptance: false,
    };
    fs.writeFileSync(preparationFile, JSON.stringify(preparation, null, 2) + '\n', { flag: 'wx' });
  }
  if (process.argv.includes('--queue')) {
    assert.equal(mathDigest(canonicalMathJson(state.problem)), preparation.problemSHA256);
    const result = await queueRunEdit(run, preparation.proposal);
    const receipt = { observedAt: new Date().toISOString(), runId: state.runId,
      editId: preparation.proposal.id, result, preparationFile,
      preparationSHA256: mathDigest(fs.readFileSync(preparationFile)),
      attribution: 'Locally kernel-checked conditional zeroth-mass helper increment delivered as shared advisory; not native TaskProof acceptance.',
      mathematicalAcceptance: false, directCheckpointWrites: false, directActiveSourceWrites: false };
    fs.writeFileSync(receiptFile, JSON.stringify(receipt, null, 2) + '\n', { flag: 'wx' });
    console.log(JSON.stringify({ phase: 'queued', result, receiptFile }));
  } else console.log(JSON.stringify({ phase: 'prepared', preparationFile, validation: preparation.validation,
    expectedInvalidatedTaskIds: preparation.expectedInvalidatedTaskIds, expectedAddedTaskIds: preparation.expectedAddedTaskIds,
    lineBytes: preparation.lineBytes, visibility: preparation.visibility.viewers }));
}
