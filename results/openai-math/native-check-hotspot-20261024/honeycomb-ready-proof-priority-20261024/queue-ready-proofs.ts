import fs from 'node:fs';
import path from 'node:path';
import assert from 'node:assert/strict';
import { queueRunEdit } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/honeycomb-new-build-continuation-20261024/runtime/src/solver/humanEdit';
import { canonicalMathJson, mathDigest } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/honeycomb-new-build-continuation-20261024/runtime/src/math/mathRuntimeIo';
import { invalidatedTaskIds, parseCooperationPlan } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/honeycomb-new-build-continuation-20261024/runtime/src/solver/tasks';

const stage = import.meta.dir;
const run = '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/tasks/HoneycombBridgeFiniteness/attempts/workflow-20261024/result.json';
const id = 'honeycomb-ready-column-proof-priority-20261024';
const priorityIds = ['bridge_column_step_unique_a0424391', 'bridge_full_column_word_injective_a0424391'];
const receiptFile = path.join(stage, 'queue-receipt.json');
if (fs.existsSync(receiptFile)) {
  console.log(JSON.stringify({ status: 'already-recorded', receiptFile }));
} else {
  const bytes = fs.readFileSync(run + '.runtime/state.json');
  const state = JSON.parse(bytes.toString('utf8'));
  assert.equal(state.runId, '8bd4a613-c70e-4e96-b298-c9d22cfafaf3');
  assert.equal(state.buildDigest, '7e2c42e897361d27b0aa6bf216f74ed7ba71aa32987771ade075193bed54c19f');
  assert.equal(state.phase, 'running');
  const co = state.cooperation;
  assert(!co.edits?.some((edit: any) => edit.id === id));
  const original = co.tasks.map((node: any) => node.task);
  const ready = priorityIds.map(taskId => {
    const node = co.tasks.find((item: any) => item.task.id === taskId);
    assert(node && node.status === 'pending' && !node.assignment && node.attempts === 0);
    return node.task;
  });
  const rest = original.filter((task: any) => !priorityIds.includes(task.id));
  const firstAdvisory = rest.findIndex((task: any) => task.id === 'initial_research_1');
  assert(firstAdvisory >= 0);
  const tasks = [...rest.slice(0, firstAdvisory), ...ready, ...rest.slice(firstAdvisory)];
  const groups = co.groups.map((record: any) => record.group);
  const proposal = { id, baseVersion: co.planVersion, tasks, groups,
    ...(co.proofRoutes ? { proofRoutes: co.proofRoutes } : {}) };
  const plan = parseCooperationPlan(state.problem, proposal);
  assert.equal(plan.tasks.length, co.tasks.length);
  for (const node of co.tasks) assert.equal(
    canonicalMathJson(plan.tasks.find(task => task.id === node.task.id)), canonicalMathJson(node.task));
  assert.equal(canonicalMathJson(plan.groups), canonicalMathJson(groups));
  assert.equal(canonicalMathJson(plan.proofRoutes ?? null), canonicalMathJson(co.proofRoutes ?? null));
  const dependencies = new Map(co.tasks.map((node: any) => [node.task.id,
    [...node.task.dependsOn, ...(node.alternativeRoutes?.flatMap((route: any) =>
      [...route.prerequisiteTaskIds, route.closingTaskId]) ?? []),
      ...(node.assignment?.dependencies?.map((item: any) => item.taskId) ?? [])]]));
  assert.deepEqual([...invalidatedTaskIds(co.tasks, plan.tasks, new Set(), dependencies)], []);
  const validation = await queueRunEdit(run, proposal, true);
  assert.equal(validation.status, 'validated');
  fs.writeFileSync(path.join(stage, 'state-before.json'), bytes, { flag: 'wx' });
  fs.writeFileSync(path.join(stage, 'preparation.json'), JSON.stringify({ capturedAt: new Date().toISOString(),
    run, runId: state.runId, stateSHA256: mathDigest(bytes), proposal, validation,
    oldTaskOrder: original.map((task: any) => task.id), newTaskOrder: tasks.map((task: any) => task.id),
    taskObjectsUnchanged: true, expectedInvalidatedTasks: [],
    assignmentsBefore: co.tasks.filter((node: any) => node.assignment).map((node: any) => ({ taskId: node.task.id, assignment: node.assignment }))
  }, null, 2) + '\n', { flag: 'wx' });
  const queued = await queueRunEdit(run, proposal);
  fs.writeFileSync(receiptFile, JSON.stringify({ capturedAt: new Date().toISOString(), runId: state.runId,
    editId: id, result: queued, newLeanInvocations: 0, nativeTaskProofAccepted: false }, null, 2) + '\n', { flag: 'wx' });
  console.log(JSON.stringify(queued));
}
