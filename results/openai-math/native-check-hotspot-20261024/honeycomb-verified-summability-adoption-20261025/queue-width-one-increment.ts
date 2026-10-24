import fs from 'node:fs';
import path from 'node:path';
import assert from 'node:assert/strict';
import { queueRunEdit } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/honeycomb-new-build-continuation-20261024/runtime/src/solver/humanEdit';
import { canonicalMathJson, mathDigest } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/honeycomb-new-build-continuation-20261024/runtime/src/math/mathRuntimeIo';
import { invalidatedTaskIds, parseCooperationPlan } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/honeycomb-new-build-continuation-20261024/runtime/src/solver/tasks';

const stage = import.meta.dir;
const run = '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/tasks/HoneycombBridgeFiniteness/attempts/workflow-20261024/result.json';
const id = 'honeycomb-width-one-inline-source-20261025';
const taskId = 'width_one_bridge_sums_b433299a';
const receiptFile = path.join(stage, 'width-one-source-queue-receipt.json');
if (fs.existsSync(receiptFile)) {
  console.log(JSON.stringify({ status: 'already-recorded', receiptFile }));
} else {
  const increment = fs.readFileSync(path.join(stage, '../honeycomb-width-one-20261024/WidthOne.lean.inc'), 'utf8');
  assert.equal(mathDigest(increment), '34d8701c1c13598d4a96ca2f4044cb6aacbc8ccba88d771e381fbfb4d930a532');
  const bytes = fs.readFileSync(run + '.runtime/state.json');
  const state = JSON.parse(bytes.toString('utf8')), co = state.cooperation;
  assert.equal(state.runId, '8bd4a613-c70e-4e96-b298-c9d22cfafaf3');
  assert.equal(state.buildDigest, '7e2c42e897361d27b0aa6bf216f74ed7ba71aa32987771ade075193bed54c19f');
  assert(!co.edits?.some((edit: any) => edit.id === id));
  const node = co.tasks.find((item: any) => item.task.id === taskId);
  assert(node && node.status === 'pending' && !node.assignment && !node.proof && node.attempts === 0);
  assert(!node.task.objective.includes(increment));
  const tasks = co.tasks.map((item: any) => item.task.id === taskId
    ? { ...item.task, objective: item.task.objective + '\n\nComplete verified Lean increment (insert once in the canonical namespace):\n```lean\n' + increment + '\n```\n' }
    : item.task);
  const groups = co.groups.map((record: any) => record.group);
  const proposal = { id, baseVersion: co.planVersion, tasks, groups,
    ...(co.proofRoutes ? { proofRoutes: co.proofRoutes } : {}) };
  const plan = parseCooperationPlan(state.problem, proposal);
  for (const item of co.tasks) if (item.task.id !== taskId) assert.equal(
    canonicalMathJson(plan.tasks.find(task => task.id === item.task.id)), canonicalMathJson(item.task));
  const changed = plan.tasks.find(task => task.id === taskId)!;
  const { objective: _old, ...oldMath } = node.task;
  const { objective: _new, ...newMath } = changed;
  assert.equal(canonicalMathJson(oldMath), canonicalMathJson(newMath));
  const dependencies = new Map(co.tasks.map((item: any) => [item.task.id,
    [...item.task.dependsOn, ...(item.alternativeRoutes?.flatMap((route: any) =>
      [...route.prerequisiteTaskIds, route.closingTaskId]) ?? []),
      ...(item.assignment?.dependencies?.map((value: any) => value.taskId) ?? [])]]));
  assert.deepEqual([...invalidatedTaskIds(co.tasks, plan.tasks, new Set(), dependencies)], [taskId]);
  const wireBytes = Buffer.byteLength(JSON.stringify(proposal) + '\n');
  assert(wireBytes <= 1024 * 1024);
  const validation = await queueRunEdit(run, proposal, true);
  assert.equal(validation.status, 'validated');
  fs.writeFileSync(path.join(stage, 'width-one-source-state-before.json'), bytes, { flag: 'wx' });
  fs.writeFileSync(path.join(stage, 'width-one-source-preparation.json'), JSON.stringify({
    capturedAt: new Date().toISOString(), runId: state.runId, proposal, validation, wireBytes,
    incrementSHA256: mathDigest(increment), originalTaskMathematicsUnchanged: true,
    correctedDelivery: 'The first edit embedded HANDOFF.txt, which referred to the separate proposal objective but did not itself include the width-one increment. Add the exact checked increment to the still-unassigned pending task.',
    expectedAffectedTasks: [taskId], preexistingAssignmentsPreserved: true,
  }, null, 2) + '\n', { flag: 'wx' });
  const queued = await queueRunEdit(run, proposal);
  fs.writeFileSync(receiptFile, JSON.stringify({ capturedAt: new Date().toISOString(),
    runId: state.runId, editId: id, result: queued, newLeanInvocations: 0,
    nativeTaskProofAccepted: false }, null, 2) + '\n', { flag: 'wx' });
  console.log(JSON.stringify(queued));
}
