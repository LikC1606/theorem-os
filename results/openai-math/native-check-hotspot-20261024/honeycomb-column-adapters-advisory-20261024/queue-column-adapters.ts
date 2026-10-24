import fs from 'node:fs';
import path from 'node:path';
import assert from 'node:assert/strict';
import { queueRunEdit } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/honeycomb-new-build-continuation-20261024/runtime/src/solver/humanEdit';
import { canonicalMathJson, mathDigest } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/honeycomb-new-build-continuation-20261024/runtime/src/math/mathRuntimeIo';
import { invalidatedTaskIds, parseCooperationPlan } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/honeycomb-new-build-continuation-20261024/runtime/src/solver/tasks';

const stage = import.meta.dir;
const run = '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/tasks/HoneycombBridgeFiniteness/attempts/workflow-20261024/result.json';
const helper = path.join(stage, '../honeycomb-column-task-adapters-20261024');
const source = fs.readFileSync(path.join(helper, 'ColumnTaskAdapters.lean'));
const result = JSON.parse(fs.readFileSync(path.join(helper, 'validation-01-result.json'), 'utf8'));
assert.equal(result.actualExitCode, 0);
assert.equal(result.sourceSHA256, mathDigest(source));
assert.equal(result.resourceLimits.maxHeartbeats, 0);
for (const key of ['wallSeconds', 'cpuSoftSeconds', 'cpuHardSeconds']) assert.equal(result.resourceLimits[key], null);
const output = fs.readFileSync(path.join(helper, 'validation-01.stdout.log'), 'utf8');
assert(!output.includes('sorryAx'));
assert.equal((output.match(/depends on axioms:/gu) ?? []).length, 6);
const handoff = fs.readFileSync(path.join(helper, 'HANDOFF.txt'), 'utf8');
assert.equal(mathDigest(handoff), 'e77fffa42afbbf0068ba8516b52e3e3c57a68768ed9cdf87fa454d47116ddc35');
const id = 'honeycomb-column-adapters-' + mathDigest(handoff).slice(0, 12);
const receiptFile = path.join(stage, 'queue-receipt.json');
if (fs.existsSync(receiptFile)) {
  console.log(JSON.stringify({ status: 'already-recorded', receiptFile }));
} else {
  const bytes = fs.readFileSync(run + '.runtime/state.json');
  const state = JSON.parse(bytes.toString('utf8'));
  assert.equal(state.runId, '8bd4a613-c70e-4e96-b298-c9d22cfafaf3');
  assert.equal(state.buildDigest, '7e2c42e897361d27b0aa6bf216f74ed7ba71aa32987771ade075193bed54c19f');
  assert.notEqual(state.phase, 'finished');
  const co = state.cooperation;
  assert(!co.edits?.some((edit: any) => edit.id === id));
  const taskId = 'finite_box_zero_mass_reference';
  const reference = co.tasks.find((node: any) => node.task.id === taskId);
  assert(reference && reference.status === 'pending' && !reference.assignment);
  assert(!reference.task.objective.includes(mathDigest(source)));
  const tasks = co.tasks.map((node: any) => node.task.id === taskId
    ? { ...node.task, objective: node.task.objective + '\n\n' + handoff } : node.task);
  const groups = co.groups.map((record: any) => record.group);
  const proposal = { id, baseVersion: co.planVersion, tasks, groups,
    ...(co.proofRoutes ? { proofRoutes: co.proofRoutes } : {}) };
  const plan = parseCooperationPlan(state.problem, proposal);
  assert.deepEqual(plan.tasks.map(task => task.id), co.tasks.map((node: any) => node.task.id));
  for (const node of co.tasks) if (node.task.id !== taskId)
    assert.equal(canonicalMathJson(plan.tasks.find(task => task.id === node.task.id)), canonicalMathJson(node.task));
  assert.equal(canonicalMathJson(plan.groups), canonicalMathJson(groups));
  assert.equal(canonicalMathJson(plan.proofRoutes ?? null), canonicalMathJson(co.proofRoutes ?? null));
  const dependencies = new Map(co.tasks.map((node: any) => [node.task.id,
    [...node.task.dependsOn, ...(node.alternativeRoutes?.flatMap((route: any) =>
      [...route.prerequisiteTaskIds, route.closingTaskId]) ?? []),
      ...(node.assignment?.dependencies?.map((item: any) => item.taskId) ?? [])]]));
  assert.deepEqual([...invalidatedTaskIds(co.tasks, plan.tasks, new Set(), dependencies)], [taskId]);
  const validation = await queueRunEdit(run, proposal, true);
  assert.equal(validation.status, 'validated');
  fs.writeFileSync(path.join(stage, 'state-before.json'), bytes, { flag: 'wx' });
  fs.writeFileSync(path.join(stage, 'preparation.json'), JSON.stringify({ capturedAt: new Date().toISOString(),
    runId: state.runId, run, sourceSHA256: mathDigest(source), handoffSHA256: mathDigest(handoff),
    stateSHA256: mathDigest(bytes), proposal, validation, expectedAffectedTasks: [taskId] }, null, 2) + '\n', { flag: 'wx' });
  const queued = await queueRunEdit(run, proposal);
  fs.writeFileSync(receiptFile, JSON.stringify({ capturedAt: new Date().toISOString(), runId: state.runId,
    editId: id, result: queued, localKernelVerified: true, nativeTaskProofAcceptance: false }, null, 2) + '\n', { flag: 'wx' });
  console.log(JSON.stringify(queued));
}
