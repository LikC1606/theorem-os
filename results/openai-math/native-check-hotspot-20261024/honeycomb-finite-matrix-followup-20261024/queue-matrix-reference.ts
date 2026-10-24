import fs from 'node:fs';
import path from 'node:path';
import assert from 'node:assert/strict';
import { queueRunEdit } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/honeycomb-new-build-continuation-20261024/runtime/src/solver/humanEdit';
import { canonicalMathJson, mathDigest } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/honeycomb-new-build-continuation-20261024/runtime/src/math/mathRuntimeIo';
import { invalidatedTaskIds, parseCooperationPlan } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/honeycomb-new-build-continuation-20261024/runtime/src/solver/tasks';

const stage = import.meta.dir;
const run = '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/tasks/HoneycombBridgeFiniteness/attempts/workflow-20261024/result.json';
const taskId = 'finite_box_zero_mass_reference';
const result = JSON.parse(fs.readFileSync(path.join(stage, 'validation-04-final-result.json'), 'utf8'));
const source = fs.readFileSync(path.join(stage, 'FiniteMatrixFirstMoment.lean'));
assert.equal(result.actualExitCode, 0);
assert.equal(result.sourceSHA256, mathDigest(source));
assert.equal(result.resourceLimits.maxHeartbeats, 0);
for (const key of ['wallSeconds', 'cpuSoftSeconds', 'cpuHardSeconds']) assert.equal(result.resourceLimits[key], null);
const output = fs.readFileSync(path.join(stage, 'validation-04-final.stdout.log'), 'utf8');
assert(!output.includes('sorryAx'));
assert.equal((output.match(/depends on axioms:/gu) ?? []).length, 2);
const handoff = fs.readFileSync(path.join(stage, 'native-advisory-handoff.md'), 'utf8');
const preparationFile = path.join(stage, 'native-advisory-preparation.json');
const receiptFile = path.join(stage, 'native-advisory-queue-receipt.json');
if (fs.existsSync(receiptFile)) {
  console.log(JSON.stringify({ phase: 'already-recorded', receiptFile }));
} else {
  let preparation: any;
  if (fs.existsSync(preparationFile)) {
    preparation = JSON.parse(fs.readFileSync(preparationFile, 'utf8'));
    assert.equal(preparation.handoffSHA256, mathDigest(handoff));
    assert.equal(preparation.sourceSHA256, mathDigest(source));
  } else {
    const stateBytes = fs.readFileSync(run + '.runtime/state.json');
    const state = JSON.parse(stateBytes.toString('utf8'));
    assert.equal(state.runId, '8bd4a613-c70e-4e96-b298-c9d22cfafaf3');
    assert.equal(state.buildDigest, '7e2c42e897361d27b0aa6bf216f74ed7ba71aa32987771ade075193bed54c19f');
    assert.notEqual(state.phase, 'finished');
    const cooperation = state.cooperation;
    const reference = cooperation.tasks.find((node: any) => node.task.id === taskId);
    assert(reference && reference.status === 'pending' && !reference.assignment);
    assert(!reference.task.objective.includes('bae1606a1e3ad7675bdfa043f99d08d1e5a9fb7e822fb31612a19eec63eff33f'));
    const tasks = cooperation.tasks.map((node: any) => node.task.id === taskId
      ? { ...node.task, objective: node.task.objective + '\n\n' + handoff } : node.task);
    const groups = cooperation.groups.map((record: any) => record.group);
    const proposal = { id: 'honeycomb-finite-matrix-' + mathDigest(handoff).slice(0, 12),
      baseVersion: cooperation.planVersion, tasks, groups,
      ...(cooperation.proofRoutes ? { proofRoutes: cooperation.proofRoutes } : {}) };
    const plan = parseCooperationPlan(state.problem, proposal);
    assert.deepEqual(plan.tasks.map(task => task.id), cooperation.tasks.map((node: any) => node.task.id));
    for (const node of cooperation.tasks) if (node.task.id !== taskId)
      assert.equal(canonicalMathJson(plan.tasks.find(task => task.id === node.task.id)), canonicalMathJson(node.task));
    assert.equal(canonicalMathJson(plan.groups), canonicalMathJson(groups));
    assert.equal(canonicalMathJson(plan.proofRoutes ?? null), canonicalMathJson(cooperation.proofRoutes ?? null));
    const dependencies = new Map(cooperation.tasks.map((node: any) => [node.task.id,
      [...node.task.dependsOn, ...(node.alternativeRoutes?.flatMap((route: any) =>
        [...route.prerequisiteTaskIds, route.closingTaskId]) ?? []),
        ...(node.assignment?.dependencies?.map((item: any) => item.taskId) ?? [])]]));
    assert.deepEqual([...invalidatedTaskIds(cooperation.tasks, plan.tasks, new Set(), dependencies)], [taskId]);
    const validation = await queueRunEdit(run, proposal, true);
    assert.equal(validation.status, 'validated');
    preparation = { observedAt: new Date().toISOString(), runId: state.runId, run,
      stateSHA256: mathDigest(stateBytes), handoffSHA256: mathDigest(handoff), sourceSHA256: mathDigest(source),
      existingTasks: cooperation.tasks.map((node: any) => ({ task: node.task, assignment: node.assignment ?? null })),
      groups, proofRoutes: cooperation.proofRoutes ?? null, proposal, validation,
      expectedAffectedTasks: [taskId], activeSourceModified: false, directCheckpointWrites: false };
    fs.writeFileSync(preparationFile, JSON.stringify(preparation, null, 2) + '\n', { flag: 'wx' });
  }
  if (process.argv.includes('--queue')) {
    const queued = await queueRunEdit(run, preparation.proposal);
    fs.writeFileSync(receiptFile, JSON.stringify({ observedAt: new Date().toISOString(),
      runId: preparation.runId, editId: preparation.proposal.id, result: queued,
      mathematicalAcceptance: false, localKernelVerified: true, sourceSHA256: mathDigest(source) }, null, 2) + '\n', { flag: 'wx' });
    console.log(JSON.stringify(queued));
  } else console.log(JSON.stringify({ validation: preparation.validation, preparationFile }));
}
