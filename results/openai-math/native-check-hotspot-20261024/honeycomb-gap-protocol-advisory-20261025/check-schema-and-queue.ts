import fs from 'node:fs';
import path from 'node:path';
import assert from 'node:assert/strict';
import { mathematicalGapSchema } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/honeycomb-new-build-continuation-20261024/runtime/src/solver/mathematicalGaps';
import { queueRunEdit } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/honeycomb-new-build-continuation-20261024/runtime/src/solver/humanEdit';
import { canonicalMathJson, mathDigest } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/honeycomb-new-build-continuation-20261024/runtime/src/math/mathRuntimeIo';
import { invalidatedTaskIds, parseCooperationPlan } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/honeycomb-new-build-continuation-20261024/runtime/src/solver/tasks';

const stage = import.meta.dir;
const run = '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/tasks/HoneycombBridgeFiniteness/attempts/workflow-20261024/result.json';
const id = 'honeycomb-gap-consumer-shape-20261025';
const referenceId = 'finite_box_zero_mass_reference';
const receiptFile = path.join(stage, 'queue-receipt.json');
if (fs.existsSync(receiptFile)) {
  console.log(JSON.stringify({ status: 'already-recorded', receiptFile }));
} else {
  const bytes = fs.readFileSync(run + '.runtime/state.json');
  const state = JSON.parse(bytes.toString('utf8')), co = state.cooperation;
  assert.equal(state.runId, '8bd4a613-c70e-4e96-b298-c9d22cfafaf3');
  assert.equal(state.buildDigest, '7e2c42e897361d27b0aa6bf216f74ed7ba71aa32987771ade075193bed54c19f');
  assert.equal(state.phase, 'running');
  assert(!co.edits?.some((edit: any) => edit.id === id));
  const goal = co.tasks.find((node: any) => node.task.id === 'initial_goal_1');
  assert.equal(goal?.task.kind, 'goal');
  assert.equal(goal.assignment.taskDigest, 'ab8c91c92c1d5d985ed03edfaee27bbef6df38455b84a82711d07d8d13e77890');
  const example = {
    consumer: { taskId: goal.task.id, taskDigest: goal.assignment.taskDigest },
    previousGap: 'Parser shape probe only, not a mathematical report.',
    reduced: 'Parser shape probe only, not a mathematical report.',
    remaining: 'Parser shape probe only, not a mathematical report.',
    evidenceScope: 'Frozen parser schema validation; no Lean invocation or proof acceptance.',
    reconsiderWhen: ['An actual mathematical report is prepared.'],
  };
  assert(mathematicalGapSchema.safeParse(example).success);
  const rejected = mathematicalGapSchema.safeParse({ ...example, consumer: { ...example.consumer, kind: 'goal' } });
  assert(!rejected.success);
  assert(rejected.error.issues.some(issue => issue.path.join('.') === 'consumer'));
  const schemaReport = {
    observedAt: new Date().toISOString(), runId: state.runId,
    consumerReference: example.consumer, validTwoKeyConsumerAccepted: true,
    extraKindRejected: true, rejectionIssues: rejected.error.issues,
    frozenSchemaSHA256: mathDigest(fs.readFileSync('/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/honeycomb-new-build-continuation-20261024/runtime/src/solver/mathematicalGaps.ts')),
    unresolvedHistoricalReceipt: co.deliveryReceipts.find((receipt: any) => receipt.id === 'eced4598fb5fa5b08eee4698e63afdf2cf7b719548b4f8f0a2c3ea979af6637e') ?? null,
    leanInvocations: 0, mathematicalAcceptance: false,
  };
  const reference = co.tasks.find((node: any) => node.task.id === referenceId);
  assert(reference && reference.status === 'pending' && !reference.assignment && !reference.proof);
  const advisory = fs.readFileSync(path.join(stage, 'protocol-advisory.md'), 'utf8');
  assert(!reference.task.objective.includes('Protocol clarification for mathematical gap reports (2026-10-25).'));
  const tasks = co.tasks.map((node: any) => node.task.id === referenceId
    ? { ...node.task, objective: node.task.objective + '\n\n' + advisory } : node.task);
  const groups = co.groups.map((record: any) => record.group);
  const proposal = { id, baseVersion: co.planVersion, tasks, groups,
    ...(co.proofRoutes ? { proofRoutes: co.proofRoutes } : {}) };
  const plan = parseCooperationPlan(state.problem, proposal);
  for (const node of co.tasks) if (node.task.id !== referenceId) assert.equal(
    canonicalMathJson(plan.tasks.find(task => task.id === node.task.id)), canonicalMathJson(node.task));
  assert.equal(canonicalMathJson(plan.groups), canonicalMathJson(groups));
  assert.equal(canonicalMathJson(plan.proofRoutes ?? null), canonicalMathJson(co.proofRoutes ?? null));
  const dependencies = new Map(co.tasks.map((node: any) => [node.task.id,
    [...node.task.dependsOn, ...(node.alternativeRoutes?.flatMap((route: any) =>
      [...route.prerequisiteTaskIds, route.closingTaskId]) ?? []),
      ...(node.assignment?.dependencies?.map((value: any) => value.taskId) ?? [])]]));
  assert.deepEqual([...invalidatedTaskIds(co.tasks, plan.tasks, new Set(), dependencies)], [referenceId]);
  const wireBytes = Buffer.byteLength(JSON.stringify(proposal) + '\n');
  assert(wireBytes <= 1024 * 1024);
  const validation = await queueRunEdit(run, proposal, true);
  assert.equal(validation.status, 'validated');
  fs.writeFileSync(path.join(stage, 'state-before.json'), bytes, { flag: 'wx' });
  fs.writeFileSync(path.join(stage, 'schema-check.json'), JSON.stringify(schemaReport, null, 2) + '\n', { flag: 'wx' });
  fs.writeFileSync(path.join(stage, 'preparation.json'), JSON.stringify({
    observedAt: new Date().toISOString(), proposal, validation, wireBytes,
    expectedAffectedTasks: [referenceId], allOtherTaskObjectsUnchanged: true,
    activeAssignmentsPreserved: true, directStateWrites: false,
    advisorySHA256: mathDigest(advisory), stateSHA256: mathDigest(bytes),
  }, null, 2) + '\n', { flag: 'wx' });
  const queued = await queueRunEdit(run, proposal);
  fs.writeFileSync(receiptFile, JSON.stringify({ observedAt: new Date().toISOString(),
    runId: state.runId, editId: id, result: queued, leanInvocations: 0,
    mathematicalAcceptance: false }, null, 2) + '\n', { flag: 'wx' });
  console.log(JSON.stringify({ schemaCheck: 'passed', ...queued }));
}
