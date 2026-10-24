import fs from 'node:fs';
import path from 'node:path';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { queueRunEdit } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/honeycomb-new-build-continuation-20261024/runtime/src/solver/humanEdit';
import { canonicalMathJson, mathDigest } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/honeycomb-new-build-continuation-20261024/runtime/src/math/mathRuntimeIo';
import { invalidatedTaskIds, parseCooperationPlan } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/honeycomb-new-build-continuation-20261024/runtime/src/solver/tasks';

const stage = import.meta.dir;
const sourceStage = path.join(stage, '../honeycomb-width-two-20261025');
const run = '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/tasks/HoneycombBridgeFiniteness/attempts/workflow-20261024/result.json';
const id = 'honeycomb-width-two-checked-proof-20261025';
const taskId = 'width_two_summability_diagnostic';
const receiptFile = path.join(stage, 'queue-receipt.json');
if (fs.existsSync(receiptFile)) {
  console.log(JSON.stringify({ status: 'already-recorded', receiptFile }));
} else {
  const source = fs.readFileSync(path.join(sourceStage, 'WidthTwo.lean'));
  const sourceHash = mathDigest(source);
  assert.equal(sourceHash, '97a34151766af41dc81716bb199f5565d87b2e505f5be38f0a289c5b657c7027');
  const result = JSON.parse(fs.readFileSync(path.join(sourceStage, 'summability-01-result.json'), 'utf8'));
  assert.equal(result.actualExitCode, 0);
  assert.equal(result.sourceSHA256, sourceHash);
  const increment = fs.readFileSync(path.join(sourceStage, 'WidthTwo.lean.inc'), 'utf8');
  assert.equal(mathDigest(increment), '6946d27d61a5056762c4fd4e3b1cbc8e9ea7da84d78fef68aa008fa6ff99e1ef');
  assert(source.toString('utf8').includes(increment));
  const output = fs.readFileSync(path.join(sourceStage, 'summability-01.stdout.log'), 'utf8');
  assert(!output.includes('sorryAx'));
  assert.equal((output.match(/depends on axioms:/gu) ?? []).length, 6);
  assert.equal(fs.readFileSync(path.join(sourceStage, 'summability-01.stderr.log')).length, 0);
  const bytes = fs.readFileSync(run + '.runtime/state.json');
  const state = JSON.parse(bytes.toString('utf8')), co = state.cooperation;
  assert.equal(state.runId, '8bd4a613-c70e-4e96-b298-c9d22cfafaf3');
  assert.equal(state.buildDigest, '7e2c42e897361d27b0aa6bf216f74ed7ba71aa32987771ade075193bed54c19f');
  assert(['running', 'checking'].includes(state.phase));
  assert(!co.edits?.some((edit: any) => edit.id === id));
  const node = co.tasks.find((item: any) => item.task.id === taskId);
  assert(node && node.status === 'pending' && !node.proof && !node.integratedCheck);
  assert(!state.workers.some((worker: any) => worker.scheduling?.status === 'working' && worker.scheduling.taskId === taskId));
  assert.equal(node.task.kind, 'lemma');
  assert.equal(node.task.theoremName, 'OAI.PolynomialVacuumBridge.Corridor.width_two_summability_diagnostic');
  assert(!node.task.objective.includes(increment));
  const canonical = spawnSync('git', ['--no-optional-locks', 'show', co.canonicalCommit + ':generated/problem/Submission.lean'],
    { cwd: state.worktree, encoding: 'utf8', maxBuffer: 4 * 1024 * 1024 });
  assert.equal(canonical.status, 0);
  for (const name of ['bridgeSummable_firstLengthWeight_of_mu_bound', 'bridgeSummable_weight_of_summable_firstLengthWeight'])
    assert(canonical.stdout.includes(name));
  assert(!canonical.stdout.includes('namespace WidthTwo'));
  const handoff = '\n\nComplete externally prepared, independently kernel-checked proof input. This is not a publisher solution or a native proof receipt. The exact assigned width-two pair is now proved unconditionally by the following complete increment. Local Lean 4.34.1 check exited 0 in ' +
    result.durationSeconds + ' seconds; source SHA256 ' + sourceHash +
    '. Six key declaration axiom reports contain only propext, Classical.choice and Quot.sound. Existing canonical helpers bridgeSummable_firstLengthWeight_of_mu_bound and bridgeSummable_weight_of_summable_firstLengthWeight are the only mathematical prefix prerequisites beyond the canonical definitions and Mathlib. Their source is already in this canonical baseline.\n\n' +
    'Insert this increment once inside namespace OAI.PolynomialVacuumBridge.Corridor, before the original goal and after those existing helpers; preserve current definitions and all other source work. Do not restore an entire reference snapshot over current work. Local linter warnings do not require cleanup or another standalone check. Save the exact assigned declaration and complete ordinary typed proof delivery so the host performs the required independent task and integration checks. Avoid extra standalone Lean/Lake loops for this unchanged input. The old rejected width-two gap report is historical intake feedback, not a mathematical failure; do not reuse its old assignment binding or report a gap in place of this supplied proof. All-height growth and the original goal remain unproved.\n\n' +
    'Increment SHA256: ' + mathDigest(increment) + '\n\n```lean\n' + increment + '\n```\n';
  const changed = { ...node.task, objective: node.task.objective + handoff };
  const rest = co.tasks.filter((item: any) => item.task.id !== taskId).map((item: any) => item.task);
  const firstAdvisory = rest.findIndex((task: any) => task.id === 'initial_research_1');
  assert(firstAdvisory >= 0);
  const tasks = [...rest.slice(0, firstAdvisory), changed, ...rest.slice(firstAdvisory)];
  const groups = co.groups.map((record: any) => record.group);
  const proposal = { id, baseVersion: co.planVersion, tasks, groups,
    ...(co.proofRoutes ? { proofRoutes: co.proofRoutes } : {}) };
  const plan = parseCooperationPlan(state.problem, proposal);
  for (const item of co.tasks) if (item.task.id !== taskId) assert.equal(
    canonicalMathJson(plan.tasks.find(task => task.id === item.task.id)), canonicalMathJson(item.task));
  const { objective: _old, ...oldMathematics } = node.task;
  const { objective: _new, ...newMathematics } = plan.tasks.find(task => task.id === taskId)!;
  assert.equal(canonicalMathJson(oldMathematics), canonicalMathJson(newMathematics));
  assert.equal(canonicalMathJson(plan.groups), canonicalMathJson(groups));
  assert.equal(canonicalMathJson(plan.proofRoutes ?? null), canonicalMathJson(co.proofRoutes ?? null));
  const dependencies = new Map(co.tasks.map((item: any) => [item.task.id,
    [...item.task.dependsOn, ...(item.alternativeRoutes?.flatMap((route: any) =>
      [...route.prerequisiteTaskIds, route.closingTaskId]) ?? []),
      ...(item.assignment?.dependencies?.map((value: any) => value.taskId) ?? [])]]));
  assert.deepEqual([...invalidatedTaskIds(co.tasks, plan.tasks, new Set(), dependencies)], [taskId]);
  const wireBytes = Buffer.byteLength(JSON.stringify(proposal) + '\n');
  assert(wireBytes <= 1024 * 1024);
  const validation = await queueRunEdit(run, proposal, true);
  assert.equal(validation.status, 'validated');
  fs.writeFileSync(path.join(stage, 'state-before.json'), bytes, { flag: 'wx' });
  fs.writeFileSync(path.join(stage, 'complete-handoff.md'), handoff, { flag: 'wx' });
  fs.writeFileSync(path.join(stage, 'preparation.json'), JSON.stringify({
    observedAt: new Date().toISOString(), runId: state.runId, proposal, validation, wireBytes,
    expectedAffectedTasks: [taskId], otherActiveAssignmentsPreserved: true,
    taskMathematicsUnchanged: true, sourceSHA256: sourceHash,
    incrementSHA256: mathDigest(increment), canonicalCommit: co.canonicalCommit,
    canonicalSourceSHA256: mathDigest(canonical.stdout), localKernelExitCode: 0,
    nativeTaskProofAccepted: false, directStateWrites: false,
  }, null, 2) + '\n', { flag: 'wx' });
  const queued = await queueRunEdit(run, proposal);
  fs.writeFileSync(receiptFile, JSON.stringify({ observedAt: new Date().toISOString(),
    runId: state.runId, editId: id, result: queued, newLeanInvocations: 0,
    nativeTaskProofAccepted: false }, null, 2) + '\n', { flag: 'wx' });
  console.log(JSON.stringify(queued));
}
