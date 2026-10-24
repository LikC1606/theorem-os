import fs from 'node:fs';
import path from 'node:path';
import assert from 'node:assert/strict';
import { queueRunEdit } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/honeycomb-new-build-continuation-20261024/runtime/src/solver/humanEdit';
import { canonicalMathJson, mathDigest } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/honeycomb-new-build-continuation-20261024/runtime/src/math/mathRuntimeIo';
import { invalidatedTaskIds, parseCooperationPlan } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/honeycomb-new-build-continuation-20261024/runtime/src/solver/tasks';

const stage = import.meta.dir;
const flat = path.join(stage, '../honeycomb-width-five-flat-20261025');
const run = '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/tasks/HoneycombBridgeFiniteness/attempts/workflow-20261024/result.json';
const id = 'honeycomb-width-five-context-repair-20261025';
const taskId = 'width_five_summability_ba0a1c09';
const sourceSHA256 = 'ff2840a46faa26cc36d2391cfbc7ef9b961283aa3ae6d72ea8933b6d155b9350';
const incrementSHA256 = '1ea208c68cea9922489f77d3976d865b24f17a25b7ea4fcd42734473288e4291';
const receiptFile = path.join(stage, 'queue-receipt.json');
const read = (file: string) => JSON.parse(fs.readFileSync(file, 'utf8'));
if (fs.existsSync(receiptFile)) {
  console.log(JSON.stringify({ status: 'already-recorded', receiptFile }));
} else {
  const source = fs.readFileSync(path.join(flat, 'kernel-compile-01-source.lean'));
  const increment = fs.readFileSync(path.join(flat, 'WidthFiveFlat.lean.inc'), 'utf8');
  assert.equal(mathDigest(source), sourceSHA256);
  assert.equal(mathDigest(increment), incrementSHA256);
  assert(source.toString('utf8').includes(increment));
  assert(!/^\s*(?:namespace|end|section|open|set_option)\b/mu.test(increment));
  const compile = read(path.join(flat, 'kernel-compile-01-result.json'));
  const probe = read(path.join(flat, 'exact-types-02-result.json'));
  assert.equal(compile.actualExitCode, 0);
  assert.equal(compile.sourceSHA256, sourceSHA256);
  assert.equal(probe.actualExitCode, 0);
  assert.equal(probe.candidateSHA256, sourceSHA256);
  assert.equal(probe.importedModuleSHA256, compile.outputModuleSHA256);
  assert.equal(mathDigest(fs.readFileSync(path.join(flat, 'exact-types-02-source.lean'))), probe.sourceSHA256);
  const output = fs.readFileSync(path.join(flat, 'exact-types-02.stdout.log'), 'utf8');
  const axiomReports = [...output.matchAll(/depends on axioms:\s*\[([^\]]*)\]/gu)];
  assert.equal(axiomReports.length, 6);
  for (const report of axiomReports) for (const axiom of report[1].split(',').map(s => s.trim()).filter(Boolean))
    assert(['propext', 'Classical.choice', 'Quot.sound'].includes(axiom));
  assert(output.includes('width_five_summability_diagnostic'));
  for (const name of ['weight', 'firstLengthWeight']) assert(output.includes(
    '(@OAI.PolynomialVacuumBridge.Corridor.' + name + ' (@OfNat.ofNat Nat (nat_lit 5)'));
  for (const stem of ['kernel-compile-01', 'exact-types-02'])
    assert.equal(fs.readFileSync(path.join(flat, stem + '.stderr.log')).length, 0);
  const guard = read(path.join(flat, 'source-preflight-02-result.json'));
  assert(guard.results.some((item: any) => item.name === 'project' && item.passed && item.sourceSHA256 === sourceSHA256));
  const loader = fs.readFileSync(path.join(stage, 'install-flat-increment.py'), 'utf8');
  const smoke = read(path.join(stage, 'loader-smoke-result.json'));
  assert.equal(smoke.loaderSHA256, mathDigest(loader));
  assert.equal(smoke.incrementSHA256, incrementSHA256);
  assert(smoke.idempotent && smoke.allPreviousSourceBytesPreserved && !smoke.activeSourceChanged && smoke.fixedSourceGuardPassedAfterInsertion);
  const bytes = fs.readFileSync(run + '.runtime/state.json');
  const state = JSON.parse(bytes.toString('utf8')), co = state.cooperation;
  assert.equal(state.runId, '8bd4a613-c70e-4e96-b298-c9d22cfafaf3');
  assert.equal(state.buildDigest, '7e2c42e897361d27b0aa6bf216f74ed7ba71aa32987771ade075193bed54c19f');
  assert(['running', 'checking'].includes(state.phase));
  assert(!co.edits.some((edit: any) => edit.id === id));
  const node = co.tasks.find((item: any) => item.task.id === taskId);
  assert(node && ['blocked', 'pending'].includes(node.status) && !node.proof && !node.integratedCheck);
  assert.equal(node.task.theoremName, 'OAI.PolynomialVacuumBridge.Corridor.width_five_summability_diagnostic');
  assert.equal(node.task.type, 'Summable (OAI.PolynomialVacuumBridge.Corridor.weight (h := 5)) ∧ Summable (OAI.PolynomialVacuumBridge.Corridor.firstLengthWeight (h := 5))');
  assert.deepEqual(node.task.dependsOn, ['sums_reduction']);
  const objective = 'The previous namespaced insertion was rejected by the fixed source-context guard before Lean checking. Use this replacement handoff only. The unconditional height-five proof below is now flattened with distinct widthFive helper names and named instances. The exact fixed source guard passes both the validation project and insertion into the current integrated canonical source; a new full Lean compile and six exact type/axiom checks pass. Do not weaken the guard or change original declarations/context.\n\n' +
    'Execute this complete loader once from your assigned worktree root. It inserts the exact checked increment before the unchanged original-goal declaration, preserves existing source bytes, and is idempotent. It stops on a partial old or new increment. The full readable Lean increment follows. Then deliver the normal typed proof for independent host native checking and integration. Preserve the all-height work. Do not repeat unchanged standalone Lean/Lake diagnostics or reformat the checked tables. These are external public mathematical helpers, not a native acceptance receipt or publisher solution.\n\n```sh\n/usr/bin/python3 - <<\'PY\'\n' +
    loader + '\nPY\n```\n\nComplete checked flat Lean increment:\n```lean\n' + increment + '\n```\n';
  const tasks = co.tasks.map((item: any) => item.task.id === taskId ? { ...item.task, objective } : item.task);
  const groups = co.groups.map((record: any) => record.group);
  const proposal = { id, baseVersion: co.planVersion, tasks, groups, ...(co.proofRoutes ? { proofRoutes: co.proofRoutes } : {}) };
  const plan = parseCooperationPlan(state.problem, proposal);
  for (const item of co.tasks) if (item.task.id !== taskId)
    assert.equal(canonicalMathJson(plan.tasks.find(task => task.id === item.task.id)), canonicalMathJson(item.task));
  const { objective: _old, ...oldContract } = node.task;
  const { objective: _new, ...newContract } = plan.tasks.find(task => task.id === taskId)!;
  assert.equal(canonicalMathJson(oldContract), canonicalMathJson(newContract));
  assert.equal(canonicalMathJson(plan.groups), canonicalMathJson(groups));
  assert.equal(canonicalMathJson(plan.proofRoutes ?? null), canonicalMathJson(co.proofRoutes ?? null));
  const dependencies = new Map(co.tasks.map((item: any) => [item.task.id,
    [...item.task.dependsOn, ...(item.alternativeRoutes?.flatMap((route: any) => [...route.prerequisiteTaskIds, route.closingTaskId]) ?? []),
      ...(item.assignment?.dependencies?.map((value: any) => value.taskId) ?? [])]]));
  assert.deepEqual([...invalidatedTaskIds(co.tasks, plan.tasks, new Set(), dependencies)], [taskId]);
  const wireBytes = Buffer.byteLength(JSON.stringify(proposal) + '\n');
  assert(wireBytes <= 1024 * 1024);
  const validation = await queueRunEdit(run, proposal, true);
  assert.equal(validation.status, 'validated');
  fs.writeFileSync(path.join(stage, 'state-before-requeue.json'), bytes, { flag: 'wx' });
  fs.writeFileSync(path.join(stage, 'complete-handoff.md'), objective, { flag: 'wx' });
  fs.writeFileSync(path.join(stage, 'preparation.json'), JSON.stringify({ observedAt: new Date().toISOString(),
    runId: state.runId, proposal, validation, wireBytes, sourceSHA256, incrementSHA256,
    fullCompileSeconds: compile.durationSeconds, expectedAffectedTasks: [taskId], originalTaskMathematicsUnchanged: true,
    allOtherTaskContractsUnchanged: true, fixedSourceGuardPassedBeforeDelivery: true,
    activeSourceOrStateDirectlyChangedByRoot: false, nativeTaskAcceptanceAddedByQueue: false,
  }, null, 2) + '\n', { flag: 'wx' });
  const queued = await queueRunEdit(run, proposal);
  fs.writeFileSync(receiptFile, JSON.stringify({ observedAt: new Date().toISOString(), runId: state.runId,
    editId: id, result: queued, nativeTaskAcceptanceAddedByQueue: false }, null, 2) + '\n', { flag: 'wx' });
  console.log(JSON.stringify(queued));
}
