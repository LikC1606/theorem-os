import fs from 'node:fs';
import path from 'node:path';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { queueRunEdit } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/honeycomb-new-build-continuation-20261024/runtime/src/solver/humanEdit';
import { canonicalMathJson, mathDigest } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/honeycomb-new-build-continuation-20261024/runtime/src/math/mathRuntimeIo';
import { invalidatedTaskIds, parseCooperationPlan } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/honeycomb-new-build-continuation-20261024/runtime/src/solver/tasks';

const stage = import.meta.dir;
const sourceStage = path.join(stage, '../honeycomb-width-five-20261025');
const run = '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/tasks/HoneycombBridgeFiniteness/attempts/workflow-20261024/result.json';
const id = 'honeycomb-width-five-checked-proof-20261025';
const receiptFile = path.join(stage, 'queue-receipt.json');
if (fs.existsSync(receiptFile)) {
  console.log(JSON.stringify({ status: 'already-recorded', receiptFile }));
} else {
  const sourceHash = 'ba0a1c09a7ff973ccb68198c1d01428684e8dd49cbaee5df3dc7e83338582750';
  const incrementHash = 'a33eef19ac38782883227589dc48e125ff7e3d4379da9f6cf4ebc20e9c8760ca';
  const source = fs.readFileSync(path.join(sourceStage, 'WidthFive.lean'));
  const increment = fs.readFileSync(path.join(sourceStage, 'WidthFive.lean.inc'), 'utf8');
  assert.equal(mathDigest(source), sourceHash);
  assert.equal(mathDigest(increment), incrementHash);
  assert(source.toString('utf8').includes(increment));
  const checks = ['summability-03', 'explicit-types-04'].map(stem => {
    const result = JSON.parse(fs.readFileSync(path.join(sourceStage, stem + '-result.json'), 'utf8'));
    assert.equal(result.actualExitCode, 0);
    assert.equal(result.sourceSHA256, sourceHash);
    const output = fs.readFileSync(path.join(sourceStage, stem + '.stdout.log'), 'utf8');
    const reports = [...output.matchAll(/depends on axioms:\s*\[([^\]]*)\]/gu)];
    assert.equal(reports.length, 6);
    for (const report of reports) for (const axiom of report[1].split(',').map(s => s.trim()).filter(Boolean))
      assert(['propext', 'Classical.choice', 'Quot.sound'].includes(axiom));
    assert.equal(fs.readFileSync(path.join(sourceStage, stem + '.stderr.log')).length, 0);
    return { stem, sourceSHA256: sourceHash, actualExitCode: 0, durationSeconds: result.durationSeconds };
  });
  const proposed = JSON.parse(fs.readFileSync(path.join(sourceStage, 'native-task-proposal.json'), 'utf8'));
  assert.equal(proposed.id, 'width_five_summability_ba0a1c09');
  assert.equal(proposed.kind, 'lemma');
  assert.deepEqual(proposed.dependsOn, ['sums_reduction']);
  assert.equal(proposed.theoremName, 'OAI.PolynomialVacuumBridge.Corridor.width_five_summability_diagnostic');
  assert.equal(proposed.type, 'Summable (OAI.PolynomialVacuumBridge.Corridor.weight (h := 5)) ∧ Summable (OAI.PolynomialVacuumBridge.Corridor.firstLengthWeight (h := 5))');
  assert(proposed.objective.includes(increment));
  const loader = fs.readFileSync(path.join(stage, 'install-increment.py'), 'utf8');
  const smoke = JSON.parse(fs.readFileSync(path.join(stage, 'loader-smoke-result.json'), 'utf8'));
  assert.equal(smoke.loaderSHA256, mathDigest(loader));
  assert.equal(smoke.incrementSHA256, incrementHash);
  assert(smoke.idempotent && smoke.allPreviousSourceBytesPreserved && !smoke.activeSourceChanged);
  const quickHandoff = 'This exact fixed-height-five proof is already fully kernel-checked. To avoid transcribing the 361-state table, execute the following complete loader once from your assigned worktree root. It verifies and inserts the exact checked increment before the unchanged original-goal declaration, preserves every existing source byte, and is idempotent. It stops on a partial name collision rather than overwriting any current proof. This command is for the ordinary assigned worker, not a direct host source edit. The full readable increment is also included below. After insertion, complete ordinary typed proof delivery so the independent host performs native acceptance and integration; do not repeat standalone Lean/Lake checks or rewrite an unchanged proven table for style or linter warnings. Preserve all existing declarations and unresolved all-height work. This input is external mathematical assistance, not a publisher solution or native receipt.\n\n```sh\n/usr/bin/python3 - <<\'PY\'\n' + loader + '\nPY\n```\n\n';
  const task = { ...proposed, objective: quickHandoff + proposed.objective };
  const bytes = fs.readFileSync(run + '.runtime/state.json');
  const state = JSON.parse(bytes.toString('utf8')), co = state.cooperation;
  assert.equal(state.runId, '8bd4a613-c70e-4e96-b298-c9d22cfafaf3');
  assert.equal(state.buildDigest, '7e2c42e897361d27b0aa6bf216f74ed7ba71aa32987771ade075193bed54c19f');
  assert(['running', 'checking'].includes(state.phase));
  assert(!co.edits?.some((edit: any) => edit.id === id));
  assert(!co.tasks.some((item: any) => item.task.id === task.id || item.task.theoremName === task.theoremName));
  assert(co.tasks.some((item: any) => item.task.id === 'sums_reduction' && item.status === 'integrated'));
  const canonical = spawnSync('git', ['--no-optional-locks', 'show', co.canonicalCommit + ':generated/problem/Submission.lean'],
    { cwd: state.worktree, encoding: 'utf8', maxBuffer: 4 * 1024 * 1024 });
  assert.equal(canonical.status, 0);
  for (const helper of ['bridgeSummable_firstLengthWeight_of_mu_bound', 'bridgeSummable_weight_of_summable_firstLengthWeight']) assert(canonical.stdout.includes(helper));
  assert(!canonical.stdout.includes('namespace WidthFive'));
  const oldTasks = co.tasks.map((record: any) => record.task), index = oldTasks.findIndex((item: any) => item.kind === 'research');
  assert(index >= 0);
  const tasks = [...oldTasks.slice(0, index), task, ...oldTasks.slice(index)];
  const groups = co.groups.map((record: any) => record.group);
  const proposal = { id, baseVersion: co.planVersion, tasks, groups, ...(co.proofRoutes ? { proofRoutes: co.proofRoutes } : {}) };
  const plan = parseCooperationPlan(state.problem, proposal);
  for (const item of co.tasks) assert.equal(canonicalMathJson(plan.tasks.find(task => task.id === item.task.id)), canonicalMathJson(item.task));
  assert.equal(canonicalMathJson(plan.groups), canonicalMathJson(groups));
  assert.equal(canonicalMathJson(plan.proofRoutes ?? null), canonicalMathJson(co.proofRoutes ?? null));
  const dependencies = new Map(co.tasks.map((item: any) => [item.task.id,
    [...item.task.dependsOn, ...(item.alternativeRoutes?.flatMap((route: any) => [...route.prerequisiteTaskIds, route.closingTaskId]) ?? []),
      ...(item.assignment?.dependencies?.map((value: any) => value.taskId) ?? [])]]));
  assert.deepEqual([...invalidatedTaskIds(co.tasks, plan.tasks, new Set(), dependencies)], []);
  const wireBytes = Buffer.byteLength(JSON.stringify(proposal) + '\n');
  assert(wireBytes <= 1024 * 1024);
  const validation = await queueRunEdit(run, proposal, true);
  assert.equal(validation.status, 'validated');
  fs.writeFileSync(path.join(stage, 'state-before.json'), bytes, { flag: 'wx' });
  fs.writeFileSync(path.join(stage, 'complete-handoff.md'), task.objective, { flag: 'wx' });
  fs.writeFileSync(path.join(stage, 'preparation.json'), JSON.stringify({ observedAt: new Date().toISOString(),
    runId: state.runId, proposal, validation, wireBytes, checks, incrementSHA256: incrementHash,
    expectedInvalidatedExistingTasks: [], existingTaskContractsUnchanged: true,
    sourceEditedDirectlyByRoot: false, nativeTaskAcceptanceAdded: false,
    canonicalCommit: co.canonicalCommit, canonicalSourceSHA256: mathDigest(canonical.stdout),
  }, null, 2) + '\n', { flag: 'wx' });
  const queued = await queueRunEdit(run, proposal);
  fs.writeFileSync(receiptFile, JSON.stringify({ observedAt: new Date().toISOString(), runId: state.runId,
    editId: id, result: queued, newLeanInvocations: 0, nativeTaskAcceptanceAdded: false }, null, 2) + '\n', { flag: 'wx' });
  console.log(JSON.stringify(queued));
}
