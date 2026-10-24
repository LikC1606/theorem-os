import fs from 'node:fs';
import path from 'node:path';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { queueRunEdit } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/honeycomb-new-build-continuation-20261024/runtime/src/solver/humanEdit';
import { canonicalMathJson, mathDigest } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/honeycomb-new-build-continuation-20261024/runtime/src/math/mathRuntimeIo';
import { invalidatedTaskIds, parseCooperationPlan } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/honeycomb-new-build-continuation-20261024/runtime/src/solver/tasks';

const stage = import.meta.dir;
const run = '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/tasks/HoneycombBridgeFiniteness/attempts/workflow-20261024/result.json';
const id = 'honeycomb-width-three-four-checked-proofs-20261025';
const receiptFile = path.join(stage, 'queue-receipt.json');
const specs = [
  { height: 3, directory: 'honeycomb-width-three-20261025', stem: 'WidthThree',
    taskFile: 'native-task-handoff.json', check: 'summability-01', axiomCount: 6,
    sourceHash: 'e0dd3d9678d060cd719c52092bed9a15244b6fdd357956779a9fa38a6f0fdf63',
    incrementHash: '375739ea3473e164e586091370a0bac3c03aab5a52a17e6a3cc46a3b7460cfc7' },
  { height: 4, directory: 'honeycomb-width-four-20261025', stem: 'WidthFour',
    taskFile: 'native-task-proposal.json', check: 'summability-02-final', axiomCount: 12,
    sourceHash: 'a8462a1922c107fde21cde91cb10c505f57860c5d926b3bb30df2869cd804e91',
    incrementHash: 'db6e35bfe5eba4bfae490a63997874ce18953292e266c8351410097cbdae41b0' },
];

if (fs.existsSync(receiptFile)) {
  console.log(JSON.stringify({ status: 'already-recorded', receiptFile }));
} else {
  const checked = specs.map(spec => {
    const directory = path.join(stage, '..', spec.directory);
    const source = fs.readFileSync(path.join(directory, spec.stem + '.lean'));
    const increment = fs.readFileSync(path.join(directory, spec.stem + '.lean.inc'), 'utf8');
    const result = JSON.parse(fs.readFileSync(path.join(directory, spec.check + '-result.json'), 'utf8'));
    const task = JSON.parse(fs.readFileSync(path.join(directory, spec.taskFile), 'utf8'));
    assert.equal(mathDigest(source), spec.sourceHash);
    assert.equal(mathDigest(increment), spec.incrementHash);
    assert.equal(result.actualExitCode, 0);
    assert.equal(result.sourceSHA256, spec.sourceHash);
    assert(source.toString('utf8').includes(increment));
    assert(task.objective.includes(increment));
    assert.equal(task.kind, 'lemma');
    assert.equal(task.proofPath, 'Submission.lean');
    assert.equal(task.groupId, 'main');
    assert.deepEqual(task.dependsOn, ['sums_reduction']);
    assert.equal(task.type, `Summable (OAI.PolynomialVacuumBridge.Corridor.weight (h := ${spec.height})) ∧ Summable (OAI.PolynomialVacuumBridge.Corridor.firstLengthWeight (h := ${spec.height}))`);
    const output = fs.readFileSync(path.join(directory, spec.check + '.stdout.log'), 'utf8');
    const reports = [...output.matchAll(/depends on axioms:\s*\[([^\]]*)\]/gu)];
    assert.equal(reports.length, spec.axiomCount);
    for (const report of reports) for (const axiom of report[1].split(',').map(s => s.trim()).filter(Boolean))
      assert(['propext', 'Classical.choice', 'Quot.sound'].includes(axiom));
    assert.equal(fs.readFileSync(path.join(directory, spec.check + '.stderr.log')).length, 0);
    return { spec, task, increment, result };
  });
  const bytes = fs.readFileSync(run + '.runtime/state.json');
  const state = JSON.parse(bytes.toString('utf8')), co = state.cooperation;
  assert.equal(state.runId, '8bd4a613-c70e-4e96-b298-c9d22cfafaf3');
  assert.equal(state.buildDigest, '7e2c42e897361d27b0aa6bf216f74ed7ba71aa32987771ade075193bed54c19f');
  assert(['running', 'checking'].includes(state.phase));
  assert(!co.edits?.some((edit: any) => edit.id === id));
  assert(co.tasks.some((item: any) => item.task.id === 'sums_reduction' && item.status === 'integrated'));
  for (const { task } of checked) assert(!co.tasks.some((item: any) =>
    item.task.id === task.id || item.task.theoremName === task.theoremName));
  const canonical = spawnSync('git', ['--no-optional-locks', 'show', co.canonicalCommit + ':generated/problem/Submission.lean'],
    { cwd: state.worktree, encoding: 'utf8', maxBuffer: 4 * 1024 * 1024 });
  assert.equal(canonical.status, 0);
  for (const name of ['bridgeSummable_firstLengthWeight_of_mu_bound', 'bridgeSummable_weight_of_summable_firstLengthWeight'])
    assert(canonical.stdout.includes(name));
  for (const { spec, task } of checked) {
    assert(!canonical.stdout.includes('namespace ' + spec.stem));
    assert(!canonical.stdout.includes(task.theoremName.split('.').at(-1)));
  }
  const oldTasks = co.tasks.map((record: any) => record.task);
  const beforeResearch = oldTasks.findIndex((task: any) => task.kind === 'research');
  assert(beforeResearch >= 0);
  const tasks = [...oldTasks.slice(0, beforeResearch), ...checked.map(({ task }) => task), ...oldTasks.slice(beforeResearch)];
  const groups = co.groups.map((record: any) => record.group);
  const proposal = { id, baseVersion: co.planVersion, tasks, groups,
    ...(co.proofRoutes ? { proofRoutes: co.proofRoutes } : {}) };
  const plan = parseCooperationPlan(state.problem, proposal);
  for (const item of co.tasks) assert.equal(canonicalMathJson(
    plan.tasks.find(task => task.id === item.task.id)), canonicalMathJson(item.task));
  assert.equal(canonicalMathJson(plan.groups), canonicalMathJson(groups));
  assert.equal(canonicalMathJson(plan.proofRoutes ?? null), canonicalMathJson(co.proofRoutes ?? null));
  const dependencies = new Map(co.tasks.map((item: any) => [item.task.id,
    [...item.task.dependsOn, ...(item.alternativeRoutes?.flatMap((route: any) =>
      [...route.prerequisiteTaskIds, route.closingTaskId]) ?? []),
      ...(item.assignment?.dependencies?.map((value: any) => value.taskId) ?? [])]]));
  assert.deepEqual([...invalidatedTaskIds(co.tasks, plan.tasks, new Set(), dependencies)], []);
  const wireBytes = Buffer.byteLength(JSON.stringify(proposal) + '\n');
  assert(wireBytes <= 1024 * 1024);
  const validation = await queueRunEdit(run, proposal, true);
  assert.equal(validation.status, 'validated');
  fs.writeFileSync(path.join(stage, 'state-before.json'), bytes, { flag: 'wx' });
  fs.writeFileSync(path.join(stage, 'complete-handoff.md'), checked.map(({ spec, task }) =>
    '# Height ' + spec.height + '\n\n' + task.objective).join('\n\n'), { flag: 'wx' });
  fs.writeFileSync(path.join(stage, 'preparation.json'), JSON.stringify({
    observedAt: new Date().toISOString(), runId: state.runId, proposal, validation, wireBytes,
    expectedAffectedExistingTasks: [], existingTasksUnchanged: true,
    sourceProofs: checked.map(({ spec, result, task }) => ({ taskId: task.id,
      sourceSHA256: spec.sourceHash, incrementSHA256: spec.incrementHash,
      actualExitCode: result.actualExitCode, durationSeconds: result.durationSeconds,
      axiomReportsChecked: spec.axiomCount })),
    canonicalCommit: co.canonicalCommit, canonicalSourceSHA256: mathDigest(canonical.stdout),
    directStateWrites: false, nativeTaskAcceptanceAdded: false,
  }, null, 2) + '\n', { flag: 'wx' });
  const queued = await queueRunEdit(run, proposal);
  fs.writeFileSync(receiptFile, JSON.stringify({ observedAt: new Date().toISOString(),
    runId: state.runId, editId: id, result: queued, newLeanInvocations: 0,
    nativeTaskAcceptanceAdded: false }, null, 2) + '\n', { flag: 'wx' });
  console.log(JSON.stringify(queued));
}
