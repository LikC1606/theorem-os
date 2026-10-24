import fs from 'node:fs';
import path from 'node:path';
import assert from 'node:assert/strict';
import { queueRunEdit } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/honeycomb-new-build-continuation-20261024/runtime/src/solver/humanEdit';
import { canonicalMathJson, mathDigest } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/honeycomb-new-build-continuation-20261024/runtime/src/math/mathRuntimeIo';
import { invalidatedTaskIds, parseCooperationPlan } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/honeycomb-new-build-continuation-20261024/runtime/src/solver/tasks';

const stage = import.meta.dir;
const recovery = path.join(stage, '../honeycomb-width-five-context-recovery-20261025');
const flat = path.join(stage, '../honeycomb-width-five-flat-20261025');
const run = '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/tasks/HoneycombBridgeFiniteness/attempts/workflow-20261024/result.json';
const taskId = 'width_five_summability_ba0a1c09';
const id = 'honeycomb-width-five-compact-handoff-20261025';
const receiptFile = path.join(stage, 'queue-receipt.json');
const read = (file: string) => JSON.parse(fs.readFileSync(file, 'utf8'));
if (fs.existsSync(receiptFile)) {
  console.log(JSON.stringify({ status: 'already-recorded', receiptFile }));
} else {
  const bytes = fs.readFileSync(run + '.runtime/state.json');
  const state = JSON.parse(bytes.toString('utf8')), co = state.cooperation;
  assert.equal(state.runId, '8bd4a613-c70e-4e96-b298-c9d22cfafaf3');
  assert.equal(state.buildDigest, '7e2c42e897361d27b0aa6bf216f74ed7ba71aa32987771ade075193bed54c19f');
  assert(['running', 'checking'].includes(state.phase));
  assert(!co.edits.some((edit: any) => edit.id === id));
  const node = co.tasks.find((item: any) => item.task.id === taskId);
  assert(node && ['running', 'pending', 'conditional'].includes(node.status) && !node.proof && !node.integratedCheck);
  const loader = fs.readFileSync(path.join(recovery, 'install-flat-increment.py'), 'utf8');
  const smoke = read(path.join(recovery, 'loader-smoke-result.json'));
  assert.equal(mathDigest(loader), smoke.loaderSHA256);
  assert(smoke.idempotent && smoke.allPreviousSourceBytesPreserved && smoke.fixedSourceGuardPassedAfterInsertion);
  assert.equal(smoke.incrementSHA256, '1ea208c68cea9922489f77d3976d865b24f17a25b7ea4fcd42734473288e4291');
  const compile = read(path.join(flat, 'kernel-compile-01-result.json'));
  const probe = read(path.join(flat, 'exact-types-02-result.json'));
  assert.equal(compile.actualExitCode, 0);
  assert.equal(probe.actualExitCode, 0);
  assert.equal(compile.sourceSHA256, probe.candidateSHA256);
  assert.equal(compile.outputModuleSHA256, probe.importedModuleSHA256);
  const objective = 'Immediate proof adoption, same unconditional height-five contract. The previous handoff repeated the readable proof table alongside its compressed loader; repeated context-threshold checkpoints produced research-only deliveries without saving the proof. This handoff contains ONLY the identical checked self-contained loader. Its increment SHA256 is ' + smoke.incrementSHA256 + '. The original fixed source guard, local kernel compile, explicit height-five types and standard axioms were checked in the public frozen evidence. These local checks do not replace host native acceptance.\n\n' +
    'From YOUR assigned worktree root execute this command FIRST. It inserts the complete checked increment into generated/problem/Submission.lean before the unchanged original goal and preserves prior bytes. Save that file in the normal proof delivery. Then deliver the ordinary typed proof for OAI.PolynomialVacuumBridge.Corridor.width_five_summability_diagnostic, with no new mathematical assumptions, so the host can check and integrate it. Do not replace proof adoption with another RESEARCH.md-only delivery. Do not recompile the unchanged standalone validation project. If insertion fails, report the exact public error; preserve existing source.\n\n```sh\n/usr/bin/python3 - <<\'PY\'\n' + loader + '\nPY\n```\n';
  const oldObjectiveBytes = Buffer.byteLength(node.task.objective);
  const objectiveBytes = Buffer.byteLength(objective);
  assert(objectiveBytes < oldObjectiveBytes / 4);
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
  assert(Buffer.byteLength(JSON.stringify(proposal) + '\n') <= 1024 * 1024);
  const validation = await queueRunEdit(run, proposal, true);
  assert.equal(validation.status, 'validated');
  fs.writeFileSync(path.join(stage, 'compact-handoff.md'), objective, { flag: 'wx' });
  fs.writeFileSync(path.join(stage, 'preparation.json'), JSON.stringify({ observedAt: new Date().toISOString(),
    runId: state.runId, buildDigest: state.buildDigest, stateSHA256: mathDigest(bytes), proposal, validation,
    taskId, oldObjectiveBytes, objectiveBytes, reductionFraction: 1 - objectiveBytes / oldObjectiveBytes,
    loaderSHA256: mathDigest(loader), incrementSHA256: smoke.incrementSHA256,
    expectedAffectedTasks: [taskId], mathematicalContractSHA256: mathDigest(canonicalMathJson(oldContract)),
    preservedTasks: co.tasks.filter((item: any) => item.task.id !== taskId).map((item: any) => ({
      id: item.task.id, contractSHA256: mathDigest(canonicalMathJson(item.task)),
      proofSHA256: mathDigest(canonicalMathJson(item.proof ?? null)),
      integrationSHA256: mathDigest(canonicalMathJson(item.integratedCheck ?? null)),
    })),
    groupContractsAndRoutesUnchanged: true, directActiveSourceOrStateWrites: false,
    repeatedLeanChecks: false, nativeAcceptanceAddedByQueue: false,
  }, null, 2) + '\n', { flag: 'wx' });
  const result = await queueRunEdit(run, proposal);
  fs.writeFileSync(receiptFile, JSON.stringify({ observedAt: new Date().toISOString(), runId: state.runId, editId: id,
    result, nativeAcceptanceAddedByQueue: false }, null, 2) + '\n', { flag: 'wx' });
  console.log(JSON.stringify({ result, oldObjectiveBytes, objectiveBytes }));
}
