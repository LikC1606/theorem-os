import fs from 'node:fs';
import path from 'node:path';
import assert from 'node:assert/strict';
import { queueRunEdit } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/snaky-conditional-native-followup-20261023/runtime/src/solver/humanEdit';
import { canonicalMathJson, mathDigest } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/snaky-conditional-native-followup-20261023/runtime/src/math/mathRuntimeIo';
import { invalidatedTaskIds, parseCooperationPlan } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/snaky-conditional-native-followup-20261023/runtime/src/solver/tasks';
import { proofReceiptsMatch } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/snaky-conditional-native-followup-20261023/runtime/src/solver/modules/evidence';

const stage = import.meta.dir;
const run = '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/snaky-conditional-native-followup-20261023/native-v8-recovery1/result.json';
const id = 'READ-scratch-tmp-HOST-REVIEW-EVIDENCE-json';
const receiptFile = path.join(stage, 'notice-queue-receipt.json');
if (fs.existsSync(receiptFile)) {
  console.log(JSON.stringify({ status: 'already-recorded', receiptFile }));
} else {
  const bytes = fs.readFileSync(run + '.runtime/state.json');
  const state = JSON.parse(bytes.toString('utf8'));
  const co = state.cooperation;
  assert.equal(state.runId, 'e2b78e94-e26d-4b02-a8e5-53375547ef4d');
  assert.equal(state.phase, 'running');
  assert.equal(co.review?.status, 'running');
  assert(!co.edits?.some((item: any) => item.id === id));
  const evidence = JSON.parse(fs.readFileSync(path.join(stage, 'kernel-evidence.json'), 'utf8'));
  assert.equal(co.review.commit, evidence.commit);
  assert.equal(co.review.sourceDigest, evidence.sourceDigest);
  const check = state.workers.find((worker: any) => worker.check?.passed &&
    worker.check.commit === evidence.commit && worker.check.sourceDigest === evidence.sourceDigest)?.check;
  assert(check);
  assert(proofReceiptsMatch(check.verification, evidence.commit, state.problem.targets.map((target: any) => ({
    proofPath: target.proofPath, theoremName: target.theoremName, expectedSourceDeclarationHash: target.declarationHash,
    statementHash: state.problem.contract.statementHash, leanStatementHash: state.problem.contract.leanStatementHash }))));
  const reviewer = state.workers.find((worker: any) => worker.id === co.review.workerId);
  assert(reviewer);
  for (const file of evidence.sourceFiles) {
    const rel = path.join(state.problem.projectRelative, file.path);
    for (const root of [state.worktree, reviewer.worktree])
      assert.equal(mathDigest(fs.readFileSync(path.join(root, rel))), file.sha256);
  }
  const tasks = co.tasks.map((node: any) => node.task);
  const groups = co.groups.map((record: any) => record.group);
  const proposal = { id, baseVersion: co.planVersion, tasks, groups,
    ...(co.proofRoutes ? { proofRoutes: co.proofRoutes } : {}) };
  const plan = parseCooperationPlan(state.problem, proposal);
  assert.equal(canonicalMathJson(plan.tasks), canonicalMathJson(tasks));
  assert.equal(canonicalMathJson(plan.groups), canonicalMathJson(groups));
  assert.equal(canonicalMathJson(plan.proofRoutes ?? null), canonicalMathJson(co.proofRoutes ?? null));
  const dependencies = new Map(co.tasks.map((node: any) => [node.task.id,
    [...node.task.dependsOn, ...(node.assignment?.dependencies?.map((item: any) => item.taskId) ?? [])]]));
  assert.deepEqual([...invalidatedTaskIds(co.tasks, plan.tasks, new Set(), dependencies)], []);
  const wireBytes = Buffer.byteLength(JSON.stringify({ id, baseVersion: co.planVersion, ...plan }) + '\n');
  assert(wireBytes < 64_000);
  const validation = await queueRunEdit(run, proposal, true);
  assert.equal(validation.status, 'validated');
  const root = fs.realpathSync(reviewer.worktree);
  const scratch = path.join(root, '.scratch', 'tmp');
  fs.mkdirSync(scratch, { recursive: true });
  assert.equal(fs.realpathSync(scratch), scratch);
  const file = path.join(scratch, 'HOST-REVIEW-EVIDENCE.json');
  const document = JSON.stringify({ schema: 'theorem-os.host-review-advisory.v1',
    origin: 'User-authorized supervising host session; existing kernel receipts only.',
    guidance: 'Inspect the original question, assumptions and saved source using these matching recorded receipts. ' +
      'Investigate any concrete gap independently; no verdict is supplied. An unchanged whole-file rerun adds no new source evidence. ' +
      'Save independent review findings and any verdict in worktree-root RESEARCH.md using the existing protocol. ' +
      'The host final check and fixed publisher comparator remain required.', evidence }, null, 2) + '\n';
  fs.writeFileSync(file, document, { flag: 'wx', mode: 0o444 });
  fs.writeFileSync(path.join(stage, 'HOST-REVIEW-EVIDENCE.json'), document, { flag: 'wx' });
  fs.writeFileSync(path.join(stage, 'notice-state-before.json'), bytes, { flag: 'wx' });
  fs.writeFileSync(path.join(stage, 'notice-preparation.json'), JSON.stringify({ capturedAt: new Date().toISOString(),
    run, runId: state.runId, proposal, validation, wireBytes, nativeReaderBytes: 64000,
    evidenceScratchFile: file, evidenceSHA256: mathDigest(document), existingTaskObjectsUnchanged: true,
    expectedInvalidatedTasks: [], expectedAffectedTasks: [], reviewAssignment: co.review }, null, 2) + '\n', { flag: 'wx' });
  const queued = await queueRunEdit(run, proposal);
  fs.writeFileSync(receiptFile, JSON.stringify({ capturedAt: new Date().toISOString(), runId: state.runId,
    editId: id, result: queued, newLeanInvocations: 0, verdictSupplied: false,
    mechanism: 'Unchanged complete plan through the normal edit queue triggers its existing active-session notification. ' +
      'The notification id points to the advisory scratch file; no task, proof, state or runtime is replaced.' }, null, 2) + '\n', { flag: 'wx' });
  console.log(JSON.stringify(queued));
}
