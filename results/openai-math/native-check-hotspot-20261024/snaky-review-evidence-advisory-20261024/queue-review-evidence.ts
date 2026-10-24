import fs from 'node:fs';
import path from 'node:path';
import assert from 'node:assert/strict';
import { queueRunEdit } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/snaky-conditional-native-followup-20261023/runtime/src/solver/humanEdit';
import { canonicalMathJson, mathDigest } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/snaky-conditional-native-followup-20261023/runtime/src/math/mathRuntimeIo';
import { invalidatedTaskIds, parseCooperationPlan } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/snaky-conditional-native-followup-20261023/runtime/src/solver/tasks';
import { proofReceiptsMatch } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/snaky-conditional-native-followup-20261023/runtime/src/solver/modules/evidence';
import { ownedSourceDigest } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/snaky-conditional-native-followup-20261023/runtime/src/solver/cooperativeProof';

const stage = import.meta.dir;
const run = '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/snaky-conditional-native-followup-20261023/native-v8-recovery1/result.json';
const taskId = 'snaky_fixed_review_kernel_evidence_reference';
const receiptFile = path.join(stage, 'queue-receipt.json');
if (fs.existsSync(receiptFile)) {
  console.log(JSON.stringify({ status: 'already-recorded', receiptFile }));
} else {
  const bytes = fs.readFileSync(run + '.runtime/state.json');
  const state = JSON.parse(bytes.toString('utf8'));
  const co = state.cooperation;
  assert.equal(state.runId, 'e2b78e94-e26d-4b02-a8e5-53375547ef4d');
  assert.equal(state.buildDigest, '3cf310891edf8cb396f218531e1eb6c5a997622adb6d835e4b368ffa1c8e637d');
  assert.equal(state.phase, 'running');
  assert.equal(co.review?.status, 'running');
  assert(!co.tasks.some((node: any) => node.task.id === taskId));
  const review = co.review;
  const check = [state.check, ...state.workers.map((worker: any) => worker.check)]
    .find((item: any) => item?.passed && item.commit === review.commit && item.sourceDigest === review.sourceDigest);
  assert(check);
  assert(proofReceiptsMatch(check.verification, review.commit, state.problem.targets.map((target: any) => ({
    proofPath: target.proofPath, theoremName: target.theoremName, expectedSourceDeclarationHash: target.declarationHash,
    statementHash: state.problem.contract.statementHash, leanStatementHash: state.problem.contract.leanStatementHash }))));
  assert.equal(ownedSourceDigest(state.problem, state.worktree, review.commit), review.sourceDigest);
  const reviewer = state.workers.find((worker: any) => worker.id === review.workerId);
  assert(reviewer);
  const sourceFiles = state.problem.ownedFiles.map((file: string) => {
    const relative = path.join(state.problem.projectRelative, file);
    const canonical = fs.readFileSync(path.join(state.worktree, relative));
    const reviewed = fs.readFileSync(path.join(reviewer.worktree, relative));
    assert(canonical.equals(reviewed));
    return { path: file, bytes: canonical.length, sha256: mathDigest(canonical) };
  });
  const evidence = {
    evidence: 'recorded-not-replayed; advisory only; grants no acceptance',
    commit: check.commit, sourceDigest: check.sourceDigest, allOriginalTargetsMatched: true, sourceFiles,
    status: check.verification.status, durationMs: check.verification.durationMs,
    receipts: check.verification.results.map((item: any) => Object.fromEntries([
      'receiptId', 'theoremName', 'proofPath', 'proofHash', 'sourceDeclarationHash', 'statementHash', 'axioms',
      'goalsRemaining', 'sorryCount', 'admitCount', 'checkedAt', 'targetCommit', 'status'
    ].map(key => [key, item[key]])))
  };
  const objective = 'Operational evidence for the currently fixed independent review, supplied by the supervising user-authorized session. ' +
    'This paused shared reference schedules no new work and changes no proof contract. The host has already checked every original target ' +
    'at exactly the current review commit and owned-source digest; the current reviewer source files were compared byte-for-byte. ' +
    'Inspect these recorded kernel receipts, the saved proof, original assumptions and target meaning. They are evidence, not a verdict. ' +
    'If a specific discrepancy needs a Lean diagnostic, perform the discriminating check and save its reusable result. ' +
    'An unchanged whole-file rerun solely to obtain another success diagnostic adds no new source evidence. ' +
    'Two earlier review dispatches ended with an SSE stream idle timeout before publishing a verdict. ' +
    'Save the actual independent findings and any verdict in worktree-root RESEARCH.md using the existing review schema when ready; ' +
    'report a concrete gap instead of assuming acceptance. The independent host final check and fixed publisher comparator are still required.\n' +
    JSON.stringify(evidence);
  const task = { id: taskId, kind: 'research', objective, dependsOn: [], revision: 0,
    groupId: 'main', sharing: 'problem', status: 'paused' };
  const tasks = [...co.tasks.map((node: any) => node.task), task];
  const groups = co.groups.map((record: any) => record.group);
  const id = 'snaky-review-evidence-' + mathDigest(canonicalMathJson(evidence)).slice(0, 12);
  assert(!co.edits?.some((edit: any) => edit.id === id));
  const proposal = { id, baseVersion: co.planVersion, tasks, groups,
    ...(co.proofRoutes ? { proofRoutes: co.proofRoutes } : {}) };
  const plan = parseCooperationPlan(state.problem, proposal);
  for (const node of co.tasks) assert.equal(
    canonicalMathJson(plan.tasks.find(item => item.id === node.task.id)), canonicalMathJson(node.task));
  assert.equal(canonicalMathJson(plan.groups), canonicalMathJson(groups));
  assert.equal(canonicalMathJson(plan.proofRoutes ?? null), canonicalMathJson(co.proofRoutes ?? null));
  const dependencies = new Map(co.tasks.map((node: any) => [node.task.id,
    [...node.task.dependsOn, ...(node.alternativeRoutes?.flatMap((route: any) =>
      [...route.prerequisiteTaskIds, route.closingTaskId]) ?? []),
      ...(node.assignment?.dependencies?.map((item: any) => item.taskId) ?? [])]]));
  assert.deepEqual([...invalidatedTaskIds(co.tasks, plan.tasks, new Set(), dependencies)], []);
  const validation = await queueRunEdit(run, proposal, true);
  assert.equal(validation.status, 'validated');
  fs.writeFileSync(path.join(stage, 'state-before.json'), bytes, { flag: 'wx' });
  fs.writeFileSync(path.join(stage, 'kernel-evidence.json'), JSON.stringify(evidence, null, 2) + '\n', { flag: 'wx' });
  fs.writeFileSync(path.join(stage, 'preparation.json'), JSON.stringify({ capturedAt: new Date().toISOString(),
    run, runId: state.runId, stateSHA256: mathDigest(bytes), review, proposal, validation,
    existingTasksInvalidated: [], existingProofsAndReviewPreserved: true }, null, 2) + '\n', { flag: 'wx' });
  const queued = await queueRunEdit(run, proposal);
  fs.writeFileSync(receiptFile, JSON.stringify({ capturedAt: new Date().toISOString(), runId: state.runId,
    editId: id, result: queued, evidenceSHA256: mathDigest(canonicalMathJson(evidence)),
    newLeanInvocations: 0, verdictSupplied: false, nativeFinalAcceptance: false }, null, 2) + '\n', { flag: 'wx' });
  console.log(JSON.stringify(queued));
}
