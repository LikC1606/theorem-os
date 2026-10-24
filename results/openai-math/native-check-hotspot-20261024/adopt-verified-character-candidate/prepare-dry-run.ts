import fs from 'node:fs';
import path from 'node:path';
import assert from 'node:assert/strict';
import { queueRunEdit } from '../../character-environment-adapter-20261023/unlimited-preparation-v2/runtime/src/solver/humanEdit';
import { mathDigest, canonicalMathJson } from '../../character-environment-adapter-20261023/unlimited-preparation-v2/runtime/src/math/mathRuntimeIo';
import { parseCooperationPlan } from '../../character-environment-adapter-20261023/unlimited-preparation-v2/runtime/src/solver/tasks';
import { readDeliveryLines } from '../../character-environment-adapter-20261023/unlimited-preparation-v2/runtime/src/solver/deliveries';
import { hasDeterministicLeanFailure } from '../../character-environment-adapter-20261023/unlimited-preparation-v2/runtime/src/solver/proofReuse';
import { attributeProofEvidence } from '../../character-environment-adapter-20261023/unlimited-preparation-v2/runtime/src/solver/modules/evidence';
import { createCharacterSourceTransport } from '../../character-environment-adapter-20261023/character-source-transport';

// The external-signal path is not recoverable in this frozen build. This entry
// deliberately has no enqueue or process-control mode: prepare and dry-run only.
assert.equal(process.argv.length, 2, 'This preflight supports no queue, signal, Lean or model actions.');
const stage = import.meta.dir;
const campaign = path.resolve(stage, '../../..');
const frozen = path.join(campaign, 'validation/character-environment-adapter-20261023/unlimited-preparation-v2');
const runtime = path.join(frozen, 'runtime');
const run = path.join(frozen, 'native-followup/result.json');
const stateFile = run + '.runtime/state.json';
const state = JSON.parse(fs.readFileSync(stateFile, 'utf8'));
assert.equal(state.runId, 'be2c8bbd-71c7-4dc5-aa21-1c3a7550a2c6');
assert.notEqual(state.phase, 'finished');
const candidateDirectory = path.join(stage, '../character-sync-def-v2-candidate');
const sourceFile = path.join(candidateDirectory, 'Submission.lean');
const source = fs.readFileSync(sourceFile);
const sourceSHA256 = mathDigest(source);
assert.equal(sourceSHA256, '5c0cbc35bd6335ab7c6d8d57bdece22a3065c6fdc7dee871d2577826b50396d3');
assert.equal(source.length, 795645);
const guardFile = path.join(stage, '../guard-preflight-v2/receipt.json');
const guard = JSON.parse(fs.readFileSync(guardFile, 'utf8'));
assert(guard.passed && guard.canonicalMergeFixedPoint && guard.sourceGuardPassedBeforeAndAfterMerge);
assert.equal(guard.sourceSHA256, sourceSHA256);
const buildFile = path.join(candidateDirectory, 'build-receipt.json');
const auditFile = path.join(candidateDirectory, 'audit-receipt.json');
const build = JSON.parse(fs.readFileSync(buildFile, 'utf8'));
const audit = JSON.parse(fs.readFileSync(auditFile, 'utf8'));
assert.equal(build.sourceSHA256, sourceSHA256);
assert.equal(audit.sourceSHA256, sourceSHA256);
assert.equal(build.exitCode, 0);
assert.equal(audit.exitCode, 0);
assert(audit.passed);
assert.equal(build.oleanSHA256, audit.oleanSHA256);
assert.equal(mathDigest(fs.readFileSync(path.join(candidateDirectory, 'Submission.olean'))), build.oleanSHA256);
assert.deepEqual([...audit.axioms].sort(), ['Classical.choice', 'Quot.sound', 'propext'].sort());
const transportEvidenceFile = path.join(stage, '../native-sync-def-attempt/transport-preparation.json');
const transportEvidence = JSON.parse(fs.readFileSync(transportEvidenceFile, 'utf8'));
assert.equal(transportEvidence.sourceSHA256, sourceSHA256);
assert(transportEvidence.exactSourceSandboxRoundtripPassed && transportEvidence.frozenDeliveryReaderConsumedLine);
const archive = state.cooperation;
const goal = archive.tasks.find((node: any) => node.task.kind === 'goal' && node.task.theoremName === guard.originalTarget);
assert(goal && archive.planVersion);
const target = state.problem.targets.find((target: any) => target.theoremName === goal.task.theoremName);
assert.equal(target.declarationHash, guard.originalDeclarationHash);
assert.equal(state.problem.contract.formalStatement,
  fs.readFileSync(path.join(campaign, 'metadata/challenges/CharacterVarietiesAllSeamsSupport.lean'), 'utf8'));
const transport = createCharacterSourceTransport(source, goal.task.id,
  path.posix.join(state.problem.projectRelative, goal.task.proofPath));
const serialInstruction = 'Run check-lean and submit through ordinary native delivery. Fixed review, host all-target kernel verification and the unchanged publisher comparator remain required. Reference receipts do not grant native acceptance.';
assert(transport.objective.includes(serialInstruction));
const objective = transport.objective.replace(serialInstruction,
  'Execute the exact loader once, confirm the printed source SHA and length, then immediately submit an ordinary completed native delivery for this assigned task. The host will perform all native mathematical verification. Do not run check-lean, Lean, Lake, a local checker, or a waiting loop in the model session. This V2 candidate has genuinely passed a complete independent Lean compilation and permitted-axiom audit. Fixed review, native independent host kernel verification, original-source guards and the unchanged publisher comparator remain required; independent preparation evidence is not native acceptance.');
const plan = {
  tasks: archive.tasks.map((node: any) => node === goal ? { ...node.task,
    ownerId: 'engineer', objective, revision: node.task.revision + 1 } : structuredClone(node.task)),
  groups: archive.groups.map((record: any) => structuredClone(record.group)),
  ...(archive.proofRoutes !== undefined ? { proofRoutes: structuredClone(archive.proofRoutes) } : {}),
};
const proposal = { id: 'character-verified-v2-' + sourceSHA256.slice(0, 12), baseVersion: archive.planVersion, ...plan };
const before = parseCooperationPlan(state.problem, { tasks: archive.tasks.map((node: any) => node.task),
  groups: archive.groups.map((record: any) => record.group),
  ...(archive.proofRoutes !== undefined ? { proofRoutes: archive.proofRoutes } : {}) });
const after = parseCooperationPlan(state.problem, proposal);
assert.deepEqual(after.groups, before.groups);
assert.deepEqual(after.proofRoutes, before.proofRoutes);
assert.equal(after.tasks.length, before.tasks.length);
for (let index = 0; index < before.tasks.length; ++index) {
  const oldTask = before.tasks[index]!, newTask = after.tasks[index]!;
  if (oldTask.id !== goal.task.id) assert.deepEqual(newTask, oldTask);
  else assert.deepEqual(newTask, { ...oldTask, ownerId: 'engineer', objective, revision: oldTask.revision + 1 });
}
const normalized = { id: proposal.id, baseVersion: proposal.baseVersion, ...after };
const line = JSON.stringify(normalized) + '\n';
assert(Buffer.byteLength(line) <= 64000);
const editLineFile = path.join(stage, 'proposed-edit.jsonl');
fs.writeFileSync(editLineFile, line);
const consumed = readDeliveryLines(editLineFile, 0);
assert.equal(consumed.entries!.length, 1);
assert.equal(consumed.entries![0]!.line, line.slice(0, -1));
const validation = await queueRunEdit(run, proposal, true);
assert.equal(validation.status, 'validated');

// Exercise the real frozen attribution functions using explicitly synthetic
// data only. These are control-flow fixtures, never formal verification receipts.
const commit = 'synthetic-control-flow-fixture';
const item = { proofPath: target.proofPath, theoremName: target.theoremName,
  statementHash: 'synthetic-task-digest', leanStatementHash: 'synthetic-task-digest',
  expectedSourceDeclarationHash: target.declarationHash, claim: 'statement' as const };
const cases = [
  { name: 'child killed; null exit status', error: 'Lean exited with status unknown.', output: '', expectedAttributable: false },
  { name: 'wrapper reports SIGKILL as 137', error: 'Lean exited with status 137.', output: '', expectedAttributable: false },
  { name: 'wrapper reports SIGTERM as 143', error: 'Lean exited with status 143.', output: '', expectedAttributable: false },
  { name: 'exit 1 without Lean diagnostic', error: 'Lean exited with status 1.', output: '', expectedAttributable: false },
  { name: 'genuine Lean diagnostic control', error: 'Lean exited with status 1.',
    output: 'Submission.lean:1:1: error: synthetic control diagnostic', expectedAttributable: true },
].map(test => {
  const verification: any = { status: 'failed', targetCommit: commit,
    results: [{ status: 'failed', targetCommit: commit, proofPath: item.proofPath,
      theoremName: item.theoremName, statementHash: item.statementHash, leanStatementHash: item.leanStatementHash,
      claim: 'statement', sourceDeclarationHash: item.expectedSourceDeclarationHash,
      error: test.error, stdoutPreview: test.output, stderrPreview: '' }] };
  const attribution = attributeProofEvidence(verification, commit, [item])[0]!;
  assert.equal(attribution.attributable, test.expectedAttributable);
  return { ...test, actualAttributable: attribution.attributable,
    actualDeterministicFailure: hasDeterministicLeanFailure(verification) };
});
const restoreSnapshot = {
  phase: state.phase,
  taskStatuses: archive.tasks.map((node: any) => ({ taskId: node.task.id, status: node.status,
    hasProof: Boolean(node.proof), hasIntegratedCheck: Boolean(node.integratedCheck),
    pendingValidation: Boolean(node.pendingValidation) })),
  pendingSyncEditIds: (archive.edits ?? []).filter((edit: any) => edit.pendingSync).map((edit: any) => edit.id),
  hasWholeCheck: Boolean(state.check),
};
const noExistingProofRecheck = !restoreSnapshot.hasWholeCheck && !restoreSnapshot.pendingSyncEditIds.length &&
  restoreSnapshot.taskStatuses.every((node: any) => !node.hasProof && !node.hasIntegratedCheck &&
    !node.pendingValidation && !['conditional', 'delivered', 'integrated'].includes(node.status));
assert(noExistingProofRecheck, 'Reinspect restoration before drawing a graceful-resume conclusion.');
const protocol = { schema: 'theorem-os.external-check-termination-control-flow.v1',
  observedAt: new Date().toISOString(), fixturesOnly: true, notFormalVerificationReceipts: true, cases,
  conclusion: 'External termination of the in-flight Lean does not produce attributable proof evidence. The frozen task checker throws math_verifier_unavailable before stale-assignment handling; cooperative research aborts the entire old run.',
  gracefulWholeSolverResume: {
    supportedByFrozenCode: true, executed: false, snapshot: restoreSnapshot,
    currentSnapshotHasNoMandatoryOldProofRecheck: noExistingProofRecheck,
    conclusion: 'A graceful SIGINT/SIGTERM handled by the top-level solver controller is a supported stop/resume path. It aborts the whole invocation coherently, saves limit_reached/math_run_stopped and retains the run/archive. Same-identity --resume accepts that outcome. For the current archive, restoration turns the sole running goal into pending without a saved proof to recheck; no signal-only proof is forced through the fatal attribution path before the normal edit reader resumes.',
    requiredConditions: ['Signal the top-level native solver, not its isolated Lean child, and let its normal cleanup finish.',
      'Inspect terminal math_run_stopped/limit_reached and release of the native run lease before starting the exact frozen launch with --resume.',
      'Use normal queueRunEdit with a freshly read planVersion; a saved dry-run is not permission to bypass current-version validation.',
      'Do not reuse the old resume-followup.py unchanged: its phase receipt explicitly rejects a previous solving/finished/resume_failed invocation.',
      'All source guards, native proof checks, review and the original publisher comparator still run.'],
    records: 'The normal stop updates state/result phase metadata; it does not delete the archived deliveries/history or existing logs. Preserve external snapshots first if byte-for-byte pre-stop state/result evidence is required. The in-flight old check has no completed proof receipt to preserve.',
    performance: 'Same-path resume avoids the path mismatch, but full cache hits are not guaranteed: current old researcher caches include a model-side diagnostic environment identity different from native startup.',
    scope: 'Code-path assessment only; no stop, queue, resume, model or Lean was performed.',
  },
  sourceEvidence: [
    { file: 'src/math/mathProcess.ts', line: 140, meaning: 'records child exit code and signal independently' },
    { file: 'src/math/verifier.ts', line: 2040, meaning: 'ordinary external signal exit becomes failed/unknown or wrapper exit code' },
    { file: 'src/solver/proofReuse.ts', line: 41, meaning: 'deterministic failure requires real Lean error diagnostics and status 1' },
    { file: 'src/solver/modules/evidence.ts', line: 71, meaning: 'failed signal-only result is not attributable' },
    { file: 'src/solver/cooperationTaskProofs.ts', line: 427, meaning: 'unattributed proof throws math_verifier_unavailable' },
    { file: 'src/solver/cooperationTaskProofs.ts', line: 493, meaning: 'stale-assignment handling runs only after that check returns' },
    { file: 'src/solver/research.ts', line: 765, meaning: 'math_verifier_unavailable aborts the cooperative run' },
    { file: 'src/solver/run.ts', line: 102, meaning: 'top-level SIGINT/SIGTERM triggers the coherent solver AbortController' },
    { file: 'src/solver/run.ts', line: 156, meaning: '--resume checks the same immutable identity and permits a stopped non-evaluated run' },
    { file: 'src/solver/run.ts', line: 403, meaning: 'coherent stop saves limit_reached with math_run_stopped and retains owned state' },
    { file: 'src/solver/cooperation.ts', line: 211, meaning: 'normal aborted cleanup preserves archive without promoting interrupted verification to fatal failure' },
    { file: 'src/solver/cooperation.ts', line: 280, meaning: 'restoration changes running tasks to pending; saved proofs alone require old proof rechecks' },
    { file: 'src/solver/research.ts', line: 106, meaning: 'restores cooperation and then starts its unchanged input poller' },
  ].map(item => ({ ...item, file: path.join(runtime, item.file), sha256: mathDigest(fs.readFileSync(path.join(runtime, item.file))) })),
  queueAllowedByThisPreflight: false, signalSent: false, leanInvoked: false, modelInvoked: false,
};
const protocolFile = path.join(stage, 'failure-control-flow.json');
fs.writeFileSync(protocolFile, JSON.stringify(protocol, null, 2) + '\n');
const receipt = { schema: 'theorem-os.character-verified-candidate-dry-run.v1',
  observedAt: new Date().toISOString(), run, runId: state.runId, stateFile,
  candidateFile: sourceFile, sourceSHA256, sourceBytes: source.length,
  buildEvidence: { file: buildFile, sha256: mathDigest(fs.readFileSync(buildFile)), exitCode: build.exitCode,
    durationSeconds: build.elapsedSeconds, oleanSHA256: build.oleanSHA256 },
  auditEvidence: { file: auditFile, sha256: mathDigest(fs.readFileSync(auditFile)), passed: audit.passed, axioms: audit.axioms },
  guardEvidence: { file: guardFile, sha256: mathDigest(fs.readFileSync(guardFile)), passed: true },
  transportEvidence: { file: transportEvidenceFile, sha256: mathDigest(fs.readFileSync(transportEvidenceFile)),
    exactSourceRoundtripReused: true },
  proposal, normalizedEditLineBytes: Buffer.byteLength(line), frozenReaderLimitBytes: 64000,
  changedTaskId: goal.task.id, oldRevision: goal.task.revision, proposedRevision: goal.task.revision + 1,
  otherTasksUnchanged: true, taskCount: before.tasks.length,
  groupsUnchanged: true, proofRoutesUnchanged: true, originalGoalContractUnchanged: true,
  buildDigest: state.buildDigest, environmentDigest: state.environmentDigest, evaluatorDigest: state.evaluatorDigest,
  validation, failureControlFlowFile: protocolFile,
  gracefulWholeSolverResumeSupportedByCode: true, gracefulStopOrResumeExecuted: false,
  stoppedAtDryRun: true, blockingReason: protocol.conclusion,
  candidateQueued: false, signalSent: false, leanInvoked: false, modelInvoked: false,
  stateModified: false, cacheModified: false, runtimeModified: false, activeSourceModified: false,
  nativeAcceptance: false,
};
const receiptFile = path.join(stage, 'dry-run.json');
fs.writeFileSync(receiptFile, JSON.stringify(receipt, null, 2) + '\n');
console.log(JSON.stringify({ receiptFile, protocolFile, runId: state.runId,
  sourceSHA256, normalizedEditLineBytes: Buffer.byteLength(line), validation,
  stoppedAtDryRun: true, candidateQueued: false, signalSent: false }));
