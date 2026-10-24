import fs from 'node:fs';
import path from 'node:path';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { queueRunEdit } from '../../character-environment-adapter-20261023/unlimited-preparation-v2/runtime/src/solver/humanEdit';
import { mathDigest } from '../../character-environment-adapter-20261023/unlimited-preparation-v2/runtime/src/math/mathRuntimeIo';
import { readSolverProblem } from '../../character-environment-adapter-20261023/unlimited-preparation-v2/runtime/src/solver/problem';
import { parseCooperationPlan } from '../../character-environment-adapter-20261023/unlimited-preparation-v2/runtime/src/solver/tasks';
import { readDeliveryLines } from '../../character-environment-adapter-20261023/unlimited-preparation-v2/runtime/src/solver/deliveries';
import { createCharacterSourceTransport } from '../../character-environment-adapter-20261023/character-source-transport';

// Default: validate only. --offline tests transport without any native state;
// --queue is the sole path that appends a supported native edit.
const stage = import.meta.dir;
const flags = process.argv.slice(2);
assert(flags.every(flag => ['--offline', '--queue'].includes(flag)));
const offline = flags.includes('--offline');
const enqueue = flags.includes('--queue');
assert(!(offline && enqueue));
const info = JSON.parse(fs.readFileSync(path.join(stage, 'preparation.json'), 'utf8'));
const run = info.output as string;
assert.equal(run, path.join(stage, 'native-followup/result.json'));
const sourceFile = info.candidateFile;
const source = fs.readFileSync(sourceFile);
const sourceSHA256 = mathDigest(source);
assert.equal(sourceSHA256, '5c0cbc35bd6335ab7c6d8d57bdece22a3065c6fdc7dee871d2577826b50396d3');
assert.equal(sourceSHA256, info.candidateSHA256);
assert.equal(source.length, 795645);
const guardFile = info.guardFile;
assert.equal(mathDigest(fs.readFileSync(guardFile)), info.guardSHA256);
const guard = JSON.parse(fs.readFileSync(guardFile, 'utf8'));
assert(guard.passed && guard.canonicalMergeFixedPoint && guard.sourceGuardPassedBeforeAndAfterMerge);
assert.equal(sourceSHA256, guard.sourceSHA256);
assert.equal(sourceSHA256, guard.integrationProjectionSHA256);
const initial = readSolverProblem(info.workspace, info.activeProblemPath);
const stateFile = run + '.runtime/state.json';
const state = offline ? undefined : JSON.parse(fs.readFileSync(stateFile, 'utf8'));
const problem = state?.problem ?? initial;
assert.equal(problem.contract.formalStatement, fs.readFileSync(info.sourceFile, 'utf8'));
assert.equal(problem.contract.formalStatement, initial.contract.formalStatement);
for (const field of ['targets', 'declarations', 'sourceStructure', 'sourceImports', 'trustedFiles'])
  assert.deepEqual(problem[field], (initial as any)[field]);
assert.equal(problem.targets.length, 1);
const target = problem.targets[0];
assert.equal(target.theoremName, guard.originalTarget);
assert.equal(target.declarationHash, guard.originalDeclarationHash);
if (state) {
  assert.notEqual(state.runId, info.activeRunId, 'Only this fresh attempt may receive the edit.');
  assert.notEqual(state.phase, 'finished');
  assert(state.cooperation?.planVersion, 'Run native startup/resume until the fresh cooperation plan exists.');
}
const queueFile = path.join(stage, 'queue-receipt.json');
if (!offline && fs.existsSync(queueFile)) {
  const prior = JSON.parse(fs.readFileSync(queueFile, 'utf8'));
  assert.equal(prior.runId, state.runId);
  assert.equal(prior.sourceSHA256, sourceSHA256);
  console.log(JSON.stringify({ phase: 'already-recorded', queueFile, result: prior.result }));
  process.exit(0);
}
const original = state?.cooperation.tasks.find((node: any) => node.task.kind === 'goal' &&
  node.task.theoremName === target.theoremName);
const taskId = original?.task.id ?? 'character_original_goal';
const ownedPath = path.posix.join(problem.projectRelative, target.proofPath);
const transport = createCharacterSourceTransport(source, taskId, ownedPath);
const serialInstruction = 'Run check-lean and submit through ordinary native delivery. Fixed review, host all-target kernel verification and the unchanged publisher comparator remain required. Reference receipts do not grant native acceptance.';
assert(transport.objective.includes(serialInstruction));
const objective = transport.objective.replace(serialInstruction,
  'Execute the exact loader once, confirm the printed source SHA and length, then immediately submit an ordinary completed native delivery for this assigned task. The host will perform all mathematical verification. Do not run check-lean, Lean, Lake, a local checker, or a waiting loop in the model session. Fixed review, independent host kernel verification, permitted-axiom audit, original-source guards and the unchanged publisher comparator remain required. Static source/merge guards are preparation evidence; only genuine host verification and publisher acceptance establish native success.');
const proposal = { id: 'character-sync-def-' + sourceSHA256.slice(0, 12),
  baseVersion: state?.cooperation.planVersion ?? 'offline-preparation',
  tasks: [{ id: taskId, kind: 'goal', ownerId: 'engineer', dependsOn: [],
    revision: (original?.task.revision ?? 0) + 1, objective,
    theoremName: target.theoremName, proofPath: target.proofPath }] };
const normalized = { id: proposal.id, baseVersion: proposal.baseVersion,
  ...parseCooperationPlan(problem, proposal) };
const line = JSON.stringify(normalized) + '\n';
assert(Buffer.byteLength(line) <= 64000, 'Unchanged frozen edit reader limit.');
const fixture = path.join(stage, 'transport-fixture');
const destination = path.join(fixture, ownedPath);
fs.mkdirSync(path.dirname(destination), { recursive: true });
fs.writeFileSync(destination, '-- disposable owned source\n');
fs.writeFileSync(path.join(fixture, 'COOPERATION.json'), JSON.stringify({ peers: [{ id: taskId,
  objective, objectiveDigest: mathDigest(objective) }] }));
fs.writeFileSync(path.join(fixture, 'edits.jsonl'), line);
const consumed = readDeliveryLines(path.join(fixture, 'edits.jsonl'), 0);
assert.equal(consumed.entries!.length, 1);
assert.equal(JSON.parse(consumed.entries![0].line!).tasks[0].objective, objective);
const loaderOutput = execFileSync('/usr/bin/bwrap', [
  '--die-with-parent', '--unshare-user', '--unshare-pid', '--unshare-net',
  '--ro-bind', '/', '/', '--bind', fixture, fixture, '--proc', '/proc', '--chdir', fixture,
  '/bin/sh', '-c', transport.command,
], { cwd: fixture, encoding: 'utf8' }).trim();
assert.deepEqual(fs.readFileSync(destination), source);
const validation = offline ? { status: 'offline-only; native queue validation pending' }
  : await queueRunEdit(run, proposal, true);
const preparation = { observedAt: new Date().toISOString(), phase: offline ? 'offline-transport-verified' : 'dry-run',
  run, stateFile: offline ? null : stateFile, runId: state?.runId ?? null,
  sourceFile, sourceSHA256, sourceBytes: source.length, guardFile,
  guardSHA256: mathDigest(fs.readFileSync(guardFile)),
  taskId, ownedPath, proposal, normalizedEditLineBytes: Buffer.byteLength(line),
  frozenReaderLimitBytes: 64000, encoding: transport.encoding, compressedBytes: transport.compressedBytes,
  exactSourceSandboxRoundtripPassed: true, frozenDeliveryReaderConsumedLine: true, loaderOutput,
  validation, leanInvoked: false, modelInvoked: false, kernelAcceptance: false,
  nativeAcceptance: false, candidateQueued: false, frozenRuntimeModified: false };
const preparationFile = path.join(stage, offline ? 'transport-preparation.json' : 'queue-dry-run.json');
fs.writeFileSync(preparationFile, JSON.stringify(preparation, null, 2) + '\n');
if (enqueue) {
  const result = await queueRunEdit(run, proposal);
  const receipt = { observedAt: new Date().toISOString(), runId: state.runId, run,
    sourceSHA256, sourceBytes: source.length, result, preparationFile,
    preparationSHA256: mathDigest(fs.readFileSync(preparationFile)),
    attribution: 'External candidate delivered through supported queueRunEdit; host acceptance remains required.',
    candidateQueued: true, nativeAcceptance: false, mathematicalAcceptance: false,
    frozenRuntimeModified: false, nativeCheckpointModified: false };
  fs.writeFileSync(queueFile, JSON.stringify(receipt, null, 2) + '\n', { flag: 'wx' });
  console.log(JSON.stringify(receipt));
} else {
  console.log(JSON.stringify({ phase: preparation.phase, preparationFile, sourceSHA256,
    sourceBytes: source.length, normalizedEditLineBytes: preparation.normalizedEditLineBytes,
    compressedBytes: transport.compressedBytes, validation,
    exactSourceSandboxRoundtripPassed: true, candidateQueued: false, nativeAcceptance: false }));
}
