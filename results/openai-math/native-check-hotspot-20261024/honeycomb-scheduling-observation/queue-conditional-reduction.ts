import fs from 'node:fs';
import path from 'node:path';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { queueRunEdit } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/honeycomb-new-build-continuation-20261024/runtime/src/solver/humanEdit';
import { canonicalMathJson, mathDigest } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/honeycomb-new-build-continuation-20261024/runtime/src/math/mathRuntimeIo';
import { parseCooperationPlan, taskProofContractVersion, taskVersion, invalidatedTaskIds } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/honeycomb-new-build-continuation-20261024/runtime/src/solver/tasks';
import { MAX_DELIVERY_LINE_BYTES, readDeliveryLines } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/honeycomb-new-build-continuation-20261024/runtime/src/solver/deliveries';

const stage = import.meta.dir;
const run = '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/tasks/HoneycombBridgeFiniteness/attempts/workflow-20261024/result.json';
const runtime = run + '.runtime';
const stateFile = path.join(runtime, 'state.json');
const preparationFile = path.join(stage, 'human-edit-preparation.json');
const receiptFile = path.join(stage, 'human-edit-queue-receipt.json');
const checkpoint = '0e6ec0cfff4aceb912de8009331ed5ca3ea4d794';
const sourceSHA256 = '6f81ffc481e22c8a189ced1d0de1d154c39e0edc57f17e9c1f492a271139f6e2';
const sourceBytes = 8813;
const expectedRunId = '8bd4a613-c70e-4e96-b298-c9d22cfafaf3';
const expectedBuild = '7e2c42e897361d27b0aa6bf216f74ed7ba71aa32987771ade075193bed54c19f';
const targetName = 'OAI.PolynomialVacuumBridge.Corridor.finite_bridge_sums';
const taskId = 'sums_reduction';
const sourcePath = 'generated/problem/Submission.lean';
const stateBytes = fs.readFileSync(stateFile);
const state = JSON.parse(stateBytes.toString('utf8'));
assert.equal(state.runId, expectedRunId);
assert.equal(state.buildDigest, expectedBuild);
assert.equal(state.problem.receiptDigest, '288f5d5aa511a456e7c9b4e2b2bed14521b39e76f27c1fbf51c9ac980cc0d37c');
assert.equal(state.problem.baseCommit, '72c3ac48330f6892bbb941350a9612ca15a1ac2f');
assert.equal(state.problem.targets.length, 1);
assert.equal(state.problem.targets[0].theoremName, targetName);
assert.equal(state.problem.projectRelative, 'generated/problem');
assert.deepEqual(state.problem.ownedFiles, ['Submission.lean']);
assert.notEqual(state.phase, 'finished');

if (fs.existsSync(receiptFile)) {
  const receipt = JSON.parse(fs.readFileSync(receiptFile, 'utf8'));
  assert.equal(receipt.runId, expectedRunId);
  console.log(JSON.stringify({ phase: 'already-recorded', receiptFile, result: receipt.result }));
} else {
  let preparation: any;
  if (fs.existsSync(preparationFile)) {
    preparation = JSON.parse(fs.readFileSync(preparationFile, 'utf8'));
    assert.equal(preparation.runId, expectedRunId);
    assert.equal(preparation.sourceSHA256, sourceSHA256);
    assert.equal(preparation.buildDigest, expectedBuild);
  } else {
    const nodes = state.cooperation.tasks;
    assert(nodes.every((node: any) => !node.capacityExploration), 'Reinspect host-owned capacity tasks before editing.');
    const previous = nodes.find((node: any) => node.task.id === taskId);
    assert(previous && previous.task.kind === 'lemma' && !previous.proof && !previous.integratedCheck);
    assert.equal(previous.task.theoremName, 'OAI.PolynomialVacuumBridge.Corridor.finite_bridge_sums_of_stripGrowthBelowMu');
    assert.equal(previous.task.conditional, true);
    assert.deepEqual(previous.task.dependsOn, []);
    const engineerWorktree = state.workers.find((worker: any) => worker.id === 'engineer').worktree;
    const source = execFileSync('git', ['--no-optional-locks', 'show', checkpoint + ':' + sourcePath], { cwd: engineerWorktree });
    assert.equal(source.length, sourceBytes);
    assert.equal(mathDigest(source), sourceSHA256);
    assert.deepEqual(source, fs.readFileSync(path.join(stage, 'retained-reduction.lean')));

    const loader = `/usr/bin/python3 - <<'PY'\n` +
      `import hashlib, subprocess\nfrom pathlib import Path\n` +
      `source = subprocess.check_output(['git', '--no-optional-locks', 'show', '${checkpoint}:${sourcePath}'])\n` +
      `assert len(source) == ${sourceBytes}\n` +
      `assert hashlib.sha256(source).hexdigest() == '${sourceSHA256}'\n` +
      `Path('${sourcePath}').write_bytes(source)\n` +
      `print('restored ${sourceSHA256} ${sourceBytes}')\nPY`;
    const objective = previous.task.objective + '\n\n' +
      'Execution handoff: this exact task proves the closed conditional implication H -> FiniteBridgeSums. ' +
      'The source retained at checkpoint ' + checkpoint + ' contains the named reduction with the exact requested type; ' +
      'its local-check claims are worker reports, so native typed acceptance is still required. ' +
      'Use the following loader once in your newly assigned worktree and confirm its printed source SHA and byte count. ' +
      'Then finish this assigned lemma through ordinary completed proof delivery, allowing the host to run the native typed checker and integration. ' +
      'Use the current assignment-specific ready/proof protocol if an explicit delivery event is needed. ' +
      'The quantified strip-growth assumption is the antecedent of this lemma; its separate unresolved proof does not make this implication task inconclusive. ' +
      'Keep the original finite_bridge_sums target and strip_growth_below_mu task unchanged and report their remaining mathematical gap separately. ' +
      'The restored source retains the original goal sorry, so this handoff supplies no unconditional original-goal proof. ' +
      'Avoid extra standalone Lean, Lake, check-lean, or waiting loops in the model session; native host verification remains required.\n\n' +
      '```sh\n' + loader + '\n```';
    const updated = { ...previous.task, ownerId: 'engineer', revision: previous.task.revision + 1, objective };
    assert.equal(taskProofContractVersion(updated), taskProofContractVersion(previous.task));
    const groups = state.cooperation.groups.map((record: any) => record.group);
    const proposal = {
      id: 'honeycomb-sums-typed-' + sourceSHA256.slice(0, 12) + '-r' + updated.revision + '-' + state.cooperation.planVersion.slice(0, 8),
      baseVersion: state.cooperation.planVersion,
      tasks: nodes.map((node: any) => node.task.id === taskId ? updated : node.task),
      groups,
      ...(state.cooperation.proofRoutes ? { proofRoutes: state.cooperation.proofRoutes } : {}),
    };
    const normalized = { id: proposal.id, baseVersion: proposal.baseVersion, ...parseCooperationPlan(state.problem, proposal) };
    assert.deepEqual(normalized.tasks.map(task => task.id), nodes.map((node: any) => node.task.id));
    assert.equal(canonicalMathJson(normalized.groups), canonicalMathJson(groups));
    assert.equal(canonicalMathJson(normalized.proofRoutes ?? null), canonicalMathJson(state.cooperation.proofRoutes ?? null));
    for (const task of normalized.tasks) {
      const prior = nodes.find((node: any) => node.task.id === task.id).task;
      if (task.id === taskId) {
        const omitEdit = ({ objective: _objective, ownerId: _ownerId, revision: _revision, ...other }: any) => other;
        assert.equal(canonicalMathJson(omitEdit(task)), canonicalMathJson(omitEdit(prior)));
      } else assert.equal(canonicalMathJson(task), canonicalMathJson(prior));
    }
    const dependencies = new Map(normalized.tasks.map(task => [task.id, task.dependsOn]));
    const expectedInvalidated = [...invalidatedTaskIds(nodes, normalized.tasks, new Set(), dependencies)];
    assert(!expectedInvalidated.includes('strip_growth_below_mu'));
    const line = JSON.stringify(normalized) + '\n';
    assert(Buffer.byteLength(line) <= MAX_DELIVERY_LINE_BYTES);
    const fixture = path.join(stage, 'source-loader-fixture');
    fs.mkdirSync(path.join(fixture, 'generated/problem'), { recursive: true });
    fs.writeFileSync(path.join(fixture, 'edits.jsonl'), line);
    const consumed = readDeliveryLines(path.join(fixture, 'edits.jsonl'), 0);
    assert.equal(consumed.entries!.length, 1);
    assert.equal(JSON.parse(consumed.entries![0].line!).tasks.find((task: any) => task.id === taskId).objective, objective);
    const gitDirectory = execFileSync('git', ['--no-optional-locks', 'rev-parse', '--absolute-git-dir'], { cwd: engineerWorktree, encoding: 'utf8' }).trim();
    const loaderOutput = execFileSync('/bin/bash', ['-c', loader], {
      cwd: fixture, encoding: 'utf8', timeout: 10_000,
      env: { ...process.env, GIT_DIR: gitDirectory, GIT_WORK_TREE: fixture, GIT_OPTIONAL_LOCKS: '0' },
    }).trim();
    assert.deepEqual(fs.readFileSync(path.join(fixture, sourcePath)), source);
    const validation = await queueRunEdit(run, proposal, true);
    assert.equal(validation.status, 'validated');
    preparation = {
      observedAt: new Date().toISOString(), runId: expectedRunId, run, buildDigest: expectedBuild,
      stateFileSHA256: mathDigest(stateBytes), originalTarget: targetName,
      originalProblemSHA256: mathDigest(canonicalMathJson(state.problem)),
      sourceCommit: checkpoint, sourceSHA256, sourceBytes,
      beforeTaskGraph: nodes.map((node: any) => node.task), proposal,
      changedTaskIds: [taskId], changedFields: ['ownerId', 'revision', 'objective'],
      exactMathematicalTaskContractPreserved: true, fullTaskGraphPreserved: true,
      groupAndRouteConfigurationPreserved: true,
      mergeSemantics: 'Full plan replacement, protected by edits.lock and baseVersion CAS. The full current graph is included.',
      expectedNativeInvalidatedTaskIds: expectedInvalidated,
      retainedOriginalConditionalProof: 'Existing two-input original-goal proof remains historical evidence and requires recheck for the revised input task version.',
      normalizedEditLineBytes: Buffer.byteLength(line), deliveryReaderLimitBytes: MAX_DELIVERY_LINE_BYTES,
      exactDeliveryReaderRoundtripPassed: true, exactSourceLoaderFixtureRoundtripPassed: true, loaderOutput,
      validation, directStateWrites: false, directActiveSourceWrites: false,
      modelsStartedByThisScript: false, leanStartedByThisScript: false,
      mathematicalAcceptance: false, nativeAcceptance: false,
    };
    fs.writeFileSync(path.join(stage, 'human-edit-proposal.json'), JSON.stringify(proposal, null, 2) + '\n', { flag: 'wx' });
    fs.writeFileSync(preparationFile, JSON.stringify(preparation, null, 2) + '\n', { flag: 'wx' });
  }
  if (process.argv.includes('--queue')) {
    assert.equal(mathDigest(canonicalMathJson(state.problem)), preparation.originalProblemSHA256);
    const result = await queueRunEdit(run, preparation.proposal);
    const receipt = {
      observedAt: new Date().toISOString(), runId: expectedRunId, run, editId: preparation.proposal.id,
      result, preparationFile, preparationSHA256: mathDigest(fs.readFileSync(preparationFile)),
      fullTaskGraphPreservedInProposal: true, exactMathematicalTaskContractPreserved: true,
      sourceCommit: checkpoint, sourceSHA256, sourceBytes,
      attribution: 'Instruction and ownership edit appended through the frozen queueRunEdit host protocol. No mathematical verdict supplied.',
      directStateWrites: false, directActiveSourceWrites: false,
      modelsStartedByThisScript: false, leanStartedByThisScript: false,
      mathematicalAcceptance: false, nativeAcceptance: false,
    };
    fs.writeFileSync(receiptFile, JSON.stringify(receipt, null, 2) + '\n', { flag: 'wx' });
    console.log(JSON.stringify({ phase: 'queued', receiptFile, result, expectedNativeInvalidatedTaskIds: preparation.expectedNativeInvalidatedTaskIds }));
  } else {
    console.log(JSON.stringify({ phase: 'prepared', preparationFile, validation: preparation.validation,
      normalizedEditLineBytes: preparation.normalizedEditLineBytes,
      fullTaskGraphPreserved: true, mathematicalContractPreserved: true,
      expectedNativeInvalidatedTaskIds: preparation.expectedNativeInvalidatedTaskIds, nativeAcceptance: false }));
  }
}
