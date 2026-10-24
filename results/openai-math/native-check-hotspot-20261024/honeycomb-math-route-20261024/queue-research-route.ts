import fs from 'node:fs';
import path from 'node:path';
import assert from 'node:assert/strict';
import { queueRunEdit } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/honeycomb-new-build-continuation-20261024/runtime/src/solver/humanEdit';
import { canonicalMathJson, mathDigest } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/honeycomb-new-build-continuation-20261024/runtime/src/math/mathRuntimeIo';
import { parseCooperationPlan, invalidatedTaskIds } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/honeycomb-new-build-continuation-20261024/runtime/src/solver/tasks';
import { MAX_DELIVERY_LINE_BYTES } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/honeycomb-new-build-continuation-20261024/runtime/src/solver/deliveries';

const stage = import.meta.dir;
const run = '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/tasks/HoneycombBridgeFiniteness/attempts/workflow-20261024/result.json';
const stateBytes = fs.readFileSync(run + '.runtime/state.json');
const state = JSON.parse(stateBytes.toString('utf8'));
assert.equal(state.runId, '8bd4a613-c70e-4e96-b298-c9d22cfafaf3');
assert.equal(state.buildDigest, '7e2c42e897361d27b0aa6bf216f74ed7ba71aa32987771ade075193bed54c19f');
assert.equal(state.problem.receiptDigest, '288f5d5aa511a456e7c9b4e2b2bed14521b39e76f27c1fbf51c9ac980cc0d37c');
assert.notEqual(state.phase, 'finished');
const taskId = 'initial_research_2';
const preparationFile = path.join(stage, 'native-advisory-preparation.json');
const receiptFile = path.join(stage, 'native-advisory-queue-receipt.json');
const handoff = fs.readFileSync(path.join(stage, 'native-advisory-handoff.md'), 'utf8');
assert(handoff.trim().length > 0);

if (fs.existsSync(receiptFile)) {
  const prior = JSON.parse(fs.readFileSync(receiptFile, 'utf8'));
  console.log(JSON.stringify({ phase: 'already-recorded', receiptFile, result: prior.result }));
} else {
  let preparation: any;
  if (fs.existsSync(preparationFile)) {
    preparation = JSON.parse(fs.readFileSync(preparationFile, 'utf8'));
    assert.equal(preparation.runId, state.runId);
    assert.equal(preparation.handoffSHA256, mathDigest(handoff));
  } else {
    const cooperation = state.cooperation;
    const nodes = cooperation.tasks;
    assert(nodes.every((node: any) => !node.capacityExploration));
    const previous = nodes.find((node: any) => node.task.id === taskId);
    assert.equal(previous.task.kind, 'research');
    assert.equal(previous.task.ownerId, 'researcher-2');
    const updated = { ...previous.task, revision: previous.task.revision + 1,
      objective: previous.task.objective + '\n\nExternal advisory input; attribution: Codex mathematical route analysis, not a publisher solution.\n\n' + handoff };
    const groups = cooperation.groups.map((record: any) => record.group);
    const proposal = {
      id: 'honeycomb-direct-summability-' + mathDigest(handoff).slice(0, 12),
      baseVersion: cooperation.planVersion,
      tasks: nodes.map((node: any) => node.task.id === taskId ? updated : node.task),
      groups,
      ...(cooperation.proofRoutes ? { proofRoutes: cooperation.proofRoutes } : {}),
    };
    const normalized = parseCooperationPlan(state.problem, proposal);
    assert.deepEqual(normalized.tasks.map(task => task.id), nodes.map((node: any) => node.task.id));
    assert.equal(canonicalMathJson(normalized.groups), canonicalMathJson(groups));
    assert.equal(canonicalMathJson(normalized.proofRoutes ?? null), canonicalMathJson(cooperation.proofRoutes ?? null));
    for (const task of normalized.tasks) {
      const old = nodes.find((node: any) => node.task.id === task.id).task;
      const omitAdvisory = ({ objective: _objective, revision: _revision, ...other }: any) => other;
      assert.equal(canonicalMathJson(task.id === taskId ? omitAdvisory(task) : task),
        canonicalMathJson(task.id === taskId ? omitAdvisory(old) : old));
    }
    const dependencies = new Map(normalized.tasks.map(task => [task.id, task.dependsOn]));
    const invalidated = [...invalidatedTaskIds(nodes, normalized.tasks, new Set(), dependencies)];
    assert(invalidated.every(id => id === taskId), 'Do not invalidate mathematical proof tasks for an advisory input.');
    const lineBytes = Buffer.byteLength(JSON.stringify(proposal) + '\n');
    assert(lineBytes <= MAX_DELIVERY_LINE_BYTES);
    const validation = await queueRunEdit(run, proposal, true);
    assert.equal(validation.status, 'validated');
    preparation = {
      observedAt: new Date().toISOString(), runId: state.runId, run,
      stateSHA256AtPreparation: mathDigest(stateBytes), problemSHA256: mathDigest(canonicalMathJson(state.problem)),
      handoffSHA256: mathDigest(handoff), originalResearchTask: previous.task,
      proposal, validation, expectedInvalidatedTaskIds: invalidated, lineBytes,
      changedTaskIds: [taskId], changedFields: ['objective', 'revision'],
      mathematicalContractsPreserved: true, directCheckpointWrites: false, directActiveSourceWrites: false,
      mathematicalAcceptance: false,
    };
    fs.writeFileSync(preparationFile, JSON.stringify(preparation, null, 2) + '\n', { flag: 'wx' });
  }
  if (process.argv.includes('--queue')) {
    assert.equal(mathDigest(canonicalMathJson(state.problem)), preparation.problemSHA256);
    const result = await queueRunEdit(run, preparation.proposal);
    const receipt = { observedAt: new Date().toISOString(), runId: state.runId,
      editId: preparation.proposal.id, result, preparationFile,
      preparationSHA256: mathDigest(fs.readFileSync(preparationFile)),
      attribution: 'Unproved mathematical route supplied through ordinary advisory objective edit.',
      mathematicalAcceptance: false, directCheckpointWrites: false, directActiveSourceWrites: false };
    fs.writeFileSync(receiptFile, JSON.stringify(receipt, null, 2) + '\n', { flag: 'wx' });
    console.log(JSON.stringify({ phase: 'queued', result, receiptFile }));
  } else console.log(JSON.stringify({ phase: 'prepared', preparationFile, validation: preparation.validation,
    expectedInvalidatedTaskIds: preparation.expectedInvalidatedTaskIds, lineBytes: preparation.lineBytes }));
}
