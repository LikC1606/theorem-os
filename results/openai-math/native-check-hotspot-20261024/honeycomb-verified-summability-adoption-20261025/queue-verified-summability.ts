import fs from 'node:fs';
import path from 'node:path';
import assert from 'node:assert/strict';
import { queueRunEdit } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/honeycomb-new-build-continuation-20261024/runtime/src/solver/humanEdit';
import { canonicalMathJson, mathDigest } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/honeycomb-new-build-continuation-20261024/runtime/src/math/mathRuntimeIo';
import { invalidatedTaskIds, parseCooperationPlan } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/honeycomb-new-build-continuation-20261024/runtime/src/solver/tasks';

const stage = import.meta.dir;
const run = '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/tasks/HoneycombBridgeFiniteness/attempts/workflow-20261024/result.json';
const editId = 'honeycomb-verified-summability-subtasks-20261025';
const receiptFile = path.join(stage, 'queue-receipt.json');
const evidence = [
  { directory: 'honeycomb-confined-finiteness-20261024', source: 'ConfinedFiniteness.lean',
    result: 'validation-01-result.json', output: 'validation-01.stdout.log',
    sourceSHA256: '9dd59d27aa8ab3bec43bd0bd475153e2b52efa2f83a9b391f082a3c7f426d694',
    axiomsCount: 11, taskId: 'confined_bridge_sums_all_heights_9dd59d27',
    theoremName: 'OAI.PolynomialVacuumBridge.Corridor.bridgeConfined_sums',
    type: '∀ h : ℕ, Summable (fun p : ConfinedBridgePath h => weight p.val) ∧ Summable (fun p : ConfinedBridgePath h => firstLengthWeight p.val) ∧ Summable (fun p : ConfinedBridgePath h => firstLengthWeight p.val / confinedMass h)',
    dependsOn: [] as string[],
    meaning: 'Unconditionally prove the three confined summability clauses for every height using the finite confined path type. This does not prove the full-strip clauses or the complete original goal.' },
  { directory: 'honeycomb-width-one-20261024', source: 'WidthOne.lean',
    result: 'validation-02-final-result.json', output: 'validation-02-final.stdout.log',
    sourceSHA256: 'b433299aec2620b7b6dcad1e029f54133a41f255d831e9e73af699f754047aac',
    axiomsCount: 6, taskId: 'width_one_bridge_sums_b433299a',
    theoremName: 'OAI.PolynomialVacuumBridge.Corridor.finite_bridge_sums_at_one',
    type: 'Summable (weight (h := 1)) ∧ Summable (firstLengthWeight (h := 1)) ∧ Summable (fun p : BridgePath 1 => firstLengthWeight p / bridgeMass 1) ∧ Summable (fun p : ConfinedBridgePath 1 => weight p.val) ∧ Summable (fun p : ConfinedBridgePath 1 => firstLengthWeight p.val) ∧ Summable (fun p : ConfinedBridgePath 1 => firstLengthWeight p.val / confinedMass 1)',
    dependsOn: ['sums_reduction'],
    meaning: 'Integrate the existing unconditional width-one classification and its checked counting-to-summability adapter. This proves the six clauses only at height one; the all-height growth frontier remains unresolved.' }
];

if (fs.existsSync(receiptFile)) {
  console.log(JSON.stringify({ status: 'already-recorded', receiptFile }));
} else {
  const bytes = fs.readFileSync(run + '.runtime/state.json');
  const state = JSON.parse(bytes.toString('utf8'));
  assert.equal(state.runId, '8bd4a613-c70e-4e96-b298-c9d22cfafaf3');
  assert.equal(state.buildDigest, '7e2c42e897361d27b0aa6bf216f74ed7ba71aa32987771ade075193bed54c19f');
  assert.equal(state.phase, 'running');
  const co = state.cooperation;
  assert(!co.edits?.some((edit: any) => edit.id === editId));
  const original = co.tasks.map((node: any) => node.task);
  const checks = evidence.map(item => {
    assert(!co.tasks.some((node: any) => node.task.id === item.taskId || node.task.theoremName === item.theoremName));
    const helper = path.join(stage, '..', item.directory);
    const source = fs.readFileSync(path.join(helper, item.source));
    const result = JSON.parse(fs.readFileSync(path.join(helper, item.result), 'utf8'));
    assert.equal(mathDigest(source), item.sourceSHA256);
    assert.equal(result.sourceSHA256, item.sourceSHA256);
    assert.equal(result.actualExitCode, 0);
    const snapshot = item.result.replace('-result.json', '-source.lean');
    assert.equal(mathDigest(fs.readFileSync(path.join(helper, snapshot))), item.sourceSHA256);
    assert.equal(result.resourceLimits.maxHeartbeats, 0);
    assert.equal(result.resourceLimits.threads, 1);
    assert.equal(result.resourceLimits.addressSpaceGiB, 32);
    for (const key of ['wallSeconds', 'cpuSoftSeconds', 'cpuHardSeconds']) assert.equal(result.resourceLimits[key], null);
    const output = fs.readFileSync(path.join(helper, item.output), 'utf8');
    assert(!output.includes('sorryAx') && !/\berror:/u.test(output));
    const matches = [...output.matchAll(/'([^']+)' depends on axioms:\s*\[([^\]]*)\]/gu)];
    assert.equal(matches.length, item.axiomsCount);
    assert(matches.some(match => match[1] === item.theoremName));
    for (const match of matches) for (const axiom of match[2]!.split(',').map(x => x.trim()).filter(Boolean))
      assert(['propext', 'Classical.choice', 'Quot.sound'].includes(axiom));
    const handoff = fs.readFileSync(path.join(helper, 'HANDOFF.txt'), 'utf8');
    assert(handoff.includes(item.theoremName));
    return { ...item, resultSHA256: mathDigest(fs.readFileSync(path.join(helper, item.result))),
      handoffSHA256: mathDigest(handoff), handoff, sourceBytes: source.length };
  });
  const additions = checks.map(item => ({ id: item.taskId, kind: 'lemma', revision: 0,
    proofPath: 'Submission.lean', theoremName: item.theoremName, type: item.type,
    dependsOn: item.dependsOn, groupId: 'main', sharing: 'problem',
    objective: item.meaning + '\n\nExternal auxiliary input, not a publisher solution. ' +
      'The complete independently checked increment follows. Integrate it into the current namespace before the original target, retaining all canonical definitions and existing work. ' +
      'Reuse identical declarations that are already present. Save the exact assigned theorem and deliver it through the normal typed proof protocol; an advisory report alone is not a proof delivery. ' +
      'Host verification and canonical integration are still required. Do not assume or claim the unresolved original theorem.\n\n' + item.handoff }));
  const firstAdvisory = original.findIndex((task: any) => task.id === 'initial_research_1');
  assert(firstAdvisory >= 0);
  const tasks = [...original.slice(0, firstAdvisory), ...additions, ...original.slice(firstAdvisory)];
  const groups = co.groups.map((record: any) => record.group);
  const proposal = { id: editId, baseVersion: co.planVersion, tasks, groups,
    ...(co.proofRoutes ? { proofRoutes: co.proofRoutes } : {}) };
  const plan = parseCooperationPlan(state.problem, proposal);
  for (const node of co.tasks) assert.equal(
    canonicalMathJson(plan.tasks.find(task => task.id === node.task.id)), canonicalMathJson(node.task));
  assert.equal(canonicalMathJson(plan.groups), canonicalMathJson(groups));
  assert.equal(canonicalMathJson(plan.proofRoutes ?? null), canonicalMathJson(co.proofRoutes ?? null));
  const dependencies = new Map(co.tasks.map((node: any) => [node.task.id,
    [...node.task.dependsOn, ...(node.alternativeRoutes?.flatMap((route: any) =>
      [...route.prerequisiteTaskIds, route.closingTaskId]) ?? []),
      ...(node.assignment?.dependencies?.map((item: any) => item.taskId) ?? [])]]));
  assert.deepEqual([...invalidatedTaskIds(co.tasks, plan.tasks, new Set(), dependencies)], []);
  const wireBytes = Buffer.byteLength(JSON.stringify(proposal) + '\n');
  assert(wireBytes <= 1024 * 1024);
  const validation = await queueRunEdit(run, proposal, true);
  assert.equal(validation.status, 'validated');
  fs.writeFileSync(path.join(stage, 'state-before.json'), bytes, { flag: 'wx' });
  fs.writeFileSync(path.join(stage, 'preparation.json'), JSON.stringify({ capturedAt: new Date().toISOString(),
    run, runId: state.runId, stateSHA256: mathDigest(bytes), proposal, validation, wireBytes,
    sourceEvidence: checks.map(({ handoff: _handoff, ...item }) => item),
    originalTaskObjectsPreserved: true, expectedInvalidatedExistingTasks: [],
    expectedAffectedTasks: additions.map(task => task.id) }, null, 2) + '\n', { flag: 'wx' });
  const queued = await queueRunEdit(run, proposal);
  fs.writeFileSync(receiptFile, JSON.stringify({ capturedAt: new Date().toISOString(), runId: state.runId,
    editId, result: queued, addedTaskIds: additions.map(task => task.id),
    localKernelVerified: true, newLeanInvocations: 0, nativeTaskProofAccepted: false }, null, 2) + '\n', { flag: 'wx' });
  console.log(JSON.stringify(queued));
}
