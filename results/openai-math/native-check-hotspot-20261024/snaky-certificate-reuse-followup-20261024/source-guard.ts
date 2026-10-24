import fs from 'node:fs';
import path from 'node:path';
import assert from 'node:assert/strict';
import { bootstrapLeanTask } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/snaky-conditional-native-followup-20261023/runtime/src/math/leanTask';
import { getLeanTaskEnvironment } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/snaky-conditional-native-followup-20261023/runtime/src/math/leanTaskEnvironment';
import { inspectScopedLeanDeclarations } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/snaky-conditional-native-followup-20261023/runtime/src/math/leanSource';
import { readSolverProblem, assertSolverProjectSources } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/snaky-conditional-native-followup-20261023/runtime/src/solver/problem';
import { mathDigest } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/snaky-conditional-native-followup-20261023/runtime/src/math/mathRuntimeIo';

const directory = import.meta.dir;
const original = fs.readFileSync('/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/metadata/challenges/SnakyConditional.lean', 'utf8');
assert.equal(mathDigest(original), '3ab27d66779b557d0efcc3cfcf8317c40511e3cc655da29e61e95ba3f34d45ea');
const workspace = path.join(directory, 'source-guard-fixture');
const receipt = bootstrapLeanTask(workspace, {
  source: original,
  task: 'Local source preflight for the single Snaky certificate-reuse candidate; no solver execution.',
  environment: 'openai-math',
});
const problem = readSolverProblem(workspace, receipt.activeProblemPath);
assert.equal(receipt.environmentDigest, getLeanTaskEnvironment('openai-math').dependencyDigest);
assert.deepEqual(receipt.publicObligations.map(t => t.name), ['OAI.SnakyConditional.snaky_winning_strategy_with_legal_states']);
const checks = [];
for (const label of ['canonical', 'merged']) {
  const source = fs.readFileSync(path.join(directory, label + '-source.lean'), 'utf8');
  const candidate = fs.readFileSync(path.join(directory, label + '-reuse-candidate.lean'), 'utf8');
  fs.writeFileSync(path.join(receipt.projectRoot, 'Submission.lean'), candidate);
  assertSolverProjectSources(problem, receipt.projectRoot);
  assert(Buffer.byteLength(candidate) < 1024 * 1024);
  assert.deepEqual(inspectScopedLeanDeclarations(candidate).map(x => x.qualifiedName),
    inspectScopedLeanDeclarations(source).map(x => x.qualifiedName));
  checks.push({label, sourceSHA256: mathDigest(source), candidateSHA256: mathDigest(candidate),
    candidateBytes: Buffer.byteLength(candidate), unchangedFrozenSourceGuardPassed: true,
    sameQualifiedDeclarations: true, belowOneMiB: true});
}
const result = {
  checkedAt: new Date().toISOString(), originalSourceSHA256: mathDigest(original),
  environmentDigest: receipt.environmentDigest, workspace,
  frozenRuntime: '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/snaky-conditional-native-followup-20261023/runtime',
  checks, guardImplementationChanged: false, leanInvoked: false,
  activeWorkspaceModified: false, nativeAcceptance: false, campaignAcceptance: false,
  fixtureSeedCommitOnly: true, candidateCommittedOrPublished: false,
};
fs.writeFileSync(path.join(directory, 'source-guard-result.json'), JSON.stringify(result, null, 2) + '\n', {flag: 'wx'});
console.log(JSON.stringify(result));
