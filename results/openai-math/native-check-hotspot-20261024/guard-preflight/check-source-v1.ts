import fs from 'node:fs';
import path from 'node:path';
import assert from 'node:assert/strict';
import { bootstrapLeanTask } from '../../character-environment-adapter-20261023/unlimited-preparation-v2/runtime/src/math/leanTask';
import { inspectScopedLeanDeclarations, hashMathFormalSourceDeclaration, inspectLeanDeclarationRegions } from '../../character-environment-adapter-20261023/unlimited-preparation-v2/runtime/src/math/leanSource';
import { readSolverProblem, assertSolverSources, assertSolverProjectSources, commitSolverSources, git } from '../../character-environment-adapter-20261023/unlimited-preparation-v2/runtime/src/solver/problem';
import { taskChanges, applyTaskChanges, createTaskSourceProjector } from '../../character-environment-adapter-20261023/unlimited-preparation-v2/runtime/src/solver/cooperativeProof';
import { mathDigest } from '../../character-environment-adapter-20261023/unlimited-preparation-v2/runtime/src/math/mathRuntimeIo';

const stage = import.meta.dir;
const campaignRoot = path.resolve(stage, '../../..');
const runtime = path.join(campaignRoot, 'validation/character-environment-adapter-20261023/unlimited-preparation-v2/runtime');
const candidateFile = path.join(stage, '../character-sync-def-candidate/Submission.lean');
const baselineFile = path.join(stage, '../character-canonical-baseline.lean');
const activeStateFile = path.join(path.dirname(runtime), 'native-followup/result.json.runtime/state.json');
const candidate = fs.readFileSync(candidateFile, 'utf8');
const baseline = fs.readFileSync(baselineFile, 'utf8');
const active = JSON.parse(fs.readFileSync(activeStateFile, 'utf8'));
const started = performance.now();
const report: Record<string, unknown> = { schema: 'theorem-os.frozen-native-def-source-preflight.v1',
  observedAt: new Date().toISOString(), candidateFile, sourceSHA256: mathDigest(candidate),
  sourceBytes: Buffer.byteLength(candidate), baselineFile, baselineSHA256: mathDigest(baseline),
  activeRunId: active.runId, activeStateFile, runtime,
  frozenSources: Object.fromEntries(['src/solver/problem.ts', 'src/solver/cooperativeProof.ts',
    'src/math/leanSource.ts', 'src/math/leanTask.ts'].map(file => [file, mathDigest(fs.readFileSync(path.join(runtime, file)))])),
  passed: false, leanInvoked: false, modelInvoked: false, activeRuntimeModified: false,
  activeStateModified: false, kernelAcceptance: false, nativeAcceptance: false };
let phase = 'byte-delta';
try {
  const changedTheorems = [...baseline.matchAll(/^theorem _root_\./gm)].length;
  assert.equal(changedTheorems, 168);
  assert.equal(candidate, baseline.replace(/^theorem (?=_root_\.)/gm, 'def '),
    'Candidate must differ only in the 168 added declaration keywords.');
  const declarations = inspectScopedLeanDeclarations(candidate);
  assert.equal(declarations.length, 251);
  assert.equal(declarations.filter(d => d.kind === 'theorem').length, 1);
  assert.equal(declarations.filter(d => d.kind === 'definition').length, 250);
  const baselineRegions = inspectLeanDeclarationRegions(baseline);
  const candidateRegions = inspectLeanDeclarationRegions(candidate);
  assert.equal(baselineRegions.length, candidateRegions.length);
  for (let i = 0; i < baselineRegions.length; ++i) {
    const a = baselineRegions[i]!, b = candidateRegions[i]!;
    assert.equal(a.name, b.name); assert.equal(a.declarationType, b.declarationType);
    assert.equal(baseline.slice(a.bodyOffset, a.endOffset), candidate.slice(b.bodyOffset, b.endOffset));
  }
  Object.assign(report, { changedTheorems, declarationCount: declarations.length,
    candidateTheorems: 1, candidateDefinitions: 250, onlyAddedKeywordsChanged: true,
    allHeadersByteEquivalent: true, allBodiesByteIdentical: true });
  phase = 'bootstrap';
  const originalFile = path.join(campaignRoot, 'metadata/challenges/CharacterVarietiesAllSeamsSupport.lean');
  const original = fs.readFileSync(originalFile, 'utf8');
  const receipt = bootstrapLeanTask(path.join(stage, 'workspace'), {
    source: original, task: 'Disposable exact frozen source guard and merge preflight; no proof acceptance.',
    environment: 'openai-math-character-reviewed-v1' });
  const problem = readSolverProblem(receipt.workspaceRoot, receipt.activeProblemPath);
  assert.equal(receipt.environmentDigest, active.environmentDigest);
  assert.equal(receipt.environmentDigest, '776e5201fa24ba3dba47f84d50336a9c3426372bd58f711b923b94219c4b632d');
  assert.equal(problem.contract.formalStatement, active.problem.contract.formalStatement);
  assert.equal(problem.contract.formalStatement, original);
  assert.deepEqual(problem.targets, active.problem.targets);
  assert.deepEqual(problem.declarations, active.problem.declarations);
  assert.deepEqual(problem.sourceStructure, active.problem.sourceStructure);
  assert.deepEqual(problem.sourceImports, active.problem.sourceImports);
  assert.deepEqual(problem.trustedFiles, active.problem.trustedFiles);
  assert.equal(problem.targets.length, 1);
  const target = problem.targets[0]!;
  assert.equal(hashMathFormalSourceDeclaration(candidate, target.theoremName), target.declarationHash);
  const goal = { id: 'original_goal', kind: 'goal' as const, revision: 0,
    objective: 'Prove the unchanged original CharacterVarieties target.', dependsOn: [],
    proofPath: target.proofPath, theoremName: target.theoremName };
  const submission = path.join(receipt.projectRoot, target.proofPath);
  phase = 'candidate-source-guard';
  fs.writeFileSync(submission, candidate);
  assertSolverProjectSources(problem, receipt.projectRoot);
  assertSolverSources(problem, receipt.workspaceRoot);
  const candidateCommit = commitSolverSources(problem, receipt.workspaceRoot);
  phase = 'candidate-projection';
  const goalProjection = createTaskSourceProjector(problem, receipt.workspaceRoot, candidateCommit)(goal, []).get(goal.proofPath)!;
  assert(goalProjection);
  fs.writeFileSync(path.join(stage, 'CandidateProjected.lean'), goalProjection);
  phase = 'canonical-merge';
  const changes = taskChanges(problem, receipt.workspaceRoot, candidateCommit, goal, { seedCommit: problem.baseCommit });
  git(receipt.workspaceRoot, ['checkout', '--quiet', '--detach', problem.baseCommit]);
  applyTaskChanges(problem, receipt.workspaceRoot, changes);
  assertSolverSources(problem, receipt.workspaceRoot);
  const merged = fs.readFileSync(submission, 'utf8');
  fs.writeFileSync(path.join(stage, 'IntegrationMerged.lean'), merged);
  const mergedCommit = commitSolverSources(problem, receipt.workspaceRoot);
  const projected = createTaskSourceProjector(problem, receipt.workspaceRoot, mergedCommit)(goal, []).get(goal.proofPath)!;
  assert(projected);
  fs.writeFileSync(path.join(stage, 'IntegrationProjected.lean'), projected);
  const names = (s: string) => inspectScopedLeanDeclarations(s).map(d => d.qualifiedName);
  assert.deepEqual(names(merged), names(candidate)); assert.deepEqual(names(projected), names(candidate));
  const nonblank = (s: string) => s.split('\n').filter(line => line.trim()).join('\n');
  assert.equal(nonblank(merged), nonblank(candidate)); assert.equal(nonblank(projected), nonblank(candidate));
  phase = 'fixed-point-replay';
  fs.writeFileSync(submission, projected);
  const replayCommit = commitSolverSources(problem, receipt.workspaceRoot);
  const replayChanges = taskChanges(problem, receipt.workspaceRoot, replayCommit, goal, { seedCommit: problem.baseCommit });
  git(receipt.workspaceRoot, ['checkout', '--quiet', '--detach', problem.baseCommit]);
  applyTaskChanges(problem, receipt.workspaceRoot, replayChanges);
  assertSolverSources(problem, receipt.workspaceRoot);
  const repeated = fs.readFileSync(submission, 'utf8');
  const repeatedCommit = commitSolverSources(problem, receipt.workspaceRoot);
  const repeatedProjection = createTaskSourceProjector(problem, receipt.workspaceRoot, repeatedCommit)(goal, []).get(goal.proofPath)!;
  assert.equal(repeated, projected); assert.equal(repeatedProjection, projected);
  assert.equal(candidate, goalProjection); assert.equal(candidate, projected);
  assert.equal(fs.readFileSync(candidateFile, 'utf8'), candidate);
  Object.assign(report, { passed: true, originalTarget: target.theoremName,
    originalDeclarationHash: target.declarationHash, originalTargetUnchanged: true,
    originalContextUnchanged: true, activeProtectedFilesAndSourceConstraintsIdentical: true,
    environmentDigest: receipt.environmentDigest, workspace: receipt.workspaceRoot,
    changedDeclarations: changes.length, candidateProjectionSHA256: mathDigest(goalProjection),
    mergedSHA256: mathDigest(merged), integrationProjectionSHA256: mathDigest(projected),
    candidateEqualsGoalProjection: true, candidateEqualsIntegrationProjection: true,
    sameQualifiedDeclarations: true, sameNonblankSourceLines: true,
    canonicalMergeFixedPoint: true, sourceGuardPassedBeforeAndAfterMerge: true,
    candidateUnchanged: true,
    claim: 'Static source/contract and exact merge-fixedpoint compatibility only; no Lean, comparator, native acceptance or cache hit is claimed.' });
} catch (error) {
  Object.assign(report, { failedPhase: phase, error: error instanceof Error ?
    { name: error.name, message: error.message.slice(0, 4000) } : String(error) });
  process.exitCode = 1;
} finally {
  report.durationSeconds = (performance.now() - started) / 1000;
  fs.writeFileSync(path.join(stage, 'receipt.json'), JSON.stringify(report, null, 2) + '\n');
  console.log(JSON.stringify(report));
}
