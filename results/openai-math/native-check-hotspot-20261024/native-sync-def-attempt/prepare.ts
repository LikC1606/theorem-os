import fs from 'node:fs';
import path from 'node:path';
import assert from 'node:assert/strict';
import { bootstrapLeanTask } from '../../character-environment-adapter-20261023/unlimited-preparation-v2/runtime/src/math/leanTask';
import { bindLeanPackages } from '../../character-environment-adapter-20261023/unlimited-preparation-v2/runtime/src/math/leanDiagnostics';
import { readMathBuildManifest } from '../../character-environment-adapter-20261023/unlimited-preparation-v2/runtime/src/math/mathBuildManifest';
import { mathDigest } from '../../character-environment-adapter-20261023/unlimited-preparation-v2/runtime/src/math/mathRuntimeIo';
import { readSolverProblem, assertSolverSources } from '../../character-environment-adapter-20261023/unlimited-preparation-v2/runtime/src/solver/problem';

// Source-only preparation: this script never starts the native runtime or Lean.
const stage = import.meta.dir;
const campaign = path.resolve(stage, '../../..');
const frozen = path.join(campaign, 'validation/character-environment-adapter-20261023/unlimited-preparation-v2');
const run = path.join(stage, 'native-followup');
const candidateFile = path.join(stage, '../character-sync-def-v2-candidate/Submission.lean');
const candidateSHA256 = mathDigest(fs.readFileSync(candidateFile));
assert.equal(candidateSHA256, '5c0cbc35bd6335ab7c6d8d57bdece22a3065c6fdc7dee871d2577826b50396d3');
const guardFile = path.join(stage, '../guard-preflight-v2/receipt.json');
const guard = JSON.parse(fs.readFileSync(guardFile, 'utf8'));
assert(guard.passed && guard.canonicalMergeFixedPoint && guard.sourceGuardPassedBeforeAndAfterMerge);
assert.equal(guard.sourceSHA256, candidateSHA256);
const id = 'CharacterVarietiesAllSeamsSupport';
const sourceFile = path.join(campaign, 'metadata/challenges/' + id + '.lean');
const source = fs.readFileSync(sourceFile, 'utf8');
const target = JSON.parse(fs.readFileSync(path.join(campaign, 'metadata/target-map.json'), 'utf8'))
  .targets.find((item: any) => item.id === id);
assert(target);
assert.equal(mathDigest(source), target.source.lean.sha256);
assert.equal(mathDigest(fs.readFileSync(target.source.config.path)), target.source.config.sha256);
assert.equal(target.explicit_axiom_declarations.length, 0);
const buildFile = path.join(frozen, 'build.json');
const build = JSON.parse(fs.readFileSync(buildFile, 'utf8'));
assert.equal(build.buildId, 'd3369e50-0985-4155-804e-baba6801c575');
readMathBuildManifest(build.buildManifestRef, path.join(frozen, 'runtime'), build.bundleRoot);
const activeStateFile = path.join(frozen, 'native-followup/result.json.runtime/state.json');
const active = JSON.parse(fs.readFileSync(activeStateFile, 'utf8'));
const activeSource = JSON.parse(fs.readFileSync(active.problem.activeProblemPath, 'utf8'));
const templateFile = path.join(frozen, 'native-followup/launch.json');
const template = JSON.parse(fs.readFileSync(templateFile, 'utf8'));
const task = fs.readFileSync(path.join(frozen, 'native-followup/task.md'), 'utf8');
assert(!fs.existsSync(run), 'Preparation is one-shot; inspect an existing attempt instead of overwriting it.');
fs.mkdirSync(run, { mode: 0o700 });
const receipt = bootstrapLeanTask(path.join(run, 'workspace'), {
  source, task, environment: 'openai-math-character-reviewed-v1',
});
bindLeanPackages(receipt.projectRoot, path.join(campaign, 'environment/project/.lake/packages'));
const problem = readSolverProblem(receipt.workspaceRoot, receipt.activeProblemPath);
assertSolverSources(problem, receipt.workspaceRoot);
assert.equal(receipt.environmentDigest, activeSource.environmentDigest);
assert.equal(problem.contract.formalStatement, source);
assert.equal(problem.contract.formalStatement, active.problem.contract.formalStatement);
const sourceFields = ['targets', 'declarations', 'sourceStructure', 'sourceImports', 'trustedFiles'];
for (const field of sourceFields) assert.deepEqual((problem as any)[field], active.problem[field]);
assert.equal(problem.targets.length, 1);
assert.equal(problem.targets[0]!.declarationHash,
  'fb95bc071af2179a40770979bb7e3eb978b53a19ec0691d8eaf4e38a4e3d50d8');
const taskFile = path.join(run, 'task.md');
const output = path.join(run, 'result.json');
fs.writeFileSync(taskFile, task, { flag: 'wx', mode: 0o600 });
const args = [...template.args];
for (const [flag, value] of [['--workspace', receipt.workspaceRoot], ['--task-file', taskFile], ['--output', output]]) {
  assert.equal(args.filter((arg: string) => arg === flag).length, 1);
  args[args.indexOf(flag) + 1] = value;
}
assert.equal(args[1], path.join(frozen, 'runtime/out/main/math-solver.js'));
assert.equal(args[args.indexOf('--build-manifest') + 1], build.buildManifestRef);
const budgetFlags = ['--max-run-seconds', '--max-turns', '--max-turn-seconds',
  '--max-total-tokens', '--evaluator-timeout-seconds'];
for (const flag of [...budgetFlags, '--prepare-timeout-seconds']) assert.equal(args[args.indexOf(flag) + 1], '0');
const publisherCommand = args[args.indexOf('--evaluator-command') + 1];
assert.equal(mathDigest(publisherCommand), '8fc5775ca184697301d273e82692d3df19afb9f4442b431c894fe5b0458c0b0f');
assert.equal(Buffer.byteLength(publisherCommand), 2434);
const launch = { ...template, args };
assert.equal(launch.cwd, campaign);
assert.equal(launch.environmentDigest, receipt.environmentDigest);
fs.writeFileSync(path.join(run, 'launch.json'), JSON.stringify(launch, null, 2) + '\n', { flag: 'wx', mode: 0o600 });
fs.writeFileSync(path.join(stage, 'build.json'), JSON.stringify(build, null, 2) + '\n', { flag: 'wx' });
const info = {
  schema: 'theorem-os.native-sync-def-preparation.v1', observedAt: new Date().toISOString(),
  candidateFile, candidateSHA256, candidateBytes: fs.statSync(candidateFile).size,
  guardFile, guardSHA256: mathDigest(fs.readFileSync(guardFile)),
  id, campaign, frozenStage: frozen, runtime: path.join(frozen, 'runtime'), build,
  buildRecordSHA256: mathDigest(fs.readFileSync(buildFile)),
  buildManifestSHA256: mathDigest(fs.readFileSync(build.buildManifestRef)),
  workspace: receipt.workspaceRoot, taskFile, output, project: receipt.projectRoot,
  activeProblemPath: receipt.activeProblemPath,
  environment: receipt.environment, environmentDigest: receipt.environmentDigest,
  activeRunEnvironmentDigest: active.environmentDigest, activeRunId: active.runId,
  targets: problem.targets, sourceFile, originalChallengeSHA256: mathDigest(source),
  originalComparatorSHA256: target.source.config.sha256,
  taskSHA256: mathDigest(task), frozenLaunchFile: templateFile,
  frozenLaunchSHA256: mathDigest(fs.readFileSync(templateFile)),
  launchFile: path.join(run, 'launch.json'),
  launchSHA256: mathDigest(fs.readFileSync(path.join(run, 'launch.json'))),
  publisherCommandSHA256: mathDigest(publisherCommand), publisherCommandBytes: Buffer.byteLength(publisherCommand),
  sourceConstraintsIdenticalToActive: true, originalSourceGuardPassed: true,
  originalSubmissionRetained: fs.readFileSync(path.join(receipt.projectRoot, 'Submission.lean'), 'utf8') === source,
  taskIdenticalToActive: true, onlyLaunchPathValuesChanged: true, frozenBuildValidated: true,
  budgetCaps: template.budgetCaps, prepareTimeoutSeconds: 0,
  sourceAttribution: 'Original frozen challenge; external assistance must use supported native queueRunEdit.',
  leanInvoked: false, modelInvoked: false, nativeRuntimeStarted: false, candidateQueued: false,
  kernelAcceptance: false, nativeAcceptance: false, originalCampaignChanged: false,
};
fs.writeFileSync(path.join(stage, 'preparation.json'), JSON.stringify(info, null, 2) + '\n', { flag: 'wx' });
console.log(JSON.stringify(info));
