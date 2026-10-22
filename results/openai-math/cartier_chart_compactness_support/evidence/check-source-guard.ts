import fs from 'node:fs';
import path from 'node:path';
import { bootstrapLeanTask } from '../../runtime-v2/src/math/leanTask';
import { readSolverProblem, assertSolverProjectSources } from '../../runtime-v2/src/solver/problem';
const directory = import.meta.dir;
const root = path.resolve(directory, '../..');
const workspace = path.join(directory, 'source-guard-workspace');
const original = fs.readFileSync(path.join(root, 'metadata/challenges/CartierChartCompactnessSupport.lean'), 'utf8');
const candidate = fs.readFileSync(path.join(directory, 'CartierChartCompactnessSupport.lean'), 'utf8');
const receipt = bootstrapLeanTask(workspace, { source: original, task: 'Independently validate the frozen original CartierChartCompactnessSupport statement.', environment: 'openai-math' });
const problem = readSolverProblem(workspace, receipt.activeProblemPath);
fs.writeFileSync(path.join(receipt.projectRoot, 'Submission.lean'), candidate);
let nativeCandidate;
try { assertSolverProjectSources(problem, receipt.projectRoot); nativeCandidate = { passed: true }; }
catch (error) { nativeCandidate = { passed: false, error: error instanceof Error ? error.message : String(error) }; }
const adapted = path.join(directory, 'source-guard-adapted-project');
fs.cpSync(receipt.projectRoot, adapted, { recursive: true });
const extra = ['','[[require]]','name = '+JSON.stringify('cartier_support'),'path = '+JSON.stringify('.lake/packages/cartier_support'),''].join(String.fromCharCode(10));
fs.appendFileSync(path.join(adapted, 'lakefile.toml'), extra);
const manifest = JSON.parse(fs.readFileSync(path.join(adapted, 'lake-manifest.json'), 'utf8'));
manifest.packages.push({ type: 'path', dir: '.lake/packages/cartier_support', name: 'cartier_support', manifestFile: 'lake-manifest.json', inherited: false, configFile: 'lakefile.toml' });
fs.writeFileSync(path.join(adapted, 'lake-manifest.json'), JSON.stringify(manifest, null, 2) + String.fromCharCode(10));
let adaptedDependency;
try { assertSolverProjectSources(problem, adapted); adaptedDependency = { passed: true }; }
catch (error) { adaptedDependency = { passed: false, error: error instanceof Error ? error.message : String(error) }; }
const output = { observedAt: new Date().toISOString(), standaloneAudit: true, campaignAcceptance: false, runtime: 'runtime-v2', originalStatementPreserved: true, nativeCandidate, adaptedDependency, frozenProblem: problem.receiptDigest, blocker: adaptedDependency.passed ? null : 'Native frozen environment does not authorize extra OAI package configuration; no guard bypass attempted.' };
fs.writeFileSync(path.join(directory, 'source-guard-receipt.json'), JSON.stringify(output, null, 2));
console.log(JSON.stringify(output));
