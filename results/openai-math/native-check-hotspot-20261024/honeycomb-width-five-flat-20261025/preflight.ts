import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import { assertSolverProjectSources } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/honeycomb-new-build-continuation-20261024/runtime/src/solver/problem';

const stage = import.meta.dir;
const label = process.argv[2] ?? '01';
if (!/^[0-9]+$/.test(label)) throw new Error('label');
const snapshot = JSON.parse(fs.readFileSync(path.join(stage, 'fixed-source-constraints.json'), 'utf8'));
const digest = (bytes: Buffer) => crypto.createHash('sha256').update(bytes).digest('hex');
const modulePath = '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/honeycomb-new-build-continuation-20261024/runtime/src/solver/problem.ts';
const variants = ['baseline', 'namespaced', 'flat-anonymous', 'flat-named-simp', 'project'];
const results = variants.map(name => {
  const project = path.join(stage, name);
  const source = fs.readFileSync(path.join(project, 'Submission.lean'));
  const startedAt = new Date().toISOString();
  try {
    assertSolverProjectSources(snapshot.constraints, project);
    return { name, project, sourceSHA256: digest(source), startedAt, passed: true };
  } catch (error) {
    const e = error as Error & {proofPath?: string; declarationName?: string; recovery?: string};
    return { name, project, sourceSHA256: digest(source), startedAt, passed: false,
      error: e.message, proofPath: e.proofPath, declarationName: e.declarationName, recovery: e.recovery };
  }
});
const output = { guardModule: modulePath,
  guardModuleSHA256: digest(fs.readFileSync(modulePath)),
  fixedConstraintsSnapshotSHA256: digest(fs.readFileSync(path.join(stage, 'fixed-source-constraints.json'))),
  guardImplementationChanged: false, activeSourceChanged: false,
  results,
};
fs.writeFileSync(path.join(stage, `source-preflight-${label}-result.json`), JSON.stringify(output, null, 2) + '\n', {flag: 'wx'});
console.log(JSON.stringify(output));
if (!results[0].passed || !results.at(-1)?.passed) process.exitCode = 1;
