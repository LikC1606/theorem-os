import fs from 'node:fs';
import path from 'node:path';
import { proofReuseEnvironment as fixedEnvironment } from './runtime/src/solver/proofReuse';
import { resolveMathematicsRuntimeEnvironment } from './runtime/src/math/mathRuntimeEnvironment';
import { resolveMathProofEnvironment } from './runtime/src/math/mathProofEnvironment';
import { LAKE_CONFIGURATION_FILES } from './runtime/src/math/mathConstructionSources';
import { mathDigest } from './runtime/src/math/mathRuntimeIo';
import { proofReuseEnvironment as frozenEnvironment } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/character-environment-adapter-20261023/unlimited-preparation-v2/runtime/src/solver/proofReuse';

const base = '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/native-check-hotspot-20261024/native-sync-def-attempt/native-followup';
const pid = 2305626;
const native = Object.fromEntries(fs.readFileSync(`/proc/${pid}/environ`).toString().split('\0').filter(Boolean).map(item => {
  const index = item.indexOf('='); return [item.slice(0, index), item.slice(index + 1)];
}));
const accessEnvironmentSource = path.join(base, 'result.json.runtime/environment-solver.json');
const env = resolveMathematicsRuntimeEnvironment({ ...native, DEEPSCIENTIST_MATH_ENV_FILE: accessEnvironmentSource });
const projects = [
  ['delivery-source-project', path.join(base, 'result.json.runtime/worktree-4/generated/problem')],
  ['clean-integration-projection', '/tmp/math-check-ahZooU/worktree/generated/problem'],
  ['second-clean-projection', '/tmp/math-check-wLoT3a/worktree/generated/problem'],
] as const;
const hash = (file: string) => {
  try { return mathDigest(fs.readFileSync(file)); }
  catch (error) { if ((error as NodeJS.ErrnoException).code === 'ENOENT') return null; throw error; }
};
const before = projects.map(([stage, project]) => ({ stage, project,
  submissionSha256: hash(path.join(project, 'Submission.lean')),
  configuration: LAKE_CONFIGURATION_FILES.map(file => [file, hash(path.join(project, file))]),
}));
const observations = before.map(input => {
  const sealed = resolveMathProofEnvironment(input.project, env);
  const old = frozenEnvironment(input.project, env), fixed = fixedEnvironment(input.project, env);
  return { ...input, validatedSealedIdentity: sealed?.identity ?? null,
    frozen: { reusable: old.reusable, digest: old.digest }, fixed: { reusable: fixed.reusable, digest: fixed.digest } };
});
const after = projects.map(([stage, project]) => ({ stage, project,
  submissionSha256: hash(path.join(project, 'Submission.lean')),
  configuration: LAKE_CONFIGURATION_FILES.map(file => [file, hash(path.join(project, file))]),
}));
const valid = observations.every(item => item.validatedSealedIdentity && item.fixed.reusable && item.fixed.digest) &&
  new Set(observations.map(item => item.fixed.digest)).size === 1;
const inputsUnchanged = JSON.stringify(before) === JSON.stringify(after);
process.stdout.write(JSON.stringify({ schema: 'theorem-os.sealed-reuse-fix-observation.v1',
  observedAt: new Date().toISOString(), accessEnvironmentSource, nativeParentPid: pid,
  method: 'Read-only calls to frozen and isolated fixed proofReuseEnvironment plus the actual sealed resolver on existing live project paths.',
  leanInvoked: false, modelInvoked: false, cacheLookupInvoked: false, verifierReceiptCreated: false,
  projectInputsUnchanged: inputsUnchanged, fixedSealedDigestsEqual: valid, observations,
}, null, 2) + '\n');
if (!valid || !inputsUnchanged) process.exitCode = 1;
