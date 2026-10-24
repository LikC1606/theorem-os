import fs from 'node:fs';
import path from 'node:path';
import { proofReuseEnvironment } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/character-environment-adapter-20261023/unlimited-preparation-v2/runtime/src/solver/proofReuse.ts';
import { resolveMathematicsRuntimeEnvironment } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/character-environment-adapter-20261023/unlimited-preparation-v2/runtime/src/math/mathRuntimeEnvironment.ts';
import { LAKE_CONFIGURATION_FILES } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/character-environment-adapter-20261023/unlimited-preparation-v2/runtime/src/math/mathConstructionSources.ts';
import { mathDigest } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/character-environment-adapter-20261023/unlimited-preparation-v2/runtime/src/math/mathRuntimeIo.ts';
const base = '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/native-check-hotspot-20261024/native-sync-def-attempt/native-followup';
const native = Object.fromEntries(fs.readFileSync('/proc/2305626/environ').toString().split('\0').filter(Boolean).map(item => { const i=item.indexOf('='); return [item.slice(0,i),item.slice(i+1)]; }));
const accessEnvironment = resolveMathematicsRuntimeEnvironment({ ...native, DEEPSCIENTIST_MATH_ENV_FILE: path.join(base,'result.json.runtime/environment-solver.json') });
const projects = [
  ['delivery-source-project',path.join(base,'result.json.runtime/worktree-4/generated/problem')],
  ['existing-clean-projection-as-integration-configuration', '/tmp/math-check-WmqJZg/worktree/generated/problem'],
  ['lead-all-target-project',path.join(base,'result.json.runtime/worktree/generated/problem')],
  ['final-workspace-project',path.join(base,'workspace/generated/problem')],
];
const observations=projects.map(([stage,project]) => {
  const result=proofReuseEnvironment(project,accessEnvironment);
  const configuration=LAKE_CONFIGURATION_FILES.map(file => {try {return [file,mathDigest(fs.readFileSync(path.join(project,file)))];} catch(e) { if(e.code==='ENOENT') return [file,null]; throw e;} });
  return {stage,project,reusable:result.reusable,proofReuseEnvironmentDigest:result.digest,configuration};
});
process.stdout.write(JSON.stringify({schema:'theorem-os.character-stage-reuse-environment.v1',observedAt:new Date().toISOString(),accessEnvironmentSource:path.join(base,'result.json.runtime/environment-solver.json'),nativeParentPid:2305626,method:'Calls actual frozen proofReuseEnvironment; reads only existing projects. The clean projection is an existing checkout, not a newly created integration or verifier run.',leanInvoked:false,modelInvoked:false,activeFilesModified:false,observations},null,2)+'\n');
