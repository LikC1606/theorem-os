import fs from 'node:fs';
import path from 'node:path';
import { runMathematicsSandboxedCommand } from '../../runtime-v2/src/math/verifier';
import { resolveMathematicsRuntimeEnvironment } from '../../runtime-v2/src/math/mathRuntimeEnvironment';
import { prepareMathProofEnvironment, MATH_PROOF_ENVIRONMENT_ENV } from '../../runtime-v2/src/math/mathProofEnvironment';
import { DEFAULT_MATH_PROOF_ENVIRONMENT_CACHE_ROOT } from '../../runtime-v2/src/math/mathProofEnvironmentCache';
const directory = import.meta.dir;
const root = path.resolve(directory, '../..');
const project = path.join(directory, 'standalone-project');
const command = fs.readFileSync(path.join(directory, 'isolated-evaluator.sh'), 'utf8');
const staticEnv = resolveMathematicsRuntimeEnvironment({ HOME: '/home/lzh', DEEPSCIENTIST_MATH_ENV_FILE: path.join(root, 'math.env') });
const packages = path.join(directory, 'authorized-packages');
const sealed = await prepareMathProofEnvironment(project, packages, { env: staticEnv, cacheRoot: DEFAULT_MATH_PROOF_ENVIRONMENT_CACHE_ROOT,
  onProgress: phase => console.log(JSON.stringify({ event: 'sealed-preparation', phase })) });
try {
  const result = await runMathematicsSandboxedCommand({ checkoutRoot: project, command: '/bin/sh', args: ['-c', command],
    timeoutMs: 600000, env: { ...staticEnv, [MATH_PROOF_ENVIRONMENT_ENV]: sealed.environmentValue }, outputLimit: 100000 });
  const passed = result.exitCode === 0 && result.stdout.includes('Your solution is okay!');
  const receipt = { observedAt: new Date().toISOString(), passed, standaloneAudit: true, campaignAcceptance: false,
    attribution: 'external independent assistance', sealedEnvironment: true, originalTargetAndAxiomWhitelistPreserved: true,
    sourceGuardAdaptedDependencyPassed: false, command, result };
  fs.writeFileSync(path.join(directory, 'sealed-isolated-comparator-receipt.json'), JSON.stringify(receipt, null, 2));
  console.log(JSON.stringify({ passed, exitCode: result.exitCode, sandboxBackend: result.sandboxBackend,
    stderr: result.stderr, stdoutTail: result.stdout.slice(-3500) }));
  process.exitCode = passed ? 0 : 1;
} finally { await sealed.dispose(); }
