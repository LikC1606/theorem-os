import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { expect, it } from 'vitest';
import { checkLeanType } from '../src/math/leanTypeDiagnostics';
import { runLeanDiagnostics } from '../src/math/leanDiagnostics';
import { readLeanResidualGoals } from '../src/math/leanResidualGoals';
import { runLeanProcess } from '../src/math/mathProcess';
import { mathDigest } from '../src/math/mathRuntimeIo';
import { prepareMathProofEnvironment, mathProofEnvironmentWorkerEnvironment,
  resolveMathProofEnvironment, MATH_PROOF_ENVIRONMENT_ENV } from '../src/math/mathProofEnvironment';

it.skipIf(process.env.DEEPSCIENTIST_TEST_FUSE !== '1')(
  'elaborates a type and reads a complete residual through a real sealed nested worker environment', async () => {
    const directory = fs.realpathSync(fs.mkdtempSync(path.join('/var/tmp', 'typed-sealed-worker-')));
    const toolchain = 'leanprover/lean4:v4.31.0';
    const bin = path.join(os.homedir(), '.elan/toolchains/leanprover--lean4---v4.31.0/bin');
    const env = { ...process.env, ELAN_HOME: path.join(os.homedir(), '.elan'), PATH: `${bin}:${process.env.PATH ?? '/usr/bin:/bin'}:/usr/sbin` };
    const project = path.join(directory, 'project'), packages = path.join(directory, 'packages');
    const worker = path.join(directory, 'workers/researcher/generated/problem');
    const library = path.join(packages, 'toy'), output = path.join(library, '.lake/build/lib/lean/SealedFixture.olean');
    let proof: Awaited<ReturnType<typeof prepareMathProofEnvironment>> | undefined;
    try {
      fs.mkdirSync(path.dirname(output), { recursive: true });
      fs.writeFileSync(path.join(library, 'SealedFixture.lean'), 'namespace Fixture\nstructure Box where\n  value : Nat\nend Fixture\n');
      const compile = await runLeanProcess(path.join(bin, 'lean'), ['-R', library, '-o', output, 'SealedFixture.lean'],
        { cwd: library, env, timeoutMs: Infinity });
      expect(compile.exitCode, compile.stdout + compile.stderr).toBe(0);
      for (const root of [project, worker]) {
        fs.mkdirSync(root, { recursive: true });
        fs.writeFileSync(path.join(root, 'lean-toolchain'), `${toolchain}\n`);
        fs.writeFileSync(path.join(root, 'lakefile.toml'), 'name = "sealed_type_fixture"\n');
        fs.writeFileSync(path.join(root, 'lake-manifest.json'), JSON.stringify({ name: 'sealed_type_fixture', packages: [] }));
        fs.writeFileSync(path.join(root, 'Dependency.lean'), 'import SealedFixture\ndef localValue : Nat := 7\n');
        fs.writeFileSync(path.join(root, 'Submission.lean'), 'import Dependency\nnamespace Geometry\nopen Fixture\n' +
          'theorem original : True := by\n  skip\nend Geometry\n');
      }
      proof = await prepareMathProofEnvironment(project, packages, { env, cacheRoot: path.join(directory, 'cache') });
      const host = { ...env, [MATH_PROOF_ENVIRONMENT_ENV]: proof.environmentValue };
      const mapped = mathProofEnvironmentWorkerEnvironment(worker, host);
      const identity = resolveMathProofEnvironment(worker, mapped)!.identity;
      const original = fs.readFileSync(path.join(worker, 'Submission.lean'));
      expect(fs.existsSync(path.join(worker, '.lake/packages'))).toBe(false);
      const result = await checkLeanType({ projectRoot: worker, file: 'Submission.lean', context: 'Geometry.original',
        type: 'Box -> Nat', env: mapped, timeoutMs: Infinity });
      expect(result.status, result.stdout + result.stderr).toBe('elaborated');
      expect(result).toMatchObject({ type: 'Fixture.Box \u2192 Nat', exitCode: 0, proofAcceptance: 'not-assessed' });
      const clone = path.join(worker, path.dirname(result.artifact.path), 'project');
      expect(resolveMathProofEnvironment(clone, mapped)!.identity).toBe(identity);
      expect(fs.realpathSync(path.join(clone, '.lake/packages'))).toBe(fs.realpathSync(resolveMathProofEnvironment(worker, mapped)!.packagesRoot));
      expect(fs.readFileSync(path.join(worker, 'Submission.lean'))).toEqual(original);
      expect(fs.existsSync(path.join(worker, '.lake/build'))).toBe(false);
      const diagnostics = await runLeanDiagnostics({ projectRoot: worker, files: ['Submission.lean'], env: mapped, timeoutMs: Infinity });
      expect(diagnostics).toMatchObject({ exitCode: 1, timedOut: false });
      const consumer = { taskId: 'original', taskDigest: mathDigest('original-version'), theoremName: 'Geometry.original', proofPath: 'Submission.lean' };
      const goals = readLeanResidualGoals({ projectRoot: worker, env: mapped, consumers: [consumer] });
      expect(goals).toHaveLength(1);
      expect(goals[0]).toMatchObject({ consumer, authority: 'advisory-lean-process', goalText: '\u22a2 True' });
      fs.appendFileSync(path.join(worker, 'Dependency.lean'), '\n-- new diagnostic inputs\n');
      expect(readLeanResidualGoals({ projectRoot: worker, env: mapped, consumers: [consumer] })).toEqual([]);
    } finally {
      await proof?.dispose();
      fs.rmSync(directory, { recursive: true, force: true });
    }
  }, 60_000,
);
