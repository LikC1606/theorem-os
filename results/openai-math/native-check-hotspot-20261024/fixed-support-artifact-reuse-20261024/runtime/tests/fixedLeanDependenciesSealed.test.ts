import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import { expect, it, vi } from 'vitest';
import { fixedLeanDependencyCache } from '../src/math/fixedLeanDependencies';
import { checkManyFormalVerifications, hashMathFormalSourceDeclaration } from '../src/math/verifier';
import { prepareMathProofEnvironment, MATH_PROOF_ENVIRONMENT_ENV, resolveMathProofEnvironment } from '../src/math/mathProofEnvironment';
import { mathDigest } from '../src/math/mathRuntimeIo';
import { runLeanProcess } from '../src/math/mathProcess';

it.skipIf(process.env.DEEPSCIENTIST_TEST_FUSE !== '1')(
  'reuses real sealed supports across projects while rechecking each changed target and rejecting a bad target', async () => {
    const directory = fs.realpathSync(fs.mkdtempSync(path.join('/var/tmp', 'fixed-support-sealed-')));
    const toolchain = 'leanprover/lean4:v4.34.1';
    const bin = path.join(os.homedir(), '.elan/toolchains/leanprover--lean4---v4.34.1/bin');
    const env = { ...process.env, ELAN_HOME: path.join(os.homedir(), '.elan'),
      PATH: `${bin}:${process.env.PATH ?? '/usr/bin:/bin'}:/usr/sbin`,
      DEEPSCIENTIST_MATH_ENV_FILE: path.join(directory, 'math.env'), DEEPSCIENTIST_MATH_SANDBOX_BACKEND: 'bwrap' };
    const first = path.join(directory, 'task-projection/project'), second = path.join(directory, 'canonical/project');
    const packages = path.join(directory, 'packages'), library = path.join(packages, 'toy');
    const output = path.join(library, '.lake/build/lib/lean/SealedFixture.olean');
    const proofs: Awaited<ReturnType<typeof prepareMathProofEnvironment>>[] = [];
    const measurements: Record<string, unknown>[] = [];
    const preparations: { kind: string; hit?: boolean; compiled: boolean; durationMs: number }[] = [];
    let supportCompilations = 0;
    const prepare = fixedLeanDependencyCache.prepare.bind(fixedLeanDependencyCache);
    const spy = vi.spyOn(fixedLeanDependencyCache, 'prepare').mockImplementation(async (input, compile) => {
      let compiled = false;
      const result = await prepare(input, async project => {
        expect(fs.existsSync(path.join(project, 'Submission.lean'))).toBe(false);
        supportCompilations++; compiled = true;
        return compile(project);
      });
      preparations.push({ kind: result?.kind ?? 'fallback', hit: result?.kind === 'ready' ? result.hit : undefined,
        compiled, durationMs: result?.kind === 'ready' ? result.durationMs : 0 });
      return result;
    });
    const git = (root: string, args: string[]) => {
      const result = spawnSync('git', ['-C', root, ...args], { encoding: 'utf8', timeout: 5000 });
      if (result.status !== 0) throw result.error ?? new Error(result.stderr);
      return result.stdout.trim();
    };
    const source = (marker: string, proof = 'rfl') => 'import Lean\nimport Support\n' +
      `run_cmd Lean.logInfo "TARGET_${marker}"\ntheorem result : fixedValue = 7 := by ${proof}\n`;
    const check = async (root: string, marker: string, environment: NodeJS.ProcessEnv, proof = 'rfl') => {
      const contents = source(marker, proof);
      fs.writeFileSync(path.join(root, 'Submission.lean'), contents);
      git(root, ['add', '.']); git(root, ['-c', 'user.name=Fixture', '-c', 'user.email=fixture@localhost',
        'commit', '--quiet', '--no-gpg-sign', '-m', marker]);
      const commit = git(root, ['rev-parse', 'HEAD']), started = performance.now();
      const trusted = { 'Support.lean': mathDigest(fs.readFileSync(path.join(root, 'Support.lean'))) };
      const result = await checkManyFormalVerifications({ projectRoot: root, targetCommit: commit,
        timeoutMs: 20_000, batchTimeoutMs: 30_000, items: [{ proofPath: 'Submission.lean', theoremName: 'result',
          statementHash: mathDigest('fixedValue = 7'), leanStatementHash: mathDigest('fixedValue = 7'),
          expectedSourceDeclarationHash: hashMathFormalSourceDeclaration(contents, 'result') }] },
      { env: environment, prepareLocalDependencies: true, collectDeclarationReferences: true, trustedLocalDependencyFiles: trusted });
      const durationMs = performance.now() - started;
      expect(result.events.filter(event => event.kind === 'check.kernel_checked')).toHaveLength(1);
      const targetCompilations = result.events.filter(event => event.kind === 'diagnostic.emitted' &&
        JSON.stringify(event).includes(`TARGET_${marker}`)).length;
      expect(targetCompilations, JSON.stringify(result)).toBe(1);
      measurements.push({ marker, projectRoot: root, targetCommit: commit, status: result.status, durationMs,
        supportCompilations, targetCompilations, receiptId: result.results[0]?.receiptId, sessionId: result.sessionId,
        proofHash: result.results[0]?.proofHash, axioms: result.results[0]?.axioms, preparation: preparations.at(-1),
        kernelEvents: result.events.filter(event => event.kind === 'check.kernel_checked') });
      return result;
    };
    try {
      fs.writeFileSync(env.DEEPSCIENTIST_MATH_ENV_FILE, '');
      fs.mkdirSync(path.dirname(output), { recursive: true });
      fs.writeFileSync(path.join(library, 'lakefile.toml'), 'name = "toy"\n[[lean_lib]]\nname = "SealedFixture"\n');
      fs.writeFileSync(path.join(library, 'SealedFixture.lean'), 'def externalValue : Nat := 7\n');
      const compiled = await runLeanProcess(path.join(bin, 'lean'), ['-R', library, '-o', output, 'SealedFixture.lean'],
        { cwd: library, env, timeoutMs: 10_000 });
      expect(compiled.exitCode, compiled.stdout + compiled.stderr).toBe(0);
      for (const root of [first, second]) {
        fs.mkdirSync(root, { recursive: true });
        fs.writeFileSync(path.join(root, '.gitignore'), '.lake/\n');
        fs.writeFileSync(path.join(root, 'lean-toolchain'), toolchain + '\n');
        fs.writeFileSync(path.join(root, 'lakefile.toml'), 'name = "fixed_support_fixture"\n[[require]]\nname = "toy"\npath = ".lake/packages/toy"\n');
        fs.writeFileSync(path.join(root, 'lake-manifest.json'), JSON.stringify({ schemaVersion: '1.2.0',
          name: 'fixed_support_fixture', packages: [{ name: 'toy', type: 'path', inherited: false,
            configFile: 'lakefile.toml', dir: '.lake/packages/toy' }] }) + '\n');
        fs.writeFileSync(path.join(root, 'Support.lean'), 'import Lean\nimport SealedFixture\n' +
          'run_cmd Lean.logWarning "FIXED_SUPPORT_WARNING"\ndef fixedValue : Nat := externalValue\n');
        git(root, ['init', '--quiet']);
      }
      fixedLeanDependencyCache.dispose();
      const sealed = await prepareMathProofEnvironment(first, packages, { env, cacheRoot: path.join(directory, 'sealed-cache') });
      proofs.push(sealed);
      const host = { ...env, [MATH_PROOF_ENVIRONMENT_ENV]: sealed.environmentValue };
      expect(resolveMathProofEnvironment(first, host)!.identity).toBe(resolveMathProofEnvironment(second, host)!.identity);
      const cold = await check(first, 'COLD', host), warm = await check(second, 'OTHER_PROJECT', host);
      expect(cold.status, JSON.stringify(cold)).toBe('kernel_verified');
      expect(warm.status, JSON.stringify(warm)).toBe('kernel_verified');
      expect(preparations.slice(0, 2).map(item => [item.kind, item.hit, item.compiled])).toEqual([
        ['ready', false, true], ['ready', true, false],
      ]);
      expect(supportCompilations).toBe(1);
      expect(cold.targetCommit).not.toBe(warm.targetCommit);
      expect(cold.results[0]!.receiptId).not.toBe(warm.results[0]!.receiptId);
      expect(cold.results[0]!.proofHash).not.toBe(warm.results[0]!.proofHash);
      for (const result of [cold, warm])
        expect(result.events.some(event => event.kind === 'diagnostic.emitted' && JSON.stringify(event).includes('FIXED_SUPPORT_WARNING'))).toBe(true);
      const bad = await check(second, 'BAD_TARGET', host, 'exact False.elim (by decide)');
      expect(bad.status).toBe('failed'); expect(supportCompilations).toBe(1);
      expect(preparations.at(-1)).toMatchObject({ kind: 'ready', hit: true, compiled: false });

      fs.appendFileSync(path.join(second, 'Support.lean'), '\n-- frozen support revision\n');
      expect((await check(second, 'NEW_SUPPORT', host)).status).toBe('kernel_verified');
      expect(preparations.at(-1)).toMatchObject({ kind: 'ready', hit: false, compiled: true });
      fs.appendFileSync(path.join(second, 'lakefile.toml'), '# exact configuration revision\n');
      expect((await check(second, 'NEW_CONFIG', host)).status).toBe('kernel_verified');
      expect(preparations.at(-1)).toMatchObject({ kind: 'ready', hit: false, compiled: true });

      fs.writeFileSync(path.join(library, 'sealed-revision.txt'), 'new frozen external package bytes\n');
      const changed = await prepareMathProofEnvironment(second, packages, { env, cacheRoot: path.join(directory, 'new-sealed-cache') });
      proofs.push(changed);
      const changedHost = { ...env, [MATH_PROOF_ENVIRONMENT_ENV]: changed.environmentValue };
      expect(resolveMathProofEnvironment(second, changedHost)!.identity).not.toBe(resolveMathProofEnvironment(second, host)!.identity);
      expect((await check(second, 'NEW_PACKAGES', changedHost)).status).toBe('kernel_verified');
      expect(preparations.at(-1)).toMatchObject({ kind: 'ready', hit: false, compiled: true });

      fs.writeFileSync(path.join(second, 'Owned.lean'), 'def ownedValue : Nat := 7\n');
      fs.writeFileSync(path.join(second, 'Support.lean'), 'import Owned\ndef fixedValue : Nat := ownedValue\n');
      const beforeFallback = supportCompilations;
      expect((await check(second, 'OWNED_DEPENDENCY', changedHost)).status).toBe('kernel_verified');
      expect(supportCompilations).toBe(beforeFallback);
      expect(preparations.at(-1)).toMatchObject({ kind: 'fallback', compiled: false });
      const report = { schema: 'fixed-support-real-fixture.v1', toolchain, supportCompilations,
        targetChecks: measurements.length, targetCompilations: measurements.reduce((sum, item) => sum + Number(item.targetCompilations), 0),
        measurements, preparations, modelsCalled: 0, activeRunsModified: false };
      if (process.env.DEEPSCIENTIST_FIXED_SUPPORT_REPORT)
        fs.writeFileSync(process.env.DEEPSCIENTIST_FIXED_SUPPORT_REPORT, JSON.stringify(report, null, 2) + '\n');
      console.info(JSON.stringify(report));
    } finally {
      spy.mockRestore(); fixedLeanDependencyCache.dispose();
      for (const proof of proofs.reverse()) await proof.dispose();
      fs.rmSync(directory, { recursive: true, force: true });
    }
  }, 90_000,
);
