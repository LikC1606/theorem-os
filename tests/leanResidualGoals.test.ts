import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { mathLocalModuleBuildOrder } from '../src/math/mathConstructionSources';
import { mathDigest } from '../src/math/mathRuntimeIo';
import { leanDiagnosticEnvironmentIdentity, readLeanResidualGoals, readLeanResidualGoalSnapshot, type LeanResidualGoalConsumer } from '../src/math/leanResidualGoals';

const host = vi.hoisted(() => ({ environment: vi.fn(), tools: vi.fn() }));
vi.mock('../src/math/verifier', () => ({ formalVerificationToolIdentity: host.tools }));
vi.mock('../src/math/mathProofEnvironment', () => ({ resolveMathProofEnvironment: host.environment }));

const configurationFiles = ['lean-toolchain', 'lakefile.toml', 'lakefile.lean', 'lake-manifest.json', '.lake/package-overrides.json'];
const goalText = 'n : Nat\nh : n > 0\n\u22a2 n > 1';
const consumer: LeanResidualGoalConsumer = { taskId: 'consumer', taskDigest: mathDigest('consumer-task'),
  theoremName: 'Second.target', proofPath: 'Submission.lean' };

describe('source-bound advisory Lean residual goals', () => {
  let root: string, env: NodeJS.ProcessEnv;
  beforeEach(() => {
    root = fs.mkdtempSync(path.join(os.tmpdir(), 'lean-residual-goals-'));
    fs.writeFileSync(path.join(root, 'Submission.lean'), `import Shared
namespace First
theorem target : True := by
  exact missingFirst
end First
namespace Second
theorem target : True := by
  exact missingSecond
end Second
`);
    fs.writeFileSync(path.join(root, 'Shared.lean'), 'def localBound : Nat := 1\n');
    fs.writeFileSync(path.join(root, 'lean-toolchain'), 'leanprover/lean4:v4.31.0\n');
    fs.writeFileSync(path.join(root, 'lakefile.toml'), 'name = "ResidualFixture"\n[[lean_lib]]\nname = "Submission"\n');
    env = { PATH: '/usr/bin:/bin', ELAN_HOME: '', LEAN_PATH: '', LEAN_SYSROOT: '',
      DEEPSCIENTIST_MATH_ENV_FILE: path.join(root, 'missing.env') };
    host.environment.mockReset().mockReturnValue({ identity: mathDigest('sealed-packages') });
    host.tools.mockReset().mockReturnValue(mathDigest('fixture-tools'));
  });
  afterEach(() => { fs.rmSync(root, { recursive: true, force: true }); });

  function message(overrides: Record<string, unknown> = {}) {
    return { severity: 'error', data: `unsolved goals\n${goalText}`, fileName: 'Submission.lean',
      pos: { line: 8, column: 2 }, endPos: { line: 8, column: 21 }, kind: 'Tactic.unsolvedGoals', ...overrides };
  }

  function capture(input: { messages?: Record<string, unknown>[]; artifact?: Record<string, unknown>;
    latest?: Record<string, unknown>; requestedFiles?: string[] } = {}) {
    const requestedFiles = input.requestedFiles ?? ['Submission.lean'];
    const configuration = configurationFiles.map(file => ({ file,
      digest: fs.existsSync(path.join(root, file)) ? mathDigest(fs.readFileSync(path.join(root, file))) : null }));
    const sourceFiles = mathLocalModuleBuildOrder(root, requestedFiles).map(({ file }) =>
      ({ file, digest: mathDigest(fs.readFileSync(path.join(root, file))) }));
    const identity = leanDiagnosticEnvironmentIdentity(root, env);
    const sourceDigest = mathDigest(JSON.stringify([
      configuration.map(item => item.digest ?? ''), sourceFiles.map(item => [item.file, item.digest]),
    ]));
    const stdout = (input.messages ?? [message()]).map(value => JSON.stringify(value)).join('\n') + '\n';
    const artifact = { schema: 'theoremos.lean-diagnostics.v1', authority: 'advisory-lean-process', sourceDigest,
      ...identity, file: 'Submission.lean', sourceCurrent: true, sourceFiles,
      exitCode: 1, timedOut: false, aborted: false, captureComplete: true, captureLimit: 4_000_000,
      stdout, stderr: '', stdoutSha256: mathDigest(stdout), stderrSha256: mathDigest(''),
      ...input.artifact };
    const text = JSON.stringify(artifact) + '\n', digest = mathDigest(text);
    const artifactReference = { path: `.lake/diagnostic-artifacts/${digest}.json`, digest,
      sourceDigest, environmentDigest: identity.environmentDigest, captureComplete: artifact.captureComplete };
    fs.mkdirSync(path.join(root, '.lake/diagnostic-artifacts'), { recursive: true });
    fs.writeFileSync(path.join(root, artifactReference.path), text);
    const latest = { schema: 'theoremos.lean-diagnostics-latest.v1', authority: 'advisory-lean-process',
      sourceDigest, ...identity, configuration, sourceFiles, requestedFiles, exitCode: 1, timedOut: false, aborted: false,
      diagnosticArtifacts: [artifactReference], ...input.latest };
    fs.writeFileSync(path.join(root, '.lake/lean-diagnostics-latest.json'), JSON.stringify(latest));
    return { latest, artifactReference, artifact };
  }

  const read = (consumers: readonly LeanResidualGoalConsumer[] = [consumer], environment = env) =>
    readLeanResidualGoals({ projectRoot: root, env: environment, consumers });

  it('returns independent goals for the exact qualified consumer with advisory provenance', () => {
    const { latest, artifactReference } = capture({ messages: [
      message({ pos: { line: 4, column: 2 }, endPos: { line: 4, column: 20 } }), message(),
      message({ data: 'unsolved goals\n\u22a2 anotherGoal' }),
    ] });
    const identity = { authority: 'advisory-lean-process', consumer,
      sourceDigest: latest.sourceDigest, environmentDigest: latest.environmentDigest, toolIdentity: latest.toolIdentity,
      artifact: { path: artifactReference.path, digest: artifactReference.digest },
      file: 'Submission.lean', line: 8, column: 2 };
    expect(read()).toEqual([{ ...identity, goalText }, { ...identity, goalText: '⊢ anotherGoal' }]);
  });

  it('accepts an exact absolute file location and positions without an optional end range', () => {
    capture({ messages: [message({ fileName: path.join(root, 'Submission.lean'), endPos: undefined })] });
    expect(read()[0]?.consumer).toEqual(consumer);
  });

  it('reports source-matched diagnostics omitted after the bounded reader fills', () => {
    capture({ messages: Array.from({ length: 11 }, (_, index) => message({ data: `unsolved goals\n⊢ Goal${index}` })) });
    const snapshot = readLeanResidualGoalSnapshot({ projectRoot: root, env, consumers: [consumer] });
    expect(snapshot.goals).toHaveLength(8);
    expect(snapshot.omissions).toEqual([{ consumer, count: 3, reason: 'diagnostic-reader-budget' }]);
    fs.appendFileSync(path.join(root, 'Shared.lean'), '\n');
    expect(readLeanResidualGoalSnapshot({ projectRoot: root, env, consumers: [consumer] })).toEqual({ goals: [], omissions: [] });
  });

  it.each(['source', 'dependency', 'configuration', 'optional-configuration'])('rejects changed %s identity', change => {
    capture();
    const file = change === 'source' ? 'Submission.lean' : change === 'dependency' ? 'Shared.lean' :
      change === 'configuration' ? 'lean-toolchain' : 'lake-manifest.json';
    fs.appendFileSync(path.join(root, file), '\n');
    expect(read()).toEqual([]);
  });

  it('recomputes the complete import closure when a formerly external import becomes local', () => {
    fs.writeFileSync(path.join(root, 'Shared.lean'), 'import Emergent\ndef localBound : Nat := 1\n');
    capture();
    fs.writeFileSync(path.join(root, 'Emergent.lean'), 'def anotherBound : Nat := 2\n');
    expect(read()).toEqual([]);
  });

  it('rejects a self-consistent manifest that reports only part of the requested source closure', () => {
    const initial = capture();
    const sourceFiles = initial.latest.sourceFiles.filter(item => item.file === 'Submission.lean');
    const sourceDigest = mathDigest(JSON.stringify([
      initial.latest.configuration.map(item => item.digest ?? ''), sourceFiles.map(item => [item.file, item.digest]),
    ]));
    capture({ latest: { sourceFiles, sourceDigest }, artifact: { sourceFiles, sourceDigest } });
    expect(read()).toEqual([]);
  });

  it.each(['tools', 'sealed-environment', 'PATH'])('rejects changed %s identity', change => {
    capture();
    if (change === 'tools') host.tools.mockReturnValue(mathDigest('new-tools'));
    if (change === 'sealed-environment') host.environment.mockReturnValue({ identity: mathDigest('new-sealed-packages') });
    expect(read([consumer], change === 'PATH' ? { ...env, PATH: '/bin' } : env)).toEqual([]);
  });

  it.each(['unknown-tools', 'missing-sealed-environment', 'invalid-sealed-environment'])('rejects %s', change => {
    capture();
    if (change === 'unknown-tools') host.tools.mockReturnValue(undefined);
    if (change === 'missing-sealed-environment') host.environment.mockReturnValue(undefined);
    if (change === 'invalid-sealed-environment') host.environment.mockImplementation(() => { throw new Error('stale sealed environment'); });
    expect(read()).toEqual([]);
  });

  it.each([
    { timedOut: true }, { aborted: true }, { exitCode: null }, { exitCode: 137 }, { exitCode: -1 }, { toolIdentity: undefined },
    { configuration: [] }, { requestedFiles: [] }, { schema: 'unknown' },
  ])('rejects unsupported or incomplete latest manifests: %j', latest => {
    capture({ latest });
    expect(read()).toEqual([]);
  });

  it.each([
    { captureComplete: false }, { captureComplete: null }, { sourceCurrent: false }, { sourceCurrent: undefined },
    { timedOut: true }, { aborted: true }, { exitCode: null }, { exitCode: 137 }, { exitCode: -1 }, { toolIdentity: undefined },
    { stdoutSha256: mathDigest('uncaptured tail') }, { stderrSha256: undefined },
    { sourceDigest: mathDigest('stale-source') }, { sourceFiles: [] }, { environmentDigest: mathDigest('stale-environment') },
  ])('rejects unsupported or incomplete artifacts: %j', artifact => {
    capture({ artifact });
    expect(read()).toEqual([]);
  });

  it('rejects missing or tampered artifacts without trusting the cached messages summary', () => {
    let captured = capture();
    fs.appendFileSync(path.join(root, captured.artifactReference.path), ' ');
    expect(read()).toEqual([]);
    captured = capture();
    fs.unlinkSync(path.join(root, captured.artifactReference.path));
    expect(read()).toEqual([]);
    capture({ messages: [], artifact: { messages: [{ format: 'lean-json', severity: 'error', goalText,
      file: 'Submission.lean', line: 8, column: 2 }] } });
    expect(read()).toEqual([]);
  });

  it.each([
    { fileName: undefined }, { fileName: 'Shared.lean' }, { fileName: './Submission.lean' },
    { fileName: '/other/project/Submission.lean' }, { pos: undefined }, { pos: { line: 0, column: 2 } },
    { pos: { line: 100, column: 2 } }, { pos: { line: 8, column: 100 } }, { pos: { line: 8, column: -1 } },
    { pos: { line: 6, column: 2 }, endPos: undefined }, { endPos: { line: 10, column: 0 } },
    { endPos: { line: 7, column: 0 } }, { endPos: { line: 100, column: 0 } },
  ])('rejects missing, uncertain, or cross-declaration source positions: %j', diagnostic => {
    capture({ messages: [message(diagnostic)] });
    expect(read()).toEqual([]);
  });

  it('rejects short-name aliases, duplicate consumers, and duplicate qualified declarations', () => {
    capture();
    expect(read([{ ...consumer, theoremName: 'target' }])).toEqual([]);
    expect(read([consumer, { ...consumer, taskId: 'duplicate-consumer' }])).toEqual([]);
    const file = path.join(root, 'Submission.lean');
    fs.writeFileSync(file, fs.readFileSync(file, 'utf8').replace('end Second', 'theorem target : True := by trivial\nend Second'));
    capture();
    expect(read()).toEqual([]);
  });

  it('counts Lean Unicode columns by code point when matching declaration ranges', () => {
    const source = 'namespace Second\n/- \ud83d\ude00 -/ theorem target : True := by exact missing\nend Second\n';
    fs.writeFileSync(path.join(root, 'Submission.lean'), source);
    const line = source.split('\n')[1], column = [...line.slice(0, line.indexOf('theorem'))].length;
    capture({ messages: [message({ pos: { line: 2, column }, endPos: { line: 2, column: [...line].length } })] });
    expect(read()[0]).toMatchObject({ consumer, line: 2, column });
  });

  it('retains a complete 16000-byte goal and rejects larger goals without truncating', () => {
    const exact = '\u22a2 ' + 'x'.repeat(15_996);
    expect(Buffer.byteLength(exact)).toBe(16_000);
    capture({ messages: [message({ data: `unsolved goals\n${exact}` })] });
    expect(read()[0]?.goalText).toBe(exact);
    capture({ messages: [message({ data: `unsolved goals\n${exact}x` })] });
    expect(read()).toEqual([]);
  });

  it('ignores raw goals, warnings, and Lean errors without an actual residual goal', () => {
    const stdout = 'Submission.lean:8:3: error: unsolved goals\n\u22a2 True\n';
    capture({ artifact: { stdout, stdoutSha256: mathDigest(stdout) } });
    expect(read()).toEqual([]);
    capture({ messages: [message({ severity: 'warning' }), message({ data: 'unknown identifier missing' })] });
    expect(read()).toEqual([]);
  });

  it('rejects protected requested files, traversal references, and symbolic metadata paths', () => {
    capture({ latest: { requestedFiles: ['Solution.lean'] } });
    expect(read()).toEqual([]);
    const { artifactReference } = capture();
    capture({ latest: { diagnosticArtifacts: [{ ...artifactReference, path: '../outside.json' }] } });
    expect(read()).toEqual([]);
    const latestFile = path.join(root, '.lake/lean-diagnostics-latest.json');
    fs.unlinkSync(latestFile);
    fs.symlinkSync(path.join(root, 'Submission.lean'), latestFile);
    expect(read()).toEqual([]);
  });

  it.each(['latest', 'artifact', 'source'])('rejects a hard-linked %s file', location => {
    const { artifactReference } = capture();
    const target = location === 'latest' ? '.lake/lean-diagnostics-latest.json' :
      location === 'artifact' ? artifactReference.path : 'Submission.lean';
    fs.linkSync(path.join(root, target), path.join(root, 'additional-link'));
    expect(read()).toEqual([]);
  });

  it('preserves a UTF-8 BOM in source identities and rejects malformed source encoding', () => {
    const file = path.join(root, 'Submission.lean');
    fs.writeFileSync(file, '\ufeff' + fs.readFileSync(file, 'utf8'));
    capture();
    expect(read()[0]?.goalText).toBe(goalText);
    fs.appendFileSync(file, Buffer.from([0xff]));
    capture();
    expect(read()).toEqual([]);
  });

  it('does not supply a goal when the source changes during the final identity recheck', () => {
    capture();
    host.tools.mockImplementationOnce(() => mathDigest('fixture-tools')).mockImplementationOnce(() => {
      fs.appendFileSync(path.join(root, 'Submission.lean'), '\n');
      return mathDigest('fixture-tools');
    });
    expect(read()).toEqual([]);
  });

  it('leaves missing diagnostic state absent and avoids identity work without consumers', () => {
    expect(read()).toEqual([]);
    expect(host.tools).not.toHaveBeenCalled(); expect(host.environment).not.toHaveBeenCalled();
    host.tools.mockClear(); host.environment.mockClear();
    expect(read([])).toEqual([]);
    expect(host.tools).not.toHaveBeenCalled(); expect(host.environment).not.toHaveBeenCalled();
    expect(fs.existsSync(path.join(root, '.lake'))).toBe(false);
  });
});
