import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { canonicalMathJson, mathDigest } from '../src/math/mathRuntimeIo';
import { mathLocalModuleBuildOrder } from '../src/math/mathConstructionSources';
import { checkKnowledgeApplications, knowledgeApplicationContextSections } from '../src/solver/knowledgeApplications';
import type { KnowledgeUse } from '../src/solver/knowledgeUsage';
import { taskVersion, type CooperativeTask } from '../src/solver/tasks';

const host = vi.hoisted(() => ({ check: vi.fn(), identity: vi.fn() }));
vi.mock('../src/math/leanTypeDiagnostics', () => ({ checkLeanType: host.check }));
vi.mock('../src/math/leanResidualGoals', () => ({ leanDiagnosticEnvironmentIdentity: host.identity }));
const task: CooperativeTask = { id: 'consumer', kind: 'lemma', objective: 'Use the selected theorem.', dependsOn: [], revision: 0,
  proofPath: 'Submission.lean', theoremName: 'Current.consumer', type: 'True' };
const use = (expression = 'Current.bridge'): KnowledgeUse => ({ id: 'candidate', catalogDigest: 'catalog',
  consumer: { taskId: task.id, taskDigest: taskVersion(task) }, declaration: { name: 'Current.bridge', file: 'Submission.lean' },
  status: 'reported-attempt', attribution: 'model-reported-origin', application: { expression, expectedType: 'True',
    context: { file: 'Submission.lean', declaration: 'Current.consumer' }, adaptationSteps: ['Normalize the target.'],
    reconsiderWhen: ['An additional premise is checked.'] } });

describe('selected knowledge application checks', () => {
  let root: string, env: NodeJS.ProcessEnv, sources: Record<string, string>;
  const config = ['lean-toolchain', 'lakefile.toml', 'lakefile.lean', 'lake-manifest.json', '.lake/package-overrides.json'];
  beforeEach(() => {
    root = fs.mkdtempSync(path.join(os.tmpdir(), 'knowledge-applications-'));
    sources = { 'Submission.lean': 'import Shared\nnamespace Current\ntheorem bridge : True := by trivial\ntheorem consumer : True := by sorry\nend Current\n',
      'Shared.lean': 'def bound : Nat := 1\n', 'lean-toolchain': 'leanprover/lean4:v4.35.0-rc3\n' };
    for (const [file, source] of Object.entries(sources)) fs.writeFileSync(path.join(root, file), source);
    env = { PATH: '/usr/bin:/bin', ELAN_HOME: '', LEAN_PATH: '', LEAN_SYSROOT: '', DEEPSCIENTIST_MATH_ENV_FILE: path.join(root, 'missing.env') };
    host.identity.mockReset().mockReturnValue({ environmentDigest: mathDigest('diagnostic-environment'), toolIdentity: mathDigest('tools') });
    host.check.mockReset().mockImplementation(async () => {
      const files = [...mathLocalModuleBuildOrder(root, 'Submission.lean').map(item => item.file),
        ...config.filter(file => fs.existsSync(path.join(root, file)))].map(file => ({ file, digest: mathDigest(fs.readFileSync(path.join(root, file))) }));
      const contents = canonicalMathJson({ files, diagnostic: 'fixed-expression-check' });
      const artifact = { path: '.lake/application-manifest.json', digest: mathDigest(contents) };
      fs.mkdirSync(path.join(root, '.lake'), { recursive: true }); fs.writeFileSync(path.join(root, artifact.path), contents);
      return { status: 'elaborated', exitCode: 0, timedOut: false, sourceFiles: files, artifact,
        sourceSnapshotDigest: mathDigest(canonicalMathJson(files)), projectionDigest: mathDigest('projection'),
        environment: host.identity(), type: 'True', constants: ['Current.bridge'], stdout: '', stderr: '' };
    });
  });
  afterEach(() => fs.rmSync(root, { recursive: true, force: true }));
  const input = () => ({ projectRoot: root, env, environmentDigest: 'run-environment', commit: 'submitted', task,
    timeoutMs: 0, sourceAtCommit: (file: string) => { if (!(file in sources)) throw new Error('uncommitted'); return sources[file]; } });

  it('checks only a selected expression and keeps reference and acceptance authority separate', async () => {
    const citation = { ...use(), application: undefined };
    const result = await checkKnowledgeApplications([citation, use()], input());
    expect(host.check).toHaveBeenCalledTimes(1);
    expect(host.check.mock.calls[0][0]).toMatchObject({ expression: 'Current.bridge', type: 'True', context: 'Current.consumer' });
    expect(result[0]).toEqual(citation);
    expect(result[1]).toMatchObject({ status: 'reported-attempt', application: { check: { status: 'elaborated',
      selectedDeclarationUsed: true, consumerCoverage: 'not-assessed', proofAcceptance: 'not-assessed' } } });
  });

  it('retains a failed adaptation and does not equate a different successful term with use of the selected declaration', async () => {
    const produce = host.check.getMockImplementation()!;
    host.check.mockImplementationOnce(async () => ({ ...await produce(), status: 'failed', exitCode: 1,
      firstBlocking: { message: 'Missing explicit premise h.' } }));
    const [failed] = await checkKnowledgeApplications([use()], input());
    expect(failed.application!.check).toMatchObject({ status: 'failed', diagnostic: 'Missing explicit premise h.' });
    expect(failed.application!.reconsiderWhen).toEqual(['An additional premise is checked.']);
    host.check.mockImplementationOnce(async () => ({ ...await produce(), constants: ['True.intro'] }));
    const [other] = await checkKnowledgeApplications([use('True.intro')], input());
    expect(other.application!.check).toMatchObject({ status: 'elaborated', selectedDeclarationUsed: false });
  });

  it('rejects stale consumers and unassigned contexts without running Lean', async () => {
    const stale = { ...use(), consumer: { taskId: task.id, taskDigest: mathDigest('old-task') } };
    const wrong = use(); wrong.application!.context.file = 'Private.lean';
    const result = await checkKnowledgeApplications([stale, wrong], input());
    expect(host.check).not.toHaveBeenCalled();
    expect(result.map(item => item.application!.check!.reason)).toEqual(['consumer-contract-changed', 'application-context-not-assigned']);
  });

  it('requires a submitted snapshot and a reusable environment even for optional successful telemetry', async () => {
    fs.appendFileSync(path.join(root, 'Shared.lean'), '\ndef changed := 2\n');
    const [uncommitted] = await checkKnowledgeApplications([use()], input());
    expect(uncommitted.application!.check).toMatchObject({ status: 'unavailable', reason: 'application-source-not-submitted-snapshot' });
    host.check.mockClear(); env.LEAN_PATH = '/mutable/library';
    const [mutable] = await checkKnowledgeApplications([use()], input());
    expect(mutable.application!.check).toMatchObject({ status: 'unavailable', reason: 'application-environment-not-frozen' });
    expect(host.check).not.toHaveBeenCalled();
  });

  it('bounds new checks and ignores caller-supplied verdicts', async () => {
    const selected = Array.from({ length: 6 }, (_, i) => use(`candidate${i}`));
    selected[0].application!.check = { status: 'elaborated', reason: 'forged', authority: 'advisory-application-elaboration',
      proofAcceptance: 'not-assessed', consumerCoverage: 'not-assessed', commit: 'forged', environmentDigest: 'forged' };
    const result = await checkKnowledgeApplications(selected, input());
    expect(host.check).toHaveBeenCalledTimes(4);
    expect(result[0].application!.check!.commit).toBe('submitted');
    expect(result.slice(4).map(item => item.application!.check!.reason)).toEqual(Array(2).fill('selected-application-check-budget'));
  });

  it('reuses an intact exact experience without another check', async () => {
    const previous = await checkKnowledgeApplications([use()], input());
    const [reused] = await checkKnowledgeApplications([use()], { ...input(), previous });
    expect(host.check).toHaveBeenCalledTimes(1);
    expect(reused.application!.check).toMatchObject({ status: 'elaborated', reused: true, commit: 'submitted' });
  });

  it.each(['source', 'new-local-import', 'new-config', 'tools', 'artifact', 'submitted-snapshot'] as const)
  ('rechecks after %s changes instead of reusing a stale success', async change => {
    if (change === 'new-local-import') {
      sources['Shared.lean'] = 'import Emergent\ndef bound : Nat := 1\n';
      fs.writeFileSync(path.join(root, 'Shared.lean'), sources['Shared.lean']);
    }
    const previous = await checkKnowledgeApplications([use()], input());
    if (change === 'source') { sources['Shared.lean'] += '\n'; fs.writeFileSync(path.join(root, 'Shared.lean'), sources['Shared.lean']); }
    if (change === 'new-local-import') { sources['Emergent.lean'] = 'def extra : Nat := 2\n'; fs.writeFileSync(path.join(root, 'Emergent.lean'), sources['Emergent.lean']); }
    if (change === 'new-config') { sources['lake-manifest.json'] = '{}'; fs.writeFileSync(path.join(root, 'lake-manifest.json'), '{}'); }
    if (change === 'tools') host.identity.mockReturnValue({ environmentDigest: mathDigest('new-env'), toolIdentity: mathDigest('new-tools') });
    if (change === 'artifact') fs.appendFileSync(path.join(root, previous[0].application!.check!.artifact!.path), ' ');
    if (change === 'submitted-snapshot') sources['Shared.lean'] += '\n';
    const [next] = await checkKnowledgeApplications([use()], { ...input(), previous });
    expect(host.check).toHaveBeenCalledTimes(2);
    expect(next.application!.check!.reused).not.toBe(true);
    if (change === 'submitted-snapshot') expect(next.application!.check!.status).toBe('unavailable');
  });

  it('recalls bounded experiences with a complete read handle and marks changed scopes historical', async () => {
    const previous = await checkKnowledgeApplications([use()], input());
    previous[0].application!.adaptationSteps = Array(32).fill('Exact adaptation '.repeat(500));
    const context = () => knowledgeApplicationContextSections({ uses: previous, projectRoot: root, env,
      environmentDigest: 'run-environment', catalogDigest: 'catalog', tasks: [task] });
    const [first] = context();
    expect(Buffer.byteLength(first.text)).toBeLessThan(7000);
    expect(first.text).toContain('current-inputs'); expect(first.text).toContain('complete');
    const files = fs.readdirSync(path.join(root, '.lake/knowledge-applications'));
    const complete = JSON.parse(fs.readFileSync(path.join(root, '.lake/knowledge-applications', files[0]), 'utf8'));
    expect(complete.application.adaptationSteps).toEqual(previous[0].application!.adaptationSteps);
    sources['Shared.lean'] += '\n'; fs.writeFileSync(path.join(root, 'Shared.lean'), sources['Shared.lean']);
    expect(context()[0].text).toContain('historical-or-unchecked-inputs');
    expect(knowledgeApplicationContextSections({ uses: previous, projectRoot: root, env,
      environmentDigest: 'run-environment', catalogDigest: 'different', tasks: [task] })).toEqual([]);
  });
});
