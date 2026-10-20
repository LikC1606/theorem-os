import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { collectLeanKnowledgeEnrichment, leanKnowledgeCollectorIdentity, leanKnowledgeSourceDigest } from '../src/math/leanKnowledgeEnrichment';
import { runLeanProcess } from '../src/math/mathProcess';
import { canonicalMathJson, mathDigest } from '../src/math/mathRuntimeIo';
import { enrichAcceptedKnowledge, writeKnowledgeEnrichment } from '../src/solver/theoremKnowledgeEnrichment';
import { importAcceptedKnowledge } from '../src/solver/theoremKnowledgeAccepted';
import { buildTheoremKnowledge } from '../src/solver/theoremKnowledge';
import { getKnowledgeConsumers } from '../src/solver/theoremKnowledgeConsumers';

const { run, resolveCache } = vi.hoisted(() => ({ run: vi.fn(), resolveCache: vi.fn() }));
vi.mock('../src/math/verifier', () => ({ runMathematicsSandboxedCommand: run,
  formalVerificationToolIdentity: () => 'a'.repeat(64), resolveMathematicsLakePackagesCache: resolveCache }));
const toolchain = 'leanprover/lean4:v4.33.0';
const bin = path.join(os.homedir(), '.elan', 'toolchains', 'leanprover--lean4---v4.33.0', 'bin');
const available = fs.existsSync(path.join(bin, 'lean')) && fs.existsSync(path.join(bin, 'lake'));
const original = 'namespace A\n' +
  'def Predicate (n : Nat) : Prop := n = n\n' +
  'theorem helper (n : Nat) : Predicate n := by rfl\n' +
  'theorem same (n : Nat) : Predicate n := by exact helper n\n' +
  'universe u\n' +
  'theorem poly {\u03b1 : Sort u} (x : \u03b1) : x = x := by rfl\n' +
  'theorem proofInType : ((fun (_ : True) => True) True.intro) := True.intro\n' +
  'end A\nnamespace B\ntheorem same : True := by trivial\nend B\n';
let root: string;
beforeEach(() => {
  root = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'lean-knowledge-test-')));
  fs.writeFileSync(path.join(root, 'Submission.lean'), original);
  fs.writeFileSync(path.join(root, 'lakefile.toml'), 'name = "knowledge"\n');
  fs.writeFileSync(path.join(root, 'lean-toolchain'), `${toolchain}\n`);
  run.mockReset();
  resolveCache.mockReset().mockReturnValue(undefined);
});
afterEach(() => fs.rmSync(root, { recursive: true, force: true }));
const env = () => ({ ...process.env, PATH: `${bin}:/usr/bin:/bin`, ELAN_HOME: path.dirname(bin),
  LEAN_PATH: '', LEAN_SYSROOT: '', DEEPSCIENTIST_MATH_ENV_FILE: path.join(root, 'missing.env') });
const roots = [{ id: 'a', name: 'A.same', file: 'Submission.lean' }, { id: 'b', name: 'B.same', file: 'Submission.lean' }];

describe('offline complete-proof knowledge collection identity', () => {
  it('keeps recorded v1/v2 generators readable while identifying the larger collector separately', () => {
    const legacy = leanKnowledgeCollectorIdentity('complete-proof-knowledge-collector-v1');
    expect(legacy.digest).toBe('607b3096ace3f3b9a8a3cf1248455fe122504fc940ed924e1743a1270c07b64d');
    const previous = leanKnowledgeCollectorIdentity('complete-proof-knowledge-collector-v2');
    expect(previous.digest).toBe('c473ac4b3c7a23e7d1da1370a49242aebaabfa6b335a5305899a0c3828be618b');
    const current = leanKnowledgeCollectorIdentity();
    expect(current.version).toBe('complete-proof-knowledge-collector-v3');
    expect(current.digest).not.toBe(legacy.digest);
    expect(current.digest).not.toBe(previous.digest);
    expect(current.source).toContain('2000000');
  });

  it('records a missing original pin as unavailable without invoking a downloader or diagnostics', async () => {
    fs.writeFileSync(path.join(root, 'lean-toolchain'), 'leanprover/lean4:v99.99.99\n');
    const result = await collectLeanKnowledgeEnrichment({ projectRoot: root, roots, env: env() });
    expect(result.roots.every(item => item.status === 'unavailable')).toBe(true);
    expect(result.identity.toolchain).toBe('leanprover/lean4:v99.99.99');
    expect(result.identity.tools).toEqual([]);
    expect(result.identity).not.toHaveProperty('toolIdentity');
    expect(run).not.toHaveBeenCalled();
    expect(fs.readFileSync(path.join(root, 'Submission.lean'), 'utf8')).toBe(original);
  });

  it('binds every allowed original source and fixed configuration slot to its raw bytes', async () => {
    fs.rmSync(path.join(root, 'lean-toolchain'));
    fs.mkdirSync(path.join(root, 'Extra'));
    fs.writeFileSync(path.join(root, 'Extra', 'Untouched.lean'), 'def untouched := "\ufeff\ud83d\ude80"\r\n');
    fs.writeFileSync(path.join(root, 'Extra', 'lakefile.lean'), 'def nestedLakefileIsSource := true\n');
    const result = await collectLeanKnowledgeEnrichment({ projectRoot: root, roots, env: env() });
    expect(result.identity.sources.map(item => item.file)).toEqual(['Extra/Untouched.lean', 'Extra/lakefile.lean', 'Submission.lean']);
    expect(result.identity.configuration.map(item => item.file)).toEqual([
      'lean-toolchain', 'lakefile.toml', 'lakefile.lean', 'lake-manifest.json', '.lake/package-overrides.json',
    ]);
    expect(result.identity.configuration[0]).toEqual({ file: 'lean-toolchain', digest: null, bytes: 0 });
    expect(result.identity.sourceDigest).toBe(leanKnowledgeSourceDigest(result.identity.sources, result.identity.configuration));
    expect(result.identity.sourceDigest).toBe(mathDigest(canonicalMathJson({
      sources: result.identity.sources, configuration: result.identity.configuration,
    })));
    expect(result.identity.collector).toEqual(leanKnowledgeCollectorIdentity());
    expect(result.identity.collector.digest).toBe(mathDigest(result.identity.collector.source));
  });

  it('keeps an unknown or ambiguous qualified declaration failed and rejects duplicate root ids', async () => {
    fs.rmSync(path.join(root, 'lean-toolchain'));
    const result = await collectLeanKnowledgeEnrichment({ projectRoot: root,
      roots: [{ id: 'missing', name: 'same', file: 'Submission.lean' }], env: env() });
    expect(result.roots[0]).toMatchObject({ status: 'failed', reason: 'root-declaration-missing-or-ambiguous' });
    await expect(collectLeanKnowledgeEnrichment({ projectRoot: root, roots: [roots[0], roots[0]], env: env() }))
      .rejects.toThrow('math_knowledge_enrichment_input_invalid');
  });

  it.each([
    { queryIndices: [] }, { queryIndices: [0, 0] }, { queryIndices: [-1, 1] },
    { queryIndices: [0, 4096] }, { queryIndices: [0, 1.5] },
  ])('rejects invalid partial query indices $queryIndices before diagnostics', async ({ queryIndices }) => {
    await expect(collectLeanKnowledgeEnrichment({ projectRoot: root, roots, queryIndices, env: env() }))
      .rejects.toThrow('math_knowledge_enrichment_input_invalid');
    expect(run).not.toHaveBeenCalled();
  });
});

describe.skipIf(!available)('installed Lean complete-proof collector', () => {
  beforeEach(() => {
    run.mockImplementation(input => runLeanProcess('/bin/sh', ['-ceu', input.args.at(-1)], {
      cwd: input.checkoutRoot, timeoutMs: input.timeoutMs, signal: input.signal,
      outputLimit: input.outputLimit, outputCapture: input.outputCapture,
      env: { ...process.env, PATH: `${bin}:/usr/bin:/bin`,
        LEAN_PATH: path.join(input.checkoutRoot, '.lake', 'build', 'lib', 'lean') },
    }));
  });

  it('distinguishes same names and actual statement/proof uses while preserving every original proof', async () => {
    const result = await collectLeanKnowledgeEnrichment({ projectRoot: root, roots, env: env() });
    expect(result.roots.map(item => [item.status, item.reason])).toEqual([['collected', undefined], ['collected', undefined]]);
    const [a, b] = result.roots;
    expect(a.references, fs.readFileSync(path.join(root, a.artifacts.find(item => item.kind === 'diagnostics')!.path), 'utf8')).toBeDefined();
    expect(a.references?.statement).toContainEqual({ file: 'Submission.lean', name: 'A.Predicate' });
    expect(a.references?.statement).not.toContainEqual({ file: 'Submission.lean', name: 'A.helper' });
    expect(a.references?.proof).toContainEqual({ file: 'Submission.lean', name: 'A.helper' });
    expect(b.references).toEqual({ statement: [], proof: [] });
    expect(a.fullType).toContain('A.Predicate');
    expect(a.universes).toEqual([]);
    expect(result.identity.tools.map(item => item.command)).toEqual(['lean', 'lake']);
    expect(result.identity.toolIdentity).toBe('a'.repeat(64));
    expect(result.identity.environmentDigest).toMatch(/^[a-f0-9]{64}$/u);
    expect(result.identity.executionSourceDigest).toBe(result.identity.sourceDigest);
    expect(run.mock.calls.every(([input]) => input.timeoutMs === Infinity)).toBe(true);
    expect(fs.readFileSync(path.join(root, 'Submission.lean'), 'utf8')).toBe(original);
    expect(fs.existsSync(path.join(root, '.lake', 'build'))).toBe(false);
    for (const item of result.roots) for (const artifact of item.artifacts) {
      const file = path.join(root, artifact.path), bytes = fs.readFileSync(file);
      expect(bytes.length).toBe(artifact.bytes); expect(mathDigest(bytes)).toBe(artifact.digest);
      expect(fs.statSync(file).mode & 0o777).toBe(0o400);
    }
    expect(a.artifacts.find(item => item.kind === 'query')?.digest).toBe(a.queryDigest);
    const exported = JSON.parse(fs.readFileSync(path.join(root, a.artifacts.find(item => item.kind === 'full-type')!.path), 'utf8'));
    expect(exported).toEqual({ name: a.name, fullType: a.fullType, universes: a.universes, typeComplete: true });
  });

  it('keeps the frozen full-record query index when collecting a selected root', async () => {
    const result = await collectLeanKnowledgeEnrichment({ projectRoot: root, roots: [roots[1]], queryIndices: [7], env: env() });
    expect(result.roots[0].status).toBe('collected');
    const query = result.roots[0].artifacts.find(artifact => artifact.kind === 'query')!;
    const source = fs.readFileSync(path.join(root, query.path), 'utf8');
    expect(source).toContain('KNOWLEDGE_REFERENCES_7:');
    expect(source).toContain('.lake/KnowledgeEnrichment7-type.json');
    expect(result.roots[0].references).toEqual({ statement: [], proof: [] });
  });

  it('exports universe parameters and an independently round-tripped complete type with proof terms', async () => {
    const result = await collectLeanKnowledgeEnrichment({ projectRoot: root, roots: [
      { id: 'poly', name: 'A.poly', file: 'Submission.lean' },
      { id: 'proof-type', name: 'A.proofInType', file: 'Submission.lean' },
    ], env: env() });
    expect(result.roots.map(item => [item.status, item.reason])).toEqual([['collected', undefined], ['collected', undefined]]);
    expect(result.roots[0].universes).toEqual(['u']);
    expect(result.roots[0].fullType).toContain('Sort u');
    expect(result.roots[1].fullType).toContain('True.intro');
    expect(result.roots[1].fullType).not.toContain('\u22ef');
  });

  it('round-trips a full explicit type beyond the legacy bound while keeping its statement context bounded', async () => {
    const source = 'set_option maxRecDepth 10000\n' +
      `theorem wide (n : Nat) : ${Array(100).fill('(n + 1 = 1 + n)').join(' ∧ ')} := by simp [Nat.add_comm]\n`;
    fs.writeFileSync(path.join(root, 'Wide.lean'), source);
    const result = await collectLeanKnowledgeEnrichment({ projectRoot: root,
      roots: [{ id: 'wide', name: 'wide', file: 'Wide.lean' }], env: env() });
    const item = result.roots[0];
    const diagnostics = item.artifacts.find(artifact => artifact.kind === 'diagnostics');
    expect([item.status, item.reason], diagnostics && fs.readFileSync(path.join(root, diagnostics.path), 'utf8'))
      .toEqual(['collected', undefined]);
    expect(Buffer.byteLength(item.fullType!)).toBeGreaterThan(24000);
    expect(Buffer.byteLength(item.fullType!)).toBeLessThanOrEqual(256000);
    expect(Buffer.byteLength(item.statementContext!.type)).toBeLessThanOrEqual(24000);
    expect(item.references).toEqual({ statement: [], proof: [] });
    expect(fs.readFileSync(path.join(root, 'Wide.lean'), 'utf8')).toBe(source);
  });

  it('retains the checked full type and references when only the readable statement context exceeds its bound', async () => {
    const name = 'long_' + 'n'.repeat(500);
    const source = `theorem longReadable (${name} : Nat) : ${Array(30).fill(`(${name} = ${name})`).join(' ∧ ')} := by simp\n`;
    fs.writeFileSync(path.join(root, 'LongReadable.lean'), source);
    const result = await collectLeanKnowledgeEnrichment({ projectRoot: root,
      roots: [{ id: 'long-readable', name: 'longReadable', file: 'LongReadable.lean' }], env: env() });
    const item = result.roots[0], diagnostics = item.artifacts.find(artifact => artifact.kind === 'diagnostics');
    expect([item.status, item.reason], diagnostics && fs.readFileSync(path.join(root, diagnostics.path), 'utf8'))
      .toEqual(['collected', undefined]);
    expect(Buffer.byteLength(item.fullType!)).toBeGreaterThan(24000);
    expect(item.statementContext).toBeUndefined();
    expect(item.references).toEqual({ statement: [], proof: [] });
    expect(item.omissions).toEqual(['statement-context:statement-type-export-bound']);
    expect(fs.readFileSync(path.join(root, 'LongReadable.lean'), 'utf8')).toBe(source);
  });

  it('exports a fully explicit type beyond the v2 storage bound while keeping prompt context bounded', async () => {
    const name = 'long_' + 'n'.repeat(1500);
    const source = 'set_option maxRecDepth 10000\n' +
      `theorem largeReadable (${name} : Nat) : ${Array(100).fill(`(${name} = ${name})`).join(' ∧ ')} := by simp\n`;
    fs.writeFileSync(path.join(root, 'LargeReadable.lean'), source);
    const result = await collectLeanKnowledgeEnrichment({ projectRoot: root,
      roots: [{ id: 'large-readable', name: 'largeReadable', file: 'LargeReadable.lean' }], env: env() });
    const item = result.roots[0], diagnostics = item.artifacts.find(artifact => artifact.kind === 'diagnostics');
    expect([item.status, item.reason], diagnostics && fs.readFileSync(path.join(root, diagnostics.path), 'utf8'))
      .toEqual(['collected', undefined]);
    expect(Buffer.byteLength(item.fullType!)).toBeGreaterThan(256000);
    expect(Buffer.byteLength(item.fullType!)).toBeLessThanOrEqual(2_000_000);
    expect(item.statementContext).toBeUndefined();
    expect(item.references).toEqual({ statement: [], proof: [] });
    expect(item.omissions).toEqual(['statement-context:statement-type-export-bound']);
  });

  it('isolates a failed original proof from another root instead of erasing it to obtain references', async () => {
    const bad = 'theorem broken : True := by exact missingOriginalProof\n';
    fs.writeFileSync(path.join(root, 'Bad.lean'), bad);
    const result = await collectLeanKnowledgeEnrichment({ projectRoot: root, roots: [
      { id: 'bad', name: 'broken', file: 'Bad.lean' }, roots[0],
    ], env: env() });
    expect(result.roots.map(item => item.status)).toEqual(['failed', 'collected']);
    expect(result.roots[0]).toMatchObject({ reason: 'lean-collection-failed' });
    expect(result.roots[0]).not.toHaveProperty('references');
    expect(result.roots[0]).not.toHaveProperty('fullType');
    expect(fs.readFileSync(path.join(root, 'Bad.lean'), 'utf8')).toBe(bad);
    expect(fs.readFileSync(path.join(root, 'Submission.lean'), 'utf8')).toBe(original);
  });

  it('does not start Lean after cancellation or introduce a default collection deadline', async () => {
    const controller = new AbortController(); controller.abort();
    const result = await collectLeanKnowledgeEnrichment({ projectRoot: root, roots, env: env(), signal: controller.signal });
    expect(result.roots.every(item => item.status === 'unavailable' && item.reason === 'collection-aborted')).toBe(true);
    expect(run).not.toHaveBeenCalled();
  });

  it('keeps manifest dependencies unavailable without a seal before diagnostics can discover a mutable global cache', async () => {
    fs.writeFileSync(path.join(root, 'lake-manifest.json'), JSON.stringify({ packages: [{ name: 'dependency', rev: 'a'.repeat(40) }] }));
    expect(fs.existsSync(path.join(root, '.lake', 'packages'))).toBe(false);
    const result = await collectLeanKnowledgeEnrichment({ projectRoot: root, roots,
      env: { ...env(), DEEPSCIENTIST_MATH_TRUSTED_CACHE_ROOTS: '/explicit/mutable/cache' } });
    expect(result.roots.every(item => item.status === 'unavailable' && item.reason === 'unsealed-dependencies-unavailable')).toBe(true);
    expect(result.identity).not.toHaveProperty('environmentDigest');
    expect(run).not.toHaveBeenCalled();
  });

  it('rejects any implicit mutable package resolution even without a local package manifest', async () => {
    resolveCache.mockReturnValue('/implicit/mutable/cache');
    const result = await collectLeanKnowledgeEnrichment({ projectRoot: root, roots, env: env() });
    expect(result.roots.every(item => item.status === 'unavailable' && item.reason === 'unsealed-dependencies-unavailable')).toBe(true);
    expect(resolveCache).toHaveBeenCalledOnce();
    expect(run).not.toHaveBeenCalled();
  });

  it('preserves an existing query-name source and continues collecting another root', async () => {
    const source = 'theorem existingQueryName : True := by trivial\n';
    fs.writeFileSync(path.join(root, 'KnowledgeEnrichment0.lean'), source);
    const result = await collectLeanKnowledgeEnrichment({ projectRoot: root, roots: [
      { id: 'collision', name: 'existingQueryName', file: 'KnowledgeEnrichment0.lean' }, roots[0],
    ], env: env() });
    expect(result.roots[0]).toMatchObject({ status: 'unavailable', reason: 'query-source-name-collision' });
    expect(result.roots[1]).toMatchObject({ status: 'collected', name: 'A.same' });
    expect(fs.readFileSync(path.join(root, 'KnowledgeEnrichment0.lean'), 'utf8')).toBe(source);
  });

  it('carries real collector exports through an explicit sidecar and archive import into bounded consumers', async () => {
    const project = path.join(root, 'archive'); fs.mkdirSync(project);
    const files = { 'Submission.lean': original, 'lakefile.toml': 'name = "knowledge"\n', 'lean-toolchain': `${toolchain}\n` };
    for (const [file, text] of Object.entries(files)) fs.writeFileSync(path.join(project, file), text);
    const manifest = path.join(root, 'accepted.json');
    fs.writeFileSync(manifest, JSON.stringify([{ problem_id: 'fixture', directory: 'archive', status: 'official_accepted',
      original_source_commit: 'a'.repeat(40), result_url: 'https://example.org/result',
      source_sha256: Object.fromEntries(Object.entries(files).map(([file, text]) => [file, mathDigest(text)])) }]));
    expect(importAcceptedKnowledge(manifest).candidates.every(item => item.dependencies.coverage === 'unavailable')).toBe(true);
    expect(run).not.toHaveBeenCalled();
    const enrichment = await enrichAcceptedKnowledge(manifest, 'fixture', { env: env() });
    expect(enrichment.records[0].collection.roots.every(item => item.status === 'collected')).toBe(true);
    const sidecar = path.join(root, 'enrichment.json'); writeKnowledgeEnrichment(sidecar, enrichment);
    const executions = run.mock.calls.length;
    fs.rmSync(path.join(project, '.lake', 'knowledge-enrichment'), { recursive: true });
    const imported = importAcceptedKnowledge(manifest, { enrichmentFile: sidecar });
    expect(run).toHaveBeenCalledTimes(executions);
    const base = buildTheoremKnowledge(imported.candidates);
    const helper = base.entries.find(item => item.name === 'A.helper')!;
    expect(helper.typeKind).toBe('source-header');
    expect(helper.elaboration?.fullType).toContain('A.Predicate');
    expect(helper.dependencies.coverage).toBe('recorded');
    const consumers = getKnowledgeConsumers(base, helper.id, { maxBytes: 16000 });
    const consumer = base.entries.find(item => item.name === 'A.same')!;
    expect(consumers.consumers).toContainEqual(expect.objectContaining({ id: consumer.id, uses: ['proof-use'],
      read: expect.objectContaining({ metadata: expect.objectContaining({ id: consumer.id }),
        source: expect.objectContaining({ id: consumer.id }) }) }));
    expect(consumers.referenceSemantics).toBe('local-transitive-closure');
    expect(Buffer.byteLength(JSON.stringify(consumers)) + 1).toBeLessThanOrEqual(16000);
  }, 30000);
});
