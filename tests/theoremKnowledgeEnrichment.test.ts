import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { canonicalMathJson, mathDigest } from '../src/math/mathRuntimeIo';
import { leanKnowledgeCollectorIdentity, leanKnowledgeQuery,
  type LeanKnowledgeEnrichment } from '../src/math/leanKnowledgeEnrichment';
import { mathLocalModuleBuildOrder } from '../src/math/mathConstructionSources';
import { importAcceptedKnowledge } from '../src/solver/theoremKnowledgeAccepted';
import { buildTheoremKnowledge, knowledgeDeclaration, type KnowledgeCandidate } from '../src/solver/theoremKnowledge';
import { applyKnowledgeEnrichment, enrichAcceptedKnowledge, readKnowledgeEnrichment, validateKnowledgeEnrichment,
  writeKnowledgeEnrichment, type KnowledgeEnrichment } from '../src/solver/theoremKnowledgeEnrichment';

const host = vi.hoisted(() => ({ collect: vi.fn() }));
vi.mock('../src/math/leanKnowledgeEnrichment', async importOriginal => ({
  ...await importOriginal<typeof import('../src/math/leanKnowledgeEnrichment')>(), collectLeanKnowledgeEnrichment: host.collect,
}));
const legacyCollector = 'complete-proof-knowledge-collector-v1', boundedCollector = 'complete-proof-knowledge-collector-v2',
  currentCollector = 'complete-proof-knowledge-collector-v3';

const configurations = ['lean-toolchain', 'lakefile.toml', 'lakefile.lean', 'lake-manifest.json', '.lake/package-overrides.json'];
const source = 'import Mathlib\nimport Dependencies\nnamespace Archive\nsection\nvariable (P : Prop)\n' +
  'def contextValue : Nat := 0\nlemma retained (h : P) : P := by exact h\n' +
  'lemma later : True := by trivial\nend\nend Archive\n';
const files: Record<string, string> = { 'Submission.lean': source,
  'Dependencies.lean': 'namespace Dependencies\ndef useful : Nat := 0\nend Dependencies\n',
  'lean-toolchain': 'leanprover/lean4:v4.33.0\n', 'lakefile.toml': 'name = "enrichment-fixture"\n',
  'README.md': 'Historical accepted sources.\n', 'verification.json': '{"historical":true}\n' };

function reseal(value: KnowledgeEnrichment): KnowledgeEnrichment {
  const { digest: _digest, ...payload } = value;
  return { ...payload, digest: mathDigest(canonicalMathJson(payload)) };
}

describe('explicit accepted knowledge enrichment sidecars', () => {
  let directory: string, project: string, manifestFile: string;
  const record = () => ({ problem_id: 'example', directory: 'example', status: 'official_accepted',
    original_source_commit: 'a'.repeat(40), result_url: 'https://example.org/result/1',
    source_sha256: Object.fromEntries(Object.entries(files).map(([file, text]) => [file, mathDigest(text)])) });
  const importRaw = () => importAcceptedKnowledge(manifestFile).candidates;
  const apply = (sidecar: unknown, candidates: KnowledgeCandidate[] = importRaw()) =>
    applyKnowledgeEnrichment(candidates, sidecar, { manifestFile });
  const collect = (input: { projectRoot: string; roots: { id: string; name: string; file: string }[]; queryIndices?: readonly number[] },
    version: typeof legacyCollector | typeof boundedCollector | typeof currentCollector = currentCollector): LeanKnowledgeEnrichment => {
    const configuration = configurations.map(file => {
      const absolute = path.join(input.projectRoot, file), bytes = fs.existsSync(absolute) ? fs.readFileSync(absolute) : undefined;
      return { file, digest: bytes ? mathDigest(bytes) : null, bytes: bytes?.length ?? 0 };
    });
    const sources = Object.entries(files).filter(([file]) => file.endsWith('.lean') && file !== 'lakefile.lean')
      .map(([file]) => { const bytes = fs.readFileSync(path.join(input.projectRoot, file)); return { file, digest: mathDigest(bytes), bytes: bytes.length }; })
      .sort((a, b) => a.file < b.file ? -1 : a.file > b.file ? 1 : 0);
    const roots = input.roots.map((root, index) => {
      const artifact = (kind: 'query' | 'full-type' | 'statement-context' | 'diagnostics', text: string) => {
        const file = `.lake/knowledge-enrichment/fixture/${root.id}.${kind}.json`;
        const absolute = path.join(input.projectRoot, file);
        fs.mkdirSync(path.dirname(absolute), { recursive: true }); fs.writeFileSync(absolute, text);
        return { kind, path: file, digest: mathDigest(text), bytes: Buffer.byteLength(text) };
      };
      const fullType = root.name.endsWith('.retained') ? '∀ (P : Prop), P → P' : 'True';
      const modules = mathLocalModuleBuildOrder(input.projectRoot, root.file);
      const queryDetails = leanKnowledgeQuery(root, modules, input.queryIndices?.[index] ?? index, version);
      const query = artifact('query', queryDetails.source);
      const sourceDigest = mathDigest(JSON.stringify([configuration.map(item => item.digest ?? ''),
        [...modules.map(module => [module.file, mathDigest(fs.readFileSync(path.join(input.projectRoot, module.file)))]), [queryDetails.queryFile, query.digest]]]));
      const statementContext = { type: fullType, constants: [{ name: 'Dependencies.useful', module: 'Dependencies', type: 'Nat', definition: '0' }], omitted: [] };
      const references = { statement: [{ file: 'Dependencies.lean', name: 'Dependencies.useful' }], proof: [] };
      const referencePairs = [references.statement.map(ref => [ref.name, ref.file]), []];
      const report = version === legacyCollector ? referencePairs : { schema: 'theorem-os.lean-references.v2', theoremName: root.name,
        moduleDigest: mathDigest(JSON.stringify(modules.map(module => [module.module, module.file]))),
        limits: { maxBytes: 256000, maxReferences: 4096, fuel: 2000000 }, complete: true, references: referencePairs };
      return { ...root, status: 'collected' as const,
        sourceDigest: mathDigest(fs.readFileSync(path.join(input.projectRoot, root.file))),
        declarationDigest: mathDigest(knowledgeDeclaration(fs.readFileSync(path.join(input.projectRoot, root.file), 'utf8'), root.name)),
        fullType, universes: [], omissions: [], queryDigest: query.digest,
        statementContext, references,
        artifacts: [query, artifact('full-type', JSON.stringify({ name: root.name, fullType, universes: [], typeComplete: true })),
          artifact('statement-context', JSON.stringify([{ id: root.id, context: statementContext }])),
          artifact('diagnostics', JSON.stringify({ stdout: `${queryDetails.referenceMarker}${JSON.stringify(report)}`,
            exitCode: 0, timedOut: false, sourceDigest, environmentDigest: mathDigest('fixture environment') }))],
      };
    });
    return { schema: 'theorem-os.lean-knowledge-enrichment.v1', authority: 'advisory-lean-process', proofAcceptance: 'not-assessed',
      identity: { sources, configuration, sourceDigest: mathDigest(canonicalMathJson({ sources, configuration })),
        toolchain: files['lean-toolchain']!.trim(), toolIdentity: 'selected-fixture-tools',
        tools: ['lean', 'lake'].map(command => ({ command: command as 'lean' | 'lake', file: `/fixture/bin/${command}`, digest: mathDigest(command) })),
        environmentDigest: mathDigest('fixture environment'), sealedEnvironmentIdentity: 'fixture sealed image identity',
        collector: leanKnowledgeCollectorIdentity(version) }, roots };
  };
  const pruneArtifacts = (sidecar: KnowledgeEnrichment) => {
    const referenced = new Set(sidecar.records.flatMap(record => record.collection.roots.flatMap(root => root.artifacts.map(item => item.path))));
    sidecar.artifacts = sidecar.artifacts.filter(item => referenced.has(item.path));
    return reseal(sidecar);
  };
  const rootOutcome = (sidecar: KnowledgeEnrichment, index: number, status: 'failed' | 'unavailable' | 'missing') => {
    const roots = sidecar.records[0]!.collection.roots, root = roots[index]!;
    if (status === 'missing') roots.splice(index, 1);
    else roots[index] = { id: root.id, name: root.name, file: root.file, status,
      sourceDigest: root.sourceDigest, declarationDigest: root.declarationDigest, artifacts: [], omissions: [], reason: 'fixture incomplete' };
    return pruneArtifacts(sidecar);
  };
  const replaceArtifact = (sidecar: KnowledgeEnrichment, root: KnowledgeEnrichment['records'][number]['collection']['roots'][number],
    kind: 'full-type' | 'diagnostics' | 'statement-context', text: string) => {
    const artifact = root.artifacts.find(item => item.kind === kind)!, embedded = sidecar.artifacts.find(item => item.path === artifact.path)!;
    const bytes = Buffer.from(text);
    artifact.bytes = embedded.bytes = bytes.length; artifact.digest = embedded.digest = mathDigest(bytes);
    embedded.contentsBase64 = bytes.toString('base64');
  };
  /** Re-embeds the root's diagnostics report after `edit` changes it. */
  const editDiagnostics = (sidecar: KnowledgeEnrichment, root: Parameters<typeof replaceArtifact>[1], edit: (report: Record<string, any>) => void) => {
    const artifact = root.artifacts.find(item => item.kind === 'diagnostics')!;
    const report = JSON.parse(Buffer.from(sidecar.artifacts.find(item => item.path === artifact.path)!.contentsBase64, 'base64').toString('utf8'));
    edit(report); replaceArtifact(sidecar, root, 'diagnostics', JSON.stringify(report));
  };
  const editReferenceReport = (sidecar: KnowledgeEnrichment, edit: (report: Record<string, any>) => void, index = 0) =>
    editDiagnostics(sidecar, sidecar.records[0]!.collection.roots[index]!, diagnostics => {
      const marker = `KNOWLEDGE_REFERENCES_${index}:`, report = JSON.parse(diagnostics.stdout.slice(marker.length));
      edit(report); diagnostics.stdout = marker + JSON.stringify(report);
    });
  const omitOversizedContext = (sidecar: KnowledgeEnrichment) => {
    const root = sidecar.records[0]!.collection.roots[0]!;
    const rows = [{ id: root.id, context: { unavailable: 'statement-type-export-bound', bytes: 31000, limit: 24000 } }];
    delete root.statementContext;
    root.omissions = ['statement-context:statement-type-export-bound'];
    replaceArtifact(sidecar, root, 'statement-context', JSON.stringify(rows));
    return { root, rows };
  };

  beforeEach(() => {
    directory = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'knowledge-enrichment-test-')));
    project = path.join(directory, 'example'); fs.mkdirSync(project);
    for (const [file, text] of Object.entries(files)) {
      const absolute = path.join(project, file); fs.mkdirSync(path.dirname(absolute), { recursive: true }); fs.writeFileSync(absolute, text);
    }
    manifestFile = path.join(directory, 'accepted.json'); fs.writeFileSync(manifestFile, JSON.stringify([record()]));
    host.collect.mockReset().mockImplementation(async input => collect(input));
  });
  afterEach(() => { vi.restoreAllMocks(); fs.rmSync(directory, { recursive: true, force: true }); });

  it('keeps default import and knowledge builds free of enrichment or Lean calls', () => {
    const candidates = importRaw(), base = buildTheoremKnowledge(candidates);
    expect(host.collect).not.toHaveBeenCalled();
    expect(candidates.every(candidate => candidate.elaboration === undefined && candidate.dependencies.coverage === 'unavailable')).toBe(true);
    expect(base.evidence).toBe('recorded-not-replayed');
    expect(base.requiresFreshCheck).toBe(true);
  });

  it('binds raw source bytes when archived UTF-8 sources retain an initial BOM', async () => {
    const file = path.join(project, 'Submission.lean'); fs.writeFileSync(file, `\uFEFF${source}`);
    const item = record(); item.source_sha256['Submission.lean'] = mathDigest(fs.readFileSync(file));
    fs.writeFileSync(manifestFile, JSON.stringify([item]));
    const sidecar = await enrichAcceptedKnowledge(manifestFile, 'example'), retained = apply(sidecar)[0]!;
    expect(retained.elaboration?.sourceDigest).toBe(item.source_sha256['Submission.lean']);
    expect(retained.elaboration?.fullType).toBe('∀ (P : Prop), P → P');
  });

  it('binds elaborated types to immutable archive sources and preserves historical acceptance boundaries', async () => {
    const candidates = importRaw(), sidecar = await enrichAcceptedKnowledge(manifestFile, 'example');
    const original = canonicalMathJson(candidates);
    expect(host.collect).toHaveBeenCalledOnce();
    expect(host.collect.mock.calls[0]![0].timeoutMs).toBe(Infinity);
    const result = apply(sidecar, candidates), retained = result.find(candidate => candidate.name === 'Archive.retained')!;
    expect(retained.type).toBe(candidates[0]!.type);
    expect(retained.typeKind).toBe('source-header');
    expect(retained.elaboration).toMatchObject({ schema: 'theorem-os.knowledge-elaboration.v1', evidence: 'recorded-not-replayed',
      fullType: '∀ (P : Prop), P → P', universes: [], enrichmentDigest: sidecar.digest,
      sourceDigest: mathDigest(source), declarationDigest: mathDigest(knowledgeDeclaration(source, 'Archive.retained')),
      environmentDigest: mathDigest('fixture environment'), toolIdentity: 'selected-fixture-tools', sealedEnvironmentIdentity: 'fixture sealed image identity' });
    expect(retained.dependencies).toMatchObject({ coverage: 'recorded', statement: [{ file: 'Dependencies.lean', name: 'Dependencies.useful' }], proof: [] });
    expect(retained.provenance).toEqual({ ...candidates[0]!.provenance, environmentDigest: mathDigest('fixture environment') });
    expect(candidates[0]!.elaboration).toBeUndefined();
    expect(canonicalMathJson(candidates)).toBe(original);
    expect(result.every((candidate, index) => candidate.files === candidates[index]!.files)).toBe(true);
    const base = buildTheoremKnowledge(result);
    expect(base.evidence).toBe('recorded-not-replayed'); expect(base.requiresFreshCheck).toBe(true);
    expect(base.entries.every(entry => entry.elaboration?.fullType)).toBe(true);
  });

  it('stores complete query artifacts and survives deletion of generated project artifacts', async () => {
    const sidecar = await enrichAcceptedKnowledge(manifestFile, 'example');
    const output = path.join(directory, 'enrichment.json'), written = writeKnowledgeEnrichment(output, sidecar);
    expect(fs.statSync(output).mode & 0o777).toBe(0o400);
    expect(() => writeKnowledgeEnrichment(output, sidecar)).toThrow();
    fs.rmSync(path.join(project, '.lake/knowledge-enrichment'), { recursive: true });
    const restored = readKnowledgeEnrichment(output, written.sha256);
    expect(restored).toEqual(sidecar);
    expect(apply(restored).every(candidate => candidate.elaboration)).toBe(true);
    expect(host.collect).toHaveBeenCalledOnce();
    expect(() => readKnowledgeEnrichment(output, '0'.repeat(64))).toThrow('math_knowledge_enrichment_changed');
  });

  it('reads mixed legacy and current records from retained artifacts without invoking either collector again', async () => {
    const otherProject = path.join(directory, 'another'); fs.mkdirSync(otherProject);
    for (const [file, text] of Object.entries(files)) {
      const absolute = path.join(otherProject, file); fs.mkdirSync(path.dirname(absolute), { recursive: true }); fs.writeFileSync(absolute, text);
    }
    fs.writeFileSync(manifestFile, JSON.stringify([record(), { ...record(), problem_id: 'another', directory: 'another' }]));
    host.collect.mockImplementationOnce(async input => collect(input, legacyCollector));
    const legacy = await enrichAcceptedKnowledge(manifestFile, 'example'), current = await enrichAcceptedKnowledge(manifestFile, 'another');
    const combined = reseal({ ...legacy, records: [...legacy.records, ...current.records], artifacts: [...legacy.artifacts, ...current.artifacts] });
    const output = path.join(directory, 'mixed.json'), written = writeKnowledgeEnrichment(output, combined);
    fs.rmSync(path.join(project, '.lake/knowledge-enrichment'), { recursive: true });
    fs.rmSync(path.join(otherProject, '.lake/knowledge-enrichment'), { recursive: true });
    host.collect.mockImplementation(() => { throw new Error('readback must not run Lean'); });
    const restored = readKnowledgeEnrichment(output, written.sha256), candidates = apply(restored);
    expect(restored.records.map(record => record.collection.identity.collector.version)).toEqual([legacyCollector, currentCollector]);
    expect(candidates).toHaveLength(4);
    expect(candidates.every(candidate => candidate.elaboration?.collectorDigest ===
      leanKnowledgeCollectorIdentity(candidate.provenance.problemId === 'example' ? legacyCollector : currentCollector).digest)).toBe(true);
    expect(candidates.every(candidate => candidate.dependencies.coverage === 'recorded')).toBe(true);
    expect(host.collect).toHaveBeenCalledTimes(2);
  });

  it.each(['failed', 'unavailable', 'missing'] as const)
  ('retries only a %s root with its original full-record query index', async status => {
    host.collect.mockImplementationOnce(async input => collect(input, boundedCollector));
    const original = await enrichAcceptedKnowledge(manifestFile, 'example'), previous = rootOutcome(original, 1, status);
    const previousFile = path.join(directory, 'previous.json'), written = writeKnowledgeEnrichment(previousFile, previous);
    const previousBytes = fs.readFileSync(previousFile), controller = new AbortController();
    host.collect.mockClear();
    const retry = await enrichAcceptedKnowledge(manifestFile, 'example', { retryFile: previousFile,
      timeoutMs: 5000, signal: controller.signal });
    const target = previous.records[0]!.roots[1]!, request = host.collect.mock.calls[0]![0];
    expect(request).toMatchObject({ roots: [{ id: target.id, name: target.name, file: target.file }], queryIndices: [1],
      timeoutMs: 5000, signal: controller.signal });
    expect(host.collect).toHaveBeenCalledOnce();
    expect(retry.records[0]!.roots).toEqual(previous.records[0]!.roots);
    expect(retry.records[0]!.collection.identity.collector.version).toBe(currentCollector);
    expect(retry.records[0]!.collection.roots.map(root => root.id)).toEqual([target.id]);
    const queryArtifact = retry.records[0]!.collection.roots[0]!.artifacts.find(item => item.kind === 'query')!;
    const query = Buffer.from(retry.artifacts.find(item => item.path === queryArtifact.path)!.contentsBase64, 'base64').toString('utf8');
    expect(query).toContain('KNOWLEDGE_REFERENCES_1:');
    expect(query).toContain('KnowledgeEnrichment1-context.json');
    const candidates = apply(retry);
    expect(candidates[0]!.elaboration).toBeUndefined();
    expect(candidates[1]!.elaboration?.enrichmentDigest).toBe(retry.digest);
    expect(writeKnowledgeEnrichment(path.join(directory, 'retry.json'), retry)).toMatchObject({ roots: 2,
      reportedRoots: 1, missing: 1, collected: 1, failed: 0, unavailable: 1 });
    expect(fs.readFileSync(previousFile)).toEqual(previousBytes);
    expect(readKnowledgeEnrichment(previousFile, written.sha256).digest).toBe(previous.digest);
  });

  it('retries every failed or missing root while preserving full-record order and partial results', async () => {
    const original = await enrichAcceptedKnowledge(manifestFile, 'example');
    const previous = rootOutcome(rootOutcome(original, 1, 'missing'), 0, 'unavailable');
    const previousFile = path.join(directory, 'previous.json'); writeKnowledgeEnrichment(previousFile, previous);
    host.collect.mockClear().mockImplementationOnce(async input => {
      const result = collect(input), root = result.roots[1]!;
      result.roots[1] = { id: root.id, name: root.name, file: root.file, status: 'failed', artifacts: [],
        omissions: [], reason: 'still unavailable' };
      return result;
    });
    const retry = await enrichAcceptedKnowledge(manifestFile, 'example', { retryFile: previousFile });
    expect(host.collect.mock.calls[0]![0].queryIndices).toEqual([0, 1]);
    expect(retry.records[0]!.roots).toEqual(previous.records[0]!.roots);
    expect(retry.records[0]!.collection.roots.map(root => root.status)).toEqual(['collected', 'failed']);
    expect(writeKnowledgeEnrichment(path.join(directory, 'retry.json'), retry)).toMatchObject({ roots: 2,
      reportedRoots: 2, missing: 0, collected: 1, failed: 1, unavailable: 0 });
  });

  it('retains missing-root accounting when a retry collector reports no roots', async () => {
    const previous = rootOutcome(await enrichAcceptedKnowledge(manifestFile, 'example'), 1, 'failed');
    const previousFile = path.join(directory, 'previous.json'); writeKnowledgeEnrichment(previousFile, previous);
    host.collect.mockClear().mockImplementationOnce(async input => ({ ...collect(input), roots: [] }));
    const retry = await enrichAcceptedKnowledge(manifestFile, 'example', { retryFile: previousFile });
    expect(retry.records[0]!.roots).toHaveLength(2);
    expect(writeKnowledgeEnrichment(path.join(directory, 'retry.json'), retry)).toMatchObject({ roots: 2,
      reportedRoots: 0, missing: 2, collected: 0, unavailable: 2 });
  });

  it.each(['complete', 'unavailable-reference-closure'] as const)
  ('does not retry collected types with %s evidence', async coverage => {
    const previous = await enrichAcceptedKnowledge(manifestFile, 'example'), previousFile = path.join(directory, 'previous.json');
    if (coverage === 'unavailable-reference-closure') {
      editReferenceReport(previous, report => {
        report.complete = false; delete report.references; report.reason = 'proof-unavailable'; report.phase = 'proof';
        report.observed = 0; report.limit = 0;
      });
      const root = previous.records[0]!.collection.roots[0]!;
      delete root.references;
      root.omissions = ['proof-and-statement-references-unavailable', 'proof-and-statement-references:proof-unavailable'];
    }
    writeKnowledgeEnrichment(previousFile, reseal(previous)); host.collect.mockClear();
    await expect(enrichAcceptedKnowledge(manifestFile, 'example', { retryFile: previousFile }))
      .rejects.toThrow('math_knowledge_enrichment_no_retry_roots');
    expect(host.collect).not.toHaveBeenCalled();
  });

  it.each(['manifest', 'problem', 'configuration', 'root-set', 'invalid-digest'] as const)
  ('rejects retry %s identity changes before collection', async changed => {
    const previous = await enrichAcceptedKnowledge(manifestFile, 'example'), previousFile = path.join(directory, 'previous.json');
    if (changed === 'problem') previous.records[0]!.problemId = 'another';
    else if (changed === 'root-set') {
      previous.records[0]!.roots.pop(); previous.records[0]!.collection.roots.pop();
    }
    const checked = pruneArtifacts(previous);
    if (changed === 'invalid-digest') {
      checked.digest = mathDigest('unrelated payload'); fs.writeFileSync(previousFile, JSON.stringify(checked));
    } else writeKnowledgeEnrichment(previousFile, checked);
    if (changed === 'manifest') fs.appendFileSync(manifestFile, '\n');
    else if (changed === 'configuration') {
      fs.mkdirSync(path.join(project, '.lake'), { recursive: true }); fs.writeFileSync(path.join(project, '.lake/package-overrides.json'), '{}');
    }
    host.collect.mockClear();
    await expect(enrichAcceptedKnowledge(manifestFile, 'example', { retryFile: previousFile })).rejects.toThrow();
    expect(host.collect).not.toHaveBeenCalled();
  });

  it('rejects a retry collector that returns an original successful root outside the requested subset', async () => {
    const original = await enrichAcceptedKnowledge(manifestFile, 'example'), successful = original.records[0]!.collection.roots[0]!;
    const previous = rootOutcome(original, 1, 'failed'), previousFile = path.join(directory, 'previous.json');
    writeKnowledgeEnrichment(previousFile, previous);
    host.collect.mockClear().mockImplementationOnce(async input => {
      const result = collect(input); result.roots.push(successful as LeanKnowledgeEnrichment['roots'][number]); return result;
    });
    await expect(enrichAcceptedKnowledge(manifestFile, 'example', { retryFile: previousFile }))
      .rejects.toThrow('math_knowledge_enrichment_mismatch');
    expect(host.collect).toHaveBeenCalledOnce();
  });

  it.each(['unknown-version', 'source-and-digest', 'digest', 'other-known-version'] as const)
  ('rejects a resealed collector identity with %s', async changed => {
    const sidecar = await enrichAcceptedKnowledge(manifestFile, 'example'), identity = sidecar.records[0]!.collection.identity;
    if (changed === 'unknown-version') Object.assign(identity.collector, { version: 'complete-proof-knowledge-collector-v4' });
    else if (changed === 'source-and-digest') {
      identity.collector.source += '\n-- modified generator'; identity.collector.digest = mathDigest(identity.collector.source);
    } else if (changed === 'digest') identity.collector.digest = mathDigest('unrelated generator');
    else identity.collector = leanKnowledgeCollectorIdentity(legacyCollector);
    expect(() => validateKnowledgeEnrichment(reseal(sidecar))).toThrow(changed === 'unknown-version'
      ? 'math_knowledge_enrichment_schema_invalid' : changed === 'other-known-version'
        ? 'math_knowledge_enrichment_artifact_changed' : 'math_knowledge_enrichment_collector_changed');
  });

  it.each([[legacyCollector, 24000], [boundedCollector, 256000], [currentCollector, 2_000_000]] as const)
  ('enforces the %s full-type byte limit independently of the wider current schema', async (version, limit) => {
    host.collect.mockImplementationOnce(async input => collect(input, version));
    const sidecar = await enrichAcceptedKnowledge(manifestFile, 'example'), root = sidecar.records[0]!.collection.roots[0]!;
    root.fullType = 'True'.padEnd(limit - 2) + '\u00e9';
    replaceArtifact(sidecar, root, 'full-type', JSON.stringify({ name: root.name, fullType: root.fullType,
      universes: root.universes, typeComplete: true }));
    expect(Buffer.byteLength(apply(reseal(sidecar))[0]!.elaboration!.fullType)).toBe(limit);
    root.fullType += ' ';
    replaceArtifact(sidecar, root, 'full-type', JSON.stringify({ name: root.name, fullType: root.fullType,
      universes: root.universes, typeComplete: true }));
    expect(() => validateKnowledgeEnrichment(reseal(sidecar))).toThrow(version === currentCollector
      ? 'math_knowledge_enrichment_schema_invalid' : 'math_knowledge_enrichment_type_export_invalid');
  });

  it('keeps a full type and reference closure when v2 explicitly omits an oversized readable context', async () => {
    const sidecar = await enrichAcceptedKnowledge(manifestFile, 'example'), { root } = omitOversizedContext(sidecar);
    root.fullType = 'True'.padEnd(50000);
    replaceArtifact(sidecar, root, 'full-type', JSON.stringify({ name: root.name, fullType: root.fullType,
      universes: root.universes, typeComplete: true }));
    const output = path.join(directory, 'context-omission.json'), written = writeKnowledgeEnrichment(output, reseal(sidecar));
    fs.rmSync(path.join(project, '.lake/knowledge-enrichment'), { recursive: true });
    host.collect.mockImplementation(() => { throw new Error('readback must not run Lean'); });
    const retained = apply(readKnowledgeEnrichment(output, written.sha256))[0]!;
    expect(retained.elaboration?.fullType).toBe(root.fullType);
    expect(retained.elaboration?.statementContext).toBeUndefined();
    expect(retained.elaboration?.omissions).toEqual(['statement-context:statement-type-export-bound']);
    expect(retained.dependencies.coverage).toBe('recorded');
    expect(retained.dependencies.statement).toEqual(root.references!.statement);
    expect(host.collect).toHaveBeenCalledOnce();
  });

  it('binds context and reference omission reasons independently and in collector order', async () => {
    const sidecar = await enrichAcceptedKnowledge(manifestFile, 'example'), { root } = omitOversizedContext(sidecar);
    editReferenceReport(sidecar, report => {
      report.complete = false; delete report.references; report.reason = 'reference-count-limit'; report.phase = 'proof';
      report.observed = 4097; report.limit = 4096;
    });
    delete root.references;
    root.omissions.push('proof-and-statement-references-unavailable', 'proof-and-statement-references:reference-count-limit');
    const retained = apply(reseal(sidecar))[0]!;
    expect(retained.elaboration?.fullType).toBe(root.fullType);
    expect(retained.elaboration?.omissions).toEqual(root.omissions);
    expect(retained.dependencies.coverage).toBe('unavailable');
    root.omissions.reverse();
    expect(() => validateKnowledgeEnrichment(reseal(sidecar))).toThrow('math_knowledge_enrichment_artifact_changed');
  });

  it.each(['wrong-root', 'duplicate-root', 'bytes', 'limit', 'reason', 'extra-field', 'context-present', 'omission-missing'] as const)
  ('rejects resealed oversized context evidence with %s', async changed => {
    const sidecar = await enrichAcceptedKnowledge(manifestFile, 'example'), { root, rows } = omitOversizedContext(sidecar);
    if (changed === 'wrong-root') rows[0]!.id = mathDigest('other root');
    else if (changed === 'duplicate-root') rows.push(structuredClone(rows[0]!));
    else if (changed === 'bytes') rows[0]!.context.bytes = 24000;
    else if (changed === 'limit') rows[0]!.context.limit = 23999;
    else if (changed === 'reason') rows[0]!.context.unavailable = 'other-error';
    else if (changed === 'extra-field') Object.assign(rows[0]!.context, { trusted: true });
    else if (changed === 'context-present') root.statementContext = { type: 'True', constants: [], omitted: [] };
    else root.omissions = [];
    replaceArtifact(sidecar, root, 'statement-context', JSON.stringify(rows));
    expect(() => validateKnowledgeEnrichment(reseal(sidecar))).toThrow('math_knowledge_enrichment_artifact_changed');
  });

  it('does not interpret the new context omission protocol as valid v1 evidence', async () => {
    host.collect.mockImplementationOnce(async input => collect(input, legacyCollector));
    const sidecar = await enrichAcceptedKnowledge(manifestFile, 'example');
    omitOversizedContext(sidecar);
    expect(() => validateKnowledgeEnrichment(reseal(sidecar))).toThrow('math_knowledge_enrichment_artifact_changed');
  });

  it.each([legacyCollector, boundedCollector, currentCollector])('retains normal readable context omissions for %s', async version => {
    host.collect.mockImplementationOnce(async input => collect(input, version));
    const sidecar = await enrichAcceptedKnowledge(manifestFile, 'example'), root = sidecar.records[0]!.collection.roots[0]!;
    root.statementContext!.omitted = ['Dependencies.useful:definition-budget'];
    root.omissions = [...root.statementContext!.omitted];
    replaceArtifact(sidecar, root, 'statement-context', JSON.stringify([{ id: root.id, context: root.statementContext }]));
    expect(apply(reseal(sidecar))[0]!.elaboration?.omissions).toEqual(root.omissions);
  });

  it('retains a complete v2 reference closure above legacy byte and count limits', async () => {
    const sidecar = await enrichAcceptedKnowledge(manifestFile, 'example'), root = sidecar.records[0]!.collection.roots[0]!;
    root.references!.statement = Array.from({ length: 300 }, (_, index) => ({ name: `Dependencies.saved_${String(index).padStart(3, '0')}`,
      file: 'Dependencies.lean' }));
    editReferenceReport(sidecar, report => { report.references[0] = root.references!.statement.map(ref => [ref.name, ref.file]); });
    const retained = apply(reseal(sidecar))[0]!;
    expect(retained.dependencies.coverage).toBe('recorded');
    expect(retained.dependencies.statement).toEqual(root.references!.statement);
  });

  it.each(['theorem', 'modules', 'limits'] as const)('rejects resealed v2 reference output from other %s inputs', async changed => {
    const sidecar = await enrichAcceptedKnowledge(manifestFile, 'example');
    editReferenceReport(sidecar, report => {
      if (changed === 'theorem') report.theoremName = 'Archive.other';
      else if (changed === 'modules') report.moduleDigest = mathDigest('other modules');
      else report.limits.maxReferences--;
    });
    expect(() => validateKnowledgeEnrichment(reseal(sidecar))).toThrow('math_knowledge_enrichment_artifact_changed');
  });

  it('preserves a specific v2 reference omission reason without claiming an empty dependency set', async () => {
    const sidecar = await enrichAcceptedKnowledge(manifestFile, 'example'), record = sidecar.records[0]!, root = record.collection.roots[0]!;
    editReferenceReport(sidecar, report => {
      report.complete = false; delete report.references; report.reason = 'reference-count-limit'; report.phase = 'statement';
      report.observed = 4097; report.limit = 4096;
    });
    delete root.references;
    root.omissions = ['proof-and-statement-references-unavailable', 'proof-and-statement-references:reference-count-limit'];
    const retained = apply(reseal(sidecar))[0]!;
    expect(retained.elaboration?.omissions).toEqual(root.omissions);
    expect(retained.dependencies.coverage).toBe('unavailable');
    root.omissions.pop();
    expect(() => validateKnowledgeEnrichment(reseal(sidecar))).toThrow('math_knowledge_enrichment_artifact_changed');
  });

  it('integrates only an explicit matching sidecar when importing accepted knowledge', async () => {
    const sidecar = await enrichAcceptedKnowledge(manifestFile, 'example'), enrichmentFile = path.join(directory, 'enrichment.json');
    writeKnowledgeEnrichment(enrichmentFile, sidecar);
    const result = importAcceptedKnowledge(manifestFile, { enrichmentFile });
    expect(result.candidates.every(candidate => candidate.elaboration)).toBe(true);
    expect(importRaw().every(candidate => !candidate.elaboration)).toBe(true);
    expect(host.collect).toHaveBeenCalledOnce();
  });

  it.each(['failed', 'unavailable', 'missing'] as const)('preserves unknown reference coverage for a %s root', async status => {
    const sidecar = await enrichAcceptedKnowledge(manifestFile, 'example'), record = sidecar.records[0]!, root = record.collection.roots[0]!;
    if (status === 'missing') record.collection.roots.shift();
    else record.collection.roots[0] = { id: root.id, name: root.name, file: root.file, status,
      sourceDigest: root.sourceDigest, declarationDigest: root.declarationDigest, omissions: ['fixture unavailable evidence'], artifacts: [], reason: 'No collected closure.' };
    const result = apply(pruneArtifacts(sidecar));
    expect(result[0]!.elaboration).toBeUndefined();
    expect(result[0]!.dependencies).toEqual({ statement: [], proof: [], tasks: [], coverage: 'unavailable' });
    expect(result[1]!.elaboration).toBeDefined();
  });

  it.each([legacyCollector, boundedCollector, currentCollector])('retains %s full type information without treating missing references as an empty dependency set', async version => {
    host.collect.mockImplementationOnce(async input => collect(input, version));
    const sidecar = await enrichAcceptedKnowledge(manifestFile, 'example');
    const root = sidecar.records[0]!.collection.roots[0]!;
    delete root.references; root.omissions = ['proof-and-statement-references-unavailable',
      ...(version !== legacyCollector ? ['proof-and-statement-references:missing-report'] : [])];
    editDiagnostics(sidecar, root, report => { report.stdout = 'reference export unavailable'; });
    const retained = apply(reseal(sidecar))[0]!;
    expect(retained.elaboration).toBeDefined(); expect(retained.dependencies.coverage).toBe('unavailable');
  });

  it.each(['tools', 'environment', 'query', 'type-artifact', 'diagnostic-source', 'diagnostic-environment'] as const)
  ('does not attach partial collected output missing %s evidence', async missing => {
    const sidecar = await enrichAcceptedKnowledge(manifestFile, 'example'), record = sidecar.records[0]!, root = record.collection.roots[0]!;
    if (missing === 'tools') { delete record.collection.identity.toolIdentity; record.collection.identity.tools = []; }
    else if (missing === 'environment') delete record.collection.identity.environmentDigest;
    else if (missing === 'query') { delete root.queryDigest; root.artifacts = root.artifacts.filter(item => item.kind !== 'query'); }
    else if (missing === 'type-artifact') root.artifacts = root.artifacts.filter(item => item.kind !== 'full-type');
    else editDiagnostics(sidecar, root, report => { delete report[missing === 'diagnostic-source' ? 'sourceDigest' : 'environmentDigest']; });
    const retained = apply(pruneArtifacts(sidecar))[0]!;
    expect(retained.elaboration).toBeUndefined(); expect(retained.dependencies.coverage).toBe('unavailable');
  });

  it('checks the frozen whole-output digest before accepting edited fields', async () => {
    const sidecar = await enrichAcceptedKnowledge(manifestFile, 'example');
    sidecar.records[0]!.collection.roots[0]!.fullType = 'False';
    expect(() => validateKnowledgeEnrichment(sidecar)).toThrow('math_knowledge_enrichment_changed');
  });

  it.each(['manifest', 'record', 'source-commit', 'files', 'configuration', 'root', 'collector', 'collection-sources', 'query', 'full-type', 'context', 'references'] as const)
  ('rejects semantically mismatched %s data even if its output digest is recomputed', async changed => {
    const sidecar = await enrichAcceptedKnowledge(manifestFile, 'example'), record = sidecar.records[0]!, root = record.collection.roots[0]!;
    if (changed === 'manifest') sidecar.manifest.digest = mathDigest('another manifest');
    else if (changed === 'record') record.recordDigest = mathDigest('another record');
    else if (changed === 'source-commit') record.sourceCommit = 'b'.repeat(40);
    else if (changed === 'files') record.files[0]!.digest = mathDigest('another source');
    else if (changed === 'configuration') record.configuration[0]!.digest = mathDigest('another toolchain');
    else if (changed === 'root') root.declarationDigest = mathDigest('another declaration');
    else if (changed === 'collector') record.collection.identity.collector.source += '-- changed\n';
    else if (changed === 'collection-sources') record.collection.identity.sources[0]!.bytes++;
    else if (changed === 'query') root.queryDigest = mathDigest('unrelated query');
    else if (changed === 'context') root.statementContext!.constants[0]!.type = 'False';
    else if (changed === 'references') root.references!.statement[0]!.name = 'Dependencies.notActuallyReferenced';
    else root.fullType = 'False';
    expect(() => apply(reseal(sidecar))).toThrow();
  });

  it('rejects query artifacts swapped between roots even when all local digests are recomputed', async () => {
    const sidecar = await enrichAcceptedKnowledge(manifestFile, 'example'), roots = sidecar.records[0]!.collection.roots;
    const left = roots[0]!, right = roots[1]!, leftIndex = left.artifacts.findIndex(item => item.kind === 'query'), rightIndex = right.artifacts.findIndex(item => item.kind === 'query');
    const original = left.artifacts[leftIndex]!;
    left.artifacts[leftIndex] = right.artifacts[rightIndex]!; right.artifacts[rightIndex] = original;
    left.queryDigest = left.artifacts[leftIndex]!.digest; right.queryDigest = right.artifacts[rightIndex]!.digest;
    expect(() => validateKnowledgeEnrichment(reseal(sidecar))).toThrow('math_knowledge_enrichment_artifact_changed');
  });

  it('rejects collected status if its retained diagnostic reports failure', async () => {
    const sidecar = await enrichAcceptedKnowledge(manifestFile, 'example'), root = sidecar.records[0]!.collection.roots[0]!;
    editDiagnostics(sidecar, root, report => { report.exitCode = 1; });
    expect(() => validateKnowledgeEnrichment(reseal(sidecar))).toThrow('math_knowledge_enrichment_artifact_changed');
  });

  it.each(['collection-environment', 'diagnostic-environment', 'diagnostic-source', 'execution-configuration'] as const)
  ('rejects resealed %s changes that disagree with the retained diagnostic inputs', async changed => {
    const sidecar = await enrichAcceptedKnowledge(manifestFile, 'example'), record = sidecar.records[0]!, root = record.collection.roots[0]!;
    if (changed === 'collection-environment') record.collection.identity.environmentDigest = mathDigest('another environment');
    else if (changed === 'execution-configuration') {
      record.collection.identity.executionConfiguration = structuredClone(record.collection.identity.configuration);
      record.collection.identity.executionConfiguration.find(item => item.file === '.lake/package-overrides.json')!.digest = mathDigest('another override');
      record.collection.identity.executionSourceDigest = mathDigest(canonicalMathJson({ sources: record.collection.identity.sources,
        configuration: record.collection.identity.executionConfiguration }));
    } else editDiagnostics(sidecar, root, report => {
      report[changed === 'diagnostic-environment' ? 'environmentDigest' : 'sourceDigest'] = mathDigest('unrelated input');
    });
    expect(() => validateKnowledgeEnrichment(reseal(sidecar))).toThrow('math_knowledge_enrichment_artifact_changed');
  });

  it.each(['bytes', 'digest', 'contents', 'base64', 'path'] as const)('rejects changed embedded artifact %s', async changed => {
    const sidecar = await enrichAcceptedKnowledge(manifestFile, 'example'), item = sidecar.artifacts[0]!;
    if (changed === 'bytes') item.bytes++;
    else if (changed === 'digest') item.digest = mathDigest('wrong artifact');
    else if (changed === 'contents') item.contentsBase64 = Buffer.from('changed text').toString('base64');
    else if (changed === 'base64') item.contentsBase64 += ' ';
    else item.path = '../escape';
    expect(() => validateKnowledgeEnrichment(reseal(sidecar))).toThrow();
  });

  it.each(['extra-top-level', 'extra-root-field', 'failed-with-references', 'duplicate-root', 'duplicate-artifact', 'unknown-reference'] as const)
  ('strictly rejects %s schemas or inconsistent evidence', async changed => {
    const sidecar = await enrichAcceptedKnowledge(manifestFile, 'example'), record = sidecar.records[0]!, root = record.collection.roots[0]!;
    if (changed === 'extra-top-level') Object.assign(sidecar, { trusted: true });
    else if (changed === 'extra-root-field') Object.assign(root, { officialAccepted: true });
    else if (changed === 'failed-with-references') root.status = 'failed';
    else if (changed === 'duplicate-root') record.collection.roots.push(structuredClone(root));
    else if (changed === 'duplicate-artifact') sidecar.artifacts.push(structuredClone(sidecar.artifacts[0]!));
    else root.references!.statement.push({ file: 'Unrecorded.lean', name: 'unrelated' });
    expect(() => validateKnowledgeEnrichment(reseal(sidecar))).toThrow();
  });

  it.each(['source', 'manifest', 'configuration', 'extra-source'] as const)
  ('refuses an explicit old sidecar after current %s changes', async changed => {
    const sidecar = await enrichAcceptedKnowledge(manifestFile, 'example');
    if (changed === 'source') fs.appendFileSync(path.join(project, 'Submission.lean'), '\n-- changed\n');
    else if (changed === 'manifest') fs.appendFileSync(manifestFile, '\n');
    else if (changed === 'configuration') {
      fs.mkdirSync(path.join(project, '.lake'), { recursive: true }); fs.writeFileSync(path.join(project, '.lake/package-overrides.json'), '{"changed":true}\n');
    } else fs.writeFileSync(path.join(project, 'Extra.lean'), 'lemma added : True := by trivial\n');
    expect(() => apply(sidecar)).toThrow();
  });

  it('refuses a sidecar if immutable archive inputs change while collection is awaiting', async () => {
    host.collect.mockImplementationOnce(async input => {
      const output = collect(input); fs.appendFileSync(manifestFile, '\n'); return output;
    });
    await expect(enrichAcceptedKnowledge(manifestFile, 'example')).rejects.toThrow('math_knowledge_enrichment_mismatch');
  });

  it('rejects collector artifact bytes changed before the explicit operation embeds them', async () => {
    host.collect.mockImplementationOnce(async input => {
      const output = collect(input), item = output.roots[0]!.artifacts[0]!;
      fs.appendFileSync(path.join(input.projectRoot, item.path), '-- changed\n'); return output;
    });
    await expect(enrichAcceptedKnowledge(manifestFile, 'example')).rejects.toThrow('math_knowledge_enrichment_artifact_changed');
  });

  it('rejects symlink sidecars and artifact paths without following them', async () => {
    const sidecar = await enrichAcceptedKnowledge(manifestFile, 'example'), output = path.join(directory, 'enrichment.json');
    writeKnowledgeEnrichment(output, sidecar); fs.symlinkSync('enrichment.json', path.join(directory, 'linked.json'));
    expect(() => readKnowledgeEnrichment(path.join(directory, 'linked.json'))).toThrow('math_path_invalid');
    host.collect.mockImplementationOnce(async input => {
      const output = collect(input), item = output.roots[0]!.artifacts[0]!, file = path.join(input.projectRoot, item.path);
      fs.renameSync(file, `${file}.saved`); fs.symlinkSync(`${path.basename(file)}.saved`, file); return output;
    });
    await expect(enrichAcceptedKnowledge(manifestFile, 'example')).rejects.toThrow('math_path_invalid');
  });

  it('preserves explicit limits and cancellation while defaulting to no deadline', async () => {
    const controller = new AbortController();
    await enrichAcceptedKnowledge(manifestFile, 'example', { timeoutMs: 5000, signal: controller.signal });
    expect(host.collect.mock.calls[0]![0]).toMatchObject({ timeoutMs: 5000, signal: controller.signal });
    controller.abort();
    await expect(enrichAcceptedKnowledge(manifestFile, 'example', { signal: controller.signal })).rejects.toMatchObject({ name: 'AbortError' });
    expect(host.collect).toHaveBeenCalledOnce();
  });

  it('reports an unknown explicit problem without invoking Lean', async () => {
    await expect(enrichAcceptedKnowledge(manifestFile, 'unknown')).rejects.toThrow('math_knowledge_enrichment_problem_not_found');
    expect(host.collect).not.toHaveBeenCalled();
  });
});
