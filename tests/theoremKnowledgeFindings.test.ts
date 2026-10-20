import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { execFileSync } from 'node:child_process';
import { afterEach, describe, expect, it } from 'vitest';
import { canonicalMathJson, mathDigest } from '../src/math/mathRuntimeIo';
import { writeSolverRunState, type SolverRunState } from '../src/solver/archive';
import { parseMathResponse, type DeliveryRecord } from '../src/solver/deliveries';
import { taskVersion, type CooperativeTask } from '../src/solver/tasks';
import { buildTheoremKnowledge, searchTheoremKnowledge, validateTheoremKnowledge, writeTheoremKnowledge } from '../src/solver/theoremKnowledge';
import { buildKnowledgeRouteFindings, getKnowledgeRouteFinding, getKnowledgeRouteFindingPage, searchKnowledgeRouteFindings,
  searchKnowledgeRouteFindingRequests, type KnowledgeRouteFindingCandidate, type KnowledgeRouteFindingSearchRequest } from '../src/solver/theoremKnowledgeFindings';
import { importKnowledgeRuns } from '../src/solver/theoremKnowledgeRuns';
import { copyKnowledgeSnapshot, readKnowledgeCatalog, writePackedKnowledge } from '../src/solver/theoremKnowledgeStore';
import { recordRouteBlockers, validateBlockerProposals } from '../src/solver/routeControl';

const roots: string[] = [];
afterEach(() => { for (const root of roots.splice(0)) fs.rmSync(root, { recursive: true, force: true }); });
const directory = () => {
  const root = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'knowledge-findings-'))); roots.push(root); return root;
};
function fixture() {
  const root = directory(), repository = path.join(root, 'repository'); fs.mkdirSync(repository);
  const git = (...args: string[]) => execFileSync('git', ['-C', repository, ...args], { encoding: 'utf8' }).trim();
  const dependency: CooperativeTask = { id: 'core', kind: 'lemma', objective: 'Prove the finite density bridge',
    proofPath: 'Submission.lean', theoremName: 'core', type: '∀ (n : Nat), 2 * n ≤ n', premises: ['n is unrestricted'],
    dependsOn: [], revision: 0 };
  const task: CooperativeTask = { id: 'feasibility', kind: 'research', objective: 'Challenge the finite density bridge on a small witness',
    dependsOn: ['core'], revision: 0, sharing: 'problem' };
  const notes = JSON.stringify({ summary: 'The proposed density inequality fails at n = 1; the original theorem is not refuted.',
    conclusion: 'refuted', evidenceRefs: ['RESEARCH.md: counterexample n=1'], remainingObligations: ['A valid sharp inequality is still needed.'],
    leanChecks: [{ status: 'inconclusive' }] });
  fs.writeFileSync(path.join(repository, 'RESEARCH.md'), notes + '\n');
  git('init', '--quiet'); git('add', 'RESEARCH.md');
  git('-c', 'user.name=Fixture', '-c', 'user.email=fixture@localhost', 'commit', '--quiet', '--no-gpg-sign', '-m', 'research evidence');
  const commit = git('rev-parse', 'HEAD');
  const finding = JSON.stringify(parseMathResponse(notes, 'math-result', { taskId: task.id, conclusion: 'inconclusive' }, 'summary'));
  const delivery: DeliveryRecord = { id: 'delivery', producer: 'researcher', taskId: task.id, taskDigest: taskVersion(task),
    groupId: 'main', kind: 'research', status: 'conditional', statement: task.objective, premises: [],
    dependencies: [{ taskId: dependency.id, taskDigest: taskVersion(dependency) }], remainingObligations: ['A valid sharp inequality is still needed.'],
    summary: 'Density route refuted', evidenceRefs: ['RESEARCH.md: counterexample n=1'], createdAt: 1, commit,
    findingDigest: mathDigest(finding) };
  const state = { schema: 'deepscientist.math.solver.v1', runId: 'old-run', taskDigest: mathDigest('task'),
    buildDigest: mathDigest('build'), environmentDigest: mathDigest('environment'), evaluatorDigest: mathDigest('evaluator'),
    problem: { workspace: repository, receiptDigest: mathDigest('problem receipt'), contract: { problemId: 'density' },
      declarations: {} }, worktree: repository, model: 'never-called', effort: 'none', phase: 'finished', turns: 1,
    cooperation: { tasks: [{ task: dependency, status: 'blocked', attempts: 1 },
      { task, status: 'completed', attempts: 1, finding }], deliveries: [delivery] } } as unknown as SolverRunState;
  const stateFile = path.join(root, 'state.json');
  const save = () => { writeSolverRunState(stateFile, state); return stateFile; };
  const node = state.cooperation!.tasks[1]!;
  const importFinding = () => importKnowledgeRuns([save()], { includeFindings: true });
  return { root, repository, task, dependency, state, stateFile, delivery, node, save, importFinding, notes, commit };
}

describe('explicit advisory route finding import', () => {
  it('imports nothing by default and never turns refuted prose into a checked theorem', () => {
    const f = fixture();
    expect(importKnowledgeRuns([f.save()])).toEqual({ candidates: [], skipped: [] });
    const imported = f.importFinding();
    expect(imported.skipped).toEqual([]); expect(imported.candidates).toEqual([]); expect(imported.findings).toHaveLength(1);
    const entry = imported.findings![0]!;
    expect(entry).toMatchObject({ conclusion: 'refuted', evidence: 'recorded-advisory-not-replayed', acceptance: 'not-assessed',
      scope: { problemId: 'density', environmentDigest: f.state.environmentDigest, problemReceiptDigest: f.state.problem.receiptDigest,
        source: { kind: 'research', statementKind: 'research-objective', statement: f.task.objective },
        dependencies: [{ statementKind: 'closed-task-type', statement: f.dependency.type, premises: f.dependency.premises }] },
      provenance: { source: f.stateFile, runId: 'old-run', sourceCommit: f.commit, findingDigest: mathDigest(f.node.finding!) } });
    expect(entry.notes).toBe(f.notes + '\n');
    expect(entry.provenance.notesDigest).toBe(mathDigest(f.notes + '\n'));
    const base = buildTheoremKnowledge(imported.candidates, undefined, imported.findings);
    expect(base.entries).toEqual([]); expect(base.sources).toEqual({}); expect(base.routeFindings).toHaveLength(1);
    expect(searchTheoremKnowledge(base, 'density').hits).toEqual([]);
    expect(JSON.stringify(base)).not.toContain('kernel_verified');
    expect(f.state.cooperation!.tasks.map(node => node.status)).toEqual(['blocked', 'completed']);
  });

  it('reads the frozen journal at the delivery commit instead of the mutable file', () => {
    const f = fixture(); fs.writeFileSync(path.join(f.repository, 'RESEARCH.md'), 'Mutable note must never be imported');
    expect(f.importFinding().findings?.[0]!.finding).toBe(f.node.finding);
  });

  it('retains recorded obstruction scopes and reconsideration conditions as advisory metadata', () => {
    const f = fixture(), tasks = f.state.cooperation!.tasks;
    const proposals = validateBlockerProposals([{ mechanism: 'Nonuniform constant', scope: 'The finite density bridge at n=1',
      evidenceRefs: ['RESEARCH.md'], reopenOn: [{ kind: 'contract-changed' }, { kind: 'dependency-checked', taskId: 'core' }] }], f.task, tasks);
    f.state.cooperation!.blockers = [];
    recordRouteBlockers(f.state.cooperation!.blockers, proposals, f.task, tasks,
      f.state.environmentDigest, f.state.problem.receiptDigest, 1);
    const imported = f.importFinding();
    expect(imported.findings?.[0]).toMatchObject({
      obstructions: [{ mechanism: 'Nonuniform constant', scope: 'The finite density bridge at n=1', evidenceRefs: ['RESEARCH.md'] }],
      reconsiderWhen: ['The challenged mathematical contract changes.', `Fresh evidence for the dependency: ${f.dependency.type}`],
      acceptance: 'not-assessed',
    });
    expect(f.state.cooperation!.blockers[0]!.status).toBe('open');
  });

  it.each(['digest', 'source', 'dependency', 'commit'] as const)('rejects an invalid %s binding', binding => {
    const f = fixture();
    if (binding === 'digest') f.delivery.findingDigest = mathDigest('other finding');
    if (binding === 'source') {
      f.node.finding = JSON.stringify({ ...JSON.parse(f.node.finding!), summary: 'Forged checkpoint refutation' });
      f.delivery.findingDigest = mathDigest(f.node.finding);
    }
    if (binding === 'dependency') f.delivery.dependencies[0]!.taskDigest = mathDigest('other task');
    if (binding === 'commit') f.delivery.commit = 'f'.repeat(40);
    const imported = f.importFinding();
    expect(imported.findings).toEqual([]); expect(imported.skipped).toHaveLength(1);
    expect(imported.skipped[0]!.reason).toBe({ digest: 'math_knowledge_run_finding_delivery_missing',
      source: 'math_knowledge_run_finding_source_mismatch', dependency: 'math_knowledge_run_finding_dependency_missing',
      commit: 'math_knowledge_run_source_unavailable' }[binding]);
  });

  it.each(['source', 'dependency', 'implicit-multi-group'] as const)('excludes private %s findings', target => {
    const f = fixture();
    if (target === 'source') {
      f.node.task = { ...f.task, sharing: 'group' };
      f.delivery.taskDigest = taskVersion(f.node.task);
    }
    if (target === 'dependency') {
      f.state.cooperation!.tasks[0]!.task = { ...f.dependency, sharing: 'group' };
      f.delivery.dependencies[0]!.taskDigest = taskVersion(f.state.cooperation!.tasks[0]!.task);
    }
    if (target === 'implicit-multi-group') {
      f.node.task = { ...f.task, sharing: undefined };
      f.delivery.taskDigest = taskVersion(f.node.task);
      f.state.cooperation!.groups = ['main', 'private'].map(id => ({ turns: 0,
        group: { id, objective: id, status: 'active', revision: 0 } }));
    }
    const imported = f.importFinding();
    expect(imported.findings).toEqual([]); expect(imported.skipped[0]!.reason).toBe('math_knowledge_run_finding_private');
  });

  it('requires complete historical dependency versions rather than borrowing current changed assumptions', () => {
    const f = fixture();
    f.state.cooperation!.tasks[0]!.task = { ...f.dependency, type: '∀ (n : Nat), n ≤ 2 * n' };
    expect(f.importFinding().skipped[0]!.reason).toBe('math_knowledge_run_finding_dependency_missing');
    f.state.cooperation!.history = [{ task: f.dependency }];
    expect(f.importFinding().findings?.[0]!.scope.dependencies[0]!.statement).toBe(f.dependency.type);
  });
});

describe('scoped route recall and immutable catalog storage', () => {
  const baseFixture = () => {
    const f = fixture(), imported = f.importFinding();
    return { ...f, candidate: imported.findings![0]!, base: buildTheoremKnowledge([], undefined, imported.findings) };
  };

  it('recalls identical statements after task names change without pretending lexical matches prove applicability', () => {
    const f = baseFixture();
    const renamed = { ...f.candidate, provenance: { ...f.candidate.provenance, taskId: 'new_research_id', runId: 'new-run' } };
    const base = buildTheoremKnowledge([], f.base, [renamed]);
    expect(base.routeFindings).toHaveLength(1); expect(base.routeFindings![0]!.provenance).toHaveLength(2);
    const result = searchKnowledgeRouteFindings(base, '', { goal: f.dependency.type,
      environmentDigest: f.state.environmentDigest, problemReceiptDigest: f.state.problem.receiptDigest });
    expect(result).toMatchObject({ advisoryOnly: true, acceptance: 'not-assessed', total: 1,
      hits: [{ statementMatch: 'exact-recorded-text', scopeMatch: 'statement-and-recorded-environment', requiresScopeReview: true }] });
    expect(searchKnowledgeRouteFindings(base, 'density', { goal: '∀ (n : Nat), n ≤ 2 * n',
      environmentDigest: 'changed-env', problemReceiptDigest: mathDigest('changed-problem') }).hits[0])
      .toMatchObject({ statementMatch: 'lexical-only', environmentMatch: 'different', problemReceiptMatch: 'different', scopeMatch: 'not-established' });
    expect(searchKnowledgeRouteFindings(base, 'density', { problemId: 'unrelated' }).hits).toEqual([]);
    expect(buildTheoremKnowledge([], base, [renamed])).toEqual(base);
    const changedRaw = JSON.stringify({ ...JSON.parse(f.candidate.finding), taskId: 'new_research_id' });
    const honestRename = { ...renamed, finding: changedRaw,
      provenance: { ...renamed.provenance, findingDigest: mathDigest(changedRaw) } };
    const preserved = buildTheoremKnowledge([], f.base, [honestRename]);
    expect(preserved.routeFindings).toHaveLength(2);
    expect(new Set(preserved.routeFindings!.map(item => item.scopeDigest)).size).toBe(1);
    expect(searchKnowledgeRouteFindings(preserved, '', { goal: f.dependency.type }).total).toBe(2);
  });

  it('keeps changed hypothesis and environment versions separate and authenticates their complete metadata', () => {
    const f = baseFixture();
    const changed = { ...f.candidate, scope: { ...f.candidate.scope, environmentDigest: 'new-env',
      dependencies: [{ ...f.candidate.scope.dependencies[0]!, premises: ['n = 0'] }] } };
    const base = buildTheoremKnowledge([], f.base, [changed]);
    expect(base.routeFindings).toHaveLength(2);
    expect(new Set(base.routeFindings!.map(item => item.scopeDigest)).size).toBe(2);
    expect(validateTheoremKnowledge(base)).toEqual(base);
    const tampered = structuredClone(base); tampered.routeFindings![0]!.scope.dependencies[0]!.statement = 'False';
    expect(() => validateTheoremKnowledge(tampered)).toThrow('math_knowledge_finding_identity_changed');
  });

  it.each(['v1', 'v2'] as const)('preserves findings and worker snapshot identity in %s catalogs', format => {
    const f = baseFixture(), file = path.join(f.root, `catalog-${format}.json`);
    const written = format === 'v1' ? writeTheoremKnowledge(file, f.base) : writePackedKnowledge(file, f.base);
    const loaded = readKnowledgeCatalog(file, written.sha256);
    expect(loaded.base).toEqual(f.base);
    const copy = path.join(f.root, 'worker', path.basename(file)); copyKnowledgeSnapshot(loaded, file, copy);
    expect(readKnowledgeCatalog(copy, written.sha256).base).toEqual(f.base);
    const id = f.base.routeFindings![0]!.id;
    expect(getKnowledgeRouteFinding(loaded.base, id)).toMatchObject({ id, advisoryOnly: true, finding: f.node.finding });
    const text = JSON.parse(fs.readFileSync(file, 'utf8')); text.routeFindings[0].summary = 'Forged summary';
    fs.chmodSync(file, 0o600); fs.writeFileSync(file, JSON.stringify(text));
    expect(() => readKnowledgeCatalog(file, written.sha256)).toThrow('math_knowledge_identity_changed');
    expect(() => readKnowledgeCatalog(file)).toThrow('math_knowledge_finding_identity_changed');
  });

  it('keeps large arguments and Unicode exact through bounded JSON pages', () => {
    const f = baseFixture(), text = '完整反例与假设 🧮 '.repeat(2000);
    const candidate = { ...f.candidate, finding: text, summary: text, provenance: { ...f.candidate.provenance, findingDigest: mathDigest(text) } };
    const base = buildTheoremKnowledge([], undefined, [candidate]), id = base.routeFindings![0]!.id;
    let offset = 0, restored = '', count = 0;
    for (;;) {
      const page = getKnowledgeRouteFindingPage(base, id, { startOffset: offset, maxBytes: 2048 });
      expect(Buffer.byteLength(JSON.stringify(page)) + 1).toBeLessThanOrEqual(2048);
      expect(page.text).not.toContain('\uFFFD'); restored += page.text; count++;
      if (!page.truncated) break;
      expect(page.nextOffset).toBeGreaterThan(offset); offset = page.nextOffset!;
    }
    expect(count).toBeGreaterThan(1); expect(restored).toBe(canonicalMathJson(getKnowledgeRouteFinding(base, id)));
    expect(JSON.parse(restored).finding).toBe(text);
    expect(() => getKnowledgeRouteFindingPage(base, id, { startOffset: -1 })).toThrow('options_invalid');
    expect(() => getKnowledgeRouteFindingPage(base, id, { maxBytes: 12 })).toThrow('options_invalid');
  });

  it('does not retain an optional findings field in old catalogs or read sources for advisory retrieval', () => {
    const base = buildTheoremKnowledge([]);
    expect(base).not.toHaveProperty('routeFindings'); expect(validateTheoremKnowledge(base)).toEqual(base);
    expect(() => searchKnowledgeRouteFindings(base, '', {})).toThrow('invalid_query');
    expect(() => searchKnowledgeRouteFindings(base, 'density', { limit: 0 })).toThrow('invalid_query');
    expect(searchKnowledgeRouteFindings(base, 'density').hits).toEqual([]);
    expect(() => getKnowledgeRouteFinding(base, mathDigest('missing'))).toThrow('finding_not_found');
  });
});

describe('batched route finding recall', () => {
  const candidate = (statement: string): KnowledgeRouteFindingCandidate => ({
    evidence: 'recorded-advisory-not-replayed', acceptance: 'not-assessed', conclusion: 'supporting',
    summary: `Saved ${statement}`, finding: 'Archived reasoning', notes: 'Archived notes',
    scope: { problemId: 'historical', problemReceiptDigest: mathDigest('receipt'), environmentDigest: 'environment',
      source: { kind: 'lemma', statementKind: 'closed-task-type', statement, premises: [] }, dependencies: [] },
    evidenceRefs: [], obstructions: [], remainingObligations: [], reconsiderWhen: [],
    provenance: { source: '/archive/state.json', sourceDigest: mathDigest('state'), runId: 'old-run', taskId: 'old-task',
      taskDigest: mathDigest(statement), groupId: 'main', deliveryId: 'delivery', sourceCommit: 'a'.repeat(40),
      findingDigest: mathDigest('Archived reasoning'), notesDigest: mathDigest('Archived notes') },
  });
  const catalog = (...candidates: KnowledgeRouteFindingCandidate[]) => ({ routeFindings: buildKnowledgeRouteFindings(candidates) });

  it('preserves every independent goal, exact dependency match, annotation, count and ordering', () => {
    const nat = candidate('NatBound'), real = candidate('RealEstimate'), dependency = candidate('InvestigateBridge');
    dependency.scope.dependencies = [{ kind: 'lemma', statementKind: 'closed-task-type', statement: 'MeasurePushforward', premises: [] }];
    const different = { ...nat, scope: { ...nat.scope, environmentDigest: 'different-environment', problemReceiptDigest: mathDigest('different') } };
    const base = catalog(nat, real, dependency, different), requests = Object.freeze([
      { query: '', goal: 'NatBound' }, { query: '', goal: 'MeasurePushforward' },
      { query: 'saved', goal: 'MissingTarget' }, { query: '', goal: 'RealEstimate' }, { query: '', goal: 'NatBound' },
    ]);
    const options = { limit: 2, problemId: 'historical', environmentDigest: 'environment', problemReceiptDigest: mathDigest('receipt') };
    const results = searchKnowledgeRouteFindingRequests(base, requests, options);
    expect(results).toEqual(requests.map(({ query, goal }) => searchKnowledgeRouteFindings(base, query, { ...options, goal })));
    expect(results[0]!.total).toBe(2);
    expect(results[0]!.hits.map(hit => hit.id)).toEqual(results[0]!.hits.map(hit => hit.id).toSorted());
    expect(results[0]!.hits).toContainEqual(expect.objectContaining({ scopeMatch: 'statement-and-recorded-environment', environmentMatch: 'match' }));
    expect(results[0]!.hits).toContainEqual(expect.objectContaining({ scopeMatch: 'not-established', environmentMatch: 'different', problemReceiptMatch: 'different' }));
    expect(results[1]!.hits[0]).toMatchObject({ statementMatch: 'exact-recorded-text', score: 1001, matched: ['measurepushforward'] });
    expect(results[2]!.total).toBe(4); expect(results[2]!.hits).toHaveLength(2);
    expect(searchKnowledgeRouteFindingRequests(base, [{ query: '', goal: 'NatBound' }])[0]!.hits[0])
      .toMatchObject({ environmentMatch: 'unknown', problemReceiptMatch: 'unknown', scopeMatch: 'not-established' });
  });

  it('keeps raw hypotheses and whitespace in exact identities and clones repeated result objects', () => {
    const nat = 'h : Nat\n|- SharedTarget', real = 'h : Real\n|- SharedTarget', base = catalog(candidate(nat), candidate(real));
    const requests = [{ query: '', goal: nat }, { query: '', goal: real }, { query: '', goal: nat + ' ' }, { query: '', goal: nat }];
    const results = searchKnowledgeRouteFindingRequests(base, requests);
    expect(results).toEqual(requests.map(({ query, goal }) => searchKnowledgeRouteFindings(base, query, { goal })));
    expect(results[0]!.hits[0]!.id).not.toBe(results[1]!.hits[0]!.id);
    expect(results[0]!.hits[0]!.statementMatch).toBe('exact-recorded-text');
    expect(results[2]!.hits.every(hit => hit.statementMatch === 'lexical-only')).toBe(true);
    results[0]!.hits[0]!.matched.push('caller-change'); results[0]!.hits[0]!.readWith.id = 'caller-change';
    expect(results[3]!.hits[0]!.matched).not.toContain('caller-change');
    expect(results[3]!.hits[0]!.readWith.id).not.toBe('caller-change');
  });

  it('prepares each record once, observes fresh metadata next call and propagates later read failures', () => {
    const base = catalog(candidate('NatBound')), item = base.routeFindings[0]!;
    let reads = 0, statement = item.scope.source.statement, failed = false;
    Object.defineProperty(item.scope.source, 'statement', { get: () => {
      reads++; if (failed) throw new Error('metadata-read-failed'); return statement;
    } });
    searchKnowledgeRouteFindingRequests(base, [{ query: '', goal: 'NatBound' }, { query: 'saved' }, { query: '', goal: 'RealEstimate' }]);
    expect(reads).toBe(1);
    statement = 'ChangedMarker';
    expect(searchKnowledgeRouteFindingRequests(base, [{ query: '', goal: statement }])[0]!.hits[0]!.statementMatch).toBe('exact-recorded-text');
    expect(reads).toBe(2);
    failed = true;
    expect(() => searchKnowledgeRouteFindingRequests(base, [{ query: 'saved' }])).toThrow('metadata-read-failed');
  });

  it('filters before reading statement metadata and does not load complete archived arguments or sources', () => {
    const foreign = candidate('ForeignTarget'); foreign.scope.problemId = 'foreign';
    const base = catalog(candidate('NatBound'), foreign);
    for (const item of base.routeFindings) {
      for (const field of ['finding', 'notes', 'provenance']) Object.defineProperty(item, field, { get: () => { throw new Error('unexpected-argument-read'); } });
      if (item.scope.problemId === 'foreign') Object.defineProperty(item.scope.source, 'statement', { get: () => { throw new Error('unexpected-foreign-read'); } });
    }
    Object.defineProperty(base, 'sources', { get: () => { throw new Error('unexpected-source-read'); } });
    const results = searchKnowledgeRouteFindingRequests(base, [{ query: '', goal: 'NatBound' }, { query: 'saved' }], { problemId: 'historical' });
    expect(results.every(result => result.total === 1)).toBe(true);
  });

  it.each([
    [], Array(9).fill({ query: 'saved' }), [null], [{ query: 'saved' }, { query: '' }],
    [{ query: 'saved' }, { query: 'x'.repeat(4001) }], [{ query: 'saved' }, { query: '', goal: 'x'.repeat(16001) }],
    [{ query: 'saved', goal: null }],
  ].map(requests => ({ requests })))('validates the complete batch before reading metadata: $requests', ({ requests }) => {
    const base = { get routeFindings(): never { throw new Error('must-not-prepare'); } };
    expect(() => searchKnowledgeRouteFindingRequests(base, requests as KnowledgeRouteFindingSearchRequest[]))
      .toThrow('math_knowledge_invalid_query');
  });

  it('preserves inclusive UTF-8 boundaries, strict single-query null rejection and old empty catalogs', () => {
    const base = catalog(candidate('NatBound'));
    const requests = [{ query: 'saved'.padEnd(4000, ' ') }, { query: '', goal: 'NatBound'.padEnd(16000, ' ') }];
    expect(searchKnowledgeRouteFindingRequests(base, requests)).toEqual(requests.map(({ query, goal }) => searchKnowledgeRouteFindings(base, query, { goal })));
    expect(() => searchKnowledgeRouteFindings(base, 'saved', { goal: null as unknown as string })).toThrow('math_knowledge_invalid_query');
    expect(() => searchKnowledgeRouteFindingRequests(base, [{ query: '\u754c'.repeat(1334) }])).toThrow('math_knowledge_invalid_query');
    expect(() => searchKnowledgeRouteFindingRequests(base, [{ query: '', goal: '\u754c'.repeat(5334) }])).toThrow('math_knowledge_invalid_query');
    expect(searchKnowledgeRouteFindingRequests({}, [{ query: 'saved' }])[0]!.hits).toEqual([]);
  });
});

describe('advisory findings CLI', () => {
  const cli = (...args: string[]) => JSON.parse(execFileSync('bun', [path.resolve('bin/math.ts'), 'knowledge', ...args],
    { cwd: path.resolve('.'), encoding: 'utf8', env: { ...process.env, NO_COLOR: '1' } }).trim());

  it('requires explicit import and search flags and returns bounded complete finding read handles', () => {
    const f = fixture(), initial = path.join(f.root, 'proofs-only.json'), catalog = path.join(f.root, 'advisory.json');
    cli('build', '--state', f.save(), '--output', initial);
    expect(readKnowledgeCatalog(initial).base.routeFindings).toBeUndefined();
    expect(cli('build', '--state', f.save(), '--output', catalog, '--include-findings')).toMatchObject({ inputFindings: 1, routeFindings: 1, entries: 0 });
    expect(cli('search', '--catalog', catalog, '--query', 'density')).not.toHaveProperty('routeFindings');
    const result = cli('search', '--catalog', catalog, '--query', 'density', '--include-findings');
    expect(result.routeFindings).toMatchObject({ advisoryOnly: true, total: 1 });
    const page = cli('finding', '--catalog', catalog, '--id', result.routeFindings.hits[0].id, '--max-bytes', '2048');
    expect(Buffer.byteLength(JSON.stringify(page)) + 1).toBeLessThanOrEqual(2048);
    expect(page).toMatchObject({ advisoryOnly: true, acceptance: 'not-assessed' });
  });
});
