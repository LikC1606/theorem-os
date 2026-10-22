import path from 'node:path';
import { mathGitBytes } from '../math/mathGit';
import { canonicalMathJson, mathDigest, readMathText } from '../math/mathRuntimeIo';
import { assertMathCanonicalPath } from '../math/paths';
import { readSolverRunState, type SolverRunState } from './archive';
import { recordedTaskProofStatus } from './progress';
import { isAdvisoryTask, taskGroup, taskVersion, type CooperativeTask, type TaskRecord } from './tasks';
import { allowedKnowledgeFile, locateKnowledgeDeclaration, type KnowledgeCandidate, type KnowledgeImportResult } from './theoremKnowledge';
import type { DeliveryRecord } from './deliveries';
import { prepareResearchDelivery, type ResearchAdmissionScope } from './researchAdmission';
import { buildKnowledgeRouteFindings, type KnowledgeRouteContract, type KnowledgeRouteFindingCandidate } from './theoremKnowledgeFindings';

const oid = /^[a-f0-9]{40}(?:[a-f0-9]{24})?$/u;
const digest = /^[a-f0-9]{64}$/u;
const error = (reason: string): never => { throw new Error(`math_knowledge_run_${reason}`); };
const relativeDirectory = (value: string) => typeof value === 'string' && value && !path.posix.isAbsolute(value) &&
  !value.includes('\\') && !value.includes('\0') && value.split('/').every(part => part && part !== '.' && part !== '..' && !part.startsWith('.'));
type Snapshot = { files: Record<string, string>; ownedDigest: string };

function committedFiles(roots: readonly string[], commit: string, project: string, names: readonly string[]): Record<string, string> {
  const paths = names.map(file => project ? `${project}/${file}` : file);
  for (const root of roots) {
    try {
      assertMathCanonicalPath(root);
      const tree = mathGitBytes(root, ['ls-tree', '--full-tree', '-z', commit, '--', ...paths],
        { maxBuffer: 1024 * 1024, errorMessage: 'math_knowledge_run_source_unavailable' }).toString('utf8');
      const modes = new Map(tree.split('\0').filter(Boolean).map(line => {
        const match = /^(\d+) blob [a-f0-9]+\t(.+)$/u.exec(line);
        return match ? [match[2]!, match[1]!] : ['', ''];
      }));
      if (paths.some(file => !modes.has(file))) continue;
      if (paths.some(file => !/^100(?:644|755)$/u.test(modes.get(file)!))) error('forbidden_source');
      return Object.fromEntries(names.map((file, index) => [file, new TextDecoder('utf-8', { fatal: true }).decode(
        mathGitBytes(root, ['show', `${commit}:${paths[index]}`],
          { maxBuffer: 1024 * 1024, errorMessage: 'math_knowledge_run_source_unavailable' }))]));
    } catch (failure) {
      if (failure instanceof Error && failure.message === 'math_knowledge_run_forbidden_source') throw failure;
    }
  }
  return error('source_unavailable');
}

function runCandidate(state: SolverRunState, node: TaskRecord, stateFile: string, stateDigest: string,
  cache: Map<string, Snapshot>): KnowledgeCandidate {
  const { task } = node, proof = node.integratedCheck ?? node.proof;
  if (!['lemma', 'goal'].includes(task.kind) || !proof) return error('proof_missing');
  const version = taskVersion(task), status = recordedTaskProofStatus(node, state.environmentDigest);
  if (status !== 'checked') return error(`proof_${status}`);
  if (proof.taskDigest !== version || proof.conditions?.length) return error('proof_stale_or_conditional');
  if (!oid.test(proof.commit) || !oid.test(proof.verification.targetCommit) || !digest.test(proof.sourceDigest))
    return error('proof_identity_invalid');
  if (!task.proofPath || !allowedKnowledgeFile(task.proofPath) || !state.problem.ownedFiles.includes(task.proofPath))
    return error('forbidden_source');
  if (!task.theoremName || (task.kind === 'lemma' && !task.type?.trim())) return error('target_missing');
  const receipts = proof.verification.results;
  if (receipts.length !== 1 || receipts.some(receipt => receipt.status !== 'kernel_verified' || !receipt.receiptId ||
      receipt.targetCommit !== proof.verification.targetCommit || receipt.proofPath !== task.proofPath ||
      receipt.theoremName !== task.theoremName || receipt.statementHash !== version || receipt.leanStatementHash !== version ||
      receipt.claim !== 'statement' || receipt.cleanupError)) return error('receipt_mismatch');
  const target = task.kind === 'goal' ? state.problem.targets.find(item =>
    item.theoremName === task.theoremName && item.proofPath === task.proofPath) : undefined;
  if (task.kind === 'goal' && !target) return error('target_mismatch');
  const problem = state.problem;
  if (!relativeDirectory(problem.projectRelative) || problem.ownedFiles.some(file => !allowedKnowledgeFile(file)))
    return error('forbidden_source');
  const names = [...new Set([...problem.ownedFiles, ...Object.keys(problem.trustedFiles).filter(allowedKnowledgeFile)])].sort();
  if (!names.length || names.length > 4096) return error('source_selection_invalid');
  const roots = [...new Set([problem.workspace, state.worktree, ...(state.workers ?? []).map(worker => worker.worktree)]
    .filter((root): root is string => typeof root === 'string' && path.isAbsolute(root)))];
  const key = canonicalMathJson([roots, proof.commit, problem.projectRelative, names, problem.ownedFiles]);
  let snapshot = cache.get(key);
  if (!snapshot) {
    const files = committedFiles(roots, proof.commit, problem.projectRelative, names);
    snapshot = { files, ownedDigest: mathDigest(canonicalMathJson(problem.ownedFiles.map(file => [file, mathDigest(files[file]!)]))) };
    cache.set(key, snapshot);
  }
  if (snapshot.ownedDigest !== proof.sourceDigest) return error('source_digest_mismatch');
  for (const file of names) if (Object.hasOwn(problem.trustedFiles, file) &&
      mathDigest(snapshot.files[file]!) !== problem.trustedFiles[file]) return error('trusted_source_mismatch');
  const source = snapshot.files[task.proofPath]!, root = locateKnowledgeDeclaration(source, task.theoremName);
  const declarationHash = mathDigest(root.declarationType);
  if (receipts.some(receipt => receipt.sourceDeclarationHash !== undefined &&
      receipt.sourceDeclarationHash !== declarationHash) || (target && target.declarationHash !== declarationHash))
    return error('declaration_receipt_mismatch');
  if (task.kind === 'lemma' && root.kind !== 'theorem') return error('declaration_kind_mismatch');
  const references = proof.references;
  if (references && (references.sourceCommit !== proof.commit || references.root.file !== task.proofPath ||
      references.root.name !== task.theoremName || [...references.statement, ...references.proof].some(reference =>
        !allowedKnowledgeFile(reference.file) || !Object.hasOwn(snapshot.files, reference.file)))) return error('reference_mismatch');
  return {
    name: task.theoremName, file: task.proofPath, type: task.kind === 'lemma' ? task.type! : root.declarationType,
    typeKind: task.kind === 'lemma' ? 'closed-task-type' : 'source-header', kind: task.kind as 'lemma' | 'goal',
    description: task.informalStatement ?? task.objective, premises: [...(task.premises ?? [])],
    dependencies: { statement: references?.statement ?? [], proof: references?.proof ?? [], tasks: references?.tasks ?? [],
      coverage: references?.tasks && !references.scope ? 'recorded' : 'unavailable' },
    files: snapshot.files,
    provenance: { kind: 'solver-check', source: stateFile, sourceDigest: stateDigest, sourceCommit: proof.commit,
      checkedCommit: proof.verification.targetCommit, runId: state.runId, taskId: task.id, taskDigest: version,
      environmentDigest: state.environmentDigest, problemReceiptDigest: problem.receiptDigest,
      problemId: problem.contract.problemId, receiptIds: receipts.map(receipt => receipt.receiptId) },
  };
}

function publicResearchTask(task: CooperativeTask, state: SolverRunState): boolean {
  return task.sharing === 'problem' || task.sharing === undefined && (state.cooperation?.groups?.length ?? 1) <= 1;
}

function routeContract(task: CooperativeTask, state: SolverRunState): KnowledgeRouteContract {
  if (isAdvisoryTask(task)) return { kind: task.kind, statementKind: 'research-objective',
    statement: task.objective, premises: [...(task.premises ?? [])] };
  if (task.kind === 'lemma' && task.type?.trim()) return { kind: task.kind, statementKind: 'closed-task-type',
    statement: task.type, premises: [...(task.premises ?? [])] };
  if (task.kind === 'goal') {
    const headers = state.problem.declarations[task.proofPath!] ?? [];
    const exact = headers.filter(item => item.name === task.theoremName);
    const found = exact.length ? exact : headers.filter(item => item.name.split('.').at(-1) === task.theoremName?.split('.').at(-1));
    if (found.length === 1) return { kind: task.kind, statementKind: 'source-header',
      statement: found[0]!.header, premises: [...(task.premises ?? [])] };
  }
  return error('finding_contract_missing');
}

function runFinding(state: SolverRunState, node: TaskRecord, delivery: DeliveryRecord,
  stateFile: string, stateDigest: string): KnowledgeRouteFindingCandidate {
  const task = node.task;
  if (!publicResearchTask(task, state)) return error('finding_private');
  if (!isAdvisoryTask(task) || typeof node.finding !== 'string' || node.status !== 'completed' ||
      delivery.kind !== 'research' || !['advisory', 'conditional'].includes(delivery.status) ||
      delivery.taskId !== task.id || delivery.taskDigest !== taskVersion(task) || !delivery.commit || !oid.test(delivery.commit) ||
      delivery.findingDigest !== mathDigest(node.finding)) return error('finding_delivery_mismatch');
  const finding = JSON.parse(node.finding);
  if (!finding || finding.taskId !== task.id || !['supporting', 'refuted', 'inconclusive'].includes(finding.conclusion) ||
      typeof finding.summary !== 'string' || !finding.summary.trim()) return error('finding_invalid');
  const records = [...(state.cooperation?.tasks ?? []), ...(state.cooperation?.history ?? [])];
  const gap = delivery.mathematicalGap, gapScope = delivery.mathematicalGapScope;
  if (gap || gapScope || finding.mathematicalGap !== undefined) {
    if (!gap || !gapScope || canonicalMathJson(gap) !== canonicalMathJson(finding.mathematicalGap) ||
        gapScope.problemReceiptDigest !== state.problem.receiptDigest || gapScope.source.id !== task.id ||
        taskVersion(gapScope.source) !== taskVersion(task) || gapScope.consumer.kind !== 'goal' ||
        gap.consumer.taskId !== gapScope.consumer.id || gap.consumer.taskDigest !== taskVersion(gapScope.consumer) ||
        !records.some(record => record.task.id === gapScope.consumer.id && taskVersion(record.task) === gap.consumer.taskDigest))
      return error('finding_gap_scope_invalid');
    if (!publicResearchTask(gapScope.consumer, state) || (state.cooperation?.tasks ?? []).some(record =>
      record.task.id === gapScope.consumer.id && !publicResearchTask(record.task, state))) return error('finding_private');
  }
  const dependencies = (delivery.dependencies ?? []).map(input => {
    const found = records.find(record => record.task.id === input.taskId && taskVersion(record.task) === input.taskDigest);
    if (!found) return error('finding_dependency_missing');
    if (!publicResearchTask(found.task, state)) return error('finding_private');
    return found.task;
  });
  // Do not use the live journal or trust an independently edited checkpoint finding.
  const roots = [...new Set([state.problem.workspace, state.worktree, ...(state.workers ?? []).map(worker => worker.worktree)]
    .filter((root): root is string => typeof root === 'string' && path.isAbsolute(root)))];
  const notes = committedFiles(roots, delivery.commit, '', ['RESEARCH.md'])['RESEARCH.md']!;
  // Replay the publication admission, including host identity defaults and gap normalization.
  // Historical notes can omit taskDigest, but cannot override the frozen task identity.
  const admissionScope: ResearchAdmissionScope = { source: task,
    assignment: { taskId: task.id, taskDigest: taskVersion(task), workerId: delivery.producer, seedCommit: delivery.commit },
    identity: { problemReceiptDigest: state.problem.receiptDigest,
      environmentDigest: gapScope?.environmentDigest ?? state.environmentDigest },
    tasks: [...records.map(record => ({ status: 'completed' as const, attempts: 0, ...record })),
      ...dependencies.map(task => ({ task, status: 'completed' as const, attempts: 0 })),
      ...(gapScope ? [{ task: gapScope.consumer, status: 'completed' as const, attempts: 0 }] : []), node],
    deliveries: state.cooperation?.deliveries };
  const recorded = prepareResearchDelivery({ kind: 'notes', text: notes }, admissionScope);
  const archived = prepareResearchDelivery({ kind: 'event', value: finding }, admissionScope);
  if (recorded.status !== 'admitted' || archived.status !== 'admitted' ||
      canonicalMathJson(recorded.finding) !== canonicalMathJson(archived.finding)) return error('finding_source_mismatch');
  const blockers = (state.cooperation?.blockers ?? []).filter(blocker => blocker.taskId === task.id &&
    blocker.taskDigest === delivery.taskDigest);
  const reconsiderWhen = [...new Set(blockers.flatMap(blocker => blocker.reopenOn.map(condition => {
    if (condition.kind === 'contract-changed') return 'The challenged mathematical contract changes.';
    if (condition.kind === 'environment-changed') return 'The pinned Lean environment changes.';
    const dependency = dependencies.find(task => task.id === condition.taskId);
    return dependency ? `Fresh evidence for the dependency: ${routeContract(dependency, state).statement}` :
      'New checked evidence for a recorded dependency is available.';
  })))];
  const candidate: KnowledgeRouteFindingCandidate = {
    evidence: 'recorded-advisory-not-replayed', acceptance: 'not-assessed',
    conclusion: finding.conclusion, summary: finding.summary, finding: node.finding, notes,
    scope: { problemId: state.problem.contract.problemId, problemReceiptDigest: state.problem.receiptDigest,
      environmentDigest: gapScope?.environmentDigest ?? state.environmentDigest, source: routeContract(task, state),
      ...(delivery.mathematicalGapScope ? { originalConsumer: routeContract(delivery.mathematicalGapScope.consumer, state) } : {}),
      dependencies: dependencies.map(task => routeContract(task, state)).sort((a, b) => canonicalMathJson(a).localeCompare(canonicalMathJson(b))) },
    evidenceRefs: [...delivery.evidenceRefs],
    obstructions: blockers.map(blocker => ({ mechanism: blocker.mechanism, scope: blocker.scope, evidenceRefs: [...blocker.evidenceRefs] })),
    remainingObligations: [...delivery.remainingObligations], reconsiderWhen: [...new Set([...reconsiderWhen,
      ...(delivery.mathematicalGap?.reconsiderWhen ?? [])])],
    ...(delivery.mathematicalGap ? { mathematicalGap: delivery.mathematicalGap } : {}),
    provenance: { source: stateFile, sourceDigest: stateDigest, runId: state.runId, taskId: task.id,
      taskDigest: taskVersion(task), groupId: taskGroup(task), deliveryId: delivery.id,
      sourceCommit: delivery.commit, findingDigest: delivery.findingDigest, notesDigest: mathDigest(notes) },
  };
  // Apply the same bounds and identities used by persisted catalogs before reporting a successful import.
  buildKnowledgeRouteFindings([candidate]);
  return candidate;
}

/** Explicit checkpoints only. Historical receipts retain provenance but never grant fresh acceptance. */
export function importKnowledgeRuns(stateFiles: readonly string[], options: { includeFindings?: boolean } = {}): KnowledgeImportResult {
  const result: KnowledgeImportResult = { candidates: [], skipped: [], ...(options.includeFindings ? { findings: [] } : {}) },
    cache = new Map<string, Snapshot>();
  for (const supplied of [...new Set(stateFiles)]) {
    const source = path.resolve(supplied);
    let state: SolverRunState, stateDigest: string;
    try {
      if (path.basename(source) !== 'state.json') error('state_path_invalid');
      assertMathCanonicalPath(source);
      const text = readMathText(source, 32 * 1024 * 1024);
      state = readSolverRunState(source); stateDigest = mathDigest(text);
      if (mathDigest(readMathText(source, 32 * 1024 * 1024)) !== stateDigest) error('state_changed');
    } catch {
      result.skipped.push({ source, reason: 'math_knowledge_run_state_invalid' }); continue;
    }
    for (const record of [...(state.cooperation?.tasks ?? []), ...(state.cooperation?.history ?? [])]) {
      if (!['lemma', 'goal'].includes(record.task.kind) || (!record.proof && !record.integratedCheck)) continue;
      try {
        // Historical plan versions omit scheduling fields; they retain their own mathematical task identity.
        const node = { status: 'integrated', attempts: 0, ...record } as TaskRecord;
        result.candidates.push(runCandidate(state, node, source, stateDigest, cache));
      } catch (failure) {
        result.skipped.push({ source, name: record.task.theoremName,
          reason: failure instanceof Error && /^math_knowledge_/u.test(failure.message) ? failure.message : 'math_knowledge_run_record_invalid' });
      }
    }
    if (options.includeFindings) for (const record of [...(state.cooperation?.tasks ?? []), ...(state.cooperation?.history ?? [])]) {
      if (!isAdvisoryTask(record.task) || !record.finding) continue;
      const node = { status: 'completed', attempts: 0, ...record } as TaskRecord;
      const delivery = [...(state.cooperation?.deliveries ?? [])].reverse().find(item => item.kind === 'research' &&
        item.taskId === record.task.id && item.taskDigest === taskVersion(record.task) && item.findingDigest === mathDigest(record.finding!));
      try {
        if (!delivery) error('finding_delivery_missing');
        result.findings!.push(runFinding(state, node, delivery, source, stateDigest));
      } catch (failure) {
        result.skipped.push({ source, name: record.task.id,
          reason: failure instanceof Error && /^math_knowledge_/u.test(failure.message) ? failure.message : 'math_knowledge_run_finding_invalid' });
      }
    }
  }
  return result;
}
