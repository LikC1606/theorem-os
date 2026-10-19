import path from 'node:path';
import { mathGitBytes } from '../math/mathGit';
import { canonicalMathJson, mathDigest, readMathText } from '../math/mathRuntimeIo';
import { assertMathCanonicalPath } from '../math/paths';
import { readSolverRunState, type SolverRunState } from './archive';
import { recordedTaskProofStatus } from './progress';
import { taskVersion, type TaskRecord } from './tasks';
import { allowedKnowledgeFile, locateKnowledgeDeclaration, type KnowledgeCandidate, type KnowledgeImportResult } from './theoremKnowledge';

const oid = /^[a-f0-9]{40}(?:[a-f0-9]{24})?$/u;
const digest = /^[a-f0-9]{64}$/u;
const error = (reason: string): never => { throw new Error(`math_knowledge_run_${reason}`); };
const relativeDirectory = (value: string) => typeof value === 'string' && value && !path.posix.isAbsolute(value) &&
  !value.includes('\\') && !value.includes('\0') && value.split('/').every(part => part && part !== '.' && part !== '..' && !part.startsWith('.'));
type Snapshot = { files: Record<string, string>; ownedDigest: string };

function committedFiles(roots: readonly string[], commit: string, project: string, names: readonly string[]): Record<string, string> {
  const paths = names.map(file => `${project}/${file}`);
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

/** Explicit checkpoints only. Historical receipts retain provenance but never grant fresh acceptance. */
export function importKnowledgeRuns(stateFiles: readonly string[]): KnowledgeImportResult {
  const result: KnowledgeImportResult = { candidates: [], skipped: [] }, cache = new Map<string, Snapshot>();
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
  }
  return result;
}
