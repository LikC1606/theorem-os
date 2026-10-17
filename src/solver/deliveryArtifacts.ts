import { mathGitBytes } from '../math/mathGit';
import { canonicalMathJson, mathDigest } from '../math/mathRuntimeIo';
import { inspectLeanDeclarationRegions, inspectLeanSource, inspectScopedLeanDeclarations } from '../math/leanSource';
import { MAX_RESEARCH_NOTES_BYTES } from './deliveries';
import type { SolverProblem } from './problem';
import type { TaskAssignment } from './tasks';

export type DeliveryArtifact = Readonly<{
  id: string;
  kind: 'owned-source' | 'notes-lean';
  file: string;
  proofPath?: string;
  fileSha256: string;
  sha256: string;
  bytes: number;
  /** Offsets address UTF-16 text in the committed UTF-8 file; hashes address exact UTF-8 bytes. */
  startOffset?: number;
  endOffset?: number;
  declarations: readonly { name: string; header: string; sha256: string; draft: boolean }[];
}>;

export type ReportedLeanCheck = Readonly<{
  status: 'passed' | 'failed' | 'inconclusive';
  path?: string;
  declarations?: readonly string[];
  artifactIds?: readonly string[];
}>;

/** Recoverable candidates and worker claims are never independent Lean evidence. */
export type DeliveryArtifactManifest = Readonly<{
  schema: 'theorem-os.delivery-artifacts.v1';
  scope: 'advisory-unverified';
  problemReceiptDigest: string;
  taskId: string;
  taskDigest: string;
  seedCommit: string;
  commit: string;
  artifacts: readonly DeliveryArtifact[];
  reportedChecks?: readonly ReportedLeanCheck[];
}>;

const oid = /^[a-f0-9]{40,64}$/u;
const maxBytes = 4 * 1024 * 1024;
const gitBytes = (worktree: string, args: readonly string[]) => mathGitBytes(worktree, args,
  { maxBuffer: maxBytes, errorMessage: 'math_delivery_artifact_source_unavailable' });

function readBlob(worktree: string, commit: string, file: string, limit = maxBytes): Buffer | undefined {
  const entry = gitBytes(worktree, ['ls-tree', commit, '--', file]).toString('utf8').trim();
  if (!entry) return;
  if (!/^100(?:644|755) blob [a-f0-9]{40,64}\t/u.test(entry)) throw new Error('math_delivery_artifact_not_regular_file');
  const size = Number(gitBytes(worktree, ['cat-file', '-s', `${commit}:${file}`]).toString('utf8'));
  if (!Number.isSafeInteger(size) || size > limit) throw new Error('math_delivery_artifact_too_large');
  return gitBytes(worktree, ['show', `${commit}:${file}`]);
}

function declarations(source: string, previous = ''): DeliveryArtifact['declarations'] {
  const beforeScoped = new Map(inspectScopedLeanDeclarations(previous).map(item => [item.startOffset, item.qualifiedName]));
  const before = new Map(inspectLeanDeclarationRegions(previous).map(item =>
    [beforeScoped.get(item.startOffset) ?? item.name, previous.slice(item.startOffset, item.endOffset)]));
  const scoped = new Map(inspectScopedLeanDeclarations(source).map(item => [item.startOffset, item]));
  return inspectLeanDeclarationRegions(source).flatMap(item => {
    const text = source.slice(item.startOffset, item.endOffset);
    const inspected = inspectLeanSource(text), name = scoped.get(item.startOffset)?.qualifiedName ?? item.name;
    if (before.get(name) === text) return [];
    return [{ name, header: source.slice(item.startOffset, item.bodyOffset).trim(), sha256: mathDigest(text),
      draft: inspected.sorryCount > 0 || inspected.admitCount > 0 || inspected.axioms.length > 0 }];
  });
}

function leanBlocks(notes: string) {
  return [...notes.matchAll(/^```lean(?:4)?[^\S\n]*\r?\n([\s\S]*?)^```[^\S\n]*$/gmu)].map(match => {
    const startOffset = match.index! + match[0].indexOf('\n') + 1;
    return { code: match[1], startOffset, endOffset: startOffset + match[1].length };
  });
}

/** Capture before rejecting an unfinished typed root, so its supporting declarations remain recoverable. */
export function captureDeliveryArtifacts(input: {
  problem: SolverProblem; worktree: string; commit: string; assignment: TaskAssignment;
}): DeliveryArtifactManifest {
  const { problem, worktree, commit, assignment } = input;
  if (![commit, assignment.seedCommit, problem.baseCommit].every(value => oid.test(value)))
    throw new Error('math_delivery_artifact_invalid_commit');
  // The host supplies the problem and assignment. A worker cannot nominate another repository or path.
  for (const target of [assignment.seedCommit, commit])
    gitBytes(worktree, ['merge-base', '--is-ancestor', problem.baseCommit, target]);
  gitBytes(worktree, ['merge-base', '--is-ancestor', assignment.seedCommit, commit]);
  const artifacts: DeliveryArtifact[] = [];
  const add = (artifact: Omit<DeliveryArtifact, 'id'>) => {
    artifacts.push({ id: mathDigest(canonicalMathJson({ commit, ...artifact })), ...artifact });
  };
  for (const proofPath of problem.ownedFiles.filter(file => file.endsWith('.lean'))) {
    if (proofPath.split(/[\\/]/u).includes('..') || proofPath.startsWith('/') ||
        /(?:^|\/)Solution\.lean$/u.test(proofPath)) throw new Error('math_delivery_artifact_path_invalid');
    const file = `${problem.projectRelative}/${proofPath}`;
    const bytes = readBlob(worktree, commit, file);
    if (!bytes) continue;
    const before = readBlob(worktree, assignment.seedCommit, file)?.toString('utf8') ?? '';
    const changed = declarations(bytes.toString('utf8'), before);
    if (!changed.length) continue;
    const sha256 = mathDigest(bytes);
    add({ kind: 'owned-source', file, proofPath, fileSha256: sha256, sha256, bytes: bytes.length, declarations: changed });
  }
  const notes = readBlob(worktree, commit, 'RESEARCH.md', MAX_RESEARCH_NOTES_BYTES);
  if (notes) {
    const previous = readBlob(worktree, assignment.seedCommit, 'RESEARCH.md', MAX_RESEARCH_NOTES_BYTES)?.toString('utf8') ?? '';
    const oldBlocks = new Set(leanBlocks(previous).map(block => mathDigest(block.code)));
    for (const block of leanBlocks(notes.toString('utf8'))) {
      const sha256 = mathDigest(block.code), declared = declarations(block.code);
      if (oldBlocks.has(sha256) || !declared.length) continue;
      add({ kind: 'notes-lean', file: 'RESEARCH.md', fileSha256: mathDigest(notes), sha256,
        bytes: Buffer.byteLength(block.code), startOffset: block.startOffset, endOffset: block.endOffset,
        declarations: declared });
    }
  }
  return { schema: 'theorem-os.delivery-artifacts.v1', scope: 'advisory-unverified',
    problemReceiptDigest: problem.receiptDigest, taskId: assignment.taskId, taskDigest: assignment.taskDigest,
    seedCommit: assignment.seedCommit, commit, artifacts };
}

/** Explicit successful local-check claims must identify retained source, not a prose success report. */
export function validateDeliveryArtifactClaims(value: unknown, manifest: DeliveryArtifactManifest): ReportedLeanCheck[] {
  const claims = (value as { leanChecks?: unknown } | undefined)?.leanChecks;
  if (claims === undefined) return [];
  if (!Array.isArray(claims) || claims.length > 32) throw new Error('math_delivery_artifact_claim_invalid');
  return claims.map(claim => {
    if (!claim || !['passed', 'failed', 'inconclusive'].includes(claim.status))
      throw new Error('math_delivery_artifact_claim_invalid');
    if (claim.status !== 'passed') return { status: claim.status };
    if (typeof claim.path !== 'string' || !Array.isArray(claim.declarations) || !claim.declarations.length ||
        claim.declarations.some((name: unknown) => typeof name !== 'string' || !name.trim()) ||
        (claim.sha256 !== undefined && (typeof claim.sha256 !== 'string' || !/^[a-f0-9]{64}$/u.test(claim.sha256))))
      throw new Error('math_delivery_artifact_claim_invalid');
    const candidates = manifest.artifacts.filter(artifact =>
      (artifact.file === claim.path || artifact.proofPath === claim.path) &&
      (claim.sha256 === undefined || artifact.sha256 === claim.sha256 || artifact.fileSha256 === claim.sha256));
    if (!claim.declarations.every((name: string) => candidates.some(artifact =>
      artifact.declarations.some(declaration => declaration.name === name && !declaration.draft))))
      throw new Error('math_delivery_artifact_required: Retain the complete named Lean code in the owned source or a new lean fence in RESEARCH.md; local-check claims remain advisory.');
    return { status: 'passed', path: claim.path, declarations: [...new Set<string>(claim.declarations)],
      artifactIds: candidates.filter(artifact => artifact.declarations.some(declaration =>
        claim.declarations.includes(declaration.name) && !declaration.draft)).map(artifact => artifact.id) };
  });
}

/** Surface an unbound prose claim for follow-up without treating natural-language discussion as an error. */
export function diagnoseUnbackedLeanClaims(value: unknown, manifest: DeliveryArtifactManifest): string | undefined {
  const text = typeof value === 'string' ? value : (value as { summary?: unknown } | undefined)?.summary;
  if (typeof text !== 'string' || manifest.artifacts.some(artifact => artifact.declarations.some(item => !item.draft))) return;
  if (/(?:exitCode|exit code)\s*[:=]?\s*0\b|(?:saved[- ]file|Lean|Helpers|Submission)\s+(?:check|compilation)\s+(?:passed|succeeded)/iu.test(text))
    return 'A local Lean success is reported without recoverable new code. Request the complete candidate artifact and exact declaration names before typed adoption; this prose is advisory.';
}
