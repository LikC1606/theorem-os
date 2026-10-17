import { canonicalMathJson, mathDigest } from '../math/mathRuntimeIo';
import { maskLeanComments } from '../math/leanSyntax';
import type { LeanDeclarationReferences } from '../math/leanReferences';
import { inspectLeanDeclarationRegions } from '../math/leanSource';
import { committedSource, git } from './problem';
import type { SolverProblem } from './problem';

export type ProofReferences = LeanDeclarationReferences & {
  sourceCommit: string; environmentDigest: string; contextDigest: string;
  scope?: 'statement';
  statementType?: string;
  root: { name: string; file: string };
  inputs: { file: string; name?: string; digest: string }[];
  tasks?: { taskId: string; taskDigest: string }[];
};

/** Only committed content is cached; mutable worktree files never authorize reference reuse. */
const snapshots = new Map<string, { sources: Map<string, string>; regions: Map<string, ReturnType<typeof inspectLeanDeclarationRegions>>;
  contextDigest: string; bytes: number }>();
let snapshotBytes = 0;
function sourceSnapshot(problem: SolverProblem, worktree: string, sourceCommit: string, files: string[]) {
  const repository = git(worktree, ['rev-parse', '--path-format=absolute', '--git-common-dir']);
  const commit = /^[a-f0-9]{40,64}$/u.test(sourceCommit) ? sourceCommit : git(worktree, ['rev-parse', `${sourceCommit}^{commit}`]);
  const key = canonicalMathJson([repository, problem.projectRelative, problem.receiptDigest, commit, files]);
  const cached = snapshots.get(key);
  if (cached) { snapshots.delete(key); snapshots.set(key, cached); return cached; }
  const sources = new Map(files.map(file => [file, maskLeanComments(committedSource(worktree, commit, `${problem.projectRelative}/${file}`))]));
  const regions = new Map([...sources].map(([file, source]) => [file, inspectLeanDeclarationRegions(source)]));
  const contextDigest = mathDigest(canonicalMathJson([...sources].map(([file, source]) => {
    for (const region of [...regions.get(file)!].reverse()) {
      const prefix = source.slice(source.lastIndexOf('\n', region.startOffset - 1) + 1, region.startOffset);
      if (!prefix.trim() && /^(?:theorem|lemma|def|abbrev|opaque)\s/u.test(source.slice(region.startOffset, region.bodyOffset)))
        source = source.slice(0, region.startOffset) + source.slice(region.endOffset);
    }
    return [file, source];
  })));
  const bytes = [...sources.values()].reduce((total, source) => total + Buffer.byteLength(source), 0);
  const snapshot = { sources, regions, contextDigest, bytes };
  const limit = 16 * 1024 * 1024;
  if (bytes <= limit) {
    while (snapshots.size && (snapshots.size >= 8 || snapshotBytes + bytes > limit)) {
      const oldest = snapshots.keys().next().value!;
      snapshotBytes -= snapshots.get(oldest)!.bytes; snapshots.delete(oldest);
    }
    snapshots.set(key, snapshot); snapshotBytes += bytes;
  }
  return snapshot;
}

/** Source is used to fingerprint Lean-selected declarations, never to infer their references. */
export function captureProofReferences(problem: SolverProblem, worktree: string, sourceCommit: string,
  root: ProofReferences['root'], references: LeanDeclarationReferences, environmentDigest: string,
  scope?: 'statement', statementType?: string): ProofReferences | undefined {
  if (statementType !== undefined && (scope !== 'statement' || !statementType.trim())) return;
  const files = [...new Set([...Object.keys(problem.trustedFiles), ...problem.ownedFiles])].filter(file => file.endsWith('.lean'));
  if ([root, ...references.statement, ...references.proof].some(item => !files.includes(item.file))) return;
  const { sources, regions, contextDigest } = sourceSnapshot(problem, worktree, sourceCommit, files);
  const inputs = new Map<string, ProofReferences['inputs'][number]>();
  // Pending helper types need not have a saved declaration. Their exact task type
  // binds the root; Lean-selected local definitions still bind the source inputs.
  for (const item of [...(statementType === undefined ? [root] : []), ...references.statement, ...references.proof]) {
    const source = sources.get(item.file)!;
    const matches = regions.get(item.file)!.filter(region => item.name === region.name || item.name.endsWith('.' + region.name));
    // Generated declarations or ambiguous source names require the entire module to stay fixed.
    const region = matches.length === 1 ? matches[0] : undefined;
    const name = region?.name;
    const headerOnly = scope === 'statement' && region && (/^(?:theorem|lemma)\s/u.test(source.slice(region.startOffset, region.bodyOffset)) ||
      (item.file === root.file && item.name === root.name));
    inputs.set(item.file + '\0' + (name ?? ''), { file: item.file, ...(name ? { name } : {}),
      digest: mathDigest(region ? headerOnly ? region.declarationType : source.slice(region.startOffset, region.endOffset) : source) });
  }
  return { ...references, root, sourceCommit, environmentDigest, contextDigest,
    ...(scope ? { scope } : {}),
    ...(statementType === undefined ? {} : { statementType: maskLeanComments(statementType) }),
    inputs: [...inputs.values()].sort((a, b) => a.file.localeCompare(b.file) || (a.name ?? '').localeCompare(b.name ?? '')) };
}

export function proofReferencesUnchanged(problem: SolverProblem, worktree: string, commit: string,
  references: ProofReferences, environmentDigest: string): boolean {
  if (references.environmentDigest !== environmentDigest) return false;
  const current = captureProofReferences(problem, worktree, commit, references.root, references, environmentDigest, references.scope, references.statementType);
  return Boolean(current && current.contextDigest === references.contextDigest &&
    canonicalMathJson(current.inputs) === canonicalMathJson(references.inputs));
}
