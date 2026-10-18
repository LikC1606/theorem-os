import { allowedKnowledgeFile, type TheoremKnowledgeBase, type TheoremKnowledgeEntry } from './theoremKnowledge';

type DependencyNode = {
  id: string; name: string; file: string; contextDigest: string; environmentDigest?: string;
  sourceSha256: string; depth: number; coverage: 'recorded' | 'unavailable';
  tasks: TheoremKnowledgeEntry['dependencies']['tasks']; tasksTruncated: boolean;
};
type DependencyReference = {
  from: string; kind: 'statement' | 'proof'; file: string; name: string;
  resolution: 'indexed' | 'ambiguous' | 'source-available' | 'missing-source';
  targetIds: string[]; targetsTruncated: boolean;
  source?: { theoremId: string; file: string; sha256: string };
};

/** Follow recorded references only within the same complete context and environment. */
export function getKnowledgeDependencies(base: TheoremKnowledgeBase, id: string, options: {
  depth?: number; maxNodes?: number; maxReferences?: number;
} = {}) {
  const depth = options.depth ?? 2, maxNodes = options.maxNodes ?? 64, maxReferences = options.maxReferences ?? 256;
  if (!Number.isInteger(depth) || depth < 0 || depth > 8 || !Number.isInteger(maxNodes) || maxNodes < 1 || maxNodes > 128 ||
      !Number.isInteger(maxReferences) || maxReferences < 1 || maxReferences > 512)
    throw new Error('math_knowledge_invalid_dependency_options');
  const root = base.entries.find(item => item.id === id);
  if (!root) throw new Error('math_knowledge_theorem_not_found');
  const index = new Map<string, TheoremKnowledgeEntry[]>();
  const key = (item: TheoremKnowledgeEntry, file = item.file, name = item.name) =>
    JSON.stringify([item.contextDigest, item.environmentDigest ?? null, file, name]);
  for (const item of base.entries) {
    const identity = key(item), versions = index.get(identity) ?? [];
    versions.push(item); index.set(identity, versions);
  }
  const nodes: DependencyNode[] = [], references: DependencyReference[] = [];
  const queue = [{ item: root, depth: 0 }], queued = new Set([root.id]);
  const truncated = { depth: false, nodes: false, references: false, targets: false, tasks: false };
  for (let position = 0; position < queue.length; position++) {
    const current = queue[position]!, item = current.item, files = base.contexts[item.contextDigest]!;
    const tasks = item.dependencies.tasks.slice(0, 8);
    nodes.push({ id: item.id, name: item.name, file: item.file, contextDigest: item.contextDigest,
      environmentDigest: item.environmentDigest, sourceSha256: files[item.file]!, depth: current.depth,
      coverage: item.dependencies.coverage, tasks, tasksTruncated: tasks.length < item.dependencies.tasks.length });
    truncated.tasks ||= tasks.length < item.dependencies.tasks.length;
    if (current.depth >= depth) {
      truncated.depth ||= item.dependencies.statement.length + item.dependencies.proof.length > 0;
      continue;
    }
    for (const kind of ['statement', 'proof'] as const) {
      for (const ref of item.dependencies[kind]) {
        if (references.length >= maxReferences) { truncated.references = true; break; }
        const sourceSha256 = allowedKnowledgeFile(ref.file) ? files[ref.file] : undefined;
        const targets = sourceSha256 ? index.get(key(item, ref.file, ref.name)) ?? [] : [];
        const resolution = !sourceSha256 ? 'missing-source' : targets.length === 1 ? 'indexed' :
          targets.length > 1 ? 'ambiguous' : 'source-available';
        const targetIds = targets.slice(0, 8).map(target => target.id);
        references.push({ from: item.id, kind, file: ref.file, name: ref.name, resolution,
          targetIds, targetsTruncated: targets.length > targetIds.length,
          ...(sourceSha256 ? { source: { theoremId: item.id, file: ref.file, sha256: sourceSha256 } } : {}) });
        truncated.targets ||= targets.length > targetIds.length;
        if (resolution !== 'indexed' || queued.has(targets[0]!.id)) continue;
        if (queue.length >= maxNodes) { truncated.nodes = true; continue; }
        queued.add(targets[0]!.id); queue.push({ item: targets[0]!, depth: current.depth + 1 });
      }
    }
  }
  return { schema: 'theorem-os.theorem-knowledge-dependencies.v1', evidence: base.evidence, requiresFreshCheck: true,
    rootId: root.id, nodes, references, truncated,
    hasUnavailableDependencies: nodes.some(node => node.coverage === 'unavailable'),
    interpretation: 'Recorded references are advisory. source-available identifies an archived file, not a resolved declaration. Missing coverage is unknown, not an empty dependency set. Only identical complete contexts and environments are linked; check all applications with Lean.' };
}
