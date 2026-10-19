import type { KnowledgeContextSnapshot, KnowledgeRetrieval } from './knowledgeContext';
import type { ProofCheck } from './modules/evidence';
import type { ProofReferences } from './proofReferences';
import type { CooperativeTask } from './tasks';
import { taskVersion } from './tasks';

export type KnowledgeRetrievalObservation = KnowledgeRetrieval & {
  included: boolean; omissionReason?: string; workerId: string; workerTurn: number; runTurn: number;
  contextDigest: string; at: number;
};
export type KnowledgeUse = Readonly<{
  id: string; catalogDigest: string; consumer: { taskId: string; taskDigest: string };
  declaration: { name: string; file: string }; status: 'reported-attempt' | 'checked-reference';
  attribution: 'model-reported-origin'; checkedCommit?: string; checkedSourceDigest?: string;
}>;

/** Optional usage claims cannot reject a proof or establish where a mathematical idea originated. */
export function inspectKnowledgeUses(value: unknown, knowledge: KnowledgeContextSnapshot | undefined,
  task: CooperativeTask, proof?: ProofCheck & { references?: ProofReferences }): { uses: KnowledgeUse[]; rejected: number } {
  if (value === undefined) return { uses: [], rejected: 0 };
  if (!Array.isArray(value)) return { uses: [], rejected: 1 };
  const entries = new Set(knowledge?.base.entries.map(entry => entry.id)), seen = new Set<string>();
  const uses: KnowledgeUse[] = [];
  let rejected = 0;
  for (const item of value.slice(0, 16)) {
    if (!knowledge || !item || item.catalogDigest !== knowledge.digest || typeof item.id !== 'string' || !entries.has(item.id) ||
        !item.declaration || typeof item.declaration.name !== 'string' || !item.declaration.name.trim() ||
        typeof item.declaration.file !== 'string' || !item.declaration.file.trim()) { rejected++; continue; }
    const key = JSON.stringify([item.id, item.declaration.name, item.declaration.file]);
    if (seen.has(key)) continue;
    seen.add(key);
    const references = proof?.references?.proof ?? proof?.verification.results.filter(result =>
      result.theoremName === task.theoremName && result.proofPath === task.proofPath).flatMap(result => result.declarationReferences?.proof ?? []);
    const referenced = proof?.passed && references?.some(reference =>
      reference.name === item.declaration.name && reference.file === item.declaration.file);
    uses.push({ id: item.id, catalogDigest: knowledge.digest, consumer: { taskId: task.id, taskDigest: taskVersion(task) },
      declaration: { name: item.declaration.name, file: item.declaration.file },
      status: referenced ? 'checked-reference' : 'reported-attempt', attribution: 'model-reported-origin',
      ...(referenced ? { checkedCommit: proof!.commit, checkedSourceDigest: proof!.sourceDigest } : {}) });
  }
  return { uses, rejected: rejected + Math.max(0, value.length - 16) };
}
