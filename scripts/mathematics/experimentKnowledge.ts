import fs from 'node:fs';
import path from 'node:path';
import { z } from 'zod';
import { copyKnowledgeSnapshot, readKnowledgeCatalog } from '../../src/solver/theoremKnowledgeStore';
import { inspectScopedLeanDeclarations } from '../../src/math/leanSource';

export const experimentKnowledgeSchema = z.object({
  file: z.string().min(1), digest: z.string().regex(/^[a-f0-9]{64}$/u), format: z.enum(['v1', 'v2']),
  mode: z.enum(['transfer', 'recovery']),
}).strict();
export type ExperimentKnowledge = z.infer<typeof experimentKnowledgeSchema>;

export function experimentKnowledgeMode(flags: ReadonlyMap<string, string>): ExperimentKnowledge['mode'] {
  const mode = flags.get('knowledge-mode') ?? 'transfer';
  if (mode !== 'transfer' && mode !== 'recovery') throw new Error('invalid --knowledge-mode');
  if (flags.has('knowledge-mode') && !flags.has('knowledge-base'))
    throw new Error('--knowledge-mode requires --knowledge-base');
  return mode;
}

/** Every attempt uses these saved bytes, including the catalog's content-addressed sources. */
export function freezeExperimentKnowledge(directory: string, sourceFile: string, mode: ExperimentKnowledge['mode']): ExperimentKnowledge {
  const knowledge = readKnowledgeCatalog(sourceFile), file = path.join(directory, 'knowledge', 'catalog.json');
  copyKnowledgeSnapshot(knowledge, sourceFile, file);
  return { file, digest: knowledge.digest, format: knowledge.format, mode };
}

/** A transfer comparison must not silently become recovery from the target's own archive. */
export function assertExperimentKnowledge(directory: string, value: ExperimentKnowledge | undefined,
  problem?: string, targetNames: readonly string[] = []) {
  if (value === undefined) return;
  const parsed = experimentKnowledgeSchema.safeParse(value);
  if (!parsed.success || parsed.data.file !== path.join(directory, 'knowledge', 'catalog.json'))
    throw new Error('comparison_knowledge_identity_mismatch');
  const knowledge = readKnowledgeCatalog(value.file, value.digest);
  if (knowledge.format !== value.format || (fs.statSync(value.file).mode & 0o222) !== 0)
    throw new Error('comparison_knowledge_identity_mismatch');
  const sameProblemEntries = problem === undefined ? [] : knowledge.base.entries.filter(entry =>
    entry.provenance.some(origin => origin.problemId === problem) || targetNames.includes(entry.name));
  const sameProblemFindings = problem === undefined ? [] : (knowledge.base.routeFindings ?? []).filter(item => item.scope.problemId === problem);
  const targets = new Set(targetNames), sameTargetSourceDeclarations = new Set<string>();
  if (targets.size) for (const [digest, source] of Object.entries(knowledge.base.sources)) {
    for (const declaration of inspectScopedLeanDeclarations(source))
      if (targets.has(declaration.qualifiedName)) sameTargetSourceDeclarations.add(`${digest}:${declaration.qualifiedName}`);
  }
  if (value.mode === 'transfer' && (sameProblemEntries.length || sameProblemFindings.length || sameTargetSourceDeclarations.size))
    throw new Error('comparison_transfer_contains_target_knowledge; use --knowledge-mode recovery for same-problem material');
  return { knowledge, observation: { ...value, sameProblemEntries: sameProblemEntries.length,
    sameProblemFindings: sameProblemFindings.length, sameTargetSourceDeclarations: sameTargetSourceDeclarations.size,
    scopeCheck: 'recorded-problem-target-and-source-declaration-identities' as const } };
}
