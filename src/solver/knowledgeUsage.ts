import type { KnowledgeContextSnapshot, KnowledgeRetrieval } from './knowledgeContext';
import type { ProofCheck } from './modules/evidence';
import type { ProofReferences } from './proofReferences';
import type { CooperativeTask } from './tasks';
import { taskVersion } from './tasks';
import { z } from 'zod';

export type KnowledgeRetrievalObservation = KnowledgeRetrieval & {
  included: boolean; omissionReason?: string; workerId: string; workerTurn: number; runTurn: number;
  contextDigest: string; at: number;
};
const text = z.string().trim().min(1).max(12000);
const notes = z.array(text).max(32).optional();
export const knowledgeApplicationReportSchema = z.object({
  expression: text, expectedType: text,
  context: z.object({ file: z.string().min(1).max(1000), declaration: z.string().min(1).max(1000) }).strict(),
  arguments: z.array(z.object({ parameter: text, value: text }).strict()).max(32).optional(),
  additionalPremises: notes, typeclassIssues: notes, adaptationSteps: notes, remainingGoals: notes, reconsiderWhen: notes,
}).strict();
export const knowledgeApplicationCheckSchema = z.object({
  status: z.enum(['elaborated', 'failed', 'unavailable']), reason: z.string(),
  authority: z.literal('advisory-application-elaboration'), proofAcceptance: z.literal('not-assessed'),
  consumerCoverage: z.literal('not-assessed'), commit: z.string(), environmentDigest: z.string(),
  sourceSnapshotDigest: z.string().optional(), projectionDigest: z.string().optional(),
  reuseEnvironmentDigest: z.string().optional(),
  diagnosticEnvironmentDigest: z.string().optional(), toolIdentity: z.string().optional(),
  files: z.array(z.object({ file: z.string(), digest: z.string() })).optional(),
  artifact: z.object({ path: z.string(), digest: z.string() }).optional(),
  elaboratedType: z.string().optional(), selectedDeclarationUsed: z.boolean().optional(),
  diagnostic: z.string().max(8000).optional(), reused: z.boolean().optional(),
});
export type KnowledgeApplicationCheck = z.infer<typeof knowledgeApplicationCheckSchema>;
export const knowledgeUseSchema = z.object({
  id: z.string(), catalogDigest: z.string(), consumer: z.object({ taskId: z.string(), taskDigest: z.string() }),
  declaration: z.object({ name: z.string(), file: z.string() }), status: z.enum(['reported-attempt', 'checked-reference']),
  attribution: z.literal('model-reported-origin'), checkedCommit: z.string().optional(), checkedSourceDigest: z.string().optional(),
  application: knowledgeApplicationReportSchema.extend({ check: knowledgeApplicationCheckSchema.optional() }).optional(),
});
export type KnowledgeUse = Readonly<z.infer<typeof knowledgeUseSchema>>;

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
    // An application report is optional telemetry; malformed details cannot discard a valid reference claim.
    const report = item.application === undefined ? undefined : knowledgeApplicationReportSchema.safeParse(item.application);
    if (report && !report.success) rejected++;
    const key = JSON.stringify([item.id, item.declaration.name, item.declaration.file, report?.success ? report.data : null]);
    if (seen.has(key)) continue;
    seen.add(key);
    const references = proof?.references?.proof ?? proof?.verification.results.filter(result =>
      result.theoremName === task.theoremName && result.proofPath === task.proofPath).flatMap(result => result.declarationReferences?.proof ?? []);
    const referenced = proof?.passed && references?.some(reference =>
      reference.name === item.declaration.name && reference.file === item.declaration.file);
    uses.push({ id: item.id, catalogDigest: knowledge.digest, consumer: { taskId: task.id, taskDigest: taskVersion(task) },
      declaration: { name: item.declaration.name, file: item.declaration.file },
      status: referenced ? 'checked-reference' : 'reported-attempt', attribution: 'model-reported-origin',
      ...(report?.success ? { application: report.data } : {}),
      ...(referenced ? { checkedCommit: proof!.commit, checkedSourceDigest: proof!.sourceDigest } : {}) });
  }
  return { uses, rejected: rejected + Math.max(0, value.length - 16) };
}
