import { canonicalMathJson, mathDigest } from '../math/mathRuntimeIo';
import { parseMathResponse } from './deliveries';
import type { DeliveryArtifactManifest } from './deliveryArtifacts';

export type CheckpointCandidate = Readonly<{
  digest: string; status: 'structured-candidate' | 'unclassified-draft';
}>;

const strings = (value: unknown): string[] => Array.isArray(value)
  ? [...new Set(value.filter((item): item is string => typeof item === 'string' && Boolean(item.trim())))].sort() : [];

/** Stable candidate identity excludes prose and file offsets; it never authorizes acceptance or a cutoff. */
export function checkpointCandidate(notes: string, manifest?: DeliveryArtifactManifest): CheckpointCandidate {
  let response: any;
  try { response = parseMathResponse(notes, 'math-result', {}, 'summary'); } catch { /* A checkpoint can be incomplete. */ }
  const artifacts = [...new Set((manifest?.artifacts ?? []).map(artifact => canonicalMathJson({
    kind: artifact.kind, file: artifact.file,
    declarations: artifact.declarations.map(({ name, header, sha256, draft }) => ({ name, header, sha256, draft })),
  })))].sort();
  const evidenceRefs = strings(response?.evidenceRefs), remainingObligations = strings(response?.remainingObligations);
  const proposals = [...new Set((Array.isArray(response?.lemmaRequests) ? response.lemmaRequests : []).flatMap((task: any) =>
    task?.kind === 'lemma' && typeof task.type === 'string' && task.type.trim() ? [canonicalMathJson({
      id: task.id, type: task.type, theoremName: task.theoremName, proofPath: task.proofPath,
      premises: strings(task.premises), dependsOn: strings(task.dependsOn), conditional: Boolean(task.conditional),
    })] : []))].sort();
  const blockers = [...new Set((Array.isArray(response?.blockers) ? response.blockers : []).flatMap((blocker: any) =>
    typeof blocker?.blockerId === 'string' ? [canonicalMathJson({ blockerId: blocker.blockerId })] :
      typeof blocker?.mechanism === 'string' && typeof blocker.scope === 'string' ? [canonicalMathJson({
        mechanism: blocker.mechanism.trim(), scope: blocker.scope.trim(), evidenceRefs: strings(blocker.evidenceRefs),
      })] : []))].sort();
  const structured = artifacts.length + evidenceRefs.length + proposals.length + blockers.length + remainingObligations.length > 0;
  return { digest: mathDigest(canonicalMathJson({ artifacts, evidenceRefs, proposals, blockers, remainingObligations,
    ...(structured && ['supporting', 'refuted', 'inconclusive'].includes(response?.conclusion) ? { conclusion: response.conclusion } : {}) })),
    status: structured ? 'structured-candidate' : 'unclassified-draft' };
}
