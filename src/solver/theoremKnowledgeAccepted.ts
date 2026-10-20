import fs from 'node:fs';
import path from 'node:path';
import { z } from 'zod';
import { canonicalMathJson, mathDigest, readMathFile } from '../math/mathRuntimeIo';
import { assertMathCanonicalPath } from '../math/paths';
import { inspectLeanDeclarationRegions, inspectScopedLeanDeclarations } from '../math/leanSource';
import { allowedKnowledgeFile, knowledgeDeclaration, type KnowledgeCandidate, type KnowledgeImportResult } from './theoremKnowledge';
import { applyKnowledgeEnrichment, readKnowledgeEnrichment } from './theoremKnowledgeEnrichment';

const digest = z.string().regex(/^[a-f0-9]{64}$/u);
const commit = z.string().regex(/^[a-f0-9]{40,64}$/u);
const evidenceValidation = z.object({ signatureValid: z.literal(true), solverStateUnchanged: z.literal(true),
  solverAndOfficialProjectionBytesIdentical: z.literal(true), frozenDependencyFilesIdentical: z.literal(true) }).strict();
const archiveRecord = z.object({
  problem_id: z.string().min(1).max(256), directory: z.string().min(1).max(1024),
  source_sha256: z.record(z.string(), digest).refine(value => Object.keys(value).length > 0 && Object.keys(value).length <= 4096),
  original_source_commit: commit,
  statement_revision: z.number().int().positive().optional(), model: z.string().optional(),
  submission_url: z.string().url().optional(), result_reported_at: z.string().datetime().optional(),
  result_body: z.string().optional(), original_source_url: z.string().url().optional(),
});
const localVerification = z.object({ evidence_file: z.literal('verification.json'), scope: z.literal('local_official_comparator'),
  command: z.literal('lake test'), exit_code: z.literal(0), receipt_id: z.string().min(1).max(256),
  checked_at: z.string().datetime(), solver_commit: commit, official_projection_commit: commit,
  official_baseline_commit: commit, evidence_validation: evidenceValidation }).strict();
const acceptedRecord = archiveRecord.extend({ status: z.literal('official_accepted'), result_url: z.string().url().max(4096) }).strict();
const submittedRecord = archiveRecord.extend({ status: z.literal('local_verified_pending_official'),
  workflow_url: z.string().url().optional(), local_verification: localVerification }).strict();
const acceptedManifest = z.array(z.discriminatedUnion('status', [acceptedRecord, submittedRecord])).min(1).max(1024);
const localEvidence = z.object({ schema: z.literal('theoremos.lean-eval-submission-provenance.v1'),
  problem: z.object({ problemId: z.string(), statementRevision: z.number().int().positive(), solverCommit: commit,
    officialProjectionCommit: commit,
    files: z.record(z.string(), z.object({ sha256: digest, bytes: z.number().int().nonnegative() }).strict()),
    localEvidenceValidation: evidenceValidation,
    localOfficialReceipt: z.object({ receiptId: z.string(), status: z.literal('official_verified'), exitCode: z.literal(0),
      timedOut: z.literal(false), verifier: z.literal('official-comparator'), command: z.literal('lake test'),
      problemId: z.string(), targetCommit: commit, officialBaselineCommit: commit, proofHash: digest,
      checkedAt: z.number().int().nonnegative() }).passthrough(),
  }).passthrough(),
}).passthrough();

const maxSourceBytes = 16 * 1024 * 1024;
const maxArchiveBytes = 256 * 1024 * 1024;
const auxiliaryFiles = new Set(['README.md', 'verification.json', 'compatibility-verification.json']);
const forbiddenSegment = /^(?:solution\.lean|(?:.*[-_])?(?:auth|credentials?|secrets?|tokens?|passwords?|env(?:ironment)?|sessions?|journals?|transcripts?)(?:[-_.].*)?)$/iu;
const safeRelative = (file: string) => Boolean(file && !path.posix.isAbsolute(file) && !file.includes('\\') && !file.includes('\0') &&
  file.split('/').every(part => part && part !== '.' && part !== '..' && !part.startsWith('.') && !forbiddenSegment.test(part)));

/** Import historical official or local comparator archives without granting current proof acceptance. */
export function importAcceptedKnowledge(manifestFile: string, options: { enrichmentFile?: string } = {}): KnowledgeImportResult {
  const file = path.resolve(manifestFile);
  if (!['accepted.json', 'submitted.json'].includes(path.basename(file))) throw new Error('math_knowledge_accepted_manifest_invalid');
  assertMathCanonicalPath(file);
  const manifestBytes = readMathFile(file, 16 * 1024 * 1024).bytes;
  let value: unknown;
  try { value = JSON.parse(new TextDecoder('utf-8', { fatal: true }).decode(manifestBytes)); }
  catch { throw new Error('math_knowledge_accepted_manifest_invalid'); }
  const parsed = acceptedManifest.safeParse(value);
  if (!parsed.success) throw new Error('math_knowledge_accepted_manifest_invalid');
  const records = parsed.data, root = path.dirname(file), sourceDigest = mathDigest(manifestBytes);
  if (records.some(record => (path.basename(file) === 'accepted.json') !== (record.status === 'official_accepted')))
    throw new Error('math_knowledge_accepted_manifest_status_mismatch');
  if (new Set(records.map(record => record.problem_id)).size !== records.length ||
      new Set(records.map(record => record.directory)).size !== records.length)
    throw new Error('math_knowledge_accepted_duplicate_problem');

  // Reject every path before opening any archive source, including paths in later records.
  for (const record of records) {
    if (!safeRelative(record.directory)) throw new Error('math_knowledge_accepted_forbidden_path');
    if (record.status === 'local_verified_pending_official' && !Object.hasOwn(record.source_sha256, 'verification.json'))
      throw new Error('math_knowledge_local_verification_missing');
    for (const source of Object.keys(record.source_sha256)) {
      if (!safeRelative(source) || (!allowedKnowledgeFile(source) && !auxiliaryFiles.has(source)))
        throw new Error('math_knowledge_accepted_forbidden_path');
      assertMathCanonicalPath(path.join(root, record.directory, source));
    }
  }

  let totalBytes = manifestBytes.length;
  const snapshots = records.map(record => {
    const files: Record<string, string> = {};
    const identities: Record<string, { sha256: string; bytes: number }> = {};
    let verificationText: string | undefined;
    for (const [source, expected] of Object.entries(record.source_sha256)) {
      const absolute = path.join(root, record.directory, source);
      const size = fs.lstatSync(absolute).size;
      if (size > maxSourceBytes || totalBytes + size > maxArchiveBytes)
        throw new Error('math_knowledge_accepted_source_too_large');
      const bytes = readMathFile(absolute, maxSourceBytes).bytes;
      totalBytes += bytes.length;
      if (totalBytes > maxArchiveBytes) throw new Error('math_knowledge_accepted_source_too_large');
      if (mathDigest(bytes) !== expected) throw new Error('math_knowledge_accepted_source_changed');
      identities[source] = { sha256: expected, bytes: bytes.length };
      if (record.status === 'local_verified_pending_official' && source === 'verification.json')
        verificationText = new TextDecoder('utf-8', { fatal: true }).decode(bytes);
      if (allowedKnowledgeFile(source)) {
        try { files[source] = new TextDecoder('utf-8', { fatal: true, ignoreBOM: true }).decode(bytes); }
        catch { throw new Error('math_knowledge_accepted_source_invalid_utf8'); }
      }
    }
    return { record, files, identities, verificationText };
  });

  for (const { record, files, identities, verificationText } of snapshots) {
    if (record.status !== 'local_verified_pending_official') continue;
    let value: unknown;
    try { value = JSON.parse(verificationText!); }
    catch { throw new Error('math_knowledge_local_verification_invalid'); }
    const parsed = localEvidence.safeParse(value);
    if (!parsed.success) throw new Error('math_knowledge_local_verification_invalid');
    const local = record.local_verification, problem = parsed.data.problem, receipt = problem.localOfficialReceipt;
    if (problem.problemId !== record.problem_id || problem.solverCommit !== local.solver_commit ||
        problem.officialProjectionCommit !== local.official_projection_commit ||
        (record.statement_revision !== undefined && problem.statementRevision !== record.statement_revision) ||
        receipt.problemId !== record.problem_id || receipt.receiptId !== local.receipt_id ||
        receipt.targetCommit !== local.official_projection_commit || receipt.officialBaselineCommit !== local.official_baseline_commit ||
        receipt.checkedAt !== Date.parse(local.checked_at) || receipt.proofHash !== identities['Submission.lean']?.sha256 ||
        Object.keys(problem.files).length !== Object.keys(files).length ||
        Object.entries(problem.files).some(([source, identity]) => !allowedKnowledgeFile(source) ||
          !files[source] || identities[source]?.sha256 !== identity.sha256 || identities[source]?.bytes !== identity.bytes))
      throw new Error('math_knowledge_local_verification_mismatch');
  }

  const candidates: KnowledgeCandidate[] = [], skipped: KnowledgeImportResult['skipped'] = [];
  for (const { record, files } of snapshots) {
    const before = candidates.length;
    for (const [sourceFile, source] of Object.entries(files)) {
      if (!/^Submission(?:[^/]*\.lean|\/.*\.lean)$/u.test(sourceFile)) continue;
      const regions = new Map(inspectLeanDeclarationRegions(source).map(region => [region.startOffset, region]));
      for (const declaration of inspectScopedLeanDeclarations(source).filter(item => item.kind === 'theorem')) {
        const region = regions.get(declaration.startOffset);
        if (!region) continue;
        const name = declaration.qualifiedName;
        knowledgeDeclaration(source, name);
        const headerEnd = source.slice(region.bodyOffset - 2, region.bodyOffset) === ':=' ? region.bodyOffset - 2 : region.bodyOffset;
        candidates.push({ name, file: sourceFile, type: source.slice(region.startOffset, headerEnd).trimEnd(),
          typeKind: 'source-header', kind: 'lemma',
          description: record.status === 'official_accepted'
            ? `Historical declaration from the accepted submission ${record.problem_id}; its recorded official result applies to the submission.`
            : `Historical declaration from locally verified submission ${record.problem_id}; its official result remains pending.`,
          premises: [], dependencies: { statement: [], proof: [], tasks: [], coverage: 'unavailable' }, files,
          provenance: { kind: record.status === 'official_accepted' ? 'accepted-archive' : 'local-verified-archive',
            problemId: record.problem_id, source: file, sourceDigest, sourceCommit: record.original_source_commit,
            archiveRecordDigest: mathDigest(canonicalMathJson(record)),
            ...(record.status === 'official_accepted' ? { receiptIds: [], resultUrl: record.result_url }
              : { receiptIds: [record.local_verification.receipt_id], checkedCommit: record.local_verification.official_projection_commit }) } });
      }
    }
    if (candidates.length === before) skipped.push({ source: file, name: record.problem_id, reason: 'no-submission-theorem-declarations' });
  }
  return { candidates: options.enrichmentFile
    ? applyKnowledgeEnrichment(candidates, readKnowledgeEnrichment(options.enrichmentFile), { manifestFile: file })
    : candidates, skipped };
}
