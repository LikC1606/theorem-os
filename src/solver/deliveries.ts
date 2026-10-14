import fs from 'node:fs';
import path from 'node:path';
import { assertMathCanonicalPath } from '../math/paths';
import { readMathText } from '../math/mathRuntimeIo';
import type { ProofCheck } from './modules/evidence';
import type { ProofReferences } from './proofReferences';

/** JSON for host decisions, optional Markdown for explanations; legacy fences remain readable. */
export function readMathResponse(worktree: string, legacyFence: string, bindings: Record<string, unknown> = {}, textField?: string): any {
  const file = path.join(worktree, 'RESEARCH.md');
  const errorPrefix = legacyFence === 'math-lemma' ? 'math_lemma_plan' : `math_${legacyFence}`;
  let text: string;
  try { assertMathCanonicalPath(file); text = readMathText(file).trim(); }
  catch { throw new Error(`${errorPrefix}_missing_or_too_large`); }
  const blocks = [...text.matchAll(new RegExp('```(?:math|json|' + legacyFence + ')\\s*\\n([\\s\\S]*?)\\n```', 'gu'))]
    .filter(block => !textField || block[1].trimStart().startsWith('{'));
  if (blocks.length > 1) throw new Error(`${errorPrefix}_requires_one_block`);
  const value = text.startsWith('{') ? JSON.parse(text) : blocks.length === 1 ? JSON.parse(blocks[0][1]) :
    textField && text ? { [textField]: text } : undefined;
  if (value === undefined) throw new Error(`${errorPrefix}_requires_one_block`);
  if (!value || typeof value !== 'object' || Array.isArray(value)) throw new Error('math_response_invalid');
  return { ...bindings, ...value };
}

export function advisoryEvidenceRefs(value: unknown): string[] {
  return (Array.isArray(value) ? value : [value]).filter((ref): ref is string => typeof ref === 'string');
}

export function reviewVerdict(value: unknown, errorCode: string): 'accepted' | 'changes_requested' {
  if (value !== 'accepted' && value !== 'changes_requested') throw new Error(errorCode);
  return value;
}

/** One versioned record for hints, conditional sketches, proofs, reviews and failures. */
export type DeliveryRecord = {
  id: string; submissionId?: string; statementReviewId?: string; producer: string; taskId?: string; taskDigest?: string; groupId?: string;
  kind: 'progress' | 'research' | 'proof' | 'review' | 'backtranslation' | 'statement-review' | 'failure';
  status: 'advisory' | 'conditional' | 'verified' | 'failed' | 'superseded' | 'accepted' | 'changes_requested';
  statement: string; premises: readonly string[];
  dependencies: { taskId: string; taskDigest: string }[]; remainingObligations: readonly string[];
  summary: string; evidenceRefs: readonly string[]; createdAt: number; commit?: string; sourceDigest?: string;
  evidence?: { passed: boolean; verification: Pick<ProofCheck['verification'], 'status' | 'targetCommit'> & { results: { receiptId: string }[] } };
  actualReferences?: ProofReferences;
};

export function deliveryDetails(value: any): Pick<DeliveryRecord, 'summary' | 'evidenceRefs'> &
  Partial<Pick<DeliveryRecord, 'statement' | 'premises' | 'remainingObligations'>> {
  const strings = (items: unknown) => Array.isArray(items) && items.every(item => typeof item === 'string');
  if (!value || (value.summary !== undefined && typeof value.summary !== 'string') ||
      (value.statement !== undefined && (typeof value.statement !== 'string' || !value.statement.trim())) ||
      (value.premises !== undefined && !strings(value.premises)) ||
      (value.remainingObligations !== undefined && !strings(value.remainingObligations))) throw new Error('math_delivery_invalid');
  const summary = value.summary ?? '';
  // The raw response remains in RESEARCH.md; a long advisory note does not invalidate its verdict or evidence.
  return { summary: summary.length <= 3000 ? summary : summary.slice(0, 2999).replace(/[\uD800-\uDBFF]$/u, '') + '…', evidenceRefs: advisoryEvidenceRefs(value.evidenceRefs),
    ...(value.statement === undefined ? {} : { statement: value.statement }),
    ...(value.premises === undefined ? {} : { premises: value.premises }),
    ...(value.remainingObligations === undefined ? {} : { remainingObligations: value.remainingObligations }) };
}

/** Read complete appended lines only. The durable cursor survives restarts and partial writes. */
export function readDeliveryLines(file: string, offset: number): { lines: string[]; offset: number } {
  if (!Number.isSafeInteger(offset) || offset < 0) throw new Error('math_delivery_log_invalid');
  if (!fs.existsSync(file)) return { lines: [], offset };
  assertMathCanonicalPath(file);
  const fd = fs.openSync(file, fs.constants.O_RDONLY | fs.constants.O_NOFOLLOW | fs.constants.O_NONBLOCK);
  try {
    const stat = fs.fstatSync(fd);
    if (!stat.isFile() || stat.nlink !== 1 || stat.size < offset) throw new Error('math_delivery_log_invalid');
    const buffer = Buffer.alloc(Math.min(stat.size - offset, 64_000));
    const size = fs.readSync(fd, buffer, 0, buffer.length, offset);
    const end = buffer.subarray(0, size).lastIndexOf(10);
    if (end < 0) {
      if (size === 64_000) throw new Error('math_delivery_line_too_large');
      return { lines: [], offset };
    }
    return { lines: buffer.subarray(0, end).toString('utf8').split('\n').filter(line => line.trim()), offset: offset + end + 1 };
  } finally { fs.closeSync(fd); }
}
