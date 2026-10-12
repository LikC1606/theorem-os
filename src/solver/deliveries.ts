import fs from 'node:fs';
import path from 'node:path';
import { assertMathCanonicalPath } from '../math/paths';
import type { ProofCheck } from './modules/evidence';
import type { ProofReferences } from './proofReferences';

/** One response format; legacy fences keep existing workspaces resumable. */
export function readMathResponse(worktree: string, legacyFence: string, bindings: Record<string, unknown> = {}): any {
  const file = path.join(worktree, 'RESEARCH.md');
  const errorPrefix = legacyFence === 'math-lemma' ? 'math_lemma_plan' : `math_${legacyFence}`;
  if (!fs.existsSync(file) || fs.statSync(file).size > 64_000) throw new Error(`${errorPrefix}_missing_or_too_large`);
  const blocks = [...fs.readFileSync(file, 'utf8').matchAll(new RegExp('```(?:math|' + legacyFence + ')\\s*\\n([\\s\\S]*?)\\n```', 'gu'))];
  if (blocks.length !== 1) throw new Error(`${errorPrefix}_requires_one_block`);
  const value = JSON.parse(blocks[0][1]);
  if (!value || typeof value !== 'object' || Array.isArray(value)) throw new Error('math_response_invalid');
  return { ...bindings, ...value };
}

/** One versioned record for hints, conditional sketches, proofs, reviews and failures. */
export type DeliveryRecord = {
  id: string; submissionId?: string; statementReviewId?: string; producer: string; taskId?: string; taskDigest?: string; groupId?: string;
  kind: 'progress' | 'research' | 'proof' | 'review' | 'backtranslation' | 'statement-review' | 'failure';
  status: 'advisory' | 'conditional' | 'verified' | 'failed' | 'superseded' | 'accepted' | 'changes_requested';
  statement: string; premises: readonly string[];
  dependencies: { taskId: string; taskDigest: string }[]; remainingObligations: readonly string[];
  summary: string; evidenceRefs: readonly string[]; createdAt: number; commit?: string; sourceDigest?: string;
  evidence?: Pick<ProofCheck, 'passed' | 'verification'>;
  actualReferences?: ProofReferences;
};

export function deliveryDetails(value: any): Pick<DeliveryRecord, 'summary' | 'evidenceRefs'> &
  Partial<Pick<DeliveryRecord, 'statement' | 'premises' | 'remainingObligations'>> {
  const strings = (items: unknown, max: number, length: number) => Array.isArray(items) && items.length <= max &&
    items.every(item => typeof item === 'string' && item.length <= length);
  if (!value || typeof value.summary !== 'string' || value.summary.length > 3000 || !strings(value.evidenceRefs ?? [], 16, 1000) ||
      (value.statement !== undefined && (typeof value.statement !== 'string' || !value.statement.trim() || value.statement.length > 8000)) ||
      (value.premises !== undefined && !strings(value.premises, 32, 2000)) ||
      (value.remainingObligations !== undefined && !strings(value.remainingObligations, 32, 2000))) throw new Error('math_delivery_invalid');
  return { summary: value.summary, evidenceRefs: value.evidenceRefs ?? [],
    ...(value.statement === undefined ? {} : { statement: value.statement }),
    ...(value.premises === undefined ? {} : { premises: value.premises }),
    ...(value.remainingObligations === undefined ? {} : { remainingObligations: value.remainingObligations }) };
}

/** Read complete appended lines only. The durable cursor survives restarts and partial writes. */
export function readDeliveryLines(file: string, offset: number): { lines: string[]; offset: number } {
  if (!fs.existsSync(file)) return { lines: [], offset };
  assertMathCanonicalPath(file);
  const fd = fs.openSync(file, fs.constants.O_RDONLY | fs.constants.O_NOFOLLOW);
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
