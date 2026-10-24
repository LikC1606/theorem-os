import fs from 'node:fs';
import path from 'node:path';
import { assertMathCanonicalPath } from '../math/paths';
import { mathDigest, readMathText } from '../math/mathRuntimeIo';
import type { ProofCheck } from './modules/evidence';
import type { ProofReferences } from './proofReferences';
import type { DeliveryArtifactManifest } from './deliveryArtifacts';
import type { CooperativeTask } from './tasks';
import type { KnowledgeUse } from './knowledgeUsage';
import type { ResearchRecord } from './researchRecords';
import { mathematicalGapSchema, type MathematicalGap, type MathematicalGapScope } from './mathematicalGaps';

// Long-lived task graphs can exceed a short prompt's display allowance. Keep the
// complete host response bounded by the committed-source reader's byte allowance.
export const MAX_RESEARCH_NOTES_BYTES = 1_000_000;
// Explicit research snapshots carry up to 1 MB of Lean sources alongside the
// complete finding. Allow bounded JSON escaping without rejecting existing files.
export const MAX_DELIVERY_LINE_BYTES = 16_000_000;

/** JSON for host decisions, optional Markdown for explanations; legacy fences remain readable. */
export function readMathResponse(worktree: string, legacyFence: string, bindings: Record<string, unknown> = {}, textField?: string): any {
  const file = path.join(worktree, 'RESEARCH.md');
  const errorPrefix = `math_${legacyFence}`;
  let text: string;
  try { assertMathCanonicalPath(file); text = readMathText(file, MAX_RESEARCH_NOTES_BYTES).trim(); }
  catch { throw new Error(`${errorPrefix}_missing_or_too_large`); }
  return parseMathResponse(text, legacyFence, bindings, textField);
}

/** A research control response is explicit; JSON used to explain mathematics stays prose. */
function researchResponse(text: string, textField?: string): unknown {
  const blocks = [...text.matchAll(/```([a-z-]+)\s*\n([\s\S]*?)\n```/gu)];
  const explicit = blocks.filter(block => block[1] === 'math-result');
  if (explicit.length > 1) throw new Error('math_math-result_requires_one_block');
  if (explicit.length) return JSON.parse(explicit[0][2]);
  // A different control response must never become an ordinary research finding.
  if (/```math-[a-z-]+\s*\n/u.test(text)) throw new Error('math_math-result_requires_one_block');
  if (text.startsWith('{')) return JSON.parse(text);
  const researchKeys = /"(?:summary|conclusion|taskId|taskDigest|mathematicalGap|lemmaRequests|remainingObligations|evidenceRefs|blockers|knowledgeUses|leanChecks)"\s*:/u;
  const legacy = blocks.filter(block => {
    if (!['math', 'json'].includes(block[1]) || !block[2].trimStart().startsWith('{')) return false;
    try {
      const value = JSON.parse(block[2]);
      return value && typeof value === 'object' && !Array.isArray(value) &&
        Object.keys(value).some(key => researchKeys.test(JSON.stringify(key) + ':'));
    } catch { return researchKeys.test(block[2]); }
  });
  if (legacy.length > 1) throw new Error('math_math-result_requires_one_block');
  if (legacy.length) return JSON.parse(legacy[0][2]);
  return textField && text ? { [textField]: text } : undefined;
}

/** Select the Lead control object without counting illustrative mathematical JSON as a plan. */
function planResponse(text: string): unknown {
  const blocks = [...text.matchAll(/```([a-z-]+)\s*\n([\s\S]*?)\n```/gu)];
  const explicit = blocks.filter(block => block[1] === 'math-plan');
  if (explicit.length > 1) throw new Error('math_math-plan_requires_one_block');
  if (explicit.length) return JSON.parse(explicit[0][2]);
  if (/```math-[a-z-]+\s*\n/u.test(text)) throw new Error('math_math-plan_requires_one_block');
  if (text.startsWith('{')) return JSON.parse(text);
  const planKeys = /"(?:tasks|groups|proofRoutes|recovery|handoffDecisions|challengeDecisions|assessments|dispatchNonce|baseVersion)"\s*:/u;
  const legacy = blocks.filter(block => {
    if (!['math', 'json'].includes(block[1]) || !block[2].trimStart().startsWith('{')) return false;
    try {
      const value = JSON.parse(block[2]);
      return value && typeof value === 'object' && !Array.isArray(value) &&
        (Object.keys(value).some(key => planKeys.test(JSON.stringify(key) + ':')) ||
          ['plan', 'handoff', 'assessment'].includes(value.kind));
    } catch { return planKeys.test(block[2]); }
  });
  if (legacy.length > 1) throw new Error('math_math-plan_requires_one_block');
  return legacy.length ? JSON.parse(legacy[0][2]) : undefined;
}

/** The same parser also reads immutable checkpoint text without consulting a live workspace. */
export function parseMathResponse(text: string, legacyFence: string, bindings: Record<string, unknown> = {}, textField?: string): any {
  const errorPrefix = `math_${legacyFence}`;
  text = text.trim();
  if (legacyFence === 'math-result' || legacyFence === 'math-plan') {
    const value = legacyFence === 'math-plan' ? planResponse(text) : researchResponse(text, textField);
    if (value === undefined) throw new Error(errorPrefix + '_requires_one_block');
    if (!value || typeof value !== 'object' || Array.isArray(value)) throw new Error('math_response_invalid');
    return { ...bindings, ...value };
  }
  const blocks = [...text.matchAll(new RegExp('```(?:math|json|' + legacyFence + ')\\s*\\n([\\s\\S]*?)\\n```', 'gu'))]
    .filter(block => !textField || block[1].trimStart().startsWith('{'));
  if (blocks.length > 1) throw new Error(`${errorPrefix}_requires_one_block`);
  // A different control response is not an ordinary Markdown finding.
  if (textField && !blocks.length && /```math-[a-z-]+\s*\n/u.test(text)) throw new Error(`${errorPrefix}_requires_one_block`);
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
  id: string; submissionId?: string; assignmentKey?: string; statementReviewId?: string; producer: string; taskId?: string; taskDigest?: string; groupId?: string;
  kind: 'progress' | 'research' | 'proof' | 'review' | 'backtranslation' | 'statement-review' | 'failure';
  status: 'advisory' | 'conditional' | 'verified' | 'failed' | 'superseded' | 'accepted' | 'changes_requested';
  statement: string; premises: readonly string[];
  dependencies: { taskId: string; taskDigest: string }[]; remainingObligations: readonly string[];
  summary: string; evidenceRefs: readonly string[]; createdAt: number; commit?: string; sourceDigest?: string;
  /** Host identity for the complete advisory finding, separate from the short delivery summary. */
  findingDigest?: string;
  /** Each publication retains its own complete finding, including during an active proof. */
  finding?: string;
  researchRecord?: ResearchRecord;
  knowledgeUses?: readonly KnowledgeUse[];
  mathematicalGap?: MathematicalGap;
  mathematicalGapScope?: MathematicalGapScope;
  evidence?: { passed: boolean; verification: Pick<ProofCheck['verification'], 'status' | 'targetCommit'> & { results: { receiptId: string }[] } };
  actualReferences?: ProofReferences;
  artifacts?: DeliveryArtifactManifest;
  artifactWarning?: string;
  lemmaRequests?: readonly CooperativeTask[];
};

export function deliveryFinding(record: DeliveryRecord, nodeFinding?: string): string | undefined {
  const finding = record.finding ?? nodeFinding;
  return record.kind === 'research' && typeof finding === 'string' && record.findingDigest === mathDigest(finding)
    ? finding : undefined;
}

export function deliveryDetails(value: any): Pick<DeliveryRecord, 'summary' | 'evidenceRefs'> &
  Partial<Pick<DeliveryRecord, 'statement' | 'premises' | 'remainingObligations' | 'mathematicalGap'>> {
  const strings = (items: unknown) => Array.isArray(items) && items.every(item => typeof item === 'string');
  if (!value || (value.summary !== undefined && typeof value.summary !== 'string') ||
      (value.statement !== undefined && (typeof value.statement !== 'string' || !value.statement.trim())) ||
      (value.premises !== undefined && !strings(value.premises)) ||
      (value.remainingObligations !== undefined && !strings(value.remainingObligations)) ||
      (value.mathematicalGap !== undefined && !mathematicalGapSchema.safeParse(value.mathematicalGap).success)) throw new Error('math_delivery_invalid');
  const summary = value.summary ?? '';
  // The raw response remains in RESEARCH.md; a long advisory note does not invalidate its verdict or evidence.
  return { summary: summary.length <= 3000 ? summary : summary.slice(0, 2999).replace(/[\uD800-\uDBFF]$/u, '') + '…', evidenceRefs: advisoryEvidenceRefs(value.evidenceRefs),
    ...(value.statement === undefined ? {} : { statement: value.statement }),
    ...(value.premises === undefined ? {} : { premises: value.premises }),
    ...(value.remainingObligations === undefined ? {} : { remainingObligations: value.remainingObligations }),
    ...(value.mathematicalGap === undefined ? {} : { mathematicalGap: mathematicalGapSchema.parse(value.mathematicalGap) }) };
}

type DeliveryLogEntry = { line?: string; error?: 'math_delivery_line_too_large'; offset: number; discardingOversized: boolean };
type DeliveryLogBatch = { lines: string[]; offset: number; entries?: DeliveryLogEntry[]; discardingOversized?: boolean };

/** Read complete appended lines only. The durable cursor survives restarts and partial writes. */
export function readDeliveryLines(file: string, offset: number,
  recovery?: { discardingOversized: boolean }): DeliveryLogBatch {
  if (!Number.isSafeInteger(offset) || offset < 0) throw new Error('math_delivery_log_invalid');
  if (!fs.existsSync(file)) return { lines: [], offset, entries: [],
    ...(recovery ? { discardingOversized: recovery.discardingOversized } : {}) };
  assertMathCanonicalPath(file);
  const fd = fs.openSync(file, fs.constants.O_RDONLY | fs.constants.O_NOFOLLOW | fs.constants.O_NONBLOCK);
  try {
    const stat = fs.fstatSync(fd);
    if (!stat.isFile() || stat.nlink !== 1 || stat.size < offset) throw new Error('math_delivery_log_invalid');
    const buffer = Buffer.alloc(Math.min(stat.size - offset, MAX_DELIVERY_LINE_BYTES + 1));
    const size = fs.readSync(fd, buffer, 0, buffer.length, offset);
    const entries: DeliveryLogEntry[] = [];
    let start = 0, discarding = recovery?.discardingOversized ?? false;
    // A rejected long line may span several polls; never parse its trailing fragment.
    if (discarding) {
      const newline = buffer.subarray(0, size).indexOf(10);
      if (newline < 0) return { lines: [], offset: offset + size, entries, discardingOversized: true };
      start = newline + 1; discarding = false;
    }
    while (start < size) {
      const newline = buffer.subarray(0, size).indexOf(10, start);
      if (newline < 0) {
        if (start === 0 && size > MAX_DELIVERY_LINE_BYTES) {
          if (!recovery) throw new Error('math_delivery_line_too_large');
          start = size; discarding = true;
          entries.push({ error: 'math_delivery_line_too_large', offset: offset + start, discardingOversized: true });
        }
        break;
      }
      const line = buffer.subarray(start, newline).toString('utf8');
      start = newline + 1;
      entries.push({ line, offset: offset + start, discardingOversized: false });
    }
    return { lines: entries.flatMap(entry => entry.line?.trim() ? [entry.line] : []), offset: offset + start,
      entries, ...(recovery ? { discardingOversized: discarding } : {}) };
  } finally { fs.closeSync(fd); }
}
