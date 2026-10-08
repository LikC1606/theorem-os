/**
 * @license
 * Copyright 2026 DeepScientist (deepscientist.cc)
 * SPDX-License-Identifier: Apache-2.0
 */

export type TargetDiscoveryToolResult = {
  content?: Array<{ type?: string; text?: string }>;
  structuredContent?: unknown;
  isError?: boolean;
  [key: string]: unknown;
};

export type TargetDiscoverySemanticFailure = {
  failed: boolean;
  reasons: string[];
};

export const TARGET_DISCOVERY_BATCH_LIMIT = 20;
export const TARGET_DISCOVERY_BATCH_CONCURRENCY = 4;

const FAILURE_STATUSES = new Set(['error', 'failed']);
const ENVELOPE_KEYS = ['result', 'response', 'payload', 'data'] as const;

const safeJsonParse = (value: string): unknown => {
  try {
    return JSON.parse(value);
  } catch {
    return undefined;
  }
};

const hasErrorValue = (value: unknown): boolean => {
  if (value == null || value === false || value === 0) return false;
  if (typeof value === 'string') return value.trim().length > 0;
  if (Array.isArray(value)) return value.length > 0;
  if (typeof value === 'object') return Object.keys(value).length > 0;
  return true;
};

const inspectEnvelope = (value: unknown, path: string, reasons: Set<string>, depth = 0): void => {
  if (!value || typeof value !== 'object' || Array.isArray(value) || depth > 3) return;
  const record = value as Record<string, unknown>;

  if (Object.prototype.hasOwnProperty.call(record, 'error') && hasErrorValue(record.error)) {
    reasons.add(`${path}.error`);
  }
  if (record.success === false) reasons.add(`${path}.success=false`);
  if (record.ok === false) reasons.add(`${path}.ok=false`);
  if (typeof record.status === 'string' && FAILURE_STATUSES.has(record.status.trim().toLowerCase())) {
    reasons.add(`${path}.status=${record.status.trim().toLowerCase()}`);
  }

  for (const key of ENVELOPE_KEYS) {
    if (record[key] && typeof record[key] === 'object' && !Array.isArray(record[key])) {
      inspectEnvelope(record[key], `${path}.${key}`, reasons, depth + 1);
    }
  }
};

/** Detect transport errors and JSON-level failure envelopes without scanning domain records. */
export const detectTargetDiscoverySemanticFailure = (
  result: TargetDiscoveryToolResult
): TargetDiscoverySemanticFailure => {
  const reasons = new Set<string>();
  if (result.isError) reasons.add('mcp.isError=true');

  inspectEnvelope(result, 'mcp', reasons);
  inspectEnvelope(result.structuredContent, 'structuredContent', reasons);
  for (const [index, item] of (result.content || []).entries()) {
    if (item.type !== 'text' || !item.text?.trim()) continue;
    const parsed = safeJsonParse(item.text);
    inspectEnvelope(parsed, `content[${index}]`, reasons);
  }

  return { failed: reasons.size > 0, reasons: [...reasons] };
};

export const assessTargetDiscoveryToolResult = (result: TargetDiscoveryToolResult) => {
  const semanticFailure = detectTargetDiscoverySemanticFailure(result);
  return {
    ok: !semanticFailure.failed,
    evidenceStatus: semanticFailure.failed ? ('needs_review' as const) : ('available' as const),
    failure: semanticFailure.failed ? { kind: 'tool_result' as const, reasons: semanticFailure.reasons } : undefined,
    warnings: semanticFailure.failed
      ? semanticFailure.reasons.map((reason) => `Origene tool failure signal: ${reason}.`)
      : undefined,
  };
};

/** Promise.allSettled semantics with bounded concurrency and input-order results. */
export const mapSettledWithConcurrency = async <Input, Output>(
  items: readonly Input[],
  concurrency: number,
  mapper: (item: Input, index: number) => Promise<Output>
): Promise<Array<PromiseSettledResult<Output>>> => {
  if (!Number.isInteger(concurrency) || concurrency < 1) {
    throw new Error('concurrency must be a positive integer.');
  }
  const results = new Array<PromiseSettledResult<Output>>(items.length);
  let nextIndex = 0;

  const worker = async (): Promise<void> => {
    while (nextIndex < items.length) {
      const index = nextIndex;
      nextIndex += 1;
      try {
        results[index] = { status: 'fulfilled', value: await mapper(items[index] as Input, index) };
      } catch (reason) {
        results[index] = { status: 'rejected', reason };
      }
    }
  };

  const workerCount = Math.min(concurrency, items.length);
  await Promise.all(Array.from({ length: workerCount }, () => worker()));
  return results;
};
