/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

export const LEAN_EVAL_FAILURE_CATEGORIES = [
  'wrong_problem_id',
  'stale_benchmark_commit',
  'statement_revision_mismatch',
  'trusted_file_changed',
  'submission_namespace_mismatch',
  'missing_hole',
  'import_or_olean_mismatch',
  'toolchain_unavailable',
  'comparator_failure',
  'landrun_failure',
  'nanoda_failure',
  'actual_proof_failure',
] as const;
export type LeanEvalFailureCategory = (typeof LEAN_EVAL_FAILURE_CATEGORIES)[number];

export type LeanEvalRetryDecision = Readonly<{
  retryable: boolean;
  action:
    | 'repair_identity'
    | 'refresh_benchmark'
    | 'restore_trusted_files'
    | 'complete_submission'
    | 'repair_imports'
    | 'prepare_toolchain'
    | 'retry_sandbox'
    | 'inspect_comparator'
    | 'repair_proof';
}>;

type StructuredLeanDiagnostic = Readonly<{
  message?: unknown;
  data?: unknown;
  errorMessage?: unknown;
  stderr?: unknown;
  kind?: unknown;
  code?: unknown;
  severity?: unknown;
  errorCode?: unknown;
}>;

/** Preserve structured Lean/JSON diagnostics before falling back to text. */
function diagnosticText(error: unknown): string {
  if (typeof error === 'string') return error;
  if (error instanceof Error) return error.message;
  if (error && typeof error === 'object') {
    const value = error as StructuredLeanDiagnostic;
    return [
      value.kind,
      value.code,
      value.errorCode,
      value.severity,
      value.message,
      value.data,
      value.errorMessage,
      value.stderr,
    ]
      .filter((item): item is string | number => typeof item === 'string' || typeof item === 'number')
      .join('\n');
  }
  return String(error);
}

export type LeanEvalFailureClassification = Readonly<{
  category: LeanEvalFailureCategory;
  diagnosticText: string;
  structured: boolean;
}>;

/** Probes retain JSON-lines; ignore source locations, but preserve explicit error codes. */
function classificationText(message: string): string {
  return message
    .split(/\r?\n/u)
    .map((line) => {
      try {
        const diagnostic: unknown = JSON.parse(line);
        if (!diagnostic || typeof diagnostic !== 'object' || Array.isArray(diagnostic)) return line;
        const entry = diagnostic as Record<string, unknown>;
        if (entry.severity !== 'error' || typeof entry.data !== 'string') return line;
        return [entry.code, entry.errorCode, entry.kind, entry.data]
          .filter((part): part is string => typeof part === 'string')
          .join('\n');
      } catch {
        return line;
      }
    })
    .join('\n')
    .toLowerCase();
}

/** Deterministically separates evaluator/infrastructure faults from proof failure. */
export function classifyLeanEvalFailure(error: unknown): LeanEvalFailureCategory {
  const message = diagnosticText(error);
  const normalized = classificationText(message);
  // Require a diagnostic headed by the facility and an actual failure. A
  // facility's name in an identifier, goal or local context is not evidence
  // that its process failed. Do not discard explicit errors in mixed output.
  const failure =
    /\b(?:fail(?:ed|ure)?|error|unavailable|unsupported|denied|not permitted|not supported|not installed|not found|could not|cannot|did not|requires|exited|killed)\b/u;
  const facilityFailed = (header: RegExp): boolean =>
    normalized.split('\n').some((line) => header.test(line.trim()) && failure.test(line));
  if (/wrong problem|problem id|unknown problem|not in (?:the )?catalog/u.test(normalized)) return 'wrong_problem_id';
  if (
    /stale (?:benchmark|baseline|checkout|revision|commit)|baseline commit|benchmark.*commit|revision.*mismatch|pinned.*commit/u.test(
      normalized
    )
  )
    return 'stale_benchmark_commit';
  if (/statement revision|statement.*mismatch|hash.*mismatch/u.test(normalized)) return 'statement_revision_mismatch';
  if (
    /trusted file|workspace.*changed|protected.*file|protected (?:solution|challenge)\.lean|(?:challenge|solution)\.lean.*(?:changed|modified|mismatch)/u.test(
      normalized
    )
  )
    return 'trusted_file_changed';
  if (/namespace submission|submission namespace|outside the allowed/u.test(normalized))
    return 'submission_namespace_mismatch';
  if (/missing.*hole|hole.*missing|configured holes/u.test(normalized)) return 'missing_hole';
  // Machine codes and host setup diagnostics describe execution capability,
  // even when the message has no conventional "failed" verb. Keep matching
  // anchored to diagnostic headers: these names may also occur in Lean terms.
  if (
    /^(?:error:\s*)?sandbox_unavailable(?:$|[\s:])/mu.test(normalized) ||
    normalized
      .split('\n')
      .some(
        (line) =>
          /^(?:error:\s*)?(?:(?:lean\s+)?sandbox\b|sealed proof environments?\b|private workspace packages\b|lean environment lease\b)/u.test(
            line.trim()
          ) && /\b(?:mismatch|missing|changed|require[sd]?|must|cannot|cancelled|exceeded)\b/u.test(line)
      )
  )
    return 'landrun_failure';
  // Lean search/resource diagnostics describe the candidate, not sandbox health.
  if (
    /(?:maximum (?:number of )?heartbeats|maxheartbeats|deterministic timeout|maxrecdepth|maximum recursion depth|deep recursion|tactic.*(?:timed?\s*out|timeout)|(?:timed?\s*out|timeout).*tactic)/u.test(
      normalized
    )
  )
    return 'actual_proof_failure';
  if (
    /(?:unknown module prefix|failed to import|(?:import|module|object file|\.olean)\b[^\n]*(?:not found|does not exist|missing|mismatch|incompatible|failed))/u.test(
      normalized
    )
  )
    return 'import_or_olean_mismatch';
  if (
    /^(?:error:\s*)?(?:(?:lean|lake|landrun|sandbox|process|operation|request|command)\b[^\n]*)?(?:timed?\s*out|timeout)\b/mu.test(
      normalized
    )
  )
    return 'landrun_failure';
  if (
    facilityFailed(
      /^(?:error:\s*)?(?:(?:(?:lean|lake)\s+)?(?:toolchain|executable)\b|(?:lean|lake)\s+(?:is\s+)?(?:unavailable|not found)\b)/u
    )
  )
    return 'toolchain_unavailable';
  if (facilityFailed(/^(?:error:\s*)?(?:official\s+)?comparator\b/u)) return 'comparator_failure';
  if (
    facilityFailed(
      /^(?:error:\s*)?(?:(?:secure|lean|linux|the|required)\s+)*(?:landrun|landlock|namespace|sandbox|unshare|bwrap)\b/u
    ) ||
    /^(?:landrun|landlock|sandbox|namespace)_(?:failure|error|unavailable)$/mu.test(normalized) ||
    /^no (?:supported linux sandbox backend|namespace sandbox) is installed\b/mu.test(normalized) ||
    /^lean verification capability unavailable:[^\n]*sandbox/mu.test(normalized) ||
    /^(?:failed|unable) to (?:create|enter|unshare)[^\n]*\bnamespace\b/mu.test(normalized)
  )
    return 'landrun_failure';
  if (facilityFailed(/^(?:error:\s*)?nanoda\b/u)) return 'nanoda_failure';
  return 'actual_proof_failure';
}

/** Return classification provenance so callers can avoid treating opaque diagnostics as proof facts. */
export function classifyLeanEvalFailureDetailed(error: unknown): LeanEvalFailureClassification {
  return Object.freeze({
    category: classifyLeanEvalFailure(error),
    diagnosticText: diagnosticText(error).slice(0, 12_000),
    structured: Boolean(error && typeof error === 'object' && !(error instanceof Error)),
  });
}

export function leanEvalRetryDecision(category: LeanEvalFailureCategory): LeanEvalRetryDecision {
  switch (category) {
    case 'wrong_problem_id':
      return { retryable: false, action: 'repair_identity' };
    case 'stale_benchmark_commit':
      return { retryable: true, action: 'refresh_benchmark' };
    case 'statement_revision_mismatch':
      return { retryable: false, action: 'repair_identity' };
    case 'trusted_file_changed':
      return { retryable: false, action: 'restore_trusted_files' };
    case 'submission_namespace_mismatch':
      return { retryable: true, action: 'complete_submission' };
    case 'missing_hole':
      return { retryable: true, action: 'complete_submission' };
    case 'import_or_olean_mismatch':
      return { retryable: true, action: 'repair_imports' };
    case 'toolchain_unavailable':
      return { retryable: true, action: 'prepare_toolchain' };
    case 'comparator_failure':
      return { retryable: true, action: 'inspect_comparator' };
    case 'landrun_failure':
      return { retryable: true, action: 'retry_sandbox' };
    case 'nanoda_failure':
      return { retryable: true, action: 'inspect_comparator' };
    case 'actual_proof_failure':
      return { retryable: true, action: 'repair_proof' };
  }
}
