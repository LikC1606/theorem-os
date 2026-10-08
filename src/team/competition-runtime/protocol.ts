/**
 * @license
 * Copyright 2026 DeepScientist (deepscientist.cc)
 * SPDX-License-Identifier: Apache-2.0
 */

export const IOAI_ENGINE_PROTOCOL_VERSION = 1;

export type CompetitionEngineRequest = {
  protocol_version: typeof IOAI_ENGINE_PROTOCOL_VERSION;
  request_id: string;
  action: string;
  params: Record<string, unknown>;
};

export type CompetitionEngineErrorPayload = {
  code: string;
  message: string;
  retryable: boolean;
  recovery_hint?: string;
  details?: Record<string, unknown>;
};

export type CompetitionEngineResponse =
  | {
      protocol_version: typeof IOAI_ENGINE_PROTOCOL_VERSION;
      request_id: string;
      action: string;
      ok: true;
      result: Record<string, unknown>;
    }
  | {
      protocol_version: typeof IOAI_ENGINE_PROTOCOL_VERSION;
      request_id: string;
      action: string;
      ok: false;
      error: CompetitionEngineErrorPayload;
    };

export class CompetitionEngineProtocolError extends Error {
  readonly code = 'invalid_stdout';

  constructor(message: string) {
    super(message);
    this.name = 'CompetitionEngineProtocolError';
  }
}

export function parseCompetitionEngineResponse(
  raw: string,
  expected: Pick<CompetitionEngineRequest, 'request_id' | 'action'>
): CompetitionEngineResponse {
  let parsed: unknown;
  try {
    parsed = JSON.parse(raw);
  } catch {
    throw new CompetitionEngineProtocolError('engine stdout is not valid JSON');
  }
  if (!isRecord(parsed)) {
    throw new CompetitionEngineProtocolError('engine response must be a JSON object');
  }
  if (parsed.protocol_version !== IOAI_ENGINE_PROTOCOL_VERSION) {
    throw new CompetitionEngineProtocolError('engine protocol version mismatch');
  }
  if (parsed.request_id !== expected.request_id) {
    throw new CompetitionEngineProtocolError('engine response request_id mismatch');
  }
  if (parsed.action !== expected.action) {
    throw new CompetitionEngineProtocolError('engine response action mismatch');
  }
  if (parsed.ok === true) {
    if (!isRecord(parsed.result)) {
      throw new CompetitionEngineProtocolError('successful engine response is missing result');
    }
    return parsed as CompetitionEngineResponse;
  }
  if (parsed.ok !== false || !isEngineError(parsed.error)) {
    throw new CompetitionEngineProtocolError('failed engine response is missing a valid error');
  }
  return parsed as CompetitionEngineResponse;
}

function isEngineError(value: unknown): value is CompetitionEngineErrorPayload {
  if (!isRecord(value)) return false;
  return (
    typeof value.code === 'string' &&
    value.code.length > 0 &&
    typeof value.message === 'string' &&
    typeof value.retryable === 'boolean' &&
    (value.recovery_hint === undefined || typeof value.recovery_hint === 'string') &&
    (value.details === undefined || isRecord(value.details))
  );
}

export function isRecord(value: unknown): value is Record<string, unknown> {
  return !!value && typeof value === 'object' && !Array.isArray(value);
}
