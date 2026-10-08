/**
 * @license
 * Copyright 2025 DeepScientist (deepscientist.cc)
 * SPDX-License-Identifier: Apache-2.0
 */

import { LEGACY_APP_NAMESPACE, legacyEnvName } from "../common/config/legacyIdentifiers";
import { DS_TEAM_PROJECT_MCP_NAME } from "../common/types/team/dsTeamProject";
import os from 'node:os';
import path from 'node:path';

// Keep this constant local to avoid pulling in common/config/storage side effects
// when the built-in MCP server boots in a standalone stdio process.
export const BUILTIN_IMAGE_GEN_ID = 'builtin-image-gen';
export const BUILTIN_IMAGE_GEN_NAME = 'deepscientist-image-generation';
export const BUILTIN_IMAGE_GEN_LEGACY_NAMES = [
  'DeepScientist Image Generation',
  BUILTIN_IMAGE_GEN_ID,
  `${LEGACY_APP_NAMESPACE}-image-generation`,
  'deepscientist-image-generation',
] as const;
export const BUILTIN_LARK_PROJECT_AGENT_ID = 'builtin-lark-project-agent';
export const BUILTIN_LARK_PROJECT_AGENT_NAME = DS_TEAM_PROJECT_MCP_NAME;
export const BUILTIN_MEDICAL_EVIDENCE_ID = 'builtin-medical-evidence';
export const BUILTIN_MEDICAL_EVIDENCE_NAME = 'deepscientist-medical-evidence';
export const BUILTIN_RESEARCH_EVIDENCE_ID = 'builtin-research-evidence';
export const BUILTIN_RESEARCH_EVIDENCE_NAME = 'deepscientist-research-evidence';
export const BUILTIN_ALPHA_DOJO_FINANCE_ID = 'builtin-alpha-dojo-finance';
export const BUILTIN_ALPHA_DOJO_FINANCE_NAME = 'deepscientist-finance-data';
export const BUILTIN_SCIENCE_ARTIFACT_ID = 'builtin-science-artifact';
export const BUILTIN_SCIENCE_ARTIFACT_NAME = 'deepscientist-science-artifact';
export const BUILTIN_LAB_SKILL_ID = 'builtin-lab-skill';
export const BUILTIN_LAB_SKILL_NAME = 'deepscientist-lab-skill';
export const BUILTIN_USER_INPUT_ID = 'builtin-user-input';
export const BUILTIN_USER_INPUT_NAME = 'deepscientist-user-input';
export const BUILTIN_USER_INPUT_DEFAULT_TIMEOUT_MS = 7 * 24 * 60 * 60_000;
export const BUILTIN_USER_INPUT_MIN_TIMEOUT_MS = BUILTIN_USER_INPUT_DEFAULT_TIMEOUT_MS;
export const BUILTIN_USER_INPUT_MAX_TIMEOUT_MS = 30 * 24 * 60 * 60_000;
export const BUILTIN_USER_INPUT_HEARTBEAT_INTERVAL_MS = 25_000;
export const BUILTIN_USER_INPUT_GATEWAY_STATE_SCHEMA = 'deepscientist.user_input.gateway.v1';
export const BUILTIN_USER_INPUT_GATEWAY_STATE_ENV = 'DEEPSCIENTIST_USER_INPUT_STATE_PATH';
export const BUILTIN_FINANCE_RECEIPT_SECRET_ENV = 'DEEPSCIENTIST_FINANCE_RECEIPT_SECRET';
export const BUILTIN_FINANCE_RECEIPT_KEY_PATH_ENV = 'DEEPSCIENTIST_FINANCE_RECEIPT_KEY_PATH';

export type BuiltinUserInputGatewayState = {
  schema: typeof BUILTIN_USER_INPUT_GATEWAY_STATE_SCHEMA;
  url: string;
  token: string;
  pid: number;
  updatedAt: number;
};

export function resolveBuiltinUserInputGatewayStatePath(explicitPath?: string): string {
  if (explicitPath?.trim()) return explicitPath.trim();
  const isMultiInstance =
    process.env.DEEPSCIENTIST_MULTI_INSTANCE === '1' || process.env[legacyEnvName('MULTI_INSTANCE')] === '1';
  const environment = process.env.NODE_ENV === 'development' ? (isMultiInstance ? 'dev-2' : 'dev') : 'production';
  const identity = (
    process.env.VITEST
      ? `test-${process.pid}`
      : `${String(typeof process.getuid === 'function' ? process.getuid() : process.env.USERNAME || 'user')}-${environment}`
  )
    .replace(/[^a-zA-Z0-9_-]/g, '_')
    .slice(0, 64);
  return path.join(os.tmpdir(), `deepscientist-user-input-${identity}.json`);
}

export function resolveBuiltinFinanceReceiptKeyPath(explicitPath?: string): string {
  if (explicitPath?.trim()) return explicitPath.trim();
  const isMultiInstance =
    process.env.DEEPSCIENTIST_MULTI_INSTANCE === '1' || process.env[legacyEnvName('MULTI_INSTANCE')] === '1';
  const environment = process.env.NODE_ENV === 'development' ? (isMultiInstance ? 'dev-2' : 'dev') : 'production';
  const identity = (
    process.env.VITEST
      ? `test-${process.pid}`
      : `${String(typeof process.getuid === 'function' ? process.getuid() : process.env.USERNAME || 'user')}-${environment}`
  )
    .replace(/[^a-zA-Z0-9_-]/g, '_')
    .slice(0, 64);
  return path.join(os.tmpdir(), `deepscientist-finance-receipt-${identity}.key`);
}

export function resolveBuiltinUserInputTimeoutMs(value: unknown): number {
  const requested = typeof value === 'number' && Number.isFinite(value) ? value : BUILTIN_USER_INPUT_DEFAULT_TIMEOUT_MS;
  return Math.min(BUILTIN_USER_INPUT_MAX_TIMEOUT_MS, Math.max(BUILTIN_USER_INPUT_MIN_TIMEOUT_MS, requested));
}

export function parseBuiltinUserInputGatewayState(value: unknown): BuiltinUserInputGatewayState | undefined {
  if (!value || typeof value !== 'object' || Array.isArray(value)) return undefined;
  const candidate = value as Record<string, unknown>;
  if (
    candidate.schema !== BUILTIN_USER_INPUT_GATEWAY_STATE_SCHEMA ||
    typeof candidate.url !== 'string' ||
    typeof candidate.token !== 'string' ||
    !candidate.token.trim() ||
    typeof candidate.pid !== 'number' ||
    !Number.isInteger(candidate.pid) ||
    candidate.pid <= 0 ||
    typeof candidate.updatedAt !== 'number' ||
    !Number.isFinite(candidate.updatedAt)
  ) {
    return undefined;
  }

  try {
    const url = new URL(candidate.url);
    if (url.protocol !== 'http:' || url.hostname !== '127.0.0.1' || url.pathname !== '/user-input/request') {
      return undefined;
    }
  } catch {
    return undefined;
  }

  return candidate as BuiltinUserInputGatewayState;
}

export function isBuiltinUserInputGatewayProcessAlive(
  pid: number,
  signalProcess: (pid: number, signal: 0) => unknown = process.kill.bind(process)
): boolean {
  try {
    signalProcess(pid, 0);
    return true;
  } catch (error) {
    return (error as NodeJS.ErrnoException).code === 'EPERM';
  }
}

export function isBuiltinImageGenName(name?: string | null): boolean {
  if (!name) return false;
  return (
    name === BUILTIN_IMAGE_GEN_NAME ||
    BUILTIN_IMAGE_GEN_LEGACY_NAMES.includes(name as (typeof BUILTIN_IMAGE_GEN_LEGACY_NAMES)[number])
  );
}

export function isBuiltinImageGenTransport(transport?: {
  type?: string;
  command?: string;
  args?: string[] | null;
}): boolean {
  if (!transport || transport.type !== 'stdio' || transport.command !== 'node') {
    return false;
  }

  return (transport.args || []).some((arg) => typeof arg === 'string' && arg.includes('builtin-mcp-image-gen.js'));
}
