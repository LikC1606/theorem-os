/**
 * @license
 * Copyright 2025 DeepScientist (deepscientist.cc)
 * SPDX-License-Identifier: Apache-2.0
 */

export const CODEX_MODE_READ_ONLY = 'read-only';
export const CODEX_MODE_NATIVE_DEFAULT = 'auto';
export const CODEX_MODE_NATIVE_FULL_ACCESS = 'full-access';
export const CODEX_ACP_MODE_AGENT = 'agent';
export const CODEX_ACP_MODE_AGENT_FULL_ACCESS = 'agent-full-access';

// Legacy DeepScientist values kept for backward compatibility with persisted config.
// Only consumed internally by normalizeCodexMode, no external callers.
const CODEX_MODE_AUTO_EDIT = 'autoEdit';
const CODEX_MODE_FULL_AUTO = 'yolo';
const CODEX_MODE_FULL_AUTO_NO_SANDBOX = 'yoloNoSandbox';

export function normalizeCodexMode(mode?: string | null): string | undefined {
  if (!mode) return undefined;

  switch (mode) {
    case 'default':
    case CODEX_MODE_AUTO_EDIT:
    case CODEX_MODE_NATIVE_DEFAULT:
    case CODEX_ACP_MODE_AGENT:
      return CODEX_MODE_NATIVE_DEFAULT;
    case CODEX_MODE_FULL_AUTO:
    case CODEX_MODE_FULL_AUTO_NO_SANDBOX:
    case CODEX_MODE_NATIVE_FULL_ACCESS:
    case CODEX_ACP_MODE_AGENT_FULL_ACCESS:
      return CODEX_MODE_NATIVE_FULL_ACCESS;
    case CODEX_MODE_READ_ONLY:
      return CODEX_MODE_READ_ONLY;
    default:
      return mode;
  }
}

/** Translate the persisted Codex permission into the value advertised by codex-acp 0.16+. */
export function toCodexAcpMode(mode: string): string {
  switch (normalizeCodexMode(mode)) {
    case CODEX_MODE_NATIVE_DEFAULT:
      return CODEX_ACP_MODE_AGENT;
    case CODEX_MODE_NATIVE_FULL_ACCESS:
      return CODEX_ACP_MODE_AGENT_FULL_ACCESS;
    case CODEX_MODE_READ_ONLY:
      return CODEX_MODE_READ_ONLY;
    default:
      return mode;
  }
}
