/**
 * @license
 * Copyright 2026 DeepScientist (deepscientist.cc)
 * SPDX-License-Identifier: Apache-2.0
 */

export interface PaperclipCredentialConfig {
  paperclipApiKey?: string;
  paperclipBaseUrl?: string;
  timeoutMs?: number;
}

export interface PaperclipEnvKeys {
  apiKey: string;
  baseUrl: string;
  timeoutMs: string;
}

const DEFAULT_PAPERCLIP_BASE_URL = 'https://paperclip.gxl.ai';
const DEFAULT_TIMEOUT_MS = 30000;

const nonEmpty = (value?: string): string | undefined => {
  const trimmed = value?.trim();
  return trimmed || undefined;
};

export function resolvePaperclipCredentialFields(
  primary?: PaperclipCredentialConfig,
  fallback?: PaperclipCredentialConfig,
  existingEnv?: Record<string, string>,
  envKeys?: PaperclipEnvKeys,
  defaults?: Partial<Required<Pick<PaperclipCredentialConfig, 'paperclipBaseUrl' | 'timeoutMs'>>>
): Required<Pick<PaperclipCredentialConfig, 'paperclipBaseUrl' | 'timeoutMs'>> &
  Pick<PaperclipCredentialConfig, 'paperclipApiKey'> {
  const apiKey =
    nonEmpty(primary?.paperclipApiKey) ||
    nonEmpty(fallback?.paperclipApiKey) ||
    (envKeys ? nonEmpty(existingEnv?.[envKeys.apiKey]) : undefined);
  const paperclipBaseUrl =
    nonEmpty(primary?.paperclipBaseUrl) ||
    nonEmpty(fallback?.paperclipBaseUrl) ||
    (envKeys ? nonEmpty(existingEnv?.[envKeys.baseUrl]) : undefined) ||
    defaults?.paperclipBaseUrl ||
    DEFAULT_PAPERCLIP_BASE_URL;
  const timeoutMs =
    primary?.timeoutMs ||
    fallback?.timeoutMs ||
    (envKeys ? Number(existingEnv?.[envKeys.timeoutMs]) : undefined) ||
    defaults?.timeoutMs ||
    DEFAULT_TIMEOUT_MS;

  return {
    ...(apiKey ? { paperclipApiKey: apiKey } : {}),
    paperclipBaseUrl,
    timeoutMs,
  };
}

export function applyPaperclipCredentialFallback<T extends PaperclipCredentialConfig>(
  primary: T | undefined,
  fallback?: PaperclipCredentialConfig
): T & Required<Pick<PaperclipCredentialConfig, 'paperclipBaseUrl' | 'timeoutMs'>> {
  const resolved = resolvePaperclipCredentialFields(primary, fallback);
  return {
    ...(primary || ({} as T)),
    ...resolved,
  };
}
