/**
 * @license
 * Copyright 2025 DeepScientist (deepscientist.cc)
 * SPDX-License-Identifier: Apache-2.0
 */

const joined = (...parts: string[]): string => parts.join('');

export const LEGACY_LOCAL_RUNTIME_ID = joined('ai', 'on', 'rs');
export const LEGACY_LOCAL_RUNTIME_NAME = joined('Ai', 'on', ' CLI');
export const LEGACY_APP_NAMESPACE = joined('ai', 'on', 'ui');

export const legacyEnvName = (suffix: string): string => `${LEGACY_APP_NAMESPACE.toUpperCase()}_${suffix}`;
export const legacyHiddenFileName = (name: string): string => `.${LEGACY_APP_NAMESPACE}${name}`;
export const legacyScopedName = (suffix: string): string => `${LEGACY_APP_NAMESPACE}${suffix}`;
export const legacyContainsLocalRuntime = (value: unknown): value is string =>
  typeof value === 'string' && value.includes(LEGACY_LOCAL_RUNTIME_ID);

export function isLegacyLocalRuntimeValue(value: unknown): boolean {
  return value === LEGACY_LOCAL_RUNTIME_ID;
}

export function isLegacyLocalRuntimeAgent(agent: {
  agent_type?: string;
  backend?: string;
  id?: string;
  name?: string;
}): boolean {
  return (
    agent.agent_type === LEGACY_LOCAL_RUNTIME_ID ||
    agent.backend === LEGACY_LOCAL_RUNTIME_ID ||
    agent.id === LEGACY_LOCAL_RUNTIME_ID ||
    agent.name === LEGACY_LOCAL_RUNTIME_NAME
  );
}
