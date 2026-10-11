/**
 * @license
 * Copyright 2025 DeepScientist (deepscientist.cc)
 * SPDX-License-Identifier: Apache-2.0
 */

const joined = (...parts: string[]): string => parts.join('');

export const LEGACY_APP_NAMESPACE = joined('ai', 'on', 'ui');

export const legacyEnvName = (suffix: string): string => `${LEGACY_APP_NAMESPACE.toUpperCase()}_${suffix}`;
