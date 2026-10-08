/** Copyright 2026 DeepScientist contributors. SPDX-License-Identifier: Apache-2.0 */
export const PERFORMANCE_PROFILES = ['high', 'balanced', 'low'] as const;
export type PerformanceProfile = (typeof PERFORMANCE_PROFILES)[number];
