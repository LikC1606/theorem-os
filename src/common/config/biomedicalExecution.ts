/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */
export type BiomedicalExecutionMaxConcurrency = 1 | 2;
export interface BiomedicalExecutionConfig {
    enabled?: boolean;
    maxConcurrency?: BiomedicalExecutionMaxConcurrency;
}
