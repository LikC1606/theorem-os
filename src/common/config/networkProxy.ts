/** Copyright 2026 DeepScientist contributors. SPDX-License-Identifier: Apache-2.0 */
export type NetworkProxyMode = 'system' | 'direct' | 'manual';
export interface NetworkProxyConfig {
    mode: NetworkProxyMode;
    server?: string;
    bypassRules?: string;
}
