/** Copyright 2026 DeepScientist contributors. SPDX-License-Identifier: Apache-2.0 */
export const MODE_STACK_SCHEMA = 'deepscientist.mode_stack.v1' as const;
export type ModePluginId = 'science' | 'medical-evidence' | 'ioai-competition' | 'skill-deposition' | 'financial' | 'financial-factor-mining' | 'factor-research' | 'alpha-dojo-finance' | 'financial-factor' | 'loop-goal' | 'target-discovery' | 'mathematical-research' | (string & {});
export type ModeStack = {
    schema: typeof MODE_STACK_SCHEMA;
    primary: ModePluginId | 'standard';
    overlays: ModePluginId[];
};
