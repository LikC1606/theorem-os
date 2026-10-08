/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

import type { LeanEvalLeanProbeRequest, LeanEvalLeanProbeResult } from "./leanEvalLeanProbe";
import {
  runLeanEvalCounterexampleProbe,
  type LeanEvalCounterexampleProbe,
  type ProbeValueMode,
} from "./leanEvalCounterexampleProbe";

export type LeanEvalSanityProbe = LeanEvalCounterexampleProbe;

/**
 * Run bounded executable probes for a computable Lean expression. This is
 * diagnostic evidence only; it never substitutes for a kernel proof.
 */
export async function runLeanEvalSanityProbe(
  options: Readonly<{
    projectRoot: string;
    expression: string;
    precondition?: string;
    mode?: ProbeValueMode;
    cases?: readonly string[];
    imports?: readonly string[];
    timeoutMs?: number;
    signal?: AbortSignal;
    env?: NodeJS.ProcessEnv;
    lakePackagesPath?: string;
    runProbe?: (request: LeanEvalLeanProbeRequest) => Promise<LeanEvalLeanProbeResult>;
  }>
): Promise<LeanEvalSanityProbe> {
  if (!options.expression.trim() || options.expression.length > 2_000) {
    return Promise.resolve(
      Object.freeze({
        attempted: false,
        outcome: 'inconclusive',
        casesChecked: 0,
        diagnostics: ['expression is empty or too large'],
      })
    );
  }
  return runLeanEvalCounterexampleProbe({
    ...options,
    expression:
      options.mode === 'boolean'
        ? `fun sample => !((${options.expression}) sample)`
        : `fun sample => ¬ ((${options.expression}) sample)`,
  });
}
