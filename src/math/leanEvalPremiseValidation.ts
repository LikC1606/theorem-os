/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

import path from 'node:path';
import type { MathematicsUpstreamPremise } from "../common/chat/mathematics";
import type { LeanEvalLeanProbeRequest, LeanEvalLeanProbeResult } from "./leanEvalLeanProbe";
import { runLeanEvalLeanProbe } from "./leanEvalLeanProbe";

export type LeanPremiseValidation = Readonly<{
  declarationName: string;
  status: 'typed' | 'rejected';
  checkCommand: string;
  targetCompileRequired: true;
  targetProbe?: Readonly<{
    attempted: boolean;
    mode: 'exact' | 'apply';
    ok?: boolean;
    error?: string;
  }>;
  error?: string;
}>;

const validModule = (value: string): boolean => /^[A-Za-z][A-Za-z0-9_.']*$/u.test(value);
type PremiseValidationCacheEntry = Readonly<{
  expiresAt: number;
  value: LeanPremiseValidation;
}>;

const PREMISE_VALIDATION_CACHE_TTL_MS = 60_000;
const PREMISE_VALIDATION_CACHE_MAX_ENTRIES = 512;
const premiseValidationCache = new Map<string, PremiseValidationCacheEntry>();

const premiseValidationCacheKey = (
  premise: MathematicsUpstreamPremise,
  options: Readonly<{
    projectRoot: string;
    importModules?: readonly string[];
    lakeExecutable?: string;
    timeoutMs?: number;
    targetGoal?: string;
    targetProbeMode?: 'exact' | 'apply';
    proofStateFingerprint?: string;
    env?: NodeJS.ProcessEnv;
    lakePackagesPath?: string;
  }>
): string | undefined => {
  const proofStateFingerprint = options.proofStateFingerprint?.trim();
  if (!proofStateFingerprint) return undefined;
  return JSON.stringify([
    path.resolve(options.projectRoot),
    options.lakeExecutable ?? 'lake',
    options.timeoutMs ?? 20_000,
    [...new Set(options.importModules ?? [])].toSorted(),
    premise.sourceModule ?? '',
    premise.declarationName,
    options.targetGoal?.trim() ?? '',
    options.targetProbeMode ?? 'exact',
    proofStateFingerprint,
    premise.source,
    premise.declarationType,
  ]);
};

const cachedPremiseValidation = (key: string): LeanPremiseValidation | undefined => {
  const entry = premiseValidationCache.get(key);
  if (!entry) return undefined;
  if (entry.expiresAt <= Date.now()) {
    premiseValidationCache.delete(key);
    return undefined;
  }
  premiseValidationCache.delete(key);
  premiseValidationCache.set(key, entry);
  return entry.value;
};

const cachePremiseValidation = (key: string, value: LeanPremiseValidation): void => {
  premiseValidationCache.delete(key);
  premiseValidationCache.set(key, Object.freeze({ expiresAt: Date.now() + PREMISE_VALIDATION_CACHE_TTL_MS, value }));
  while (premiseValidationCache.size > PREMISE_VALIDATION_CACHE_MAX_ENTRIES) {
    const oldest = premiseValidationCache.keys().next().value;
    if (oldest === undefined) break;
    premiseValidationCache.delete(oldest);
  }
};

/** Validate a public candidate against the current project's imports with #check. */
export async function validateLeanPremiseCandidate(
  premise: MathematicsUpstreamPremise,
  options: Readonly<{
    projectRoot: string;
    importModules?: readonly string[];
    lakeExecutable?: string;
    timeoutMs?: number;
    /** When supplied, require the candidate to close this exact live Lean goal. */
    targetGoal?: string;
    targetProbeMode?: 'exact' | 'apply';
    /** Reuse a validation within one unchanged live proof frontier. */
    proofStateFingerprint?: string;
    signal?: AbortSignal;
    env?: NodeJS.ProcessEnv;
    lakePackagesPath?: string;
    runProbe?: (request: LeanEvalLeanProbeRequest) => Promise<LeanEvalLeanProbeResult>;
  }>
): Promise<LeanPremiseValidation> {
  const cacheKey = premiseValidationCacheKey(premise, options);
  if (cacheKey) {
    const cached = cachedPremiseValidation(cacheKey);
    if (cached) return cached;
  }
  const modules = [
    ...new Set([...(options.importModules ?? []), ...(premise.sourceModule ? [premise.sourceModule] : [])]),
  ].filter(validModule);
  if (!/^[\p{L}_][\p{L}\p{M}\p{N}_'.]*$/u.test(premise.declarationName)) {
    const rejected = Object.freeze({
      declarationName: premise.declarationName,
      status: 'rejected',
      checkCommand: 'lake env lean <probe>',
      targetCompileRequired: true,
      error: 'invalid declaration name',
    });
    if (cacheKey) cachePremiseValidation(cacheKey, rejected);
    return Promise.resolve(rejected);
  }
  try {
    const targetGoal = options.targetGoal?.trim();
    if (targetGoal && targetGoal.length > 12_000) {
      const rejected = Object.freeze({
        declarationName: premise.declarationName,
        status: 'rejected',
        checkCommand: 'lake env lean <probe>',
        targetCompileRequired: true,
        targetProbe: { attempted: false, mode: options.targetProbeMode ?? 'exact' },
        error: 'target goal exceeds probe size limit',
      });
      if (cacheKey) cachePremiseValidation(cacheKey, rejected);
      return Promise.resolve(rejected);
    }
    const targetMode = options.targetProbeMode ?? 'exact';
    const targetProbe = targetGoal
      ? `\nexample : ${targetGoal} := by\n  ${targetMode} ${premise.declarationName}\n`
      : '';
    const source = `${modules.map((moduleName) => `import ${moduleName}`).join('\n')}\n#check ${premise.declarationName}${targetProbe}\n`;
    const result = await (options.runProbe ?? runLeanEvalLeanProbe)({
      workspaceRoot: options.projectRoot,
      sourceFile: '.deepscientist/math/premise-probe.lean',
      sourceText: source,
      mode: 'compile',
      timeoutMs: Math.max(1_000, Math.min(options.timeoutMs ?? 20_000, 120_000)),
      ...(options.signal ? { signal: options.signal } : {}),
      ...(options.env ? { env: options.env } : {}),
      ...(options.lakePackagesPath ? { lakePackagesPath: options.lakePackagesPath } : {}),
    });
    if (result.status === 'passed') {
      const accepted = Object.freeze({
        declarationName: premise.declarationName,
        status: 'typed',
        checkCommand: 'lake env lean <sandboxed-probe>',
        targetCompileRequired: true,
        ...(targetGoal ? { targetProbe: { attempted: true, mode: targetMode, ok: true } } : {}),
      });
      if (cacheKey) cachePremiseValidation(cacheKey, accepted);
      return accepted;
    }
    const rejected = Object.freeze({
      declarationName: premise.declarationName,
      status: 'rejected',
      checkCommand: 'lake env lean <sandboxed-probe>',
      targetCompileRequired: true,
      ...(targetGoal
        ? {
            targetProbe: {
              attempted: true,
              mode: targetMode,
              ok: false,
              error: String(result.error || result.diagnostics || 'target probe failed').slice(0, 2_000),
            },
          }
        : {}),
      error: String(result.error || result.diagnostics || 'declaration #check failed').slice(0, 2_000),
    });
    if (cacheKey) cachePremiseValidation(cacheKey, rejected);
    return rejected;
  } catch (error) {
    const rejected = Object.freeze({
      declarationName: premise.declarationName,
      status: 'rejected' as const,
      checkCommand: 'lake env lean <sandboxed-probe>',
      targetCompileRequired: true as const,
      ...(options.targetGoal
        ? { targetProbe: { attempted: true, mode: options.targetProbeMode ?? ('exact' as const), ok: false } }
        : {}),
      error: error instanceof Error ? error.message.slice(0, 2_000) : String(error).slice(0, 2_000),
    });
    if (cacheKey) cachePremiseValidation(cacheKey, rejected);
    return rejected;
  }
}

export async function validateLeanPremiseCandidates(
  premises: readonly MathematicsUpstreamPremise[],
  options: Readonly<{
    projectRoot: string;
    importModules?: readonly string[];
    lakeExecutable?: string;
    timeoutMs?: number;
    targetGoal?: string;
    targetProbeMode?: 'exact' | 'apply';
    /** Avoid spending compiler processes on a long tail of weak index hits. */
    maxCandidates?: number;
    /** With an exact live goal, the first successful target probe is enough. */
    stopAfterFirstTyped?: boolean;
    signal?: AbortSignal;
    env?: NodeJS.ProcessEnv;
    lakePackagesPath?: string;
    runProbe?: (request: LeanEvalLeanProbeRequest) => Promise<LeanEvalLeanProbeResult>;
  }>
): Promise<
  Readonly<{ premises: readonly MathematicsUpstreamPremise[]; validations: readonly LeanPremiseValidation[] }>
> {
  const requestedMax = options.maxCandidates;
  const maxCandidates =
    Number.isFinite(requestedMax) && requestedMax !== undefined
      ? Math.max(1, Math.min(premises.length, Math.floor(requestedMax)))
      : premises.length;
  const validations: LeanPremiseValidation[] = [];
  for (const premise of premises.slice(0, maxCandidates)) {
    // eslint-disable-next-line no-await-in-loop
    const validation = await validateLeanPremiseCandidate(premise, options);
    validations.push(validation);
    if (options.stopAfterFirstTyped && validation.status === 'typed') break;
  }
  const typed = new Set(
    validations.filter((validation) => validation.status === 'typed').map((validation) => validation.declarationName)
  );
  return Object.freeze({
    premises: Object.freeze(premises.filter((premise) => typed.has(premise.declarationName))),
    validations: Object.freeze(validations),
  });
}
