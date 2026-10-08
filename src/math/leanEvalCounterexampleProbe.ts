/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

import type { LeanEvalLeanProbeRequest, LeanEvalLeanProbeResult } from "./leanEvalLeanProbe";
import { runLeanEvalLeanProbe } from "./leanEvalLeanProbe";
import { createHash } from 'node:crypto';
import {
  generateStructuredMathSamples,
  shrinkMathProbeSample,
  type MathStructuredSampleDesign,
} from "./mathStructuredSamples";

export type MathSampleDesign =
  | Readonly<{
      kind: 'integer_range';
      min: number;
      max: number;
      count: number;
      seed: string;
      includeBoundaries?: boolean;
    }>
  | MathStructuredSampleDesign;

export function generateMathProbeSamples(design: MathSampleDesign): readonly string[] {
  if (design.kind !== 'integer_range') return generateStructuredMathSamples(design);
  if (
    design.kind !== 'integer_range' ||
    !Number.isSafeInteger(design.min) ||
    !Number.isSafeInteger(design.max) ||
    design.min > design.max ||
    !Number.isSafeInteger(design.count) ||
    design.count < 1 ||
    design.count > MAX_CASES ||
    !design.seed ||
    design.seed.length > 512
  )
    throw new TypeError('Invalid integer sample design');
  const width = BigInt(design.max) - BigInt(design.min) + BigInt(1);
  if (BigInt(design.count) > width) throw new TypeError('Sample count exceeds the number of distinct integers');
  const values = new Set<bigint>();
  if (design.includeBoundaries !== false) {
    values.add(BigInt(design.min));
    if (design.count > 1) values.add(BigInt(design.max));
  }
  // Hash-indexed sampling is reproducible without mutable process RNG state.
  for (let index = 0; values.size < design.count; index++) {
    const digest = createHash('sha256')
      .update(JSON.stringify([design.seed, index]))
      .digest('hex');
    let value = BigInt(design.min) + (BigInt(`0x${digest}`) % width);
    while (values.has(value)) value = BigInt(design.min) + ((value - BigInt(design.min) + BigInt(1)) % width);
    values.add(value);
  }
  return Object.freeze([...values].map(String));
}

/**
 * A bounded execution result is evidence about the sampled cases only. It can
 * expose a concrete counterexample, but it can never produce a kernel verdict.
 */
export type LeanEvalCounterexampleProbe = Readonly<{
  attempted: boolean;
  outcome: 'no_counterexample_found' | 'counterexample_found' | 'inconclusive';
  casesChecked: number;
  casesRequested?: number;
  casesObserved?: number;
  casesUsed?: readonly string[];
  sampleDesign?: MathSampleDesign;
  originalCasesUsed?: readonly string[];
  minimization?: Readonly<{ probes: number; originalWitness: string; reduced: boolean }>;
  /** Samples rejected by the optional precondition and therefore not tested. */
  casesSkipped?: number;
  witness?: string;
  diagnostics: readonly string[];
  command?: string;
  proofStateFingerprint?: string;
  durationMs?: number;
  sandboxBackend?: 'unshare' | 'bwrap' | 'docker' | 'podman';
}>;

export type ProbeValueMode = 'proposition' | 'boolean';

const MAX_CASES = 16;
const MAX_CASE_CHARS = 12_000;
const MAX_DIAGNOSTIC_CHARS = 2_000;

const boundedCases = (cases: readonly string[] | undefined): readonly string[] => {
  const values = cases ?? ['0', '1', '2', '3'];
  if (values.length > MAX_CASES)
    throw new TypeError(
      `Counterexample probe accepts ${MAX_CASES} cases per batch; submit remaining cases in another batch`
    );
  if (!values.length) throw new TypeError('Lean-Eval counterexample probe requires at least one case');
  if (values.some((value) => typeof value !== 'string' || !value.trim() || value.length > MAX_CASE_CHARS)) {
    throw new TypeError(
      `Lean-Eval counterexample probe cases must be non-empty strings of at most ${MAX_CASE_CHARS} characters`
    );
  }
  if (values.some((value) => /[\r\n]/u.test(value) || value.includes('\0'))) {
    throw new TypeError('Lean-Eval counterexample probe cases must be single-line expressions');
  }
  return Object.freeze(values.map((value) => value.trim()));
};

const probeExpression = (expression: string, value: string, mode: ProbeValueMode, precondition?: string): string => {
  const applied = `((${expression.trim()}) ${value})`;
  const result = mode === 'boolean' ? `if (${applied} = true) then 1 else 0` : `if ${applied} then 1 else 0`;
  if (!precondition) return result;
  const guard = `((${precondition.trim()}) ${value})`;
  // 2 is an explicit "not applicable" marker. Keeping it in the machine
  // readable output prevents illegal samples from looking like witnesses.
  return `if ${guard} then ${result} else 2`;
};

const probeSource = (
  options: Readonly<{
    expression: string;
    precondition?: string;
    cases: readonly string[];
    imports: readonly string[];
    mode: ProbeValueMode;
  }>
): string => {
  const imports = [...new Set(options.imports.filter((item) => /^[A-Za-z][A-Za-z0-9_.]*$/u.test(item)))].slice(0, 16);
  const header = imports.length ? `${imports.map((item) => `import ${item}`).join('\n')}\n` : '';
  return `${header}${options.cases
    .map(
      (value, index) =>
        `#eval (${index}, (${probeExpression(options.expression, value, options.mode, options.precondition)}))`
    )
    .join('\n')}\n`;
};

const outputValues = (probe: LeanEvalLeanProbeResult, count: number): readonly ('0' | '1' | '2' | undefined)[] => {
  const raw = probe as LeanEvalLeanProbeResult & { informationMessages?: readonly string[] };
  const messages = raw.informationMessages?.length
    ? raw.informationMessages
    : probe.diagnostics.split(/\r?\n/u).flatMap((line) => {
        try {
          const parsed = JSON.parse(line);
          if (parsed && typeof parsed === 'object')
            return ['information', 'info'].includes(parsed.severity) && typeof parsed.data === 'string'
              ? [parsed.data]
              : [];
        } catch {
          /* Older wrappers return plain information text. */
        }
        return [line];
      });
  const indexed = new Map<number, '0' | '1' | '2'>();
  for (const message of messages) {
    const match = /^\s*\((\d+),\s*([012])\)\s*$/u.exec(message);
    if (!match) continue;
    const index = Number(match[1]);
    if (index >= count || indexed.has(index)) return [];
    indexed.set(index, match[2] as '0' | '1' | '2');
  }
  return Array.from({ length: count }, (_, index) => indexed.get(index));
};

/**
 * Evaluate a proposition (or Bool-valued predicate) over bounded concrete
 * inputs in the verifier-owned sandbox. A `1` means the supplied negation was
 * witnessed for that sample; a clean finite sweep only means no witness was
 * found in the supplied region.
 */
export async function runLeanEvalCounterexampleProbe(
  options: Readonly<{
    projectRoot: string;
    projectRelative?: string;
    /** A function-like Lean expression, applied to each item in `cases`. */
    expression: string;
    /** Optional function-like proposition used to skip illegal samples. */
    precondition?: string;
    cases?: readonly string[];
    sampleDesign?: MathSampleDesign;
    minimizeWitness?: boolean;
    /** Propositions are the default; use `boolean` for a predicate returning Bool. */
    mode?: ProbeValueMode;
    imports?: readonly string[];
    timeoutMs?: number;
    signal?: AbortSignal;
    env?: NodeJS.ProcessEnv;
    lakePackagesPath?: string;
    runProbe?: (request: LeanEvalLeanProbeRequest) => Promise<LeanEvalLeanProbeResult>;
  }>
): Promise<LeanEvalCounterexampleProbe> {
  const expression = options.expression.trim();
  if (!expression || expression.length > 12_000) {
    return Object.freeze({
      attempted: false,
      outcome: 'inconclusive',
      casesChecked: 0,
      diagnostics: Object.freeze(['expression is empty or too large']),
    });
  }

  const precondition = options.precondition?.trim();
  if (precondition && (precondition.length > 12_000 || /[\r\n]/u.test(precondition) || precondition.includes('\0'))) {
    return Object.freeze({
      attempted: false,
      outcome: 'inconclusive',
      casesChecked: 0,
      diagnostics: Object.freeze(['precondition is empty, too large, or not a single-line expression']),
    });
  }

  let cases: readonly string[];
  try {
    if (options.cases && options.sampleDesign) throw new TypeError('Choose explicit cases or sampleDesign');
    cases = boundedCases(options.sampleDesign ? generateMathProbeSamples(options.sampleDesign) : options.cases);
  } catch (error) {
    return Object.freeze({
      attempted: false,
      outcome: 'inconclusive',
      casesChecked: 0,
      diagnostics: Object.freeze([error instanceof Error ? error.message : String(error)]),
    });
  }

  const sourceText = probeSource({
    expression,
    ...(precondition ? { precondition } : {}),
    cases,
    imports: options.imports ?? [],
    mode: options.mode ?? 'proposition',
  });
  const probe = await (options.runProbe ?? runLeanEvalLeanProbe)({
    workspaceRoot: options.projectRoot,
    projectRelative: options.projectRelative,
    sourceFile: '.deepscientist-counterexample-probe.lean',
    sourceText,
    mode: 'compile',
    timeoutMs: Math.max(1_000, Math.min(options.timeoutMs ?? 15_000, 60_000)),
    ...(options.signal ? { signal: options.signal } : {}),
    ...(options.env ? { env: options.env } : {}),
    ...(options.lakePackagesPath ? { lakePackagesPath: options.lakePackagesPath } : {}),
  });

  const values = outputValues(probe, cases.length);
  const casesObserved = values.filter((value) => value !== undefined).length;
  const casesSkipped = values.filter((value) => value === '2').length;
  const casesChecked = casesObserved - casesSkipped;
  const sampling = {
    casesUsed: cases,
    ...(options.sampleDesign ? { sampleDesign: Object.freeze({ ...options.sampleDesign }) } : {}),
  };
  if (probe.status !== 'passed') {
    return Object.freeze({
      attempted: true,
      outcome: 'inconclusive',
      casesChecked,
      casesRequested: cases.length,
      casesObserved,
      casesSkipped,
      ...sampling,
      diagnostics: Object.freeze(
        [probe.error || probe.diagnostics || 'sandboxed counterexample probe did not pass'].map((value) =>
          value.slice(0, MAX_DIAGNOSTIC_CHARS)
        )
      ),
      command: 'lake env lean <sandboxed-counterexample-probe>',
      proofStateFingerprint: probe.proofStateFingerprint,
      durationMs: probe.durationMs,
      ...(probe.sandboxBackend ? { sandboxBackend: probe.sandboxBackend } : {}),
    });
  }

  if (casesObserved !== cases.length) {
    return Object.freeze({
      attempted: true,
      outcome: 'inconclusive',
      casesChecked,
      casesRequested: cases.length,
      casesObserved,
      casesSkipped,
      ...sampling,
      diagnostics: Object.freeze(['counterexample probe produced no complete machine-readable result']),
      command: 'lake env lean <sandboxed-counterexample-probe>',
      proofStateFingerprint: probe.proofStateFingerprint,
      durationMs: probe.durationMs,
      ...(probe.sandboxBackend ? { sandboxBackend: probe.sandboxBackend } : {}),
    });
  }
  const legalCases = values.length - casesSkipped;
  const witnessIndex = values.findIndex((value) => value === '1');
  const outcome =
    witnessIndex >= 0 ? 'counterexample_found' : legalCases > 0 ? 'no_counterexample_found' : 'inconclusive';
  if (witnessIndex >= 0 && options.minimizeWitness) {
    const smaller = shrinkMathProbeSample(cases[witnessIndex]!);
    if (smaller.length && !options.signal?.aborted) {
      const reduced = await runLeanEvalCounterexampleProbe({ ...options, sampleDesign: undefined, cases: smaller });
      const retained =
        reduced.outcome === 'counterexample_found'
          ? reduced
          : {
              attempted: true,
              outcome: 'counterexample_found' as const,
              witness: cases[witnessIndex],
              casesUsed: cases,
              diagnostics: Object.freeze([]),
              proofStateFingerprint: probe.proofStateFingerprint,
              command: 'lake env lean <sandboxed-counterexample-probe>',
              ...(probe.sandboxBackend ? { sandboxBackend: probe.sandboxBackend } : {}),
            };
      return Object.freeze({
        ...retained,
        casesChecked: casesChecked + reduced.casesChecked,
        casesRequested: cases.length + (reduced.casesRequested ?? 0),
        casesObserved: casesObserved + (reduced.casesObserved ?? 0),
        casesSkipped: casesSkipped + (reduced.casesSkipped ?? 0),
        originalCasesUsed: cases,
        ...(options.sampleDesign ? { sampleDesign: options.sampleDesign } : {}),
        minimization: {
          probes: 1 + (reduced.minimization?.probes ?? 0),
          originalWitness: cases[witnessIndex]!,
          reduced: reduced.outcome === 'counterexample_found',
        },
        durationMs: (probe.durationMs ?? 0) + (reduced.durationMs ?? 0),
      });
    }
  }
  return Object.freeze({
    attempted: true,
    outcome,
    casesChecked,
    casesRequested: cases.length,
    casesObserved,
    casesSkipped,
    ...sampling,
    ...(witnessIndex >= 0 ? { witness: cases[witnessIndex] } : {}),
    diagnostics: Object.freeze([]),
    command: 'lake env lean <sandboxed-counterexample-probe>',
    proofStateFingerprint: probe.proofStateFingerprint,
    durationMs: probe.durationMs,
    ...(probe.sandboxBackend ? { sandboxBackend: probe.sandboxBackend } : {}),
  });
}
