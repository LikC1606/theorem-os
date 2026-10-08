#!/usr/bin/env bun

/** Aggregate frozen proof-team receipts into the v14 cross-run report schema. */

import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import {
  deriveMathProofRunMetric,
  summarizeMathProofRunMetrics,
  type MathProofBenchmarkSlate,
  type MathProofRunMetric,
} from "../../src/math/mathProofRunReport";

type JsonRecord = Record<string, unknown>;

const readJson = (file: string): unknown => JSON.parse(fs.readFileSync(file, 'utf8')) as unknown;

const required = (flags: ReadonlyMap<string, string>, name: string): string => {
  const value = flags.get(name)?.trim();
  if (!value) throw new Error(`--${name} is required`);
  return value;
};

const parseFlags = (argv: readonly string[]): Map<string, string> => {
  const flags = new Map<string, string>();
  for (let index = 0; index < argv.length; index += 2) {
    const key = argv[index];
    if (key === '--help') {
      flags.set('help', 'true');
      continue;
    }
    const value = argv[index + 1];
    if (!key?.startsWith('--') || !value || value.startsWith('--')) throw new Error(`Invalid argument: ${key}`);
    if (flags.has(key.slice(2))) throw new Error(`Duplicate argument: ${key}`);
    flags.set(key.slice(2), value);
  }
  return flags;
};

const object = (value: unknown, label: string): JsonRecord => {
  if (!value || typeof value !== 'object' || Array.isArray(value)) throw new Error(`${label} must be an object`);
  return value as JsonRecord;
};

const array = (value: unknown, label: string): readonly JsonRecord[] => {
  if (!Array.isArray(value)) throw new Error(`${label} must be an array`);
  return value.map((item, index) => object(item, `${label}[${index}]`));
};

export function buildMathProofRunReportFromJson(
  input: Readonly<{
    value: unknown;
    slate: MathProofBenchmarkSlate;
    generatedAt?: number;
    controlMethod?: string;
    treatmentMethod?: string;
    sourceLedgerRevision?: string | null;
    sourceIndexHash?: string | null;
    generatorVersion?: string;
  }>
): ReturnType<typeof summarizeMathProofRunMetrics> {
  const root = Array.isArray(input.value) ? undefined : object(input.value, 'input');
  const rows = array(root ? root.runs : input.value, 'runs');
  const metrics: MathProofRunMetric[] = rows.map((row, index) => {
    const receipt = object(row.receipt, `runs[${index}].receipt`);
    const verifierStatus = row.verifierStatus;
    if (
      verifierStatus !== undefined &&
      verifierStatus !== 'passed' &&
      verifierStatus !== 'failed' &&
      verifierStatus !== 'missing' &&
      verifierStatus !== 'unavailable'
    )
      throw new Error(`runs[${index}].verifierStatus is invalid`);
    return deriveMathProofRunMetric({
      runId: String(row.runId ?? ''),
      runIdentity: typeof row.runIdentity === 'string' ? row.runIdentity : undefined,
      problemId: String(row.problemId ?? ''),
      benchmarkMethod: String(row.benchmarkMethod ?? ''),
      repetition: Number.isSafeInteger(row.repetition) ? Number(row.repetition) : undefined,
      receipt,
      totalTokens: Number.isSafeInteger(row.totalTokens) ? Number(row.totalTokens) : undefined,
      verifierStatus: verifierStatus as 'passed' | 'failed' | 'missing' | 'unavailable' | undefined,
      searchObservations: Array.isArray(row.searchObservations)
        ? (row.searchObservations as Parameters<typeof deriveMathProofRunMetric>[0]['searchObservations'])
        : undefined,
    });
  });
  return summarizeMathProofRunMetrics(metrics, {
    slate: input.slate,
    generatedAt: input.generatedAt,
    controlMethod: input.controlMethod,
    treatmentMethod: input.treatmentMethod,
    sourceLedgerRevision: input.sourceLedgerRevision,
    sourceIndexHash: input.sourceIndexHash,
    generatorVersion: input.generatorVersion,
  });
}

function main(): void {
  const flags = parseFlags(process.argv.slice(2));
  if (flags.has('help')) {
    console.log(
      'Usage: bun scripts/mathematics/summarizeMathProofRuns.ts --input FILE --output FILE --benchmark-id ID --benchmark-commit SHA --catalog-hash SHA --random-seed SEED --problem-ids ID1,ID2 --repetitions N [--control-method METHOD --treatment-method METHOD] [--source-ledger-revision SHA --source-index-hash SHA --generator-version VERSION]'
    );
    return;
  }
  const problemIds = [
    ...new Set(
      required(flags, 'problem-ids')
        .split(',')
        .map((id) => id.trim())
        .filter(Boolean)
    ),
  ];
  const repetitions = Number(required(flags, 'repetitions'));
  if (!problemIds.length || !Number.isSafeInteger(repetitions) || repetitions < 1)
    throw new Error('--problem-ids and --repetitions must describe a nonempty slate');
  const output = path.resolve(required(flags, 'output'));
  const report = buildMathProofRunReportFromJson({
    value: readJson(path.resolve(required(flags, 'input'))),
    slate: {
      benchmarkId: required(flags, 'benchmark-id'),
      benchmarkCommit: required(flags, 'benchmark-commit'),
      catalogHash: required(flags, 'catalog-hash'),
      randomSeed: required(flags, 'random-seed'),
      problemIds,
      repetitions,
    },
    ...(flags.has('control-method') ? { controlMethod: required(flags, 'control-method') } : {}),
    ...(flags.has('treatment-method') ? { treatmentMethod: required(flags, 'treatment-method') } : {}),
    ...(flags.has('source-ledger-revision') ? { sourceLedgerRevision: required(flags, 'source-ledger-revision') } : {}),
    ...(flags.has('source-index-hash') ? { sourceIndexHash: required(flags, 'source-index-hash') } : {}),
    ...(flags.has('generator-version') ? { generatorVersion: required(flags, 'generator-version') } : {}),
  });
  fs.mkdirSync(path.dirname(output), { recursive: true });
  const descriptor = fs.openSync(output, 'wx', 0o600);
  try {
    fs.writeFileSync(descriptor, `${JSON.stringify(report, null, 2)}\n`, 'utf8');
    fs.fsyncSync(descriptor);
  } finally {
    fs.closeSync(descriptor);
  }
  console.log(JSON.stringify({ output, reportHash: report.reportHash, totalRuns: report.totalRuns }));
}

if (process.argv[1] && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  try {
    main();
  } catch (error) {
    console.error(error instanceof Error ? error.message : String(error));
    process.exitCode = 1;
  }
}
