#!/usr/bin/env bun
/** Create one isolated solver workspace for a pinned Humanfia IMO2026 problem. */

import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { bootstrapImo2026Problem, IMO2026_SUPPORTED_PROBLEMS, verifyImo2026BootstrapReceipt } from "../../src/math/imo2026Adapter";

const parseFlags = (argv: readonly string[]): Map<string, string> => {
  const flags = new Map<string, string>();
  for (let index = 0; index < argv.length; index += 1) {
    const key = argv[index];
    if (key === '--help') {
      flags.set('help', 'true');
      continue;
    }
    if (!key?.startsWith('--')) throw new Error(`Invalid argument: ${key}`);
    const value = argv[index + 1];
    if (!value || value.startsWith('--')) throw new Error(`${key} requires a value`);
    if (flags.has(key.slice(2))) throw new Error(`Duplicate argument: ${key}`);
    flags.set(key.slice(2), value);
    index += 1;
  }
  return flags;
};

const required = (flags: Map<string, string>, key: string): string => {
  const value = flags.get(key)?.trim();
  if (!value) throw new Error(`--${key} is required`);
  return value;
};

const writeReceiptCopy = (file: string, receipt: unknown): void => {
  const resolved = path.resolve(file);
  if (fs.existsSync(resolved)) throw new Error('Receipt path already exists');
  fs.mkdirSync(path.dirname(resolved), { recursive: true, mode: 0o700 });
  const descriptor = fs.openSync(resolved, 'wx', 0o600);
  try {
    fs.writeFileSync(descriptor, `${JSON.stringify(receipt, null, 2)}\n`);
    fs.fsyncSync(descriptor);
  } finally {
    fs.closeSync(descriptor);
  }
};

async function main(): Promise<void> {
  const flags = parseFlags(process.argv.slice(2));
  if (flags.has('help')) {
    console.log(
      `Usage: bun scripts/mathematics/bootstrapImo2026.ts --repo DIR --problem ID --workspace DIR [--receipt FILE]\nSupported IDs: ${IMO2026_SUPPORTED_PROBLEMS.join(', ')}`
    );
    return;
  }
  const problemId = required(flags, 'problem');
  if (!IMO2026_SUPPORTED_PROBLEMS.includes(problemId as (typeof IMO2026_SUPPORTED_PROBLEMS)[number])) {
    throw new Error(`Unsupported IMO2026 problem: ${problemId}`);
  }
  const receipt = await bootstrapImo2026Problem({
    repositoryRoot: path.resolve(required(flags, 'repo')),
    problemId: problemId as (typeof IMO2026_SUPPORTED_PROBLEMS)[number],
    workspaceRoot: path.resolve(required(flags, 'workspace')),
  });
  verifyImo2026BootstrapReceipt(receipt);
  const receiptPath = flags.get('receipt') ? path.resolve(flags.get('receipt')!) : receipt.activeProblemPath;
  if (receiptPath !== receipt.activeProblemPath) writeReceiptCopy(receiptPath, receipt);
  console.log(
    JSON.stringify({
      problemId: receipt.problemId,
      workspaceRoot: receipt.workspaceRoot,
      projectRoot: receipt.projectRoot,
      activeProblemPath: receipt.activeProblemPath,
      receiptPath,
      sourceCommit: receipt.sourceCommit,
      theoremNames: receipt.theoremNames,
      evaluator: receipt.evaluator,
    })
  );
}

if (process.argv[1] && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  main().catch((error: unknown) => {
    console.error(error instanceof Error ? error.stack || error.message : String(error));
    process.exitCode = 1;
  });
}
