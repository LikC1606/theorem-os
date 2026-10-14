#!/usr/bin/env bun
/** Create one isolated solver workspace for a pinned Humanfia IMO2026 problem. */

import fs from 'node:fs';
import { parseFlags, required } from './arguments';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { bootstrapImo2026Problem, IMO2026_SUPPORTED_PROBLEMS, verifyImo2026BootstrapReceipt } from "../../src/math/imo2026Adapter";

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
  const flags = parseFlags(process.argv.slice(2), ['repo', 'problem', 'workspace', 'receipt']);
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
