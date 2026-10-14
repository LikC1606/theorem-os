#!/usr/bin/env bun
/** Create one pinned public Lean-Eval solver workspace for a held-out run. */

import fs from 'node:fs';
import { parseFlags, required } from './arguments';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { bootstrapLeanEvalProblem } from "../../src/math/leanEvalBootstrap";
import { classifyLeanEvalHeldOutFamily } from "../../src/math/leanEvalHeldOutEvaluation";
import { resolveMathematicsRuntimeEnvironment } from "../../src/math/mathRuntimeEnvironment";

async function main(): Promise<void> {
  const flags = parseFlags(process.argv.slice(2), ['repo', 'problem', 'workspace', 'receipt', 'evaluation-mode']);
  if (flags.has('help')) {
    console.log(
      'Usage: bun scripts/mathematics/bootstrapLeanEvalHeldOut.ts --repo DIR --problem ID --workspace DIR [--receipt FILE]'
    );
    return;
  }
  const runtime = resolveMathematicsRuntimeEnvironment();
  const evaluationMode = flags.get('evaluation-mode') ?? 'official';
  if (!['official', 'benchmark'].includes(evaluationMode)) throw new Error('Invalid --evaluation-mode');
  const repositoryValue = flags.get('repo') || runtime.DEEPSCIENTIST_LEAN_EVAL_ROOT;
  if (!repositoryValue?.trim()) throw new Error('--repo is required');
  const repositoryRoot = path.resolve(repositoryValue);
  const workspaceRoot = path.resolve(required(flags, 'workspace'));
  if (fs.existsSync(workspaceRoot)) {
    if (!fs.statSync(workspaceRoot).isDirectory() || fs.readdirSync(workspaceRoot).length > 0) {
      throw new Error('--workspace must be a fresh empty directory');
    }
  } else fs.mkdirSync(workspaceRoot, { recursive: true, mode: 0o700 });
  const result = await bootstrapLeanEvalProblem({
    repositoryRoot,
    problemId: required(flags, 'problem'),
    evaluationMode: evaluationMode as 'official' | 'benchmark',
    workspaceRoot,
  });
  const receiptPath = path.resolve(flags.get('receipt') || path.join(workspaceRoot, 'bootstrap-result.json'));
  const descriptor = fs.openSync(receiptPath, 'wx', 0o600);
  try {
    fs.writeFileSync(
      descriptor,
      `${JSON.stringify(
        {
          schema: 'deepscientist.mathematics.lean-eval-held-out-bootstrap.v1',
          problemId: result.problem.id,
          family: classifyLeanEvalHeldOutFamily(result.problem),
          benchmarkCommit: result.catalog.benchmarkCommit,
          catalogHash: result.catalog.catalogHash,
          receipt: result.receipt,
          obligationCount: result.binding.publicObligations.length,
        },
        null,
        2
      )}\n`
    );
    fs.fsyncSync(descriptor);
  } finally {
    fs.closeSync(descriptor);
  }
  console.log(
    JSON.stringify({
      problemId: result.problem.id,
      workspaceRoot: result.receipt.workspaceRoot,
      projectRoot: result.receipt.projectRoot,
      activeProblemPath: result.receipt.activeProblemPath,
      receiptPath,
    })
  );
}

if (process.argv[1] && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  main().catch((error: unknown) => {
    console.error(error instanceof Error ? error.stack || error.message : String(error));
    process.exitCode = 1;
  });
}
