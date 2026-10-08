/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

import fs from 'node:fs';
import path from 'node:path';
import { MATH_RUN_INPUTS_ENV, verifyMathRunInputs, verifyMathRunInputsEnvironment } from "./mathRunInputs";
import { resolveMathematicsRuntimeEnvironment } from "./mathRuntimeEnvironment";
import { canonicalMathJson, mathDigest } from "./mathRuntimeIo";

/** Core-held input identity survives restart and differs even for identical new tasks. */
export function readMathRunHistoryIdentity(env: NodeJS.ProcessEnv = process.env): string | undefined {
  const encoded = env[MATH_RUN_INPUTS_ENV];
  if (encoded === undefined) {
    if (resolveMathematicsRuntimeEnvironment(env).DEEPSCIENTIST_MATH_RETRIEVAL_CORPUS) {
      throw new Error('Frozen mathematics history requires managed run inputs');
    }
    return undefined;
  }
  verifyMathRunInputsEnvironment(env);
  return mathDigest(canonicalMathJson(verifyMathRunInputs(JSON.parse(encoded))));
}

/** Each managed run/problem gets its own logical root for the existing ledger APIs. */
export function resolveMathRunHistory(
  projectRoot: string,
  problemId: string | undefined,
  env: NodeJS.ProcessEnv = process.env
): Readonly<{ root: string; runIdentity?: string }> {
  const runIdentity = readMathRunHistoryIdentity(env);
  if (!runIdentity) return Object.freeze({ root: path.resolve(projectRoot) });
  if (!problemId?.trim() || problemId.length > 128) throw new Error('Mathematics run history requires a problem ID');
  const requestedRoot = path.resolve(projectRoot);
  const stat = fs.lstatSync(requestedRoot);
  if (!stat.isDirectory() || stat.isSymbolicLink()) throw new Error('Mathematics history root is not a directory');
  let root = fs.realpathSync(requestedRoot);
  for (const segment of ['.deepscientist', 'math', 'run-history', runIdentity, mathDigest(problemId)]) {
    root = path.join(root, segment);
    try {
      fs.mkdirSync(root, { mode: 0o700 });
    } catch (error) {
      if ((error as NodeJS.ErrnoException).code !== 'EEXIST') throw error;
    }
    const entry = fs.lstatSync(root);
    if (!entry.isDirectory() || entry.isSymbolicLink()) throw new Error('Mathematics history directory is invalid');
  }
  return Object.freeze({ root, runIdentity });
}
