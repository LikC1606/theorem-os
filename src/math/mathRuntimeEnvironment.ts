/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';

const SECRET_KEY = /(?:API[_-]?KEY|TOKEN|SECRET|PASSWORD|CREDENTIAL|PRIVATE[_-]?KEY)/iu;
const ENV_FILE_KEYS = new Set([
  'DEEPSCIENTIST_LEAN_EVAL_ROOT',
  'DEEPSCIENTIST_LEAN_EVAL_TOOLS_ROOT',
  'DEEPSCIENTIST_LEAN_EVAL_TOOL_MANIFEST',
  'DEEPSCIENTIST_MATH_TRUSTED_CACHE_ROOTS',
  'DEEPSCIENTIST_MATH_TRUSTED_ELAN_ROOTS',
  'DEEPSCIENTIST_MATH_SANDBOX_BACKEND',
  'DEEPSCIENTIST_MATH_SANDBOX_IMAGE',
  'DEEPSCIENTIST_MATH_ENV_FILE',
  'ELAN_HOME',
  'LAKE_HOME',
  'LEAN_PATH',
  'LEAN_SYSROOT',
  'PATH',
]);
const OPTIONAL_ENV_FILE_KEYS = new Set([
  'DEEPSCIENTIST_MATH_PROOF_ENVIRONMENT',
  'DEEPSCIENTIST_MATH_RETRIEVAL_CORPUS',
  'DEEPSCIENTIST_MATH_RETRIEVAL_CORPUS_SHA256',
]);

export const DEFAULT_MATHEMATICS_ENV_FILE = path.join(os.homedir(), '.config', 'deepscientist-math', 'math.env');

function parseValue(raw: string): string {
  const value = raw.trim();
  if (
    value.length >= 2 &&
    ((value.startsWith('"') && value.endsWith('"')) || (value.startsWith("'") && value.endsWith("'")))
  ) {
    return value.slice(1, -1);
  }
  return value;
}

function readEnvFile(file: string, base: NodeJS.ProcessEnv): Record<string, string> {
  if (!file) return {};
  let source: string;
  try {
    source = fs.readFileSync(file, 'utf8');
  } catch (error) {
    if ((error as NodeJS.ErrnoException).code === 'ENOENT' && !file.endsWith('.json')) return {};
    throw error;
  }
  if (file.endsWith('.json')) {
    let parsed: unknown;
    try {
      parsed = JSON.parse(source);
    } catch {
      throw new Error('Invalid mathematics environment projection');
    }
    if (!parsed || typeof parsed !== 'object' || Array.isArray(parsed)) {
      throw new Error('Invalid mathematics environment projection');
    }
    const values = Object.entries(parsed);
    if (
      [...ENV_FILE_KEYS].some((key) => !Object.hasOwn(parsed, key)) ||
      values.some(
        ([key, value]) =>
          (!ENV_FILE_KEYS.has(key) && !OPTIONAL_ENV_FILE_KEYS.has(key)) ||
          typeof value !== 'string' ||
          (key === 'DEEPSCIENTIST_MATH_ENV_FILE' && value !== file)
      )
    ) {
      throw new Error('Invalid mathematics environment projection');
    }
    return Object.fromEntries(values) as Record<string, string>;
  }
  const values: Record<string, string> = {};
  for (const line of source.split(/\r?\n/u)) {
    const match = /^\s*(?:export\s+)?([A-Za-z_][A-Za-z0-9_]*)\s*=\s*(.*?)\s*$/u.exec(line);
    if (!match || (!ENV_FILE_KEYS.has(match[1]!) && !OPTIONAL_ENV_FILE_KEYS.has(match[1]!))) continue;
    let value = parseValue(match[2]!);
    value = value.replace(/\$\{([A-Za-z_][A-Za-z0-9_]*)\}|\$([A-Za-z_][A-Za-z0-9_]*)/gu, (_all, braced, plain) => {
      const key = String(braced || plain);
      return values[key] ?? base[key] ?? '';
    });
    values[match[1]!] = value;
  }
  return values;
}

/** Only mathematics tool settings may enter a solver-visible environment file. */
export function projectMathematicsRuntimeEnvironment(source: NodeJS.ProcessEnv): Readonly<Record<string, string>> {
  return Object.freeze(
    Object.fromEntries([
      ...[...ENV_FILE_KEYS].toSorted().map((key) => [key, source[key] ?? '']),
      ...[...OPTIONAL_ENV_FILE_KEYS]
        .filter((key) => source[key] !== undefined)
        .toSorted()
        .map((key) => [key, source[key]!]),
    ])
  );
}

/** Merge the local mathematics env file into subprocesses without importing secrets. */
export function resolveMathematicsRuntimeEnvironment(
  source: NodeJS.ProcessEnv = process.env,
  envFile = source.DEEPSCIENTIST_MATH_ENV_FILE?.trim() || DEFAULT_MATHEMATICS_ENV_FILE
): NodeJS.ProcessEnv {
  const values = readEnvFile(envFile, source);
  // The checked-in/local env file supplies defaults. Explicit values passed by
  // a runner or test remain authoritative, while the file's PATH still
  // contributes its pinned tool directories (it was expanded against source).
  const merged: NodeJS.ProcessEnv = envFile.endsWith('.json')
    ? { ...source, ...values, DEEPSCIENTIST_MATH_ENV_FILE: envFile }
    : { ...values, ...source };
  // A frozen legacy projection must not inherit a caller's new policy overrides.
  if (envFile.endsWith('.json')) {
    for (const key of OPTIONAL_ENV_FILE_KEYS) if (!Object.hasOwn(values, key)) delete merged[key];
  }
  if (values.PATH) merged.PATH = values.PATH;
  const pathEntries = [
    merged.DEEPSCIENTIST_LEAN_EVAL_TOOLS_ROOT,
    merged.ELAN_HOME && path.join(merged.ELAN_HOME, 'bin'),
  ].filter((entry): entry is string => Boolean(entry));
  if (pathEntries.length) {
    merged.PATH = [...pathEntries, ...(merged.PATH || '').split(path.delimiter)]
      .filter(Boolean)
      .filter((entry, index, entries) => entries.indexOf(entry) === index)
      .join(path.delimiter);
  }
  return Object.fromEntries(
    Object.entries(merged).filter(([key]) => !SECRET_KEY.test(key))
  );
}

export function mathematicsRuntimeInstruction(envFile?: string): string {
  const file = envFile || DEFAULT_MATHEMATICS_ENV_FILE;
  if (file.endsWith('.json')) {
    return `Pinned environment settings: ${file}. These settings are already injected; do not source JSON as a shell script or reload a local env file. Do not install packages or replace the pinned toolchain.`;
  }
  return `Before running Lean, source ${file} when it exists, or use the absolute tools from that file. Do not install packages or replace the pinned toolchain.`;
}
