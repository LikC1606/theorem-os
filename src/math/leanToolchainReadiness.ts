/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

import crypto from 'node:crypto';
import fs from 'node:fs';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import { resolveMathematicsRuntimeEnvironment } from "./mathRuntimeEnvironment";

export type LeanToolchainReadinessStatus = 'ready' | 'unavailable' | 'invalid';

export type LeanToolchainReadiness = Readonly<{
  status: LeanToolchainReadinessStatus;
  lakePath?: string;
  leanPath?: string;
  toolchain?: string;
  projectRoot: string;
  diagnostics: string;
  fingerprint: string;
}>;

export type LeanToolchainReadinessRequest = Readonly<{
  projectRoot: string;
  env?: NodeJS.ProcessEnv;
  timeoutMs?: number;
}>;

const sha256 = (value: string): string => crypto.createHash('sha256').update(value, 'utf8').digest('hex');
const MAX_DIAGNOSTICS = 2_000;
const DEFAULT_TIMEOUT_MS = 10_000;

const bounded = (value: string): string => value.trim().replace(/\s+/gu, ' ').slice(0, MAX_DIAGNOSTICS);

const fingerprint = (value: Omit<LeanToolchainReadiness, 'fingerprint'>): string =>
  sha256(
    JSON.stringify({
      schema: 'deepscientist.mathematics.lean-toolchain-readiness.v1',
      ...value,
    })
  );

const result = (value: Omit<LeanToolchainReadiness, 'fingerprint'>): LeanToolchainReadiness =>
  Object.freeze({ ...value, fingerprint: fingerprint(value) });

function executableInPath(name: string, env: NodeJS.ProcessEnv): string | undefined {
  const candidates = name.includes(path.sep)
    ? [name]
    : (env.PATH || '')
        .split(path.delimiter)
        .filter(Boolean)
        .map((entry) => path.join(entry, name));
  for (const candidate of candidates) {
    try {
      const stat = fs.statSync(candidate);
      if (stat.isFile() && (process.platform === 'win32' || (stat.mode & 0o111) !== 0)) {
        return path.resolve(candidate);
      }
    } catch {
      // Continue searching the remaining PATH entries.
    }
  }
  return undefined;
}

/** Resolve an executable from the project-selected elan toolchain.
 *
 * The public elan shim is commonly a shared hardlink and therefore is not a
 * stable artifact for the run binding. `elan which` identifies the actual
 * toolchain binary selected by the project's `lean-toolchain` file.
 */
export function resolvePinnedLeanToolchainExecutable(
  request: Readonly<{ projectRoot: string; executable?: 'lake' | 'lean'; env?: NodeJS.ProcessEnv }>
): string | undefined {
  const projectRoot = path.resolve(request.projectRoot);
  const executable = request.executable ?? 'lake';
  const env = request.env ?? process.env;
  const elan = executableInPath('elan', env);
  if (!elan) return undefined;
  let resolved: ReturnType<typeof spawnSync>;
  try {
    resolved = spawnSync(elan, ['which', executable], {
      cwd: projectRoot,
      env,
      encoding: 'utf8',
      timeout: DEFAULT_TIMEOUT_MS,
      maxBuffer: 32 * 1024,
    });
  } catch {
    return undefined;
  }
  if (resolved.error || resolved.status !== 0) return undefined;
  const candidate = typeof resolved.stdout === 'string' ? resolved.stdout.trim() : '';
  if (!candidate || !path.isAbsolute(candidate) || candidate.includes('\0') || /[\r\n]/u.test(candidate))
    return undefined;
  try {
    const canonical = fs.realpathSync(candidate);
    const stat = fs.lstatSync(canonical);
    if (!stat.isFile() || stat.isSymbolicLink() || (process.platform !== 'win32' && (stat.mode & 0o111) === 0))
      return undefined;
    return canonical;
  } catch {
    return undefined;
  }
}

function readToolchain(projectRoot: string): string | undefined {
  const file = path.join(projectRoot, 'lean-toolchain');
  const stat = fs.lstatSync(file);
  if (stat.isSymbolicLink() || !stat.isFile()) {
    throw new Error('lean-toolchain must be a regular file');
  }
  const source = fs.readFileSync(file, 'utf8');
  const lines = source
    .split(/\r?\n/u)
    .map((line) => line.trim())
    .filter(Boolean);
  if (lines.length !== 1 || lines[0]!.length > 256 || ['\0', '\r', '\n'].some((value) => lines[0]!.includes(value))) {
    throw new Error('lean-toolchain must contain exactly one non-empty toolchain identifier');
  }
  return lines[0];
}

/** Check the pinned Lean environment before a proof assignment is dispatched. */
export function checkLeanToolchainReadiness(request: LeanToolchainReadinessRequest): LeanToolchainReadiness {
  return probeLeanToolchainReadiness(request, () => resolveMathematicsRuntimeEnvironment(request.env ?? process.env));
}

/** Probe exactly the caller's resolved snapshot without reopening a mutable env file. */
export function checkResolvedLeanToolchainReadiness(
  request: LeanToolchainReadinessRequest & Readonly<{ env: NodeJS.ProcessEnv }>
): LeanToolchainReadiness {
  return probeLeanToolchainReadiness(request, () => request.env);
}

function probeLeanToolchainReadiness(
  request: LeanToolchainReadinessRequest,
  resolveEnv: () => NodeJS.ProcessEnv
): LeanToolchainReadiness {
  const requestedRoot = typeof request.projectRoot === 'string' ? request.projectRoot.trim() : '';
  const projectRoot = requestedRoot ? path.resolve(requestedRoot) : '';
  const base = { projectRoot };
  if (!projectRoot) {
    return result({ ...base, status: 'invalid', diagnostics: 'Lean project root is required' });
  }
  let stat: fs.Stats;
  try {
    stat = fs.lstatSync(projectRoot);
  } catch (error) {
    return result({
      ...base,
      status: 'invalid',
      diagnostics: `Lean project root is unavailable: ${bounded(error instanceof Error ? error.message : String(error))}`,
    });
  }
  if (!stat.isDirectory() || stat.isSymbolicLink()) {
    return result({ ...base, status: 'invalid', diagnostics: 'Lean project root must be a regular directory' });
  }

  const env = resolveEnv();
  let toolchain: string | undefined;
  try {
    toolchain = readToolchain(projectRoot);
  } catch (error) {
    return result({
      ...base,
      status: 'invalid',
      diagnostics: bounded(error instanceof Error ? error.message : String(error)),
    });
  }
  if (!toolchain) {
    return result({ ...base, status: 'invalid', diagnostics: 'lean-toolchain is empty' });
  }

  const lakePath = executableInPath('lake', env);
  const leanPath = executableInPath('lean', env);
  if (!lakePath || !leanPath) {
    return result({
      ...base,
      status: 'unavailable',
      ...(lakePath ? { lakePath } : {}),
      ...(leanPath ? { leanPath } : {}),
      toolchain,
      diagnostics: `Pinned Lean tools are unavailable (lake=${lakePath ? 'found' : 'missing'}, lean=${leanPath ? 'found' : 'missing'})`,
    });
  }

  const timeoutMs = Math.max(250, Math.min(180_000, request.timeoutMs ?? DEFAULT_TIMEOUT_MS));
  let probe: ReturnType<typeof spawnSync>;
  try {
    // `lake env` may inspect every package checkout before launching Lean.
    // Readiness only needs to prove that the pinned compiler is executable;
    // using it directly avoids turning a network-backed package cache into a
    // startup timeout.
    probe = spawnSync(leanPath, ['--version'], {
      cwd: projectRoot,
      env,
      encoding: 'utf8',
      timeout: timeoutMs,
      maxBuffer: 32 * 1024,
    });
  } catch (error) {
    return result({
      ...base,
      status: 'unavailable',
      lakePath,
      leanPath,
      toolchain,
      diagnostics: `Lean toolchain probe could not start: ${bounded(error instanceof Error ? error.message : String(error))}`,
    });
  }
  const output = bounded(`${probe.stdout || ''} ${probe.stderr || ''}`);
  if (probe.error || probe.status !== 0) {
    const suffix = probe.signal === 'SIGTERM' ? ` (timed out after ${timeoutMs}ms)` : '';
    return result({
      ...base,
      status: 'unavailable',
      lakePath,
      leanPath,
      toolchain,
      diagnostics: `Lean toolchain probe failed${suffix}${output ? `: ${output}` : ''}`,
    });
  }
  return result({
    ...base,
    status: 'ready',
    lakePath,
    leanPath,
    toolchain,
    diagnostics: output || 'lean --version succeeded',
  });
}
