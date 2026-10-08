/**
 * @license
 * Copyright 2026 DeepScientist (deepscientist.cc)
 * SPDX-License-Identifier: Apache-2.0
 */

const SHELL_EXECUTABLES = new Set([
  'accelerate',
  'bash',
  'bun',
  'bunx',
  'cargo',
  'cat',
  'cd',
  'cmake',
  'cmd',
  'cp',
  'curl',
  'docker',
  'docker-compose',
  'echo',
  'env',
  'fish',
  'git',
  'go',
  'java',
  'jupyter',
  'make',
  'mamba',
  'matlab',
  'mpirun',
  'mv',
  'node',
  'npm',
  'npx',
  'open',
  'perl',
  'pip',
  'pip3',
  'pnpm',
  'poetry',
  'powershell',
  'pwsh',
  'pytest',
  'python',
  'python2',
  'python3',
  'rm',
  'rscript',
  'ruby',
  'sh',
  'srun',
  'torchrun',
  'conda',
  'pixi',
  'uv',
  'uvx',
  'wget',
  'yarn',
  'zsh',
]);

const SHELL_COMMAND_OPTION_REGEX = /(?:^|\s)--?[A-Za-z0-9][A-Za-z0-9_-]*(?=\s|$)/u;
const SHELL_COMMAND_OPERATOR_REGEX = /(?:^|\s)(?:&&|\|\||[|;<>])(?:\s|$)/u;
const ENV_ASSIGNMENT_REGEX = /^[A-Za-z_][A-Za-z0-9_]*=\S+$/u;
const SCRIPT_EXTENSION_REGEX = /\.(?:bat|cmd|fish|pl|ps1|py|rb|sh|zsh)$/iu;
const WINDOWS_DRIVE_PATH_REGEX = /^[A-Za-z]:[\\/]/u;
const URI_SCHEME_REGEX = /^[A-Za-z][A-Za-z0-9+.-]*:/u;
const PARENT_SEGMENT_REGEX = /(?:^|[\\/])\.\.(?:[\\/]|$)/u;

const stripShellQuotes = (value: string): string => value.replace(/^["']|["']$/gu, '');

const commandName = (value: string): string => {
  const normalized = stripShellQuotes(value).replace(/\\/gu, '/');
  return (normalized.split('/').pop() || normalized).toLowerCase().replace(/\.(?:bat|cmd|exe)$/u, '');
};

/** A conservative classifier for one-line command text accidentally supplied as a file path. */
export const isLikelyShellCommand = (value: string): boolean => {
  const trimmed = value.trim();
  if (!trimmed || !/\s/u.test(trimmed)) return false;

  const tokens = trimmed.split(/\s+/u).filter(Boolean);
  if (tokens.length < 2) return false;
  if (ENV_ASSIGNMENT_REGEX.test(stripShellQuotes(tokens[0]))) return true;

  const executable = commandName(tokens[0]);
  if (SHELL_EXECUTABLES.has(executable) || /^pip\d+$/u.test(executable) || /^python\d*(?:\.\d+)*$/u.test(executable)) {
    return true;
  }

  const firstToken = stripShellQuotes(tokens[0]);
  if (SCRIPT_EXTENSION_REGEX.test(firstToken)) {
    return true;
  }

  return SHELL_COMMAND_OPTION_REGEX.test(trimmed) || SHELL_COMMAND_OPERATOR_REGEX.test(trimmed);
};

/**
 * Reject command text, remote/virtual URLs, control characters, and relative
 * parent traversal before a value enters a local-file preview or artifact path.
 */
export const isPlausibleLocalFileReference = (value: string): boolean => {
  const trimmed = value.trim();
  if (
    !trimmed ||
    trimmed.includes(String.fromCodePoint(0)) ||
    /[\r\n]/u.test(trimmed) ||
    isLikelyShellCommand(trimmed)
  ) {
    return false;
  }

  let decoded = trimmed;
  try {
    decoded = decodeURIComponent(trimmed);
  } catch {
    // Keep the original value; malformed encoding is handled by downstream readers.
  }
  if (PARENT_SEGMENT_REGEX.test(decoded)) return false;
  if (
    decoded.startsWith('~') ||
    decoded.includes('*') ||
    decoded.includes('?') ||
    decoded.includes('[') ||
    decoded.includes(']')
  ) {
    return false;
  }
  if (WINDOWS_DRIVE_PATH_REGEX.test(decoded)) return true;
  if (URI_SCHEME_REGEX.test(decoded)) return /^file:/iu.test(decoded);
  return true;
};
