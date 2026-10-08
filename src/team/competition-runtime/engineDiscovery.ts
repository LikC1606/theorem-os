/**
 * @license
 * Copyright 2026 DeepScientist (deepscientist.cc)
 * SPDX-License-Identifier: Apache-2.0
 */

import { spawn } from 'node:child_process';
import { stat } from 'node:fs/promises';
import path from 'node:path';
import type { CompetitionEngineLaunch } from "./jsonlClient";
import { IOAI_COMPETITION_ENGINE_ROOT_ENV, IOAI_COMPETITION_PYTHON_ENV } from "./registration";

const SAFE_ENV_KEYS = [
  'PATH',
  'PATHEXT',
  'SYSTEMROOT',
  'WINDIR',
  'TEMP',
  'TMP',
  'HOME',
  'USERPROFILE',
  'USERNAME',
  'USER',
  'LOGNAME',
  'LOCALAPPDATA',
  'APPDATA',
  'PROCESSOR_ARCHITECTURE',
  'PROCESSOR_ARCHITEW6432',
  'LANG',
  'LC_ALL',
] as const;

type PythonCandidate = {
  command: string;
  prefixArgs: string[];
};

const SUPPORTED_PYTHON_MINOR_VERSIONS = [14, 13, 12, 11] as const;

export type CompetitionEngineDiscoveryOptions = {
  env?: NodeJS.ProcessEnv;
  cwd?: string;
  platform?: NodeJS.Platform;
  probe?: (candidate: PythonCandidate, env: Record<string, string>) => Promise<boolean>;
  fileExists?: (target: string) => Promise<boolean>;
};

export class CompetitionEngineDiscoveryError extends Error {
  readonly code: string;

  constructor(code: string, message: string) {
    super(message);
    this.name = 'CompetitionEngineDiscoveryError';
    this.code = code;
  }
}

export async function discoverCompetitionEngineLaunch(
  options: CompetitionEngineDiscoveryOptions = {}
): Promise<CompetitionEngineLaunch> {
  const sourceEnv = options.env ?? process.env;
  const cwd = path.resolve(options.cwd ?? process.cwd());
  const platform = options.platform ?? process.platform;
  const sourceRoot = await findEngineSourceRoot(sourceEnv, cwd);
  const env = buildChildEnvironment(sourceEnv, sourceRoot);
  const candidates = await pythonCandidates(sourceEnv, platform, options.fileExists ?? isFile);
  const probe = options.probe ?? probePython;
  for (const candidate of candidates) {
    // eslint-disable-next-line no-await-in-loop -- Candidate priority is part of the discovery contract.
    if (await probe(candidate, env)) {
      return {
        command: candidate.command,
        args: [...candidate.prefixArgs, '-B', '-m', 'deepscientist_ioai_engine.interface'],
        cwd: path.dirname(sourceRoot),
        env,
      };
    }
  }
  throw new CompetitionEngineDiscoveryError(
    'python_not_found',
    `Python 3.11 or later was not found. Install a supported Python runtime or set ${IOAI_COMPETITION_PYTHON_ENV} to its executable.`
  );
}

async function findEngineSourceRoot(sourceEnv: NodeJS.ProcessEnv, cwd: string): Promise<string> {
  const configured = sourceEnv[IOAI_COMPETITION_ENGINE_ROOT_ENV]?.trim();
  const roots = [configured, path.join(cwd, 'packages', 'ioai-competition-engine')].filter(
    (value): value is string => !!value
  );
  for (const root of roots) {
    const resolved = path.resolve(root);
    const candidates = [path.join(resolved, 'src'), resolved];
    for (const candidate of candidates) {
      // eslint-disable-next-line no-await-in-loop -- Prefer the conventional src layout when both exist.
      if (await isDirectory(path.join(candidate, 'deepscientist_ioai_engine'))) return candidate;
    }
  }
  throw new CompetitionEngineDiscoveryError(
    'engine_source_not_found',
    `IOAI engine source was not found. Set ${IOAI_COMPETITION_ENGINE_ROOT_ENV} to the packaged engine root.`
  );
}

function buildChildEnvironment(sourceEnv: NodeJS.ProcessEnv, sourceRoot: string): Record<string, string> {
  const env: Record<string, string> = {};
  for (const key of SAFE_ENV_KEYS) {
    const value = sourceEnv[key];
    if (value) env[key] = value;
  }
  env.PYTHONPATH = sourceRoot;
  env.PYTHONIOENCODING = 'utf-8';
  env.PYTHONUNBUFFERED = '1';
  return env;
}

async function pythonCandidates(
  sourceEnv: NodeJS.ProcessEnv,
  platform: NodeJS.Platform,
  fileExists: (target: string) => Promise<boolean>
): Promise<PythonCandidate[]> {
  const configured = sourceEnv[IOAI_COMPETITION_PYTHON_ENV]?.trim();
  const candidates: PythonCandidate[] = [];
  if (configured) candidates.push({ command: configured, prefixArgs: [] });
  const bundledSciencePython = sourceEnv.DEEPSCIENTIST_SCIENCE_PYTHON?.trim();
  if (bundledSciencePython) candidates.push({ command: bundledSciencePython, prefixArgs: [] });
  if (platform === 'win32') {
    candidates.push(...(await existingWindowsPythonCandidates(sourceEnv, fileExists)));
    candidates.push({ command: 'py', prefixArgs: ['-3'] });
  } else {
    candidates.push(...(await existingUnixPythonCandidates(sourceEnv, platform, fileExists)));
    for (const minor of SUPPORTED_PYTHON_MINOR_VERSIONS) {
      candidates.push({ command: `python3.${minor}`, prefixArgs: [] });
    }
  }
  candidates.push({ command: platform === 'win32' ? 'python' : 'python3', prefixArgs: [] });
  if (platform !== 'win32') candidates.push({ command: 'python', prefixArgs: [] });
  return candidates.filter(
    (candidate, index, all) =>
      all.findIndex(
        (item) => item.command === candidate.command && item.prefixArgs.join('\0') === candidate.prefixArgs.join('\0')
      ) === index
  );
}

async function existingUnixPythonCandidates(
  sourceEnv: NodeJS.ProcessEnv,
  platform: NodeJS.Platform,
  fileExists: (target: string) => Promise<boolean>
): Promise<PythonCandidate[]> {
  const home = sourceEnv.HOME?.trim();
  const directCandidates = [
    sourceEnv.VIRTUAL_ENV ? path.join(sourceEnv.VIRTUAL_ENV, 'bin', 'python3') : undefined,
    sourceEnv.CONDA_PREFIX ? path.join(sourceEnv.CONDA_PREFIX, 'bin', 'python3') : undefined,
    home ? path.join(home, '.pyenv', 'shims', 'python3') : undefined,
  ];
  const binRoots = [
    ...(platform === 'darwin' ? ['/opt/homebrew/bin'] : []),
    '/usr/local/bin',
    '/usr/bin',
    ...(home ? [path.join(home, '.local', 'bin')] : []),
  ];
  for (const minor of SUPPORTED_PYTHON_MINOR_VERSIONS) {
    for (const root of binRoots) directCandidates.push(path.join(root, `python3.${minor}`));
    if (platform === 'darwin') {
      directCandidates.push(
        path.join('/Library/Frameworks/Python.framework/Versions', `3.${minor}`, 'bin', `python3.${minor}`)
      );
    }
  }
  const absoluteCandidates = directCandidates.filter((value): value is string => !!value && path.isAbsolute(value));
  const existence = await Promise.all(absoluteCandidates.map((candidate) => fileExists(candidate)));
  return absoluteCandidates
    .filter((_candidate, index) => existence[index])
    .map((command): PythonCandidate => ({ command, prefixArgs: [] }));
}

async function existingWindowsPythonCandidates(
  sourceEnv: NodeJS.ProcessEnv,
  fileExists: (target: string) => Promise<boolean>
): Promise<PythonCandidate[]> {
  const directCandidates = [
    sourceEnv.VIRTUAL_ENV ? path.win32.join(sourceEnv.VIRTUAL_ENV, 'Scripts', 'python.exe') : undefined,
    sourceEnv.CONDA_PREFIX ? path.win32.join(sourceEnv.CONDA_PREFIX, 'python.exe') : undefined,
  ];
  const localAppData =
    sourceEnv.LOCALAPPDATA ||
    (sourceEnv.USERPROFILE ? path.win32.join(sourceEnv.USERPROFILE, 'AppData', 'Local') : undefined);
  const versionRoots = [
    localAppData ? path.win32.join(localAppData, 'Programs', 'Python') : undefined,
    sourceEnv.ProgramFiles,
    sourceEnv.ProgramW6432,
    sourceEnv.SystemDrive,
  ].filter((value): value is string => !!value && path.win32.isAbsolute(value));
  for (const minor of SUPPORTED_PYTHON_MINOR_VERSIONS) {
    const directory = `Python3${minor}`;
    for (const root of versionRoots) directCandidates.push(path.win32.join(root, directory, 'python.exe'));
  }
  const absoluteCandidates = directCandidates.filter(
    (value): value is string => !!value && path.win32.isAbsolute(value)
  );
  const existence = await Promise.all(absoluteCandidates.map((candidate) => fileExists(candidate)));
  return absoluteCandidates
    .filter((_candidate, index) => existence[index])
    .map((command): PythonCandidate => ({ command, prefixArgs: [] }));
}

async function probePython(candidate: PythonCandidate, env: Record<string, string>): Promise<boolean> {
  return await new Promise((resolve) => {
    const child = spawn(
      candidate.command,
      [...candidate.prefixArgs, '-B', '-c', 'import sys; raise SystemExit(0 if sys.version_info >= (3, 11) else 1)'],
      {
        env,
        shell: false,
        windowsHide: true,
        stdio: 'ignore',
      }
    );
    const timer = setTimeout(() => {
      child.kill();
      resolve(false);
    }, 3000);
    timer.unref?.();
    child.once('error', () => {
      clearTimeout(timer);
      resolve(false);
    });
    child.once('close', (code) => {
      clearTimeout(timer);
      resolve(code === 0);
    });
  });
}

async function isDirectory(target: string): Promise<boolean> {
  try {
    return (await stat(target)).isDirectory();
  } catch {
    return false;
  }
}

async function isFile(target: string): Promise<boolean> {
  try {
    return (await stat(target)).isFile();
  } catch {
    return false;
  }
}
