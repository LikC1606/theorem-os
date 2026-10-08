/**
 * @license
 * Copyright 2026 DeepScientist (deepscientist.cc)
 * SPDX-License-Identifier: Apache-2.0
 */

import { existsSync } from 'node:fs';
import path from 'node:path';
import {
  BUILTIN_IOAI_COMPETITION_NAME,
  IOAI_COMPETITION_CORE_BASE_URL_ENV,
} from "../../common/config/builtinMcpConstants";

export const IOAI_COMPETITION_ENGINE_ROOT_ENV = 'DEEPSCIENTIST_IOAI_ENGINE_ROOT';
export const IOAI_COMPETITION_PYTHON_ENV = 'DEEPSCIENTIST_IOAI_PYTHON';
export const IOAI_COMPETITION_MCP_SCRIPT_NAME = 'builtin-mcp-ioai-competition';
export const IOAI_COMPETITION_MCP_DESCRIPTION =
  'Built-in local bridge for Challenge workflows and role-scoped Research Team orchestration with isolated Git worktrees. Official competition submission stays disabled unless explicitly authorized.';
export const IOAI_COMPETITION_TOOL_APPROVAL_MODES = {
  ioai_competition: 'approve',
  challenge_delegate: 'approve',
  challenge_wait: 'approve',
  challenge_integrate: 'approve',
  research_team: 'approve',
} as const;

export type CompetitionRegistrationOptions = {
  env?: NodeJS.ProcessEnv;
  cwd?: string;
  resourcesPath?: string;
};

export type CompetitionMcpServerRegistration = {
  name: string;
  description: string;
  enabled: false;
  builtin: true;
  transport: {
    type: 'stdio';
    command: 'node';
    args: string[];
    env: Record<string, string>;
  };
  original_json: string;
};

export function resolveCompetitionEngineRoot(options: CompetitionRegistrationOptions = {}): string {
  const env = options.env ?? process.env;
  const cwd = path.resolve(options.cwd ?? process.cwd());
  const processResourcesPath = (process as NodeJS.Process & { resourcesPath?: string }).resourcesPath;
  const resourcesPath = (options.resourcesPath ?? processResourcesPath)?.trim();
  const configured = env[IOAI_COMPETITION_ENGINE_ROOT_ENV]?.trim();
  const configuredRoot = configured ? path.resolve(cwd, configured) : undefined;
  const developmentRoot = path.join(cwd, 'packages', 'ioai-competition-engine');
  const packagedRoot = resourcesPath ? path.resolve(resourcesPath, 'ioai-competition-engine') : undefined;
  const candidates = [configuredRoot, developmentRoot, packagedRoot].filter((candidate): candidate is string =>
    Boolean(candidate)
  );

  return candidates.find(hasCompetitionEnginePackage) ?? configuredRoot ?? packagedRoot ?? developmentRoot;
}

export function buildCompetitionMcpServerRegistration(
  scriptPath: string,
  options: CompetitionRegistrationOptions = {}
): CompetitionMcpServerRegistration {
  const envSource = options.env ?? process.env;
  const env: Record<string, string> = {
    [IOAI_COMPETITION_ENGINE_ROOT_ENV]: resolveCompetitionEngineRoot(options),
  };
  const configuredPython = envSource[IOAI_COMPETITION_PYTHON_ENV]?.trim();
  if (configuredPython) env[IOAI_COMPETITION_PYTHON_ENV] = configuredPython;
  const configuredCoreBaseUrl = envSource[IOAI_COMPETITION_CORE_BASE_URL_ENV]?.trim();
  const runtimePort = (globalThis as typeof globalThis & { __backendPort?: unknown }).__backendPort;
  const runtimeCoreBaseUrl =
    typeof runtimePort === 'number' && Number.isSafeInteger(runtimePort) && runtimePort > 0 && runtimePort <= 65_535
      ? `http://127.0.0.1:${runtimePort}`
      : undefined;
  if (configuredCoreBaseUrl || runtimeCoreBaseUrl) {
    // The desktop Core binds an ephemeral port on every launch.  A value
    // inherited from an earlier process is only a fallback; persisting it in
    // preference to the live port leaves long-lived MCP registrations pointed
    // at a dead listener after the next restart.
    env[IOAI_COMPETITION_CORE_BASE_URL_ENV] = runtimeCoreBaseUrl ?? configuredCoreBaseUrl!;
  }

  const serverConfig = {
    command: 'node' as const,
    args: [scriptPath],
    env,
  };
  return {
    name: BUILTIN_IOAI_COMPETITION_NAME,
    description: IOAI_COMPETITION_MCP_DESCRIPTION,
    enabled: false,
    builtin: true,
    transport: {
      type: 'stdio',
      ...serverConfig,
    },
    original_json: JSON.stringify({ mcpServers: { [BUILTIN_IOAI_COMPETITION_NAME]: serverConfig } }, null, 2),
  };
}

function hasCompetitionEnginePackage(root: string): boolean {
  return [path.join(root, 'src', 'deepscientist_ioai_engine'), path.join(root, 'deepscientist_ioai_engine')].some(
    (candidate) => existsSync(candidate)
  );
}
