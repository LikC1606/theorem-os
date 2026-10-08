/**
 * @license
 * Copyright 2026 DeepScientist (deepscientist.cc)
 * SPDX-License-Identifier: Apache-2.0
 */

import { spawn } from 'node:child_process';
import { existsSync } from 'node:fs';
import path from 'node:path';
import packageJson from "../../../package.json";
import type { IoaiCompetitionRuntimeAttestation } from "../../common/chat/ioaiCompetition";
import { discoverCompetitionEngineLaunch } from "./engineDiscovery";
import type { CompetitionEngineLaunch } from "./jsonlClient";
import { IOAI_ENGINE_PROTOCOL_VERSION } from "./protocol";

type CompetitionRuntimeIdentity = {
  executable: string;
  version: string;
  engineVersion: string;
};

export type CompetitionRuntimeAttestation = IoaiCompetitionRuntimeAttestation;

type RuntimeManifestLibrary = {
  IOAI_COMPETITION_RUNTIME_MANIFEST_FILENAME: string;
  IoaiCompetitionRuntimeMismatchError: new (
    reason: string,
    message: string,
    details?: Record<string, unknown>
  ) => Error & { code: string; reason: string };
  verifyIoaiCompetitionRuntimeManifest: (options: Record<string, unknown>) => CompetitionRuntimeAttestation;
};

const runtimeManifestLibrary =
  require("../../shared/ioai-competition-runtime-manifest.js") as RuntimeManifestLibrary;

export type CompetitionRuntimeAttestationOptions = {
  bundlePath: string;
  manifestPath?: string;
  deepScientistVersion?: string;
  discoverLaunch?: () => Promise<CompetitionEngineLaunch>;
  probeIdentity?: (launch: CompetitionEngineLaunch) => Promise<CompetitionRuntimeIdentity>;
};

export async function attestCompetitionRuntime(
  options: CompetitionRuntimeAttestationOptions
): Promise<CompetitionRuntimeAttestation> {
  const launch = await (options.discoverLaunch ?? discoverCompetitionEngineLaunch)();
  const identity = await (options.probeIdentity ?? probeCompetitionRuntimeIdentity)(launch);
  const engineRoot = resolveEnginePackageRoot(launch);
  return runtimeManifestLibrary.verifyIoaiCompetitionRuntimeManifest({
    manifestPath:
      options.manifestPath ??
      path.join(path.dirname(options.bundlePath), runtimeManifestLibrary.IOAI_COMPETITION_RUNTIME_MANIFEST_FILENAME),
    bundlePath: options.bundlePath,
    engineRoot,
    expectedProtocolVersion: IOAI_ENGINE_PROTOCOL_VERSION,
    expectedDeepScientistVersion: options.deepScientistVersion ?? packageJson.version,
    expectedEngineVersion: identity.engineVersion,
    python: { executable: identity.executable, version: identity.version },
  });
}

export async function probeCompetitionRuntimeIdentity(
  launch: CompetitionEngineLaunch
): Promise<CompetitionRuntimeIdentity> {
  const prefixEnd = launch.args.indexOf('-B');
  const prefixArgs = prefixEnd < 0 ? [] : launch.args.slice(0, prefixEnd);
  const script = [
    'import json, platform, sys',
    'import deepscientist_ioai_engine as engine',
    'print(json.dumps({"executable": sys.executable, "version": platform.python_version(), "engineVersion": engine.__version__}))',
  ].join('; ');
  return await new Promise((resolve, reject) => {
    const child = spawn(launch.command, [...prefixArgs, '-B', '-c', script], {
      cwd: launch.cwd,
      env: launch.env,
      shell: false,
      windowsHide: true,
      stdio: ['ignore', 'pipe', 'pipe'],
    });
    let stdout = '';
    let stderr = '';
    let settled = false;
    const finish = (error?: Error, identity?: CompetitionRuntimeIdentity) => {
      if (settled) return;
      settled = true;
      clearTimeout(timer);
      if (error) reject(error);
      else resolve(identity as CompetitionRuntimeIdentity);
    };
    const fail = (reason: string, details: Record<string, unknown> = {}) =>
      finish(
        new runtimeManifestLibrary.IoaiCompetitionRuntimeMismatchError('python_runtime_unavailable', reason, details)
      );
    const timer = setTimeout(() => {
      child.kill();
      fail('IOAI Python runtime identity probe timed out');
    }, 5000);
    timer.unref?.();
    child.stdout.on('data', (chunk: Buffer) => {
      stdout = `${stdout}${chunk.toString('utf8')}`.slice(-16_384);
    });
    child.stderr.on('data', (chunk: Buffer) => {
      stderr = `${stderr}${chunk.toString('utf8')}`.slice(-4096);
    });
    child.once('error', (error) =>
      fail('IOAI Python runtime identity probe failed to launch', { cause: error.message })
    );
    child.once('close', (code) => {
      if (settled) return;
      if (code !== 0) {
        fail('IOAI Python runtime identity probe exited abnormally', { exit_code: code, stderr: stderr.trim() });
        return;
      }
      try {
        const parsed = JSON.parse(stdout.trim()) as Partial<CompetitionRuntimeIdentity>;
        if (!parsed.executable || !parsed.version || !parsed.engineVersion)
          throw new Error('identity fields are missing');
        finish(undefined, parsed as CompetitionRuntimeIdentity);
      } catch (error) {
        fail('IOAI Python runtime identity probe returned invalid output', {
          cause: error instanceof Error ? error.message : String(error),
        });
      }
    });
  });
}

function resolveEnginePackageRoot(launch: CompetitionEngineLaunch): string {
  const sourceRoot = launch.env.PYTHONPATH;
  const candidates = [launch.cwd, sourceRoot ? path.dirname(sourceRoot) : undefined].filter(
    (candidate): candidate is string => Boolean(candidate)
  );
  const root = candidates.find(
    (candidate) =>
      existsSync(path.join(candidate, 'pyproject.toml')) &&
      existsSync(path.join(candidate, 'src', 'deepscientist_ioai_engine'))
  );
  if (root) return root;
  throw new runtimeManifestLibrary.IoaiCompetitionRuntimeMismatchError(
    'engine_source_tree_unreadable',
    'IOAI engine package root could not be resolved from the discovered launch'
  );
}
