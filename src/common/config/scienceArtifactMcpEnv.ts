/**
 * @license
 * Copyright 2026 DeepScientist (deepscientist.cc)
 * SPDX-License-Identifier: Apache-2.0
 */

import { normalizeScienceDefaultSkillIds } from "../chat/science";
import type { ScienceArtifactConfig } from "./storage";

export const SCIENCE_ARTIFACT_ENV_KEYS = {
  strictProvenance: 'DEEPSCIENTIST_STRICT_PROVENANCE',
  writeProjectManifest: 'DEEPSCIENTIST_WRITE_PROJECT_MANIFEST',
  defaultSkillIds: 'DEEPSCIENTIST_DEFAULT_SKILL_IDS',
  allowedDatabaseHosts: 'DEEPSCIENTIST_ALLOWED_DATABASE_HOSTS',
  artifactGitMaxCopyBytes: 'DEEPSCIENTIST_ARTIFACT_GIT_MAX_COPY_BYTES',
} as const;

export type ScienceArtifactMcpEnvResolveResult = {
  ok: true;
  env: Record<string, string>;
  config: ScienceArtifactConfig;
};

export function removeScienceArtifactEnvKeys(env?: Record<string, string>): Record<string, string> {
  const next = { ...env };
  for (const key of Object.values(SCIENCE_ARTIFACT_ENV_KEYS)) {
    delete next[key];
  }
  return next;
}

export function resolveScienceArtifactMcpEnv(
  config?: ScienceArtifactConfig,
  existingEnv?: Record<string, string>
): ScienceArtifactMcpEnvResolveResult {
  const strictProvenance =
    config?.strictProvenance ??
    (existingEnv?.[SCIENCE_ARTIFACT_ENV_KEYS.strictProvenance]
      ? existingEnv[SCIENCE_ARTIFACT_ENV_KEYS.strictProvenance] === 'true'
      : false);
  const writeProjectManifest =
    config?.writeProjectManifest ??
    (existingEnv?.[SCIENCE_ARTIFACT_ENV_KEYS.writeProjectManifest]
      ? existingEnv[SCIENCE_ARTIFACT_ENV_KEYS.writeProjectManifest] !== 'false'
      : true);
  const defaultSkillIds = normalizeScienceDefaultSkillIds(
    config?.defaultSkillIds?.length
      ? config.defaultSkillIds
      : existingEnv?.[SCIENCE_ARTIFACT_ENV_KEYS.defaultSkillIds]?.split(',').filter(Boolean)
  );
  const allowedDatabaseHosts = config?.allowedDatabaseHosts?.length
    ? config.allowedDatabaseHosts
    : (existingEnv?.[SCIENCE_ARTIFACT_ENV_KEYS.allowedDatabaseHosts]?.split(',').filter(Boolean) ?? []);
  const artifactGitMaxCopyBytes =
    existingEnv?.[SCIENCE_ARTIFACT_ENV_KEYS.artifactGitMaxCopyBytes] || String(25 * 1024 * 1024);

  const env: Record<string, string> = {
    [SCIENCE_ARTIFACT_ENV_KEYS.strictProvenance]: strictProvenance ? 'true' : 'false',
    [SCIENCE_ARTIFACT_ENV_KEYS.writeProjectManifest]: writeProjectManifest ? 'true' : 'false',
    [SCIENCE_ARTIFACT_ENV_KEYS.defaultSkillIds]: defaultSkillIds.join(','),
    [SCIENCE_ARTIFACT_ENV_KEYS.allowedDatabaseHosts]: allowedDatabaseHosts.join(','),
    [SCIENCE_ARTIFACT_ENV_KEYS.artifactGitMaxCopyBytes]: artifactGitMaxCopyBytes,
  };

  return {
    ok: true,
    env,
    config: {
      ...config,
      strictProvenance,
      writeProjectManifest,
      defaultSkillIds,
      allowedDatabaseHosts,
    },
  };
}
