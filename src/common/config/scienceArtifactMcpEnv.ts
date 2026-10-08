/**
 * @license
 * Copyright 2026 DeepScientist (deepscientist.cc)
 * SPDX-License-Identifier: Apache-2.0
 */

export const SCIENCE_ARTIFACT_ENV_KEYS = {
  strictProvenance: 'DEEPSCIENTIST_STRICT_PROVENANCE',
  writeProjectManifest: 'DEEPSCIENTIST_WRITE_PROJECT_MANIFEST',
  defaultSkillIds: 'DEEPSCIENTIST_DEFAULT_SKILL_IDS',
  allowedDatabaseHosts: 'DEEPSCIENTIST_ALLOWED_DATABASE_HOSTS',
  artifactGitMaxCopyBytes: 'DEEPSCIENTIST_ARTIFACT_GIT_MAX_COPY_BYTES',
} as const;
