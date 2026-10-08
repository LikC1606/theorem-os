/**
 * @license
 * Copyright 2026 DeepScientist (deepscientist.cc)
 * SPDX-License-Identifier: Apache-2.0
 */

import crypto from 'node:crypto';

export const PROJECT_MANIFEST_SCHEMA = 'deepscientist.project.v1' as const;

const RUNTIME_ONLY_KEYS = new Set(['artifactRepoPath', 'deepScientistRoot', 'projectPath', 'projectRoot']);

type ProjectManifestRecord = Record<string, unknown>;

const timestamp = (value: unknown, fallback: number): number => {
  if (typeof value === 'number' && Number.isFinite(value)) return value;
  if (typeof value === 'string') {
    const parsed = Date.parse(value);
    if (Number.isFinite(parsed)) return parsed;
  }
  return fallback;
};

const nonEmptyString = (value: unknown): string | undefined =>
  typeof value === 'string' && value.trim() ? value.trim() : undefined;

export const createProjectId = (): string => `osp_${crypto.randomBytes(8).toString('hex')}`;

export const mergeProjectManifest = (
  raw: unknown,
  options: {
    projectId?: string;
    name?: string;
    goal?: string;
    managed?: boolean;
    createdAt?: number;
    updatedAt?: number;
  } = {}
): { manifest: ProjectManifestRecord; projectId: string; createdAt: number; updatedAt: number } => {
  const source = raw && typeof raw === 'object' && !Array.isArray(raw) ? (raw as ProjectManifestRecord) : {};
  const portable = Object.fromEntries(Object.entries(source).filter(([key]) => !RUNTIME_ONLY_KEYS.has(key)));
  const fallbackCreatedAt = options.createdAt ?? Date.now();
  const createdAt = timestamp(source.createdAt, fallbackCreatedAt);
  const updatedAt = timestamp(source.updatedAt, options.updatedAt ?? createdAt);
  const projectId =
    nonEmptyString(options.projectId) ||
    nonEmptyString(source.projectId) ||
    nonEmptyString(source.id) ||
    createProjectId();
  const name = nonEmptyString(options.name) || nonEmptyString(source.name);
  const goal = nonEmptyString(options.goal) || nonEmptyString(source.goal);
  const managed = options.managed ?? (typeof source.managed === 'boolean' ? source.managed : undefined);

  const manifest: ProjectManifestRecord = {
    ...portable,
    schema: PROJECT_MANIFEST_SCHEMA,
    id: projectId,
    projectId,
    ...(name ? { name } : {}),
    ...(goal ? { goal } : {}),
    ...(managed == null ? {} : { managed }),
    createdAt: new Date(createdAt).toISOString(),
    updatedAt: new Date(updatedAt).toISOString(),
    artifactRepoRelativePath: '.deepscientist/artifact-repo',
    scienceArtifactsRelativePath: '.deepscientist/science-artifacts',
    exportsRelativePath: '.deepscientist/exports',
  };

  return { manifest, projectId, createdAt, updatedAt };
};
