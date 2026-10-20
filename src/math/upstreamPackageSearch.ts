/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

import fs from 'node:fs';
import path from 'node:path';
const MAX_RESPONSE_BYTES = 2 * 1024 * 1024;

export type LeanProjectPackageDependency = Readonly<{
  name: string;
  revision: string;
  url?: string;
  inputRevision?: string;
  subdirectory?: string;
}>;

export const objectValue = (value: unknown): Record<string, unknown> | undefined =>
  value !== null && typeof value === 'object' && !Array.isArray(value) ? (value as Record<string, unknown>) : undefined;

const stringValue = (value: unknown): string | undefined =>
  typeof value === 'string' && value.trim() ? value.trim() : undefined;

const exactRepositoryName = (query: string): string | undefined => {
  const match = /^@?([A-Za-z0-9_.-]+)\/([A-Za-z0-9_.-]+)$/u.exec(query.trim());
  return match ? `${match[1]}/${match[2]}` : undefined;
};

export const leanRepositoryIdentity = (value: string): string | undefined => {
  const normalized = value
    .trim()
    .replace(/\.git$/iu, '')
    .replace(/\/+$/u, '');
  const exact = exactRepositoryName(normalized);
  if (exact) return exact.toLowerCase();
  const github = /(?:github\.com[/:])([A-Za-z0-9_.-]+)\/([A-Za-z0-9_.-]+)$/iu.exec(normalized);
  return github ? `${github[1]}/${github[2]}`.toLowerCase() : undefined;
};

export async function readLeanProjectPackageInventory(
  projectRoot: string
): Promise<readonly LeanProjectPackageDependency[]> {
  return fs.promises
    .readFile(path.join(projectRoot, 'lake-manifest.json'), 'utf8')
    .then((value) => {
      if (Buffer.byteLength(value, 'utf8') > MAX_RESPONSE_BYTES) return Object.freeze([]);
      const manifest = objectValue(JSON.parse(value) as unknown);
      const packages = Array.isArray(manifest?.packages) ? manifest.packages.map(objectValue).filter(Boolean) : [];
      return Object.freeze(
        packages.flatMap((candidate) => {
          const name = stringValue(candidate?.name);
          const revision = stringValue(candidate?.rev);
          if (!name || !revision) return [];
          return [
            Object.freeze({
              name,
              revision,
              ...(stringValue(candidate?.url) ? { url: stringValue(candidate?.url) } : {}),
              ...(stringValue(candidate?.inputRev) ? { inputRevision: stringValue(candidate?.inputRev) } : {}),
              ...(stringValue(candidate?.subDir) ? { subdirectory: stringValue(candidate?.subDir) } : {}),
            }),
          ];
        })
      );
    })
    .catch(() => Object.freeze([]));
}
