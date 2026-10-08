/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

import fs from 'node:fs';
import path from 'node:path';
import type {
  MathematicsUpstreamPackage,
  MathematicsUpstreamPackageAdoptionStatus,
  MathematicsUpstreamPackageCompatibility,
  MathematicsUpstreamPackageLocalAvailability,
  MathematicsUpstreamPackageSearchAttempt,
  MathematicsUpstreamPackageUsageAction,
} from "../common/chat/mathematics";

/* Sequential awaits in this file are bounded retry backoff, not unbounded polling. */
/* eslint-disable no-await-in-loop */

const GITHUB_REPOSITORY_SEARCH_ENDPOINT = 'https://api.github.com/search/repositories';
const RESERVOIR_ENDPOINT = 'https://reservoir.lean-lang.org/api/v1/packages';
const DEFAULT_RESULT_LIMIT = 6;
const DEFAULT_REPOSITORY_LIMIT = 8;
const DEFAULT_TIMEOUT_MS = 8_000;
const DEFAULT_MAX_RETRIES = 2;
const DEFAULT_RETRY_BASE_DELAY_MS = 200;
const MAX_RETRY_DELAY_MS = 5_000;
const MAX_RESPONSE_BYTES = 2 * 1024 * 1024;
const PACKAGE_CACHE_TTL_MS = 30_000;
const PACKAGE_CACHE_MAX_ENTRIES = 64;

type FetchLike = (input: string | URL | Request, init?: RequestInit) => Promise<Response>;

const transientHttpStatus = (status: number): boolean =>
  status === 408 || status === 425 || status === 429 || status >= 500;

const retryAfterMilliseconds = (headers: Headers, now = Date.now()): number | undefined => {
  const value = headers.get('retry-after')?.trim();
  if (!value) return undefined;
  const seconds = Number(value);
  if (Number.isFinite(seconds) && seconds >= 0) {
    return Math.min(MAX_RETRY_DELAY_MS, Math.max(0, Math.round(seconds * 1_000)));
  }
  const timestamp = Date.parse(value);
  return Number.isFinite(timestamp) ? Math.min(MAX_RETRY_DELAY_MS, Math.max(0, timestamp - now)) : undefined;
};

const retryDelayMilliseconds = (headers: Headers, attempt: number, baseDelayMs: number): number => {
  const hinted = retryAfterMilliseconds(headers);
  if (hinted !== undefined) return hinted;
  const exponential = baseDelayMs * 2 ** Math.max(0, attempt - 1);
  // A small deterministic jitter avoids a group of workers retrying at once.
  const jitter = Math.min(100, Math.round(baseDelayMs / 2));
  return Math.min(MAX_RETRY_DELAY_MS, exponential + jitter);
};

const waitForRetry = (delayMs: number): Promise<void> =>
  delayMs <= 0 ? Promise.resolve() : new Promise((resolve) => setTimeout(resolve, delayMs));

export type LeanProjectCompatibility = Readonly<{
  leanToolchain?: string;
  mathlibRevision?: string;
  installedPackages?: readonly LeanProjectPackageDependency[];
}>;

export type LeanProjectPackageDependency = Readonly<{
  name: string;
  revision: string;
  url?: string;
  inputRevision?: string;
  subdirectory?: string;
}>;

export type MathematicsUpstreamPackageSearchResult = Readonly<{
  packages: readonly MathematicsUpstreamPackage[];
  attempts: readonly MathematicsUpstreamPackageSearchAttempt[];
}>;

type RepositoryCandidate = Readonly<{
  fullName: string;
  description?: string;
  topics: readonly string[];
}>;

type UnrankedPackage = Omit<MathematicsUpstreamPackage, 'providerRank'>;

const objectValue = (value: unknown): Record<string, unknown> | undefined =>
  value !== null && typeof value === 'object' && !Array.isArray(value) ? (value as Record<string, unknown>) : undefined;

const stringValue = (value: unknown): string | undefined =>
  typeof value === 'string' && value.trim() ? value.trim() : undefined;

const numberValue = (value: unknown): number | undefined =>
  typeof value === 'number' && Number.isFinite(value) ? value : undefined;

const stringArray = (value: unknown): readonly string[] =>
  Array.isArray(value)
    ? value.flatMap((item) => {
        const text = stringValue(item);
        return text ? [text] : [];
      })
    : [];

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

const excludedSolutionCorpus = (repository: RepositoryCandidate): boolean => {
  const searchable = [repository.fullName, repository.description ?? '', ...repository.topics].join(' ');
  return /(?:^|[^a-z])(?:benchmark|dataset|reference solutions?|solution corpus|problem statements?|competition problems?|formal[-_ ]?(?:conjectures|imo)|lean[_ -]?eval|mini[fF]2[fF]|lean[-_ ]?euclid)(?:[^a-z]|$)/iu.test(
    searchable
  );
};

const readJsonResponse = async (
  fetchImpl: FetchLike,
  url: string,
  errorPrefix: string,
  timeoutMs: number,
  maxRetries: number,
  retryBaseDelayMs: number
): Promise<unknown> => {
  for (let attempt = 0; ; attempt += 1) {
    const controller = new AbortController();
    const timeout = setTimeout(() => controller.abort(), timeoutMs);
    let response: Response;
    try {
      try {
        response = await fetchImpl(url, {
          method: 'GET',
          headers: {
            accept: 'application/vnd.github+json, application/json',
            'user-agent': 'DeepScientist Lean package discovery',
          },
          signal: controller.signal,
        });
      } catch (error) {
        if (attempt >= maxRetries) throw error;
        await waitForRetry(retryDelayMilliseconds(new Headers(), attempt + 1, retryBaseDelayMs));
        continue;
      }
    } finally {
      clearTimeout(timeout);
    }
    if (!response.ok) {
      if (transientHttpStatus(response.status) && attempt < maxRetries) {
        await waitForRetry(retryDelayMilliseconds(response.headers, attempt + 1, retryBaseDelayMs));
        continue;
      }
      throw new TypeError(`${errorPrefix}_http_${response.status}`);
    }
    const contentLength = Number(response.headers.get('content-length'));
    if (Number.isFinite(contentLength) && contentLength > MAX_RESPONSE_BYTES) {
      throw new TypeError(`${errorPrefix}_response_too_large`);
    }
    const text = await response.text();
    if (Buffer.byteLength(text, 'utf8') > MAX_RESPONSE_BYTES) {
      throw new TypeError(`${errorPrefix}_response_too_large`);
    }
    try {
      return JSON.parse(text) as unknown;
    } catch {
      throw new TypeError(`${errorPrefix}_invalid_response`);
    }
  }
};

const parseGitHubRepositories = (payload: unknown, limit: number): readonly RepositoryCandidate[] => {
  const items = objectValue(payload)?.items;
  if (!Array.isArray(items)) throw new TypeError('github_package_search_invalid_response');
  const repositories: RepositoryCandidate[] = [];
  for (const entry of items) {
    const item = objectValue(entry);
    const fullName = stringValue(item?.full_name);
    const normalizedFullName = fullName ? exactRepositoryName(fullName) : undefined;
    if (!normalizedFullName || item?.archived === true || item?.fork === true) continue;
    repositories.push(
      Object.freeze({
        fullName: normalizedFullName,
        ...(stringValue(item?.description) ? { description: stringValue(item?.description) } : {}),
        topics: Object.freeze([...stringArray(item?.topics)]),
      })
    );
    if (repositories.length >= limit) break;
  }
  return Object.freeze(repositories);
};

const discoverRepositories = async (
  query: string,
  fetchImpl: FetchLike,
  repositoryLimit: number,
  timeoutMs: number,
  maxRetries: number,
  retryBaseDelayMs: number
): Promise<readonly RepositoryCandidate[]> => {
  const exact = exactRepositoryName(query);
  if (exact) return Object.freeze([{ fullName: exact, topics: Object.freeze([]) }]);
  const search = `${query.trim()} language:Lean archived:false fork:false`;
  const url = `${GITHUB_REPOSITORY_SEARCH_ENDPOINT}?${new URLSearchParams({
    q: search,
    sort: 'updated',
    order: 'desc',
    per_page: String(repositoryLimit),
  })}`;
  return parseGitHubRepositories(
    await readJsonResponse(fetchImpl, url, 'github_package_search', timeoutMs, maxRetries, retryBaseDelayMs),
    repositoryLimit
  );
};

const parseVersions = (value: unknown): readonly Record<string, unknown>[] => {
  const data = objectValue(value)?.data;
  if (!Array.isArray(data)) throw new TypeError('reservoir_versions_invalid_response');
  return Object.freeze(
    data
      .flatMap((item) => {
        const version = objectValue(item);
        return version && stringValue(version.revision) ? [version] : [];
      })
      .toSorted((left, right) => (stringValue(right.date) ?? '').localeCompare(stringValue(left.date) ?? ''))
  );
};

const mathlibDependency = (version: Record<string, unknown>): Record<string, unknown> | undefined => {
  if (!Array.isArray(version.dependencies)) return undefined;
  return version.dependencies
    .map(objectValue)
    .find(
      (dependency) =>
        dependency &&
        (stringValue(dependency.name)?.toLowerCase() === 'mathlib' ||
          stringValue(dependency.url)?.toLowerCase().includes('leanprover-community/mathlib4'))
    );
};

const buildStatusForVersion = (
  value: unknown,
  revision: string,
  leanToolchain: string | undefined
): MathematicsUpstreamPackage['buildStatus'] => {
  const data = objectValue(value)?.data;
  if (!Array.isArray(data)) throw new TypeError('reservoir_builds_invalid_response');
  const matching = data
    .map(objectValue)
    .filter(
      (build): build is Record<string, unknown> =>
        Boolean(build) &&
        stringValue(build?.revision) === revision &&
        (!leanToolchain || stringValue(build?.toolchain) === leanToolchain)
    )
    .toSorted((left, right) => (stringValue(right.runAt) ?? '').localeCompare(stringValue(left.runAt) ?? ''))[0];
  if (matching?.built === true) return 'built';
  if (matching?.built === false) return 'failed';
  return 'unknown';
};

const packageCompatibility = (
  target: LeanProjectCompatibility,
  leanToolchain: string | undefined,
  mathlibRevision: string | undefined
): Readonly<{
  compatibility: MathematicsUpstreamPackageCompatibility;
  reasons: readonly string[];
}> => {
  const reasons: string[] = [];
  let comparisons = 0;
  let metadataIncomplete = false;
  if (target.leanToolchain && leanToolchain) {
    comparisons += 1;
    if (target.leanToolchain !== leanToolchain) reasons.push('lean_toolchain_mismatch');
  } else if (target.leanToolchain || leanToolchain) metadataIncomplete = true;
  if (target.mathlibRevision && mathlibRevision) {
    comparisons += 1;
    if (target.mathlibRevision !== mathlibRevision) reasons.push('mathlib_revision_mismatch');
  } else if (target.mathlibRevision || mathlibRevision) metadataIncomplete = true;
  if (reasons.length > 0) return Object.freeze({ compatibility: 'mismatch', reasons: Object.freeze(reasons) });
  if (comparisons > 0 && !metadataIncomplete) {
    return Object.freeze({ compatibility: 'exact', reasons: Object.freeze(['target_match']) });
  }
  return Object.freeze({ compatibility: 'unknown', reasons: Object.freeze(['target_metadata_incomplete']) });
};

const adoptionStatus = (
  compatibility: MathematicsUpstreamPackageCompatibility,
  license: string | undefined,
  buildStatus: MathematicsUpstreamPackage['buildStatus']
): MathematicsUpstreamPackageAdoptionStatus => {
  if (compatibility === 'mismatch') return 'incompatible';
  if (!license || license.toUpperCase() === 'NOASSERTION') return 'license_review_required';
  if (buildStatus !== 'built') return 'build_unverified';
  if (compatibility === 'unknown') return 'compatibility_review_required';
  return 'eligible';
};

const installedDependencyFor = (
  target: LeanProjectCompatibility,
  packageName: string,
  repositoryFullName: string
): LeanProjectPackageDependency | undefined => {
  const repositoryIdentity = leanRepositoryIdentity(repositoryFullName);
  return target.installedPackages?.find(
    (dependency) =>
      dependency.name.toLowerCase() === packageName.toLowerCase() ||
      (repositoryIdentity && dependency.url && leanRepositoryIdentity(dependency.url) === repositoryIdentity)
  );
};

type InspectedRegisteredVersion = Readonly<{
  value: Record<string, unknown>;
  revision: string;
  leanToolchain?: string;
  mathlibRevision?: string;
  mathlibInputRevision?: string;
  buildStatus: MathematicsUpstreamPackage['buildStatus'];
  compatibility: MathematicsUpstreamPackageCompatibility;
  compatibilityReasons: readonly string[];
}>;

const compatibilitySelectionRank: Readonly<Record<MathematicsUpstreamPackageCompatibility, number>> = Object.freeze({
  exact: 0,
  unknown: 1,
  mismatch: 2,
});

const buildSelectionRank: Readonly<Record<MathematicsUpstreamPackage['buildStatus'], number>> = Object.freeze({
  built: 0,
  unknown: 1,
  failed: 2,
});

const inspectRegisteredVersion = (
  value: Record<string, unknown>,
  buildsValue: unknown,
  target: LeanProjectCompatibility
): InspectedRegisteredVersion | undefined => {
  const revision = stringValue(value.revision);
  if (!revision) return undefined;
  const dependency = mathlibDependency(value);
  const leanToolchain = stringValue(value.toolchain);
  const mathlibRevision = stringValue(dependency?.rev);
  const mathlibInputRevision = stringValue(dependency?.inputRev);
  const compatibility = packageCompatibility(target, leanToolchain, mathlibRevision);
  return Object.freeze({
    value,
    revision,
    ...(leanToolchain ? { leanToolchain } : {}),
    ...(mathlibRevision ? { mathlibRevision } : {}),
    ...(mathlibInputRevision ? { mathlibInputRevision } : {}),
    buildStatus: buildStatusForVersion(buildsValue, revision, leanToolchain),
    compatibility: compatibility.compatibility,
    compatibilityReasons: compatibility.reasons,
  });
};

const selectRegisteredVersion = (
  versions: readonly Record<string, unknown>[],
  buildsValue: unknown,
  target: LeanProjectCompatibility,
  installedRevision: string | undefined
): InspectedRegisteredVersion | undefined =>
  versions
    .flatMap((value) => {
      const inspected = inspectRegisteredVersion(value, buildsValue, target);
      return inspected ? [inspected] : [];
    })
    .toSorted(
      (left, right) =>
        Number(right.revision === installedRevision) - Number(left.revision === installedRevision) ||
        compatibilitySelectionRank[left.compatibility] - compatibilitySelectionRank[right.compatibility] ||
        buildSelectionRank[left.buildStatus] - buildSelectionRank[right.buildStatus] ||
        (stringValue(right.value.date) ?? '').localeCompare(stringValue(left.value.date) ?? '')
    )[0];

const packageUsage = (
  adoption: MathematicsUpstreamPackageAdoptionStatus,
  revision: string,
  installed: LeanProjectPackageDependency | undefined
): Readonly<{
  localAvailability: MathematicsUpstreamPackageLocalAvailability;
  installedRevision?: string;
  usageAction: MathematicsUpstreamPackageUsageAction;
}> => {
  if (installed?.revision === revision) {
    return Object.freeze({
      localAvailability: 'installed_exact',
      installedRevision: installed.revision,
      usageAction: 'search_installed_package',
    });
  }
  if (installed) {
    return Object.freeze({
      localAvailability: 'installed_different_revision',
      installedRevision: installed.revision,
      usageAction: 'keep_pinned_local_revision',
    });
  }
  const usageAction: MathematicsUpstreamPackageUsageAction =
    adoption === 'eligible'
      ? 'request_dependency_approval'
      : adoption === 'license_review_required'
        ? 'review_license'
        : adoption === 'build_unverified'
          ? 'verify_registry_build'
          : 'resolve_compatibility';
  return Object.freeze({ localAvailability: 'not_installed', usageAction });
};

const reservoirPackageUrl = (repositoryFullName: string, suffix = ''): string => {
  const [owner, name] = repositoryFullName.split('/');
  return `${RESERVOIR_ENDPOINT}/${encodeURIComponent(owner)}/${encodeURIComponent(name)}${suffix}`;
};

const inspectReservoirPackage = async (
  repository: RepositoryCandidate,
  target: LeanProjectCompatibility,
  fetchImpl: FetchLike,
  timeoutMs: number,
  maxRetries: number,
  retryBaseDelayMs: number
): Promise<UnrankedPackage | undefined> => {
  let values: readonly unknown[];
  try {
    values = await Promise.all([
      readJsonResponse(
        fetchImpl,
        reservoirPackageUrl(repository.fullName),
        'reservoir_metadata',
        timeoutMs,
        maxRetries,
        retryBaseDelayMs
      ),
      readJsonResponse(
        fetchImpl,
        reservoirPackageUrl(repository.fullName, '/versions'),
        'reservoir_versions',
        timeoutMs,
        maxRetries,
        retryBaseDelayMs
      ),
      readJsonResponse(
        fetchImpl,
        reservoirPackageUrl(repository.fullName, '/builds'),
        'reservoir_builds',
        timeoutMs,
        maxRetries,
        retryBaseDelayMs
      ),
    ]);
  } catch (error) {
    if (error instanceof TypeError && error.message === 'reservoir_metadata_http_404') return undefined;
    throw error;
  }
  const [metadataValue, versionsValue, buildsValue] = values;
  if (!metadataValue || !versionsValue || !buildsValue) return undefined;
  const metadata = objectValue(metadataValue);
  const versions = parseVersions(versionsValue);
  if (!metadata || versions.length === 0) return undefined;
  const sources = Array.isArray(metadata.sources) ? metadata.sources.map(objectValue).filter(Boolean) : [];
  const githubSource = sources.find((source) => stringValue(source?.host) === 'github');
  const packageName = stringValue(metadata.name);
  const fullName = stringValue(metadata.fullName);
  const repositoryFullName = stringValue(githubSource?.fullName) ?? repository.fullName;
  const repositoryUrl = stringValue(githubSource?.repoUrl) ?? `https://github.com/${repositoryFullName}`;
  if (!packageName || !fullName) return undefined;
  const installed = installedDependencyFor(target, packageName, repositoryFullName);
  const selectedVersion = selectRegisteredVersion(versions, buildsValue, target, installed?.revision);
  if (!selectedVersion) return undefined;
  const license = stringValue(metadata.license) ?? stringValue(selectedVersion.value.license);
  const adoption = adoptionStatus(selectedVersion.compatibility, license, selectedVersion.buildStatus);
  const usage = packageUsage(adoption, selectedVersion.revision, installed);
  return Object.freeze({
    source: 'reservoir' as const,
    fullName,
    packageName,
    ...(stringValue(metadata.description) ? { description: stringValue(metadata.description) } : {}),
    repositoryFullName,
    repositoryUrl,
    registryUrl: `https://reservoir.lean-lang.org/@${encodeURIComponent(fullName.split('/')[0])}/${encodeURIComponent(packageName)}`,
    ...(stringValue(metadata.homepage) ? { homepageUrl: stringValue(metadata.homepage) } : {}),
    keywords: Object.freeze([...stringArray(metadata.keywords)]),
    ...(license ? { license } : {}),
    stars: numberValue(metadata.stars) ?? 0,
    updatedAt: stringValue(metadata.updatedAt) ?? stringValue(selectedVersion.value.date) ?? '',
    version: stringValue(selectedVersion.value.version) ?? '0.0.0',
    revision: selectedVersion.revision,
    ...(selectedVersion.leanToolchain ? { leanToolchain: selectedVersion.leanToolchain } : {}),
    ...(selectedVersion.mathlibRevision ? { mathlibRevision: selectedVersion.mathlibRevision } : {}),
    ...(selectedVersion.mathlibInputRevision ? { mathlibInputRevision: selectedVersion.mathlibInputRevision } : {}),
    buildStatus: selectedVersion.buildStatus,
    compatibility: selectedVersion.compatibility,
    compatibilityReasons: selectedVersion.compatibilityReasons,
    adoptionStatus: adoption,
    ...usage,
    dependencyMutationAllowed: false as const,
    targetValidationRequired: true as const,
  });
};

const packageErrorCode = (error: unknown): string => {
  if (error instanceof TypeError && /^[a-z]+_[a-z0-9_]+$/u.test(error.message)) return error.message;
  if (error instanceof Error && error.name === 'AbortError') return 'upstream_package_timeout';
  return 'upstream_package_unavailable';
};

const adoptionRank: Readonly<Record<MathematicsUpstreamPackageAdoptionStatus, number>> = Object.freeze({
  eligible: 0,
  compatibility_review_required: 1,
  build_unverified: 2,
  license_review_required: 3,
  incompatible: 4,
});

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

export async function readLeanProjectCompatibility(projectRoot: string): Promise<LeanProjectCompatibility> {
  const [leanToolchain, installedPackages] = await Promise.all([
    fs.promises
      .readFile(path.join(projectRoot, 'lean-toolchain'), 'utf8')
      .then((value) => value.trim().slice(0, 256) || undefined)
      .catch((): undefined => undefined),
    readLeanProjectPackageInventory(projectRoot),
  ]);
  const mathlibRevision = installedPackages.find(
    (candidate) =>
      candidate.name.toLowerCase() === 'mathlib' ||
      (candidate.url && leanRepositoryIdentity(candidate.url) === 'leanprover-community/mathlib4')
  )?.revision;
  return Object.freeze({
    ...(leanToolchain ? { leanToolchain } : {}),
    ...(mathlibRevision ? { mathlibRevision } : {}),
    installedPackages,
  });
}

const searchUpstreamLeanPackagesUncached = async (
  queries: readonly string[],
  target: LeanProjectCompatibility,
  options: Readonly<{
    fetchImpl?: FetchLike;
    resultLimit?: number;
    repositoryLimit?: number;
    timeoutMs?: number;
    maxRetries?: number;
    retryBaseDelayMs?: number;
  }> = {}
): Promise<MathematicsUpstreamPackageSearchResult> => {
  const fetchImpl = options.fetchImpl ?? globalThis.fetch;
  const resultLimit = Math.max(1, Math.min(8, options.resultLimit ?? DEFAULT_RESULT_LIMIT));
  const repositoryLimit = Math.max(1, Math.min(10, options.repositoryLimit ?? DEFAULT_REPOSITORY_LIMIT));
  const timeoutMs = Math.max(500, Math.min(30_000, options.timeoutMs ?? DEFAULT_TIMEOUT_MS));
  const maxRetries = Math.max(0, Math.min(4, Math.floor(options.maxRetries ?? DEFAULT_MAX_RETRIES)));
  const retryBaseDelayMs = Math.max(
    0,
    Math.min(2_000, Math.floor(options.retryBaseDelayMs ?? DEFAULT_RETRY_BASE_DELAY_MS))
  );
  const requested = queries.slice(0, 3).flatMap((value) => {
    const query = value.trim().slice(0, 256);
    return query ? [query] : [];
  });
  const outcomes = await Promise.all(
    requested.map(async (query) => {
      try {
        const repositories = await discoverRepositories(
          query,
          fetchImpl,
          repositoryLimit,
          timeoutMs,
          maxRetries,
          retryBaseDelayMs
        );
        const eligibleRepositories = repositories.filter((repository) => !excludedSolutionCorpus(repository));
        const settled = await Promise.allSettled(
          eligibleRepositories.map((repository) =>
            inspectReservoirPackage(repository, target, fetchImpl, timeoutMs, maxRetries, retryBaseDelayMs)
          )
        );
        const packages = settled.flatMap((result) =>
          result.status === 'fulfilled' && result.value ? [result.value] : []
        );
        const firstFailure = settled.find((result) => result.status === 'rejected');
        const unavailable = packages.length === 0 && firstFailure?.status === 'rejected';
        return {
          packages,
          attempt: Object.freeze({
            source: 'reservoir' as const,
            status: unavailable ? ('unavailable' as const) : ('ok' as const),
            resultCount: packages.length,
            excludedCount: repositories.length - eligibleRepositories.length,
            ...(unavailable ? { errorCode: packageErrorCode(firstFailure.reason) } : {}),
          }),
        };
      } catch (error) {
        return {
          packages: Object.freeze([]),
          attempt: Object.freeze({
            source: 'reservoir' as const,
            status: 'unavailable' as const,
            resultCount: 0,
            excludedCount: 0,
            errorCode: packageErrorCode(error),
          }),
        };
      }
    })
  );
  const byRepository = new Map<string, UnrankedPackage>();
  for (const outcome of outcomes) {
    for (const candidate of outcome.packages) {
      if (!byRepository.has(candidate.repositoryFullName.toLowerCase())) {
        byRepository.set(candidate.repositoryFullName.toLowerCase(), candidate);
      }
    }
  }
  const packages = [...byRepository.values()]
    .toSorted(
      (left, right) =>
        adoptionRank[left.adoptionStatus] - adoptionRank[right.adoptionStatus] ||
        right.updatedAt.localeCompare(left.updatedAt) ||
        right.stars - left.stars ||
        left.fullName.localeCompare(right.fullName)
    )
    .slice(0, resultLimit)
    .map((candidate, index) => Object.freeze({ ...candidate, providerRank: index + 1 }));
  return Object.freeze({
    packages: Object.freeze(packages),
    attempts: Object.freeze(outcomes.map(({ attempt }) => attempt)),
  });
};

type PackageCacheEntry = Readonly<{ expiresAt: number; result: MathematicsUpstreamPackageSearchResult }>;
const packageCacheByFetcher = new WeakMap<object, Map<string, PackageCacheEntry>>();
const packageInflightByFetcher = new WeakMap<object, Map<string, Promise<MathematicsUpstreamPackageSearchResult>>>();

/** Cache only successful package metadata; unavailable registries must recover on the next request. */
export async function searchUpstreamLeanPackages(
  queries: readonly string[],
  target: LeanProjectCompatibility,
  options: Readonly<{
    fetchImpl?: FetchLike;
    resultLimit?: number;
    repositoryLimit?: number;
    timeoutMs?: number;
    maxRetries?: number;
    retryBaseDelayMs?: number;
  }> = {}
): Promise<MathematicsUpstreamPackageSearchResult> {
  const fetchImpl = options.fetchImpl ?? globalThis.fetch;
  const fetcher = fetchImpl as unknown as object;
  let cache = packageCacheByFetcher.get(fetcher);
  if (!cache) {
    cache = new Map();
    packageCacheByFetcher.set(fetcher, cache);
  }
  const key = JSON.stringify({
    queries: queries.map((query) => query.trim().slice(0, 256)),
    target,
    resultLimit: options.resultLimit ?? DEFAULT_RESULT_LIMIT,
    repositoryLimit: options.repositoryLimit ?? DEFAULT_REPOSITORY_LIMIT,
    timeoutMs: options.timeoutMs ?? DEFAULT_TIMEOUT_MS,
    maxRetries: options.maxRetries ?? DEFAULT_MAX_RETRIES,
    retryBaseDelayMs: options.retryBaseDelayMs ?? DEFAULT_RETRY_BASE_DELAY_MS,
  });
  const cached = cache.get(key);
  if (cached) {
    if (cached.expiresAt > Date.now()) {
      cache.delete(key);
      cache.set(key, cached);
      return cached.result;
    }
    cache.delete(key);
  }
  let inflight = packageInflightByFetcher.get(fetcher);
  if (!inflight) {
    inflight = new Map();
    packageInflightByFetcher.set(fetcher, inflight);
  }
  const active = inflight.get(key);
  if (active) return active;
  const request = searchUpstreamLeanPackagesUncached(queries, target, options)
    .then((result) => {
      if (result.attempts.every((attempt) => attempt.status === 'ok')) {
        cache!.delete(key);
        cache!.set(key, Object.freeze({ expiresAt: Date.now() + PACKAGE_CACHE_TTL_MS, result }));
        while (cache!.size > PACKAGE_CACHE_MAX_ENTRIES) {
          const oldest = cache!.keys().next().value;
          if (oldest === undefined) break;
          cache!.delete(oldest);
        }
      }
      return result;
    })
    .finally(() => {
      inflight!.delete(key);
    });
  inflight.set(key, request);
  return request;
}

/* eslint-enable no-await-in-loop */
