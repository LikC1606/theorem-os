/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

import crypto from 'node:crypto';
import fs from 'node:fs';
import path from 'node:path';
import { parse as parseToml } from 'smol-toml';
import type { MathematicsUpstreamPackage } from "../common/chat/mathematics";
import { runMathematicsSandboxedCommand, type MathematicsSandboxCommandResult } from "./verifier";
import {
  leanRepositoryIdentity,
  readLeanProjectCompatibility,
  readLeanProjectPackageInventory,
  searchUpstreamLeanPackages,
} from "./upstreamPackageSearch";

const MAX_PACKAGE_NAME = 128;
const MAX_REPOSITORY_NAME = 256;
const DEFAULT_UPDATE_TIMEOUT_MS = 120_000;
const DEPENDENCY_FILES = Object.freeze(['lean-toolchain', 'lake-manifest.json', 'lakefile.toml', 'lakefile.lean']);

type JsonRecord = Record<string, unknown>;

export type LeanDependencyAdoptionRequest = Readonly<{
  projectRoot: string;
  package: LeanDependencyAdoptionCandidate;
  timeoutMs?: number;
  /** Construction-time override used by focused tests; production uses Lake in the sandbox. */
  runUpdate?: (
    projectRoot: string,
    timeoutMs: number,
    packageNames?: readonly string[]
  ) => Promise<MathematicsSandboxCommandResult>;
  /** Registry verification override used only by focused tests. */
  verifyCandidate?: (
    target: Awaited<ReturnType<typeof readLeanProjectCompatibility>>,
    candidate?: LeanDependencyAdoptionCandidate
  ) => Promise<boolean>;
}>;

export type LeanDependencyAdoptionCandidate = Pick<
  MathematicsUpstreamPackage,
  | 'source'
  | 'packageName'
  | 'repositoryFullName'
  | 'repositoryUrl'
  | 'revision'
  | 'license'
  | 'buildStatus'
  | 'compatibility'
  | 'adoptionStatus'
> &
  Partial<Pick<MathematicsUpstreamPackage, 'version' | 'leanToolchain' | 'mathlibRevision'>>;

export type LeanDependencyBatchAdoptionRequest = Readonly<{
  projectRoot: string;
  packages: readonly LeanDependencyAdoptionCandidate[];
  timeoutMs?: number;
  /** Construction-time override used by focused tests; production uses Lake in the sandbox. */
  runUpdate?: (
    projectRoot: string,
    timeoutMs: number,
    packageNames?: readonly string[]
  ) => Promise<MathematicsSandboxCommandResult>;
  /** Registry verification override used only by focused tests. */
  verifyCandidate?: (
    target: Awaited<ReturnType<typeof readLeanProjectCompatibility>>,
    candidate?: LeanDependencyAdoptionCandidate
  ) => Promise<boolean>;
}>;

export type LeanDependencyAdoptionResult = Readonly<{
  status: 'adopted' | 'already_present' | 'rejected' | 'failed';
  packageName: string;
  repositoryFullName: string;
  revision: string;
  projectRoot: string;
  dependencyFingerprint?: string;
  manifestRevision?: string;
  receiptPath?: string;
  diagnostics?: string;
  rollbackPerformed?: boolean;
}>;

export type LeanDependencyBatchAdoptionResult = Readonly<{
  status: 'adopted' | 'already_present' | 'rejected' | 'failed';
  packages: readonly LeanDependencyAdoptionResult[];
  projectRoot: string;
  dependencyFingerprint?: string;
  diagnostics?: string;
  rollbackPerformed?: boolean;
}>;

const text = (value: unknown): string => (typeof value === 'string' ? value.trim() : '');

const safeRelative = (value: string): string => value.replaceAll(path.sep, '/');

const isRecord = (value: unknown): value is JsonRecord =>
  Boolean(value) && typeof value === 'object' && !Array.isArray(value);

const quotedToml = (value: string): string => JSON.stringify(value);

const packageKey = (packageName: string): string =>
  packageName
    .replace(/[^A-Za-z0-9_.-]+/gu, '-')
    .replace(/^-+|-+$/gu, '')
    .slice(0, MAX_PACKAGE_NAME) || 'package';

const protectedLeanEvalProject = (projectRoot: string): boolean =>
  fs.existsSync(path.join(projectRoot, 'active-problem.json')) &&
  (fs.existsSync(path.join(projectRoot, 'holes.json')) || fs.existsSync(path.join(projectRoot, 'Challenge.lean')));

const packageRequirement = (
  contents: string,
  packageName: string,
  repositoryUrl: string,
  revision: string
): 'same' | 'conflict' | undefined => {
  let parsed: unknown;
  try {
    parsed = parseToml(contents);
  } catch {
    throw new TypeError('lakefile_invalid_toml');
  }
  if (!isRecord(parsed)) throw new TypeError('lakefile_invalid_toml');
  const requires = Array.isArray(parsed.require) ? parsed.require : [];
  for (const candidate of requires) {
    if (!isRecord(candidate) || text(candidate.name).toLowerCase() !== packageName.toLowerCase()) continue;
    const git = text(candidate.git).replace(/\.git$/iu, '');
    const rev = text(candidate.rev);
    return git === repositoryUrl && rev === revision ? 'same' : 'conflict';
  }
  return undefined;
};

const readFileIfPresent = async (filePath: string): Promise<Buffer | undefined> => {
  try {
    return await fs.promises.readFile(filePath);
  } catch (error) {
    if (['ENOENT', 'ENOTDIR'].includes((error as NodeJS.ErrnoException).code ?? '')) return undefined;
    throw error;
  }
};

const lakePackagesRoot = (projectRoot: string): string => path.join(projectRoot, '.lake', 'packages');

const packageIsMaterialized = async (projectRoot: string, packageName: string): Promise<boolean> => {
  const packagesRoot = lakePackagesRoot(projectRoot);
  const packageRoot = path.resolve(packagesRoot, packageName);
  if (path.dirname(packageRoot) !== path.resolve(packagesRoot)) return false;
  try {
    const stat = await fs.promises.lstat(packageRoot);
    if (!stat.isDirectory() || stat.isSymbolicLink()) return false;
    const gitMetadata = await fs.promises.lstat(path.join(packageRoot, '.git'));
    return gitMetadata.isDirectory() || gitMetadata.isFile();
  } catch (error) {
    if ((error as NodeJS.ErrnoException).code === 'ENOENT') return false;
    throw error;
  }
};

type LakePackagesSnapshot = Readonly<{ existed: boolean; entries: ReadonlySet<string> }>;

const snapshotLakePackages = async (projectRoot: string): Promise<LakePackagesSnapshot> => {
  const packagesRoot = lakePackagesRoot(projectRoot);
  try {
    const stat = await fs.promises.lstat(packagesRoot);
    if (!stat.isDirectory() || stat.isSymbolicLink()) throw new Error('lake_packages_directory_unsafe');
    return Object.freeze({ existed: true, entries: new Set(await fs.promises.readdir(packagesRoot)) });
  } catch (error) {
    if ((error as NodeJS.ErrnoException).code === 'ENOENT') {
      return Object.freeze({ existed: false, entries: new Set<string>() });
    }
    throw error;
  }
};

const removeNewLakePackages = async (projectRoot: string, before: LakePackagesSnapshot): Promise<void> => {
  const packagesRoot = lakePackagesRoot(projectRoot);
  let stat: fs.Stats;
  try {
    stat = await fs.promises.lstat(packagesRoot);
  } catch (error) {
    if ((error as NodeJS.ErrnoException).code === 'ENOENT') return;
    throw error;
  }
  if (!before.existed) {
    await fs.promises.rm(packagesRoot, { recursive: true, force: true });
    return;
  }
  if (!stat.isDirectory() || stat.isSymbolicLink()) throw new Error('lake_packages_directory_unsafe');
  for (const entry of await fs.promises.readdir(packagesRoot)) {
    if (!before.entries.has(entry)) {
      await fs.promises.rm(path.join(packagesRoot, entry), { recursive: true, force: true });
    }
  }
};

const restoreFile = async (filePath: string, contents: Buffer | undefined): Promise<void> => {
  if (contents === undefined) {
    try {
      await fs.promises.rm(filePath, { force: true });
    } catch (error) {
      if ((error as NodeJS.ErrnoException).code !== 'ENOTDIR') throw error;
    }
    return;
  }
  await fs.promises.writeFile(filePath, contents, { mode: 0o600 });
};

const boundedDiagnostics = (result: MathematicsSandboxCommandResult): string =>
  [result.errorMessage, result.stderr, result.stdout]
    .filter((value): value is string => Boolean(value?.trim()))
    .join('\n')
    .trim()
    .slice(-12_000);

/**
 * Hash the files that affect Lake elaboration.  Interactive sessions use this
 * identity to discard stale declarations after a dependency is adopted.
 */
export async function readLeanDependencyFingerprint(projectRoot: string): Promise<string> {
  const root = path.resolve(projectRoot);
  const hash = crypto.createHash('sha256');
  for (const relative of DEPENDENCY_FILES) {
    const contents = await readFileIfPresent(path.join(root, relative));
    hash.update(relative);
    hash.update('\0');
    if (contents) hash.update(contents);
    hash.update('\0');
  }
  return hash.digest('hex');
}

const rejected = (
  request: LeanDependencyAdoptionRequest,
  status: 'rejected' | 'failed',
  diagnostics: string,
  rollbackPerformed?: boolean
): LeanDependencyAdoptionResult =>
  Object.freeze({
    status,
    packageName: text(request.package.packageName),
    repositoryFullName: text(request.package.repositoryFullName),
    revision: text(request.package.revision),
    projectRoot: path.resolve(request.projectRoot),
    diagnostics,
    ...(rollbackPerformed !== undefined ? { rollbackPerformed } : {}),
  });

/**
 * Adopt one already-discovered Reservoir package into an isolated Worker
 * worktree.  Discovery remains read-only; this explicit operation is the only
 * path that edits Lake metadata, and it always rolls back a failed update.
 */
export async function adoptUpstreamLeanPackage(
  request: LeanDependencyAdoptionRequest
): Promise<LeanDependencyAdoptionResult> {
  const batch = await adoptUpstreamLeanPackages({
    projectRoot: request.projectRoot,
    packages: [request.package],
    timeoutMs: request.timeoutMs,
    runUpdate: request.runUpdate,
    verifyCandidate: request.verifyCandidate,
  });
  return (
    batch.packages[0] ??
    rejected(
      request,
      batch.status === 'failed' ? 'failed' : 'rejected',
      batch.diagnostics ?? 'package_not_adoptable',
      batch.rollbackPerformed
    )
  );
}

/**
 * Adopt several already-discovered Reservoir packages atomically in one
 * isolated Worker worktree.  All candidates are checked before Lake metadata
 * is changed; a failed update restores every changed file and receipt.
 */
export async function adoptUpstreamLeanPackages(
  request: LeanDependencyBatchAdoptionRequest
): Promise<LeanDependencyBatchAdoptionResult> {
  const root = path.resolve(request.projectRoot);
  const candidates = [...request.packages];
  const resultRoot = (
    packages: readonly LeanDependencyAdoptionResult[],
    status: LeanDependencyBatchAdoptionResult['status'],
    diagnostics?: string,
    rollbackPerformed?: boolean,
    dependencyFingerprint?: string
  ): LeanDependencyBatchAdoptionResult =>
    Object.freeze({
      status,
      packages: Object.freeze([...packages]),
      projectRoot: root,
      ...(dependencyFingerprint ? { dependencyFingerprint } : {}),
      ...(diagnostics ? { diagnostics } : {}),
      ...(rollbackPerformed !== undefined ? { rollbackPerformed } : {}),
    });
  const batchRejected = (
    diagnostics: string,
    status: 'rejected' | 'failed' = 'rejected',
    rollbackPerformed?: boolean
  ) =>
    resultRoot(
      candidates.map((candidate) =>
        rejected({ projectRoot: root, package: candidate }, status, diagnostics, rollbackPerformed)
      ),
      status,
      diagnostics,
      rollbackPerformed
    );
  if (!fs.existsSync(root) || !fs.statSync(root).isDirectory()) return batchRejected('project_missing');
  if (!candidates.length || candidates.length > 8) return batchRejected('package_batch_size_invalid');
  if (protectedLeanEvalProject(root)) return batchRejected('protected_lean_eval_project');
  const packageIdentities = new Set<string>();
  for (const candidate of candidates) {
    const packageName = text(candidate.packageName);
    const repositoryFullName = text(candidate.repositoryFullName);
    const revision = text(candidate.revision);
    const repositoryUrl = text(candidate.repositoryUrl).replace(/\.git$/iu, '');
    const license = text(candidate.license);
    if (!packageName || packageName.length > MAX_PACKAGE_NAME) return batchRejected('package_name_invalid');
    if (packageIdentities.has(packageName.toLowerCase())) return batchRejected('duplicate_package_name');
    packageIdentities.add(packageName.toLowerCase());
    if (
      !repositoryFullName ||
      repositoryFullName.length > MAX_REPOSITORY_NAME ||
      !/^[^/]+\/[^/]+$/u.test(repositoryFullName)
    )
      return batchRejected('repository_invalid');
    if (!/^https:\/\/github\.com\/[^/]+\/[^/]+$/iu.test(repositoryUrl)) return batchRejected('repository_url_invalid');
    if (!/^[0-9a-f]{40}$/iu.test(revision)) return batchRejected('revision_not_exact_commit');
    if (
      candidate.source !== 'reservoir' ||
      candidate.adoptionStatus !== 'eligible' ||
      candidate.compatibility !== 'exact' ||
      candidate.buildStatus !== 'built' ||
      !license ||
      license.toUpperCase() === 'NOASSERTION'
    )
      return batchRejected('package_not_adoptable');
  }

  const targetCompatibility = await readLeanProjectCompatibility(root);
  for (const candidate of candidates) {
    if (
      (candidate.leanToolchain &&
        targetCompatibility.leanToolchain &&
        candidate.leanToolchain !== targetCompatibility.leanToolchain) ||
      (candidate.mathlibRevision &&
        targetCompatibility.mathlibRevision &&
        candidate.mathlibRevision !== targetCompatibility.mathlibRevision)
    )
      return batchRejected('project_compatibility_changed');
    if (
      (targetCompatibility.leanToolchain && !candidate.leanToolchain) ||
      (targetCompatibility.mathlibRevision && !candidate.mathlibRevision)
    )
      return batchRejected('package_compatibility_metadata_incomplete');
  }
  const verification = await Promise.all(
    candidates.map(async (candidate) => {
      const verified = request.verifyCandidate
        ? await request.verifyCandidate(targetCompatibility, candidate)
        : (await searchUpstreamLeanPackages([text(candidate.repositoryFullName)], targetCompatibility)).packages.some(
            (registered) =>
              registered.packageName.toLowerCase() === text(candidate.packageName).toLowerCase() &&
              registered.repositoryFullName.toLowerCase() === text(candidate.repositoryFullName).toLowerCase() &&
              registered.revision.toLowerCase() === text(candidate.revision).toLowerCase() &&
              registered.compatibility === 'exact' &&
              registered.buildStatus === 'built' &&
              registered.adoptionStatus === 'eligible'
          );
      return verified;
    })
  );
  if (verification.some((verified) => !verified)) return batchRejected('candidate_not_currently_registered');

  const lakefilePath = path.join(root, 'lakefile.toml');
  const lakefileLeanPath = path.join(root, 'lakefile.lean');
  if (!fs.existsSync(lakefilePath)) {
    return batchRejected(
      fs.existsSync(lakefileLeanPath) ? 'lakefile_lean_requires_manual_adoption' : 'lakefile_missing'
    );
  }
  const dependencyFilesBefore = new Map(
    await Promise.all(
      DEPENDENCY_FILES.map(async (relative) => [relative, await readFileIfPresent(path.join(root, relative))] as const)
    )
  );
  const lakefileBefore = dependencyFilesBefore.get('lakefile.toml');
  if (!lakefileBefore) return batchRejected('lakefile_missing');
  const dependencyFingerprintBefore = await readLeanDependencyFingerprint(root);
  const lakePackagesBefore = await snapshotLakePackages(root);
  const packageResults: LeanDependencyAdoptionResult[] = [];
  const receiptPathsBefore = new Map(
    await Promise.all(
      candidates.map(async (candidate) => {
        const receiptPath = path.join(
          root,
          '.deepscientist',
          'math',
          'dependencies',
          packageKey(text(candidate.packageName)),
          'adoption.json'
        );
        return [receiptPath, await readFileIfPresent(receiptPath)] as const;
      })
    )
  );
  const rollback = async (): Promise<void> => {
    for (const [relative, contents] of dependencyFilesBefore) {
      await restoreFile(path.join(root, relative), contents);
    }
    await removeNewLakePackages(root, lakePackagesBefore);
    for (const [receiptPath, contents] of receiptPathsBefore) await restoreFile(receiptPath, contents);
    if ((await readLeanDependencyFingerprint(root)) !== dependencyFingerprintBefore) {
      throw new Error('dependency_rollback_fingerprint_mismatch');
    }
  };
  try {
    const lakefileText = lakefileBefore.toString('utf8');
    const inventory = await readLeanProjectPackageInventory(root);
    const pending: Array<
      Readonly<{ candidate: LeanDependencyAdoptionCandidate; appendRequirement: boolean }>
    > = [];
    for (const candidate of candidates) {
      const packageName = text(candidate.packageName);
      const repositoryFullName = text(candidate.repositoryFullName);
      const revision = text(candidate.revision);
      const repositoryUrl = text(candidate.repositoryUrl).replace(/\.git$/iu, '');
      const existing = packageRequirement(lakefileText, packageName, repositoryUrl, revision);
      const installed = inventory.find((item) => item.name.toLowerCase() === packageName.toLowerCase());
      const repositoryIdentity = leanRepositoryIdentity(repositoryFullName);
      const installedExact =
        installed?.revision.toLowerCase() === revision.toLowerCase() &&
        (!installed.url || !repositoryIdentity || leanRepositoryIdentity(installed.url) === repositoryIdentity);
      const materialized = installedExact ? await packageIsMaterialized(root, installed!.name) : false;
      if (installedExact && materialized) {
        packageResults.push({
          status: 'already_present',
          packageName,
          repositoryFullName,
          revision,
          projectRoot: root,
        });
        continue;
      }
      if ((installed && !installedExact) || existing === 'conflict') return batchRejected('package_name_conflict');
      pending.push(Object.freeze({ candidate, appendRequirement: existing !== 'same' }));
    }
    if (!pending.length) {
      return resultRoot(
        packageResults.map((item): LeanDependencyAdoptionResult => ({ ...item })),
        'already_present',
        undefined,
        undefined,
        await readLeanDependencyFingerprint(root)
      );
    }
    const requirements = pending
      .filter((item) => item.appendRequirement)
      .map(({ candidate }) => {
        const packageName = text(candidate.packageName);
        const repositoryUrl = text(candidate.repositoryUrl).replace(/\.git$/iu, '');
        const revision = text(candidate.revision);
        return `[[require]]\nname = ${quotedToml(packageName)}\ngit = ${quotedToml(repositoryUrl)}\nrev = ${quotedToml(revision)}\n`;
      })
      .join('\n');
    if (requirements) {
      const appended = `${lakefileText.replace(/\s*$/u, '')}\n\n${requirements}`;
      await fs.promises.writeFile(lakefilePath, appended, { mode: 0o600 });
    }
    const timeoutMs = Math.max(5_000, Math.min(10 * 60_000, request.timeoutMs ?? DEFAULT_UPDATE_TIMEOUT_MS));
    const pendingPackageNames = pending.map(({ candidate }) => text(candidate.packageName));
    const update =
      request.runUpdate?.(root, timeoutMs, pendingPackageNames) ??
      runMathematicsSandboxedCommand({
        checkoutRoot: root,
        command: 'lake',
        args: ['update', ...pendingPackageNames],
        timeoutMs,
        useWorkspacePackagesOnly: false,
      });
    const result = await update;
    if (result.exitCode !== 0 || result.timedOut || result.aborted || !result.started) {
      await rollback();
      return batchRejected(
        `lake_update_failed: ${boundedDiagnostics(result) || `exit_${result.exitCode ?? 'unknown'}`}`,
        'failed',
        true
      );
    }
    const afterInventory = await readLeanProjectPackageInventory(root);
    const adopted = await Promise.all(pending.map(async ({ candidate }) => {
      const packageName = text(candidate.packageName);
      const revision = text(candidate.revision);
      const repositoryIdentity = leanRepositoryIdentity(text(candidate.repositoryFullName));
      const installed = afterInventory.find(
        (item) =>
          item.name.toLowerCase() === packageName.toLowerCase() &&
          item.revision.toLowerCase() === revision.toLowerCase() &&
          (!item.url || !repositoryIdentity || leanRepositoryIdentity(item.url) === repositoryIdentity)
      );
      return installed && (await packageIsMaterialized(root, installed.name)) ? installed : undefined;
    }));
    if (adopted.some((item) => !item)) {
      await rollback();
      return batchRejected('lake_update_did_not_materialize_exact_revision', 'failed', true);
    }
    const dependencyFingerprint = await readLeanDependencyFingerprint(root);
    for (const [index, { candidate }] of pending.entries()) {
      const packageName = text(candidate.packageName);
      const repositoryFullName = text(candidate.repositoryFullName);
      const repositoryUrl = text(candidate.repositoryUrl).replace(/\.git$/iu, '');
      const revision = text(candidate.revision);
      const license = text(candidate.license);
      const receiptDirectory = path.join(root, '.deepscientist', 'math', 'dependencies', packageKey(packageName));
      await fs.promises.mkdir(receiptDirectory, { recursive: true, mode: 0o700 });
      const receiptPath = path.join(receiptDirectory, 'adoption.json');
      const receipt = {
        schema: 'deepscientist.mathematics.dependency-adoption.v1',
        packageName,
        repositoryFullName,
        repositoryUrl,
        revision,
        version: text(candidate.version) || undefined,
        license,
        adoptedAt: Date.now(),
        lakeUpdate: { exitCode: result.exitCode, durationMs: result.durationMs, batchSize: pending.length },
        dependencyFingerprint,
      };
      await fs.promises.writeFile(receiptPath, `${JSON.stringify(receipt, null, 2)}\n`, { mode: 0o600 });
      packageResults.push({
        status: 'adopted',
        packageName,
        repositoryFullName,
        revision,
        projectRoot: root,
        dependencyFingerprint,
        manifestRevision: adopted[index]!.revision,
        receiptPath: safeRelative(path.relative(root, receiptPath)),
      });
    }
    return resultRoot(packageResults, 'adopted', undefined, undefined, dependencyFingerprint);
  } catch (error) {
    try {
      await rollback();
      return batchRejected(error instanceof Error ? error.message : String(error), 'failed', true);
    } catch (rollbackError) {
      return batchRejected(
        `${error instanceof Error ? error.message : String(error)}; rollback_failed: ${
          rollbackError instanceof Error ? rollbackError.message : String(rollbackError)
        }`,
        'failed',
        false
      );
    }
  }
}
