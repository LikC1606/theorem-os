/**
 * @license
 * Copyright 2026 DeepScientist (deepscientist.cc)
 * SPDX-License-Identifier: Apache-2.0
 */

import type {
  ScienceArtifact,
  ScienceArtifactEvent,
  ScienceArtifactFileProvenanceRecord,
  ScienceArtifactFileProvenanceResult,
  ScienceArtifactGitFile,
  ScienceArtifactGitRef,
  ScienceArtifactMemoryEvent,
  ScienceArtifactSnapshotIncludePath,
  ScienceEvidenceItem,
  ScienceGitLineAnchor,
  ScienceGitLineAnchorInput,
  SciencePanelData,
} from "../../common/chat/science";
import { isPlausibleLocalFileReference } from "../../common/utils/localFileReference";
import { spawnSync } from 'node:child_process';
import crypto from 'node:crypto';
import fs from 'node:fs';
import path from 'node:path';
import { mergeProjectManifest } from "../../project-git/projectManifest";

const DEEPSCIENTIST_DIR = '.deepscientist';
const SCIENCE_ARTIFACTS_DIR = 'science-artifacts';
const ARTIFACT_REPO_DIR = 'artifact-repo';
const FILE_INDEX_SCHEMA = 'deepscientist.science-artifact-file-index.v1';
const FILE_LEDGER_SCHEMA = 'deepscientist.science-artifact-file-ledger.v1';
const EVIDENCE_INDEX_SCHEMA = 'deepscientist.science-artifact-evidence-index.v1';
const ARTIFACT_GIT_IDENTITY = [
  '-c',
  'user.name=DeepScientist Artifact Bot',
  '-c',
  'user.email=deepscientist-artifacts@local.invalid',
] as const;
const DEFAULT_MAX_COPY_BYTES = 25 * 1024 * 1024;
const DEFAULT_MAX_HASH_BYTES = 256 * 1024 * 1024;

type JsonRecord = Record<string, unknown>;

export interface ScienceProjectInfo {
  projectId: string;
  projectRoot: string;
  deepScientistRoot: string;
  artifactRepoPath: string;
  projectPath: string;
  createdAt: number;
  updatedAt: number;
}

export interface ScienceArtifactSnapshotRequest {
  projectRoot?: string;
  panel: SciencePanelData;
  state: JsonRecord;
  events: ScienceArtifactEvent[];
  event?: ScienceArtifactEvent;
  target?: ScienceArtifactEvent['target'];
  includePaths?: ScienceArtifactSnapshotIncludePath[];
  message?: string;
}

export interface ScienceArtifactSnapshotResult extends ScienceArtifactGitRef {
  ok: boolean;
  projectId?: string;
  repoPath?: string;
  commit?: string;
  shortCommit?: string;
  snapshotPath?: string;
  runPath?: string;
  files: ScienceArtifactGitFile[];
  changedFiles?: string[];
  error?: string;
  warning?: string;
}

export interface ScienceArtifactRunSnapshotRequest {
  projectRoot: string;
  runId: string;
}

export interface ScienceArtifactRunSnapshot {
  runId: string;
  state: Record<string, unknown>;
  panel?: SciencePanelData;
  events: ScienceArtifactEvent[];
  source: 'mirror' | 'git';
  commit?: string;
}

export interface ScienceArtifactEvidenceIndexRecord {
  key: string;
  runId: string;
  evidence: ScienceEvidenceItem;
  artifactIds: string[];
  claimIds: string[];
  commit?: string;
  updatedAt: number;
}

export interface ScienceArtifactEvidenceSearchRequest {
  projectRoot: string;
  query?: string;
  runId?: string;
  artifactId?: string;
  limit?: number;
}

export interface ScienceArtifactEvidenceSearchResult {
  ok: boolean;
  items: ScienceArtifactEvidenceIndexRecord[];
  error?: string;
}

export interface ScienceArtifactGitLinesRequest {
  projectRoot: string;
  anchor: ScienceGitLineAnchorInput;
}

export interface ScienceArtifactGitLinesResult {
  ok: boolean;
  anchor?: ScienceGitLineAnchor;
  content?: string;
  error?: string;
}

const now = (): number => Date.now();

const toPosix = (value: string): string => value.replace(/\\/g, '/');

const safeSegment = (value: string, fallback = 'item'): string =>
  value
    .trim()
    .replace(/[^a-z0-9_.-]+/giu, '-')
    .replace(/^-+|-+$/gu, '')
    .slice(0, 120) || fallback;

const writeJson = (filePath: string, value: unknown): void => {
  fs.mkdirSync(path.dirname(filePath), { recursive: true });
  fs.writeFileSync(filePath, `${JSON.stringify(value, null, 2)}\n`, 'utf8');
};

const readJson = <T>(filePath: string, fallback: T): T => {
  try {
    return JSON.parse(fs.readFileSync(filePath, 'utf8')) as T;
  } catch {
    return fallback;
  }
};

const writeJsonl = (filePath: string, values: unknown[]): void => {
  fs.mkdirSync(path.dirname(filePath), { recursive: true });
  fs.writeFileSync(
    filePath,
    values.map((value) => JSON.stringify(value)).join('\n') + (values.length ? '\n' : ''),
    'utf8'
  );
};

const appendJsonl = (filePath: string, values: unknown[]): void => {
  if (!values.length) return;
  fs.mkdirSync(path.dirname(filePath), { recursive: true });
  fs.appendFileSync(filePath, values.map((value) => JSON.stringify(value)).join('\n') + '\n', 'utf8');
};

const hashFile = (filePath: string, maxBytes = DEFAULT_MAX_HASH_BYTES): string | undefined => {
  const stat = fs.statSync(filePath);
  if (stat.size > maxBytes) return undefined;
  const digest = crypto.createHash('sha256');
  const data = fs.readFileSync(filePath);
  digest.update(data);
  return digest.digest('hex');
};

const hashText = (value: string): string => crypto.createHash('sha256').update(value).digest('hex');

const isAbsolutePath = (value: string): boolean => path.isAbsolute(value) || /^[a-zA-Z]:[\\/]/u.test(value);

const isInside = (root: string, candidate: string): boolean => {
  const rel = path.relative(root, candidate);
  return rel === '' || (!rel.startsWith('..') && !path.isAbsolute(rel));
};

const resolvesInsideProject = (root: string, candidate: string): boolean => {
  try {
    const realRoot = fs.realpathSync(root);
    let existing = candidate;
    while (!fs.existsSync(existing)) {
      const parent = path.dirname(existing);
      if (parent === existing) return false;
      existing = parent;
    }
    return isInside(realRoot, fs.realpathSync(existing));
  } catch {
    return false;
  }
};

const resolveProjectPath = (projectRoot: string, candidate?: string): string | undefined => {
  const text = String(candidate || '').trim();
  if (!text || !isPlausibleLocalFileReference(text)) return undefined;
  const root = path.resolve(projectRoot);
  const resolved = path.resolve(isAbsolutePath(text) ? text : path.join(root, text));
  const relative = path.relative(root, resolved);
  if (relative.startsWith('..') || path.isAbsolute(relative)) return undefined;
  if (!resolvesInsideProject(root, resolved)) return undefined;
  return resolved;
};

const relativeToProject = (projectRoot: string, filePath: string): string | undefined => {
  const rel = path.relative(projectRoot, filePath);
  if (!rel || rel === '') return '.';
  if (rel.startsWith('..') || path.isAbsolute(rel)) return undefined;
  return toPosix(rel);
};

const git = (cwd: string, args: string[]) =>
  spawnSync('git', args, {
    cwd,
    encoding: 'utf8',
    windowsHide: true,
  });

const gitOutput = (cwd: string, args: string[]): string | undefined => {
  const result = git(cwd, args);
  return result.status === 0 ? String(result.stdout || '').trim() : undefined;
};

const gitHead = (repoPath: string): string | undefined => gitOutput(repoPath, ['rev-parse', 'HEAD']);

const hasStagedGitChanges = (repoPath: string): boolean => git(repoPath, ['diff', '--cached', '--quiet']).status === 1;

const commitWithIdentity = (repoPath: string, message: string) =>
  git(repoPath, [...ARTIFACT_GIT_IDENTITY, 'commit', '-m', message]);

const updateDeepScientistGitignore = (deepScientistRoot: string): void => {
  const gitignorePath = path.join(deepScientistRoot, '.gitignore');
  const lines = fs.existsSync(gitignorePath) ? fs.readFileSync(gitignorePath, 'utf8').split(/\r?\n/u) : [];
  const required = [`/${ARTIFACT_REPO_DIR}/`, `/${SCIENCE_ARTIFACTS_DIR}/`, '/exports/'];
  let changed = false;
  for (const item of required) {
    if (!lines.includes(item)) {
      lines.push(item);
      changed = true;
    }
  }
  if (changed) fs.writeFileSync(gitignorePath, `${lines.filter(Boolean).join('\n')}\n`, 'utf8');
};

export function ensureScienceProject(projectRoot?: string): ScienceProjectInfo | undefined {
  const root = String(projectRoot || '').trim();
  if (!root) return undefined;
  const resolvedRoot = path.resolve(root);
  const deepScientistRoot = path.join(resolvedRoot, DEEPSCIENTIST_DIR);
  const projectPath = path.join(deepScientistRoot, 'project.json');
  fs.mkdirSync(deepScientistRoot, { recursive: true });
  updateDeepScientistGitignore(deepScientistRoot);

  const existing = readJson<JsonRecord>(projectPath, {});
  const merged = mergeProjectManifest(existing);
  const project: ScienceProjectInfo = {
    projectId: merged.projectId,
    projectRoot: resolvedRoot,
    deepScientistRoot,
    artifactRepoPath: path.join(deepScientistRoot, ARTIFACT_REPO_DIR),
    projectPath,
    createdAt: merged.createdAt,
    updatedAt: merged.updatedAt,
  };

  writeJson(projectPath, merged.manifest);
  return project;
}

export function ensureScienceArtifactRepo(projectRoot?: string): ScienceProjectInfo | undefined {
  const project = ensureScienceProject(projectRoot);
  if (!project) return undefined;
  fs.mkdirSync(project.artifactRepoPath, { recursive: true });
  if (!fs.existsSync(path.join(project.artifactRepoPath, '.git'))) {
    let init = git(project.artifactRepoPath, ['init', '--initial-branch=main']);
    if (init.status !== 0) {
      init = git(project.artifactRepoPath, ['init']);
      if (init.status === 0) git(project.artifactRepoPath, ['branch', '-M', 'main']);
    }
    if (init.status !== 0) return project;
    writeJson(path.join(project.artifactRepoPath, 'README.md'), {
      schema: 'deepscientist.artifact-repo.v1',
      projectId: project.projectId,
      projectRoot: project.projectRoot,
      createdAt: project.createdAt,
      note: 'DeepScientist managed artifact provenance repository. Do not edit by hand unless you know the consequences.',
    });
    git(project.artifactRepoPath, ['add', '-A']);
    commitWithIdentity(project.artifactRepoPath, 'Initialize DeepScientist artifact repository');
  }
  return project;
}

const deniedName = (name: string): boolean =>
  name === '.git' ||
  name === 'node_modules' ||
  name === '.venv' ||
  name === 'venv' ||
  name === '__pycache__' ||
  name === '.DS_Store' ||
  ['private', '.cache', 'provider-cache', 'provider_raw', 'provider-raw', 'licensed-raw', 'restricted-data'].includes(
    name.toLowerCase()
  ) ||
  /^\.env(?:\.|$)/iu.test(name) ||
  /(?:^|[._-])(?:secret|token|credential|passwd|password)(?:[._-]|$)/iu.test(name) ||
  /(?:id_rsa|id_dsa|id_ed25519|\.pem$|\.key$|\.p12$|\.pfx$)/iu.test(name);

const shouldIgnorePath = (filePath: string, project: ScienceProjectInfo): boolean => {
  if (isInside(project.artifactRepoPath, filePath)) return true;
  const rel = relativeToProject(project.projectRoot, filePath);
  const segments = toPosix(rel || filePath).split('/');
  return segments.some((segment) => deniedName(segment));
};

const collectDeclaredArtifactPaths = (artifact: ScienceArtifact): ScienceArtifactSnapshotIncludePath[] => {
  const items: ScienceArtifactSnapshotIncludePath[] = [];
  const push = (pathValue: string | undefined, role: ScienceArtifactSnapshotIncludePath['role']) => {
    if (!pathValue) return;
    items.push({
      path: pathValue,
      role,
      artifactId: artifact.id,
      artifactVersion: artifact.version,
    });
  };
  push(artifact.primaryPath, 'primary');
  push(artifact.previewPath, 'preview');
  push(artifact.thumbnailPath, 'thumbnail');
  artifact.sourcePaths?.forEach((item) => push(item, 'source'));
  artifact.inputPaths?.forEach((item) => push(item, 'input'));
  artifact.outputPaths?.forEach((item) => push(item, 'output'));
  artifact.inputs?.forEach((input) => {
    const role = input.role === 'primary' || input.role === 'reference' ? input.role : 'input';
    push(input.path, role);
  });
  push(artifact.code?.path, 'code');
  push(artifact.execution?.scriptPath, 'code');
  push(artifact.execution?.logPath, 'log');
  push(artifact.environment?.lockfilePath, 'environment');
  return items;
};

const walkDirectory = (dirPath: string, project: ScienceProjectInfo): string[] => {
  const files: string[] = [];
  const entries = fs.readdirSync(dirPath, { withFileTypes: true });
  for (const entry of entries) {
    if (deniedName(entry.name)) continue;
    const child = path.join(dirPath, entry.name);
    if (shouldIgnorePath(child, project)) continue;
    if (entry.isDirectory()) {
      files.push(...walkDirectory(child, project));
      continue;
    }
    if (entry.isFile()) files.push(child);
  }
  return files;
};

const storedFilePath = (
  runRoot: string,
  artifact: ScienceArtifact | undefined,
  include: ScienceArtifactSnapshotIncludePath,
  sourcePath: string,
  basePath: string
): string => {
  const role = safeSegment(include.role || 'file', 'file');
  const relativeSource =
    fs.existsSync(basePath) && fs.statSync(basePath).isDirectory()
      ? path.relative(basePath, sourcePath)
      : path.basename(sourcePath);
  const safeRel = toPosix(relativeSource)
    .split('/')
    .map((segment) => safeSegment(segment, 'file'))
    .join('/');
  if (!artifact) {
    return path.join(runRoot, 'snapshots', safeSegment(include.snapshotId || 'manual'), 'files', role, safeRel);
  }
  return path.join(
    runRoot,
    'artifacts',
    safeSegment(artifact.id, 'artifact'),
    `v${artifact.version || 1}`,
    'files',
    role,
    safeRel
  );
};

const materializeFile = (
  project: ScienceProjectInfo,
  runRoot: string,
  artifact: ScienceArtifact | undefined,
  include: ScienceArtifactSnapshotIncludePath,
  sourcePath: string,
  basePath: string,
  maxCopyBytes: number
): ScienceArtifactGitFile => {
  const relativePath = relativeToProject(project.projectRoot, sourcePath);
  if (shouldIgnorePath(sourcePath, project)) {
    return {
      path: sourcePath,
      relativePath,
      role: include.role,
      artifactId: artifact?.id || include.artifactId,
      artifactVersion: artifact?.version || include.artifactVersion,
      mode: 'ignored',
      reason: 'secret_or_internal_path',
    };
  }
  if (!fs.existsSync(sourcePath)) {
    return {
      path: sourcePath,
      relativePath,
      role: include.role,
      artifactId: artifact?.id || include.artifactId,
      artifactVersion: artifact?.version || include.artifactVersion,
      mode: 'missing',
      reason: 'not_found',
    };
  }
  const stat = fs.statSync(sourcePath);
  const storedPath = storedFilePath(runRoot, artifact, include, sourcePath, basePath);
  const storedRelativePath = toPosix(path.relative(project.artifactRepoPath, storedPath));
  const base: Omit<ScienceArtifactGitFile, 'mode'> = {
    path: sourcePath,
    relativePath,
    role: include.role,
    artifactId: artifact?.id || include.artifactId,
    artifactVersion: artifact?.version || include.artifactVersion,
    sizeBytes: stat.size,
    sha256: stat.isFile() ? hashFile(sourcePath) : undefined,
  };
  if (!stat.isFile()) {
    return { ...base, mode: 'pointer', reason: 'not_a_file' };
  }
  if (stat.size > maxCopyBytes) {
    return { ...base, mode: 'pointer', reason: 'large_file' };
  }
  fs.mkdirSync(path.dirname(storedPath), { recursive: true });
  fs.copyFileSync(sourcePath, storedPath);
  return { ...base, mode: 'copied', storedPath: storedRelativePath };
};

const materializeIncludePath = (
  project: ScienceProjectInfo,
  runRoot: string,
  artifactsById: Map<string, ScienceArtifact>,
  include: ScienceArtifactSnapshotIncludePath,
  defaultArtifact?: ScienceArtifact,
  maxCopyBytes = DEFAULT_MAX_COPY_BYTES
): ScienceArtifactGitFile[] => {
  const resolved = resolveProjectPath(project.projectRoot, include.path);
  const artifact = include.artifactId ? artifactsById.get(include.artifactId) || defaultArtifact : defaultArtifact;
  if (!resolved) {
    return [
      {
        path: include.path,
        relativePath: isAbsolutePath(include.path) ? undefined : toPosix(include.path),
        role: include.role,
        artifactId: artifact?.id || include.artifactId,
        artifactVersion: artifact?.version || include.artifactVersion,
        mode: 'ignored',
        reason: 'outside_project_or_symlink',
      },
    ];
  }
  if (!fs.existsSync(resolved)) {
    return [materializeFile(project, runRoot, artifact, include, resolved, resolved, maxCopyBytes)];
  }
  const stat = fs.statSync(resolved);
  if (stat.isDirectory()) {
    if (include.recursive === false) {
      return [
        {
          path: resolved,
          relativePath: relativeToProject(project.projectRoot, resolved),
          role: include.role,
          artifactId: artifact?.id || include.artifactId,
          artifactVersion: artifact?.version || include.artifactVersion,
          mode: 'pointer',
          reason: 'directory_not_recursive',
        },
      ];
    }
    return walkDirectory(resolved, project).map((filePath) =>
      materializeFile(project, runRoot, artifact, include, filePath, resolved, maxCopyBytes)
    );
  }
  return [materializeFile(project, runRoot, artifact, include, resolved, resolved, maxCopyBytes)];
};

const groupFilesForArtifact = (files: ScienceArtifactGitFile[], artifact: ScienceArtifact): ScienceArtifactGitFile[] =>
  files.filter(
    (item) =>
      item.artifactId === artifact.id &&
      (item.artifactVersion == null || artifact.version == null || item.artifactVersion === artifact.version)
  );

const normalizeComparablePath = (value?: string): string =>
  toPosix(String(value || '').trim())
    .replace(/\/+/gu, '/')
    .replace(/^\.\//u, '');

const fileRecordKey = (record: Pick<ScienceArtifactFileProvenanceRecord, 'relativePath' | 'path'>): string =>
  normalizeComparablePath(record.relativePath || record.path);

const fileIndexPath = (project: ScienceProjectInfo): string =>
  path.join(project.deepScientistRoot, SCIENCE_ARTIFACTS_DIR, 'file-index.json');

const fileLedgerPath = (project: ScienceProjectInfo): string =>
  path.join(project.deepScientistRoot, SCIENCE_ARTIFACTS_DIR, 'file-ledger.jsonl');

const evidenceIdsForFile = (
  panel: SciencePanelData,
  artifact: ScienceArtifact | undefined,
  file: ScienceArtifactGitFile
): string[] => {
  const paths = new Set(
    [file.relativePath, file.path].filter((item): item is string => Boolean(item)).map(normalizeComparablePath)
  );
  const ids = new Set<string>();
  artifact?.evidenceIds?.forEach((id) => ids.add(id));
  artifact?.inputs?.forEach((input) => {
    if (input.evidenceId && input.path && paths.has(normalizeComparablePath(input.path))) ids.add(input.evidenceId);
    if (input.evidenceId && !input.path) ids.add(input.evidenceId);
  });
  for (const evidence of panel.evidence) {
    if (artifact?.id && evidence.artifactId === artifact.id) ids.add(evidence.id);
    if (evidence.path && paths.has(normalizeComparablePath(evidence.path))) ids.add(evidence.id);
  }
  return [...ids];
};

const provenanceNodeIdsForFile = (
  panel: SciencePanelData,
  artifact: ScienceArtifact | undefined,
  file: ScienceArtifactGitFile
): string[] => {
  const paths = new Set(
    [file.relativePath, file.path].filter((item): item is string => Boolean(item)).map(normalizeComparablePath)
  );
  const ids = new Set<string>();
  artifact?.provenanceNodeIds?.forEach((id) => ids.add(id));
  for (const node of panel.provenance) {
    if (artifact?.id && node.artifactId === artifact.id) ids.add(node.id);
    if (node.path && paths.has(normalizeComparablePath(node.path))) ids.add(node.id);
  }
  return [...ids];
};

const statusForRecord = (
  project: ScienceProjectInfo,
  record: ScienceArtifactFileProvenanceRecord
): ScienceArtifactFileProvenanceResult['status'] => {
  if (record.mode === 'ignored') return 'ignored';
  if (record.mode === 'pointer') return 'pointer';
  if (record.mode === 'missing') return 'missing';
  const sourcePath = resolveProjectPath(project.projectRoot, record.relativePath || record.path) || record.path;
  if (!fs.existsSync(sourcePath)) return 'missing';
  if (!record.sha256) return 'tracked';
  try {
    const currentHash = hashFile(sourcePath);
    return currentHash && currentHash !== record.sha256 ? 'modified' : 'tracked';
  } catch {
    return 'unknown';
  }
};

const updateFileIndex = (
  project: ScienceProjectInfo,
  panel: SciencePanelData,
  gitRef: Partial<ScienceArtifactSnapshotResult>,
  files: ScienceArtifactGitFile[],
  event?: ScienceArtifactEvent
): void => {
  const artifactsByKey = new Map(
    panel.artifacts.map((artifact) => [`${artifact.id}@${artifact.version || 1}`, artifact] as const)
  );
  const artifactsById = new Map(panel.artifacts.map((artifact) => [artifact.id, artifact] as const));
  const timestamp = event?.timestamp || now();
  const records: ScienceArtifactFileProvenanceRecord[] = files.map((file) => {
    const artifact =
      file.artifactId && file.artifactVersion
        ? artifactsByKey.get(`${file.artifactId}@${file.artifactVersion}`) || artifactsById.get(file.artifactId)
        : file.artifactId
          ? artifactsById.get(file.artifactId)
          : undefined;
    return {
      projectId: project.projectId,
      projectRoot: project.projectRoot,
      runId: panel.runId,
      conversationId: event?.conversationId,
      messageId: event?.messageId,
      toolCallId: event?.toolCallId,
      eventId: event?.eventId,
      action: event?.action,
      timestamp,
      path: file.path,
      relativePath: file.relativePath,
      role: file.role,
      artifactId: file.artifactId || artifact?.id,
      artifactVersion: file.artifactVersion || artifact?.version,
      artifactTitle: artifact?.title,
      artifactType: artifact?.type,
      evidenceIds: evidenceIdsForFile(panel, artifact, file),
      provenanceNodeIds: provenanceNodeIdsForFile(panel, artifact, file),
      mode: file.mode,
      storedPath: file.storedPath,
      sha256: file.sha256,
      sizeBytes: file.sizeBytes,
      reason: file.reason,
      commit: gitRef.commit,
      shortCommit: gitRef.shortCommit,
      snapshotPath: gitRef.snapshotPath,
      status: 'tracked',
    };
  });

  const previous = readJson<{ files?: ScienceArtifactFileProvenanceRecord[] }>(fileIndexPath(project), {});
  const byKey = new Map<string, ScienceArtifactFileProvenanceRecord>();
  for (const record of previous.files || []) {
    byKey.set(fileRecordKey(record), record);
  }
  for (const record of records) {
    byKey.set(fileRecordKey(record), { ...record, status: statusForRecord(project, record) });
  }
  writeJson(fileIndexPath(project), {
    schema: FILE_INDEX_SCHEMA,
    projectId: project.projectId,
    projectRoot: project.projectRoot,
    updatedAt: now(),
    files: [...byKey.values()].toSorted((left, right) => (right.timestamp || 0) - (left.timestamp || 0)).slice(0, 2000),
  });
  appendJsonl(
    fileLedgerPath(project),
    records.map((record) =>
      Object.assign({ schema: FILE_LEDGER_SCHEMA }, record, { status: statusForRecord(project, record) })
    )
  );
};

const updateProjectIndex = (
  project: ScienceProjectInfo,
  panel: SciencePanelData,
  gitRef: Partial<ScienceArtifactSnapshotResult>
): void => {
  const indexPath = path.join(project.deepScientistRoot, SCIENCE_ARTIFACTS_DIR, 'project-index.json');
  const previous = readJson<JsonRecord>(indexPath, {});
  const runs = Array.isArray(previous.runs)
    ? previous.runs.filter((item) => (item as JsonRecord).runId !== panel.runId)
    : [];
  runs.unshift({
    runId: panel.runId,
    title: panel.report?.title || panel.question,
    summary: panel.summary,
    generatedAt: panel.generatedAt,
    status: panel.status,
    latestCommit: gitRef.commit,
    shortCommit: gitRef.shortCommit,
  });
  const artifacts = Array.isArray(previous.artifacts)
    ? previous.artifacts.filter((item) => (item as JsonRecord).runId !== panel.runId)
    : [];
  artifacts.unshift(
    ...panel.artifacts.map((artifact) => ({
      runId: panel.runId,
      artifactId: artifact.id,
      version: artifact.version,
      title: artifact.title,
      type: artifact.type,
      primaryPath: artifact.primaryPath,
      latestCommit: gitRef.commit,
      shortCommit: gitRef.shortCommit,
    }))
  );
  writeJson(indexPath, {
    schema: 'deepscientist.science-artifact-project-index.v1',
    projectId: project.projectId,
    projectRoot: project.projectRoot,
    updatedAt: now(),
    runs: runs.slice(0, 80),
    artifacts: artifacts.slice(0, 400),
  });
};

const repositoryEvidenceIndexPath = (project: ScienceProjectInfo): string =>
  path.join(project.artifactRepoPath, 'indexes', 'evidence.json');

const updateRepositoryEvidenceIndex = (project: ScienceProjectInfo, panel: SciencePanelData): void => {
  const indexPath = repositoryEvidenceIndexPath(project);
  const previous = readJson<{ items?: ScienceArtifactEvidenceIndexRecord[] }>(indexPath, {});
  const byKey = new Map<string, ScienceArtifactEvidenceIndexRecord>();
  for (const item of previous.items || []) {
    if (item.runId !== panel.runId) byKey.set(item.key, item);
  }

  for (const evidence of panel.evidence) {
    const artifactIds = new Set<string>();
    if (evidence.artifactId) artifactIds.add(evidence.artifactId);
    for (const artifact of panel.artifacts) {
      if (artifact.evidenceIds?.includes(evidence.id)) artifactIds.add(artifact.id);
      if (artifact.inputs?.some((input) => input.evidenceId === evidence.id)) artifactIds.add(artifact.id);
    }
    const claimIds = (panel.claims || [])
      .filter((claim) => claim.supportingEvidenceIds.includes(evidence.id))
      .map((claim) => claim.id);
    const key = `${panel.runId}:${evidence.id}`;
    byKey.set(key, {
      key,
      runId: panel.runId,
      evidence,
      artifactIds: [...artifactIds],
      claimIds,
      commit: evidence.gitAnchor?.commit,
      updatedAt: now(),
    });
  }

  writeJson(indexPath, {
    schema: EVIDENCE_INDEX_SCHEMA,
    projectId: project.projectId,
    projectRoot: project.projectRoot,
    updatedAt: now(),
    items: [...byKey.values()].toSorted((left, right) => right.updatedAt - left.updatedAt).slice(0, 5000),
  });
};

export function commitScienceArtifactSnapshot(request: ScienceArtifactSnapshotRequest): ScienceArtifactSnapshotResult {
  const project = ensureScienceArtifactRepo(request.projectRoot);
  if (!project) {
    return {
      ok: false,
      files: [],
      status: 'unavailable',
      error: 'projectRoot is required for Science artifact git snapshots.',
    };
  }
  if (!fs.existsSync(path.join(project.artifactRepoPath, '.git'))) {
    return {
      ok: false,
      projectId: project.projectId,
      repoPath: project.artifactRepoPath,
      files: [],
      status: 'unavailable',
      error: 'git is unavailable or the artifact repository could not be initialized.',
    };
  }

  const maxCopyBytes = Number(process.env.DEEPSCIENTIST_ARTIFACT_GIT_MAX_COPY_BYTES || DEFAULT_MAX_COPY_BYTES);
  const panel = {
    ...request.panel,
    projectRoot: request.panel.projectRoot || project.projectRoot,
  } satisfies SciencePanelData;
  const runRoot = path.join(project.artifactRepoPath, 'runs', safeSegment(panel.runId, 'run'));
  const artifactsById = new Map(panel.artifacts.map((artifact) => [artifact.id, artifact]));
  const targetArtifact =
    request.target?.kind === 'artifact' && request.target.id
      ? panel.artifacts.find(
          (artifact) =>
            artifact.id === request.target?.id &&
            (request.target?.version == null || artifact.version === request.target.version)
        )
      : undefined;

  fs.mkdirSync(runRoot, { recursive: true });
  writeJson(path.join(runRoot, 'run.json'), {
    runId: panel.runId,
    projectId: project.projectId,
    question: panel.question,
    summary: panel.summary,
    status: panel.status,
    generatedAt: panel.generatedAt,
  });
  writeJson(path.join(runRoot, 'panel.json'), panel);
  writeJson(path.join(runRoot, 'state.json'), request.state);
  writeJsonl(path.join(runRoot, 'events.jsonl'), request.events);
  writeJson(path.join(runRoot, 'evidence', 'items.json'), panel.evidence);
  writeJson(path.join(runRoot, 'claims', 'items.json'), panel.claims || []);
  writeJson(path.join(runRoot, 'pages', 'items.json'), panel.pages || []);
  writeJson(path.join(runRoot, 'provenance', 'nodes.json'), panel.provenance);
  writeJson(path.join(runRoot, 'provenance', 'edges.json'), panel.edges || []);
  writeJson(path.join(runRoot, 'provenance', 'warnings.json'), panel.graphWarnings || []);
  writeJson(path.join(runRoot, 'skills', 'used-skills.json'), panel.usedSkills || []);
  const memory = Array.isArray(request.state.memory)
    ? request.state.memory.filter((item): item is ScienceArtifactMemoryEvent =>
        Boolean(item && typeof item === 'object')
      )
    : [];
  writeJsonl(path.join(runRoot, 'memory', 'events.jsonl'), memory);
  updateRepositoryEvidenceIndex(project, panel);

  const declaredPaths = panel.artifacts.flatMap(collectDeclaredArtifactPaths);
  const manualPaths = (request.includePaths || []).map((item) => {
    const next: ScienceArtifactSnapshotIncludePath = {
      path: item.path,
      role: item.role,
      recursive: item.recursive,
      snapshotId: request.event?.eventId,
      artifactId: item.artifactId || targetArtifact?.id,
      artifactVersion: item.artifactVersion || targetArtifact?.version,
    };
    return next;
  });
  const files = [...declaredPaths, ...manualPaths].flatMap((include) =>
    materializeIncludePath(project, runRoot, artifactsById, include, targetArtifact, maxCopyBytes)
  );

  for (const artifact of panel.artifacts) {
    const artifactRoot = path.join(
      runRoot,
      'artifacts',
      safeSegment(artifact.id, 'artifact'),
      `v${artifact.version || 1}`
    );
    writeJson(path.join(artifactRoot, 'artifact.json'), artifact);
    writeJson(path.join(artifactRoot, 'files.json'), groupFilesForArtifact(files, artifact));
    writeJsonl(
      path.join(artifactRoot, 'memory', 'events.jsonl'),
      memory.filter(
        (item) =>
          item.artifactId === artifact.id && (!item.artifactVersion || item.artifactVersion === artifact.version)
      )
    );
  }
  writeJson(path.join(runRoot, 'files.json'), files);

  const message =
    request.message ||
    [
      'Artifact',
      request.event?.action || 'snapshot',
      request.target?.id || panel.report.title || panel.runId,
      `(${panel.runId})`,
    ]
      .filter(Boolean)
      .join(' ');

  const runRelativePath = toPosix(path.relative(project.artifactRepoPath, runRoot));
  git(project.artifactRepoPath, ['add', '--', runRelativePath, 'indexes/evidence.json']);
  const hadChanges = hasStagedGitChanges(project.artifactRepoPath);
  if (hadChanges) {
    commitWithIdentity(project.artifactRepoPath, message);
  }
  const commit = gitHead(project.artifactRepoPath);
  const shortCommit = commit ? commit.slice(0, 7) : undefined;
  const changedFiles = hadChanges
    ? gitOutput(project.artifactRepoPath, ['show', '--name-only', '--pretty=format:', commit || 'HEAD'])
        ?.split(/\r?\n/u)
        .map((item) => item.trim())
        .filter(Boolean)
    : [];
  const result: ScienceArtifactSnapshotResult = {
    ok: true,
    projectId: project.projectId,
    repoPath: project.artifactRepoPath,
    commit,
    shortCommit,
    snapshotPath: toPosix(path.relative(project.artifactRepoPath, runRoot)),
    runPath: runRoot,
    files,
    changedFiles,
    status: hadChanges ? 'committed' : 'unchanged',
  };
  updateProjectIndex(project, panel, result);
  updateFileIndex(project, panel, result, files, request.event);
  return result;
}

const resolveCommit = (
  repoPath: string,
  value?: string,
  side?: ScienceGitLineAnchorInput['side']
): string | undefined => {
  const requested = String(value || 'HEAD').trim() || 'HEAD';
  const ref = side === 'parent' ? `${requested}^` : requested;
  return gitOutput(repoPath, ['rev-parse', '--verify', `${ref}^{commit}`]);
};

const gitTextAt = (repoPath: string, commit: string, repoRelativePath: string): string | undefined => {
  const result = git(repoPath, ['show', `${commit}:${repoRelativePath}`]);
  if (result.status !== 0) return undefined;
  const value = String(result.stdout || '');
  if (value.length > 5 * 1024 * 1024 || value.includes('\0')) return undefined;
  return value;
};

const anchorStoredPath = (
  project: ScienceProjectInfo,
  commit: string,
  filePath: string
): { repoRelativePath: string; workspacePath?: string } | undefined => {
  const normalizedInput = normalizeComparablePath(filePath);
  if (normalizedInput && !normalizedInput.startsWith('../') && !path.isAbsolute(normalizedInput)) {
    if (gitTextAt(project.artifactRepoPath, commit, normalizedInput) !== undefined) {
      return { repoRelativePath: normalizedInput };
    }
  }

  const resolvedPath = resolveProjectPath(project.projectRoot, filePath);
  const relativePath = resolvedPath ? relativeToProject(project.projectRoot, resolvedPath) : undefined;
  const keys = new Set(
    [filePath, resolvedPath, relativePath].filter((item): item is string => Boolean(item)).map(normalizeComparablePath)
  );
  const index = readJson<{ files?: ScienceArtifactFileProvenanceRecord[] }>(fileIndexPath(project), {});
  const record = (index.files || [])
    .filter(
      (item) =>
        keys.has(fileRecordKey(item)) ||
        keys.has(normalizeComparablePath(item.path)) ||
        keys.has(normalizeComparablePath(item.storedPath))
    )
    .toSorted((left, right) => right.timestamp - left.timestamp)
    .find((item) =>
      Boolean(item.storedPath && gitTextAt(project.artifactRepoPath, commit, item.storedPath) !== undefined)
    );
  if (!record?.storedPath) return undefined;
  return {
    repoRelativePath: normalizeComparablePath(record.storedPath),
    workspacePath: resolvedPath && isInside(project.projectRoot, resolvedPath) ? resolvedPath : record.path,
  };
};

export function readScienceArtifactGitLines(request: ScienceArtifactGitLinesRequest): ScienceArtifactGitLinesResult {
  const project = ensureScienceArtifactRepo(request.projectRoot);
  if (!project || !fs.existsSync(path.join(project.artifactRepoPath, '.git'))) {
    return { ok: false, error: 'Science artifact repository is unavailable.' };
  }
  const commit = resolveCommit(project.artifactRepoPath, request.anchor.commit, request.anchor.side);
  if (!commit) return { ok: false, error: `Git commit ${request.anchor.commit || 'HEAD'} is unavailable.` };
  const resolved = anchorStoredPath(project, commit, request.anchor.filePath);
  if (!resolved) return { ok: false, error: `File ${request.anchor.filePath} is not available in commit ${commit}.` };
  const source = gitTextAt(project.artifactRepoPath, commit, resolved.repoRelativePath);
  if (source === undefined)
    return { ok: false, error: 'The selected Git object is binary, too large, or unavailable.' };

  const lines = source.split(/\r?\n/u);
  const lineStart = Math.max(1, Math.trunc(request.anchor.lineStart || 1));
  const lineEnd = Math.max(lineStart, Math.trunc(request.anchor.lineEnd || lineStart));
  if (lineStart > lines.length || lineEnd > lines.length) {
    return { ok: false, error: `Line range ${lineStart}-${lineEnd} exceeds the ${lines.length}-line Git object.` };
  }
  const content = lines.slice(lineStart - 1, lineEnd).join('\n');
  const blobSha = gitOutput(project.artifactRepoPath, ['rev-parse', `${commit}:${resolved.repoRelativePath}`]);
  return {
    ok: true,
    anchor: {
      kind: 'git_lines',
      commit,
      repoRelativePath: resolved.repoRelativePath,
      workspacePath: resolved.workspacePath,
      lineStart,
      lineEnd,
      side: request.anchor.side || 'current',
      blobSha,
      contextHash: hashText(content),
    },
    content,
  };
}

export function searchScienceArtifactEvidenceIndex(
  request: ScienceArtifactEvidenceSearchRequest
): ScienceArtifactEvidenceSearchResult {
  const project = ensureScienceProject(request.projectRoot);
  if (!project) return { ok: false, items: [], error: 'projectRoot is required.' };
  const index = readJson<{ items?: ScienceArtifactEvidenceIndexRecord[] }>(repositoryEvidenceIndexPath(project), {});
  const needle = String(request.query || '')
    .trim()
    .toLowerCase();
  const limit = Math.max(1, Math.min(request.limit || 80, 500));
  const items = (index.items || [])
    .filter((item) => !request.runId || item.runId === request.runId)
    .filter((item) => !request.artifactId || item.artifactIds.includes(request.artifactId))
    .filter((item) => {
      if (!needle) return true;
      const evidence = item.evidence;
      return [
        evidence.id,
        evidence.title,
        evidence.summary,
        evidence.path,
        evidence.url,
        evidence.virtualPath,
        evidence.sourceType,
        evidence.database?.name,
        evidence.database?.tool,
        evidence.gitAnchor?.repoRelativePath,
        ...item.artifactIds,
        ...item.claimIds,
      ]
        .filter(Boolean)
        .some((value) => String(value).toLowerCase().includes(needle));
    })
    .toSorted((left, right) => right.updatedAt - left.updatedAt)
    .slice(0, limit);
  return { ok: true, items };
}

const parseRunSnapshotRecord = (raw: string | undefined): JsonRecord | undefined => {
  if (raw === undefined) return undefined;
  try {
    const value: unknown = JSON.parse(raw);
    return value && typeof value === 'object' && !Array.isArray(value) ? (value as JsonRecord) : undefined;
  } catch {
    return undefined;
  }
};

const parseRunSnapshotEvents = (raw: string | undefined): ScienceArtifactEvent[] | undefined => {
  if (raw === undefined) return [];
  try {
    const events: ScienceArtifactEvent[] = [];
    for (const line of raw.split(/\r?\n/u)) {
      const text = line.trim();
      if (!text) continue;
      const value: unknown = JSON.parse(text);
      if (!value || typeof value !== 'object' || Array.isArray(value)) return undefined;
      events.push(value as ScienceArtifactEvent);
    }
    return events;
  } catch {
    return undefined;
  }
};

const buildRunSnapshot = (params: {
  runId: string;
  stateRaw?: string;
  panelRaw?: string;
  eventsRaw?: string;
  source: ScienceArtifactRunSnapshot['source'];
  commit?: string;
}): ScienceArtifactRunSnapshot | undefined => {
  const state = parseRunSnapshotRecord(params.stateRaw);
  if (!state) return undefined;
  const persistedRunId = typeof state.runId === 'string' ? state.runId.trim() : '';
  if (persistedRunId && persistedRunId !== params.runId) return undefined;

  let panel: SciencePanelData | undefined;
  if (params.panelRaw !== undefined) {
    const parsedPanel = parseRunSnapshotRecord(params.panelRaw);
    if (!parsedPanel) return undefined;
    const panelRunId = typeof parsedPanel.runId === 'string' ? parsedPanel.runId.trim() : '';
    if (panelRunId && panelRunId !== params.runId) return undefined;
    panel = parsedPanel as unknown as SciencePanelData;
  }

  const events = parseRunSnapshotEvents(params.eventsRaw);
  if (!events) return undefined;
  return {
    runId: params.runId,
    state,
    panel,
    events,
    source: params.source,
    commit: params.commit,
  };
};

export function readScienceArtifactRunSnapshot(
  request: ScienceArtifactRunSnapshotRequest
): ScienceArtifactRunSnapshot | undefined {
  const projectRoot = String(request.projectRoot || '').trim();
  const runId = String(request.runId || '').trim();
  if (!projectRoot || !runId) return undefined;

  const resolvedRoot = path.resolve(projectRoot);
  if (!fs.existsSync(resolvedRoot) || !fs.statSync(resolvedRoot).isDirectory()) return undefined;

  const deepScientistRoot = path.join(resolvedRoot, DEEPSCIENTIST_DIR);
  const runSegment = safeSegment(runId, 'run');
  const artifactRepoPath = path.join(deepScientistRoot, ARTIFACT_REPO_DIR);
  if (fs.existsSync(path.join(artifactRepoPath, '.git'))) {
    const commit = gitHead(artifactRepoPath);
    if (commit) {
      const runPath = `runs/${runSegment}`;
      const committed = buildRunSnapshot({
        runId,
        stateRaw: gitTextAt(artifactRepoPath, commit, `${runPath}/state.json`),
        panelRaw: gitTextAt(artifactRepoPath, commit, `${runPath}/panel.json`),
        eventsRaw: gitTextAt(artifactRepoPath, commit, `${runPath}/events.jsonl`),
        source: 'git',
        commit,
      });
      if (committed) return committed;
    }
    // Artifact Git is the authority once initialized. A missing or malformed
    // run must not be replaced by a mutable legacy mirror.
    return undefined;
  }

  // Compatibility fallback only for projects that predate Artifact Git.
  const mirrorRoot = path.join(deepScientistRoot, SCIENCE_ARTIFACTS_DIR, 'runs', runSegment);
  const readLocalFile = (name: string): string | undefined => {
    const filePath = path.join(mirrorRoot, name);
    if (!fs.existsSync(filePath)) return undefined;
    try {
      return fs.readFileSync(filePath, 'utf8');
    } catch {
      return undefined;
    }
  };
  const mirror = buildRunSnapshot({
    runId,
    stateRaw: readLocalFile('state.json'),
    panelRaw: readLocalFile('panel.json'),
    eventsRaw: readLocalFile('events.jsonl'),
    source: 'mirror',
  });
  return mirror;
}
