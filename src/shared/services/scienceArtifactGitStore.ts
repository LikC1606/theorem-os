/**
 * @license
 * Copyright 2026 DeepScientist (deepscientist.cc)
 * SPDX-License-Identifier: Apache-2.0
 */

import { readResearchRouteMap, RESEARCH_ROUTE_ARTIFACT_ID } from "../../common/chat/science";
import type {
  ScienceArtifact,
  ScienceArtifactEvent,
  ScienceArtifactFileProvenanceHistoryItem,
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
  ScienceReportBlock,
  ScienceResultSummaryBlock,
  ScienceResultSummaryMetric,
  ScienceReportTextTarget,
} from "../../common/chat/science";
import type { StructuredReportCard } from "../../common/chat/finance/index";
import type {
  LoopGoalRoadmapSnapshotRequest,
  LoopGoalRoadmapSnapshotResult,
  LoopGoalRoadmapStage,
} from "../../common/chat/loopGoal";
import { isPlausibleLocalFileReference } from "../../common/utils/localFileReference";
import { spawnSync } from 'node:child_process';
import crypto from 'node:crypto';
import fs from 'node:fs';
import path from 'node:path';
import { pathToFileURL } from 'node:url';
import { createProjectGitCheckpoint, discoverProjectGit } from "../../project-git/ProjectGitService";
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

export interface ScienceArtifactHistoryItem {
  commit: string;
  shortCommit: string;
  subject: string;
  authoredAt?: string;
  changedFiles: string[];
}

export interface ScienceArtifactHistoryRequest {
  projectRoot?: string;
  runId?: string;
  artifactId?: string;
  artifactVersion?: number;
  limit?: number;
}

export interface ScienceArtifactHistoryResult {
  ok: boolean;
  project?: ScienceProjectInfo;
  head?: string;
  items: ScienceArtifactHistoryItem[];
  error?: string;
}

export interface ScienceArtifactExportRequest {
  projectRoot?: string;
  runId: string;
  commit?: string;
  exportTypes?: Array<
    'markdown' | 'html' | 'pdf' | 'image' | 'notebook' | 'latex' | 'manifest' | 'panel' | 'run_bundle' | 'git_bundle'
  >;
  artifactIds?: string[];
  includeGitHistory?: boolean;
}

export interface ScienceArtifactExportResult {
  ok: boolean;
  project?: ScienceProjectInfo;
  exportId?: string;
  exportDir?: string;
  sourceCommit?: string;
  files: Array<{ type: string; path: string; contentHash?: string }>;
  error?: string;
}

export interface ScienceArtifactProjectPublishRequest {
  projectRoot: string;
  runId: string;
  commit?: string;
  artifactId?: string;
  artifactVersion?: number;
}

export interface ScienceArtifactProjectPublishResult {
  ok: boolean;
  status?: 'committed' | 'unchanged';
  projectId?: string;
  reportDir?: string;
  reportPath?: string;
  manifestPath?: string;
  artifactCommit?: string;
  projectCommit?: string;
  projectShortCommit?: string;
  changedFiles: string[];
  error?: string;
}

export interface ScienceArtifactFileProvenanceRequest {
  projectRoot?: string;
  filePath: string;
  limit?: number;
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

export interface ScienceArtifactTextEditRequest {
  projectRoot: string;
  runId: string;
  artifactId: string;
  artifactVersion?: number;
  filePath: string;
  content: string;
  baseRevision?: string;
  baseCommit?: string;
  expectedContentHash?: string;
  summary?: string;
  actor?: 'user' | 'agent';
}

export interface ScienceArtifactTextEditResult {
  ok: boolean;
  artifact?: ScienceArtifact;
  panel?: SciencePanelData;
  git?: ScienceArtifactGitRef;
  memory?: ScienceArtifactMemoryEvent;
  conflict?: 'revision' | 'commit' | 'content';
  error?: string;
}

export interface ScienceReportTextEditRequest {
  projectRoot: string;
  runId: string;
  target: ScienceReportTextTarget;
  content: string;
  expectedContent?: string;
  baseRevision?: string;
  baseCommit?: string;
  summary?: string;
  actor?: 'user' | 'agent';
}

export interface ScienceReportTextEditResult {
  ok: boolean;
  panel?: SciencePanelData;
  git?: ScienceArtifactGitRef;
  memory?: ScienceArtifactMemoryEvent;
  conflict?: 'revision' | 'commit' | 'content';
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

const readJsonl = <T>(filePath: string): T[] => {
  try {
    return fs
      .readFileSync(filePath, 'utf8')
      .split(/\r?\n/u)
      .map((line) => line.trim())
      .filter(Boolean)
      .map((line) => JSON.parse(line) as T);
  } catch {
    return [];
  }
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

export function resolveScienceArtifactFileProvenance(
  request: ScienceArtifactFileProvenanceRequest
): ScienceArtifactFileProvenanceResult {
  const project = ensureScienceProject(request.projectRoot);
  const filePath = String(request.filePath || '').trim();
  if (!project || !filePath) {
    return { ok: false, status: 'unknown', filePath, error: 'projectRoot and filePath are required.' };
  }

  const resolvedPath = resolveProjectPath(project.projectRoot, filePath) || filePath;
  const relativePath = relativeToProject(project.projectRoot, resolvedPath);
  const keys = new Set([normalizeComparablePath(filePath), normalizeComparablePath(resolvedPath)]);
  if (relativePath) keys.add(normalizeComparablePath(relativePath));
  if (isInside(project.artifactRepoPath, resolvedPath)) {
    keys.add(normalizeComparablePath(toPosix(path.relative(project.artifactRepoPath, resolvedPath))));
  }

  const index = readJson<{ files?: ScienceArtifactFileProvenanceRecord[] }>(fileIndexPath(project), {});
  const indexedFiles = index.files || [];
  let matchedByHash = false;
  let currentHash: string | undefined;
  const recordByPath = indexedFiles
    .filter(
      (item) =>
        keys.has(fileRecordKey(item)) ||
        keys.has(normalizeComparablePath(item.path)) ||
        keys.has(normalizeComparablePath(item.storedPath))
    )
    .toSorted((left, right) => (right.timestamp || 0) - (left.timestamp || 0))[0];
  if (!recordByPath && fs.existsSync(resolvedPath)) {
    try {
      const stat = fs.statSync(resolvedPath);
      currentHash = stat.isFile() ? hashFile(resolvedPath) : undefined;
    } catch {
      currentHash = undefined;
    }
  }
  const record =
    recordByPath ||
    (currentHash
      ? indexedFiles
          .filter((item) => Boolean(item.sha256) && item.sha256 === currentHash)
          .toSorted((left, right) => (right.timestamp || 0) - (left.timestamp || 0))[0]
      : undefined);
  matchedByHash = Boolean(!recordByPath && record && currentHash);

  if (!record) {
    return {
      ok: true,
      status: 'untracked',
      filePath: resolvedPath,
      relativePath,
      projectId: project.projectId,
      projectRoot: project.projectRoot,
      history: [],
    };
  }

  const status = matchedByHash ? 'tracked' : statusForRecord(project, record);
  const limit = Math.max(1, Math.min(request.limit || 12, 50));
  const history: ScienceArtifactFileProvenanceHistoryItem[] = readJsonl<ScienceArtifactFileProvenanceRecord>(
    fileLedgerPath(project)
  )
    .filter(
      (item) =>
        keys.has(fileRecordKey(item)) ||
        keys.has(normalizeComparablePath(item.path)) ||
        keys.has(normalizeComparablePath(item.storedPath)) ||
        (matchedByHash && Boolean(currentHash) && item.sha256 === currentHash)
    )
    .toSorted((left, right) => (right.timestamp || 0) - (left.timestamp || 0))
    .slice(0, limit)
    .map((item) => ({
      commit: item.commit,
      shortCommit: item.shortCommit,
      timestamp: item.timestamp,
      action: item.action,
      role: item.role,
      artifactId: item.artifactId,
      artifactVersion: item.artifactVersion,
      mode: item.mode,
    }));

  return {
    ok: true,
    status,
    filePath: resolvedPath,
    relativePath,
    projectId: project.projectId,
    projectRoot: project.projectRoot,
    record: { ...record, status },
    history,
  };
}

export function listScienceArtifactHistory(request: ScienceArtifactHistoryRequest): ScienceArtifactHistoryResult {
  const project = ensureScienceArtifactRepo(request.projectRoot);
  if (!project || !fs.existsSync(path.join(project.artifactRepoPath, '.git'))) {
    return { ok: false, project, items: [], error: 'Science artifact repository is unavailable.' };
  }
  const limit = Math.max(1, Math.min(request.limit || 30, 200));
  const pathspec: string[] = [];
  if (request.runId) {
    let target = `runs/${safeSegment(request.runId, 'run')}`;
    if (request.artifactId) {
      target += `/artifacts/${safeSegment(request.artifactId, 'artifact')}`;
      if (request.artifactVersion) target += `/v${request.artifactVersion}`;
    }
    pathspec.push('--', target);
  }
  const format = '%H%x1f%h%x1f%ad%x1f%s';
  const result = git(project.artifactRepoPath, [
    'log',
    '--date=iso-strict',
    `--pretty=format:${format}`,
    `-n${limit}`,
    ...pathspec,
  ]);
  if (result.status !== 0) {
    return {
      ok: false,
      project,
      head: gitHead(project.artifactRepoPath),
      items: [],
      error: result.stderr || result.stdout,
    };
  }
  const items = String(result.stdout || '')
    .split(/\r?\n/u)
    .filter(Boolean)
    .map((line) => {
      const [commit, shortCommit, authoredAt, subject] = line.split('\x1f');
      const changedFiles =
        gitOutput(project.artifactRepoPath, ['show', '--name-only', '--pretty=format:', commit, ...pathspec])
          ?.split(/\r?\n/u)
          .filter(Boolean) || [];
      return {
        commit,
        shortCommit,
        authoredAt,
        subject,
        changedFiles,
      };
    });
  return { ok: true, project, head: gitHead(project.artifactRepoPath), items };
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

const artifactDeclaredPaths = (artifact: ScienceArtifact): string[] =>
  collectDeclaredArtifactPaths(artifact).map((item) => item.path);

const makeRevision = (): string => `rev_${Date.now().toString(36)}_${crypto.randomBytes(4).toString('hex')}`;

const runStateRoot = (project: ScienceProjectInfo, runId: string): string =>
  path.join(project.deepScientistRoot, SCIENCE_ARTIFACTS_DIR, 'runs', safeSegment(runId, 'run'));

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

export function readLoopGoalRoadmapSnapshot(request: LoopGoalRoadmapSnapshotRequest): LoopGoalRoadmapSnapshotResult {
  const projectRoot = String(request.projectRoot || '').trim();
  const runId = String(request.runId || '').trim();
  const goalId = String(request.goalId || '').trim();
  if (!projectRoot || !runId || !goalId) {
    return { ok: false, error: 'projectRoot, runId, and goalId are required.' };
  }

  const resolvedRoot = path.resolve(projectRoot);
  if (!fs.existsSync(resolvedRoot) || !fs.statSync(resolvedRoot).isDirectory()) {
    return { ok: false, error: 'The bound project root is unavailable.' };
  }
  const runSnapshot = readScienceArtifactRunSnapshot({ projectRoot: resolvedRoot, runId });
  if (!runSnapshot) {
    return {
      ok: true,
      snapshot: {
        schema: 'deepscientist.discovery.roadmap-snapshot.v1',
        runId,
        exists: false,
        completionCriteria: [],
        unsatisfiedCompletionCriteria: [],
        terminal: false,
      },
    };
  }

  const state = runSnapshot.state;
  const artifacts = Array.isArray(state.artifacts)
    ? state.artifacts.filter((item): item is ScienceArtifact => Boolean(item && typeof item === 'object'))
    : [];
  const artifact = artifacts
    .filter((item) => item.id === RESEARCH_ROUTE_ARTIFACT_ID)
    .toSorted((left, right) => right.createdAt - left.createdAt || right.version - left.version)
    .find((item) => readResearchRouteMap(item.metadata));
  const roadmap = artifact ? readResearchRouteMap(artifact.metadata) : undefined;
  if (!roadmap) {
    return {
      ok: true,
      snapshot: {
        schema: 'deepscientist.discovery.roadmap-snapshot.v1',
        runId,
        exists: false,
        completionCriteria: [],
        unsatisfiedCompletionCriteria: [],
        terminal: false,
      },
    };
  }
  if (roadmap.goalId && roadmap.goalId !== goalId) {
    return { ok: false, error: 'The persisted research roadmap belongs to a different Discovery objective.' };
  }

  const focusedNode = roadmap.focusNodeId ? roadmap.nodes.find((node) => node.id === roadmap.focusNodeId) : undefined;
  const runningNode =
    (focusedNode?.lifecycle === 'running' ? focusedNode : undefined) ||
    roadmap.nodes.find((node) => node.lifecycle === 'running');
  const currentStage: LoopGoalRoadmapStage | undefined = runningNode
    ? {
        id: runningNode.id,
        title: runningNode.title,
        lifecycle: runningNode.lifecycle,
        objective: runningNode.execution?.objective,
        acceptanceCriteria: runningNode.execution?.acceptanceCriteria,
        failureCriteria: runningNode.execution?.failureCriteria,
        priorWorkRefs: runningNode.execution?.priorWorkRefs,
        doNotRepeat: runningNode.execution?.doNotRepeat,
      }
    : undefined;
  const completionCriteria = roadmap.completionContract?.criteria || [];
  const unsatisfiedCompletionCriteria = completionCriteria.filter((criterion) => criterion.status !== 'satisfied');
  const terminalNode = roadmap.nodes
    .filter((node) => ['completed', 'verified'].includes(node.lifecycle) && node.outcome?.nextAction === 'complete')
    .toSorted((left, right) => right.order - left.order)[0];
  const terminal = Boolean(completionCriteria.length && !unsatisfiedCompletionCriteria.length && terminalNode);

  return {
    ok: true,
    snapshot: {
      schema: 'deepscientist.discovery.roadmap-snapshot.v1',
      runId,
      exists: true,
      revision: artifact?.revision,
      goalId: roadmap.goalId,
      objective: roadmap.objective,
      focusNodeId: roadmap.focusNodeId,
      currentStage,
      completionCriteria,
      unsatisfiedCompletionCriteria,
      terminal,
      terminalStageId: terminal ? terminalNode?.id : undefined,
      updatedAt: roadmap.updatedAt,
    },
  };
}

export function editScienceArtifactText(request: ScienceArtifactTextEditRequest): ScienceArtifactTextEditResult {
  const project = ensureScienceArtifactRepo(request.projectRoot);
  if (!project) return { ok: false, error: 'projectRoot is required.' };
  const root = runStateRoot(project, request.runId);
  const statePath = path.join(root, 'state.json');
  const panelPath = path.join(root, 'panel.json');
  const lockPath = path.join(
    project.deepScientistRoot,
    SCIENCE_ARTIFACTS_DIR,
    'locks',
    `${safeSegment(request.runId)}.lock`
  );
  fs.mkdirSync(path.dirname(lockPath), { recursive: true });

  let lockFd: number | undefined;
  let originalFile: { path: string; content: string } | undefined;
  try {
    try {
      if (fs.existsSync(lockPath) && now() - fs.statSync(lockPath).mtimeMs > 30_000) {
        fs.unlinkSync(lockPath);
      }
      lockFd = fs.openSync(lockPath, 'wx');
      fs.writeFileSync(lockFd, `${process.pid}\n${now()}\n`, 'utf8');
    } catch {
      return { ok: false, error: 'This Artifact is being updated. Try saving again in a moment.' };
    }

    const state = readJson<JsonRecord>(statePath, {});
    const panel = readJson<SciencePanelData | undefined>(panelPath, undefined);
    if (!panel || !Array.isArray(state.artifacts)) {
      return { ok: false, error: `Science run ${request.runId} is unavailable.` };
    }
    const artifacts = state.artifacts.filter((item): item is ScienceArtifact =>
      Boolean(item && typeof item === 'object')
    );
    const candidates = artifacts
      .filter((item) => item.id === request.artifactId)
      .toSorted((left, right) => right.version - left.version);
    const artifact = request.artifactVersion
      ? candidates.find((item) => item.version === request.artifactVersion)
      : candidates[0];
    if (!artifact) return { ok: false, error: `Artifact ${request.artifactId} is unavailable.` };
    if (request.baseRevision && artifact.revision && request.baseRevision !== artifact.revision) {
      return { ok: false, conflict: 'revision', error: 'The Artifact changed after this editor was opened.' };
    }
    if (request.baseCommit) {
      const history = listScienceArtifactHistory({
        projectRoot: project.projectRoot,
        runId: request.runId,
        artifactId: artifact.id,
        artifactVersion: artifact.version,
        limit: 1,
      });
      const latestCommit = history.items[0]?.commit;
      const knownCommit = artifact.git?.commit || panel.git?.commit;
      if (latestCommit && latestCommit !== request.baseCommit && knownCommit !== request.baseCommit) {
        return { ok: false, conflict: 'commit', error: 'A newer Git snapshot exists for this Artifact.' };
      }
    }

    const filePath = resolveProjectPath(project.projectRoot, request.filePath);
    if (
      !filePath ||
      !isInside(project.projectRoot, filePath) ||
      isInside(project.deepScientistRoot, filePath) ||
      shouldIgnorePath(filePath, project)
    ) {
      return { ok: false, error: 'The selected file is outside the editable project workspace.' };
    }
    const declared = artifactDeclaredPaths(artifact)
      .map((item) => resolveProjectPath(project.projectRoot, item))
      .filter((item): item is string => Boolean(item));
    if (!declared.some((item) => item === filePath)) {
      return { ok: false, error: 'The selected file is not declared by this Artifact.' };
    }
    if (!fs.existsSync(filePath) || !fs.statSync(filePath).isFile()) {
      return { ok: false, error: 'The selected Artifact file no longer exists.' };
    }
    if (request.content.length > 5 * 1024 * 1024 || request.content.includes('\0')) {
      return { ok: false, error: 'Artifact text edits are limited to 5 MB and cannot contain binary data.' };
    }
    const currentContent = fs.readFileSync(filePath, 'utf8');
    if (request.expectedContentHash && hashText(currentContent) !== request.expectedContentHash) {
      return { ok: false, conflict: 'content', error: 'The file changed after this editor was opened.' };
    }

    originalFile = { path: filePath, content: currentContent };
    fs.writeFileSync(filePath, request.content, 'utf8');
    const relativePath = relativeToProject(project.projectRoot, filePath) || request.filePath;
    const revision = makeRevision();
    const primaryPath = resolveProjectPath(project.projectRoot, artifact.primaryPath);
    const editedPrimary = primaryPath === filePath;
    const updatedArtifact: ScienceArtifact = {
      ...artifact,
      revision,
      contentHash: hashText(request.content),
      changeSummary: request.summary || `Edited ${path.basename(filePath)}`,
      status: editedPrimary ? 'available' : 'stale',
    };
    const updatedArtifacts = artifacts.map((item) =>
      item.id === artifact.id && item.version === artifact.version ? updatedArtifact : item
    );
    const timestamp = now();
    const memory: ScienceArtifactMemoryEvent = {
      id: `memory_${timestamp.toString(36)}_${crypto.randomBytes(3).toString('hex')}`,
      runId: request.runId,
      artifactId: artifact.id,
      artifactVersion: artifact.version,
      actor: request.actor || 'user',
      action: 'edit',
      summary: request.summary || `Edited ${path.basename(filePath)}`,
      changedPaths: [relativePath],
      evidenceIds: artifact.evidenceIds,
      timestamp,
      hidden: true,
    };
    const event: ScienceArtifactEvent = {
      schema: 'deepscientist.science.event.v1',
      eventId: `sci_evt_${timestamp.toString(36)}_${crypto.randomBytes(3).toString('hex')}`,
      runId: request.runId,
      action: 'patch',
      timestamp,
      target: { kind: 'artifact', id: artifact.id, version: artifact.version },
      baseRevision: artifact.revision,
      resultingRevision: revision,
      artifactIds: [artifact.id],
      evidenceIds: artifact.evidenceIds,
      memoryId: memory.id,
    };
    const events = [...readJsonl<ScienceArtifactEvent>(path.join(root, 'events.jsonl')), event];
    const stateMemory = Array.isArray(state.memory) ? state.memory : [];
    const nextPanel: SciencePanelData = {
      ...panel,
      generatedAt: timestamp,
      artifacts: panel.artifacts.map((item) =>
        item.id === artifact.id && item.version === artifact.version ? updatedArtifact : item
      ),
    };
    const nextState: JsonRecord = {
      ...state,
      updatedAt: timestamp,
      artifacts: updatedArtifacts,
      memory: [...stateMemory, memory],
    };
    const role = editedPrimary
      ? 'primary'
      : artifact.code?.path && resolveProjectPath(project.projectRoot, artifact.code.path) === filePath
        ? 'code'
        : 'source';
    const gitRef = commitScienceArtifactSnapshot({
      projectRoot: project.projectRoot,
      panel: nextPanel,
      state: nextState,
      events,
      event,
      target: event.target,
      includePaths: [
        {
          path: relativePath,
          role,
          artifactId: artifact.id,
          artifactVersion: artifact.version,
        },
      ],
      message: `Edit ${artifact.title}: ${memory.summary}`,
    });
    if (!gitRef.ok) {
      fs.writeFileSync(filePath, currentContent, 'utf8');
      originalFile = undefined;
      return { ok: false, error: gitRef.error || 'The Artifact Git snapshot failed.' };
    }

    memory.commit = gitRef.commit;
    event.git = gitRef;
    updatedArtifact.git = gitRef;
    nextPanel.git = gitRef;
    nextPanel.artifacts = nextPanel.artifacts.map((item) =>
      item.id === artifact.id && item.version === artifact.version ? updatedArtifact : item
    );
    nextState.git = gitRef;
    nextState.artifacts = updatedArtifacts.map((item) =>
      item.id === artifact.id && item.version === artifact.version ? updatedArtifact : item
    );
    nextState.memory = [...stateMemory, memory];
    writeJson(panelPath, nextPanel);
    writeJson(statePath, nextState);
    writeJsonl(path.join(root, 'events.jsonl'), events);
    originalFile = undefined;
    return { ok: true, artifact: updatedArtifact, panel: nextPanel, git: gitRef, memory };
  } catch (error) {
    if (originalFile) {
      try {
        fs.writeFileSync(originalFile.path, originalFile.content, 'utf8');
      } catch {
        // Preserve the original failure; the caller will still receive it.
      }
    }
    return { ok: false, error: error instanceof Error ? error.message : String(error) };
  } finally {
    if (lockFd !== undefined) {
      fs.closeSync(lockFd);
      try {
        fs.unlinkSync(lockPath);
      } catch {
        // The lock may already have been removed after a failed acquisition.
      }
    }
  }
}

const reportTargetLabel = (target: ScienceReportTextTarget): string => {
  const location = [target.sectionId, target.blockIndex, target.itemIndex]
    .filter((value) => value !== undefined)
    .join(':');
  return location ? `${target.field}:${location}` : target.field;
};

const readScienceReportText = (panel: SciencePanelData, target: ScienceReportTextTarget): string | undefined => {
  if (target.field === 'question') return panel.question;
  if (target.field === 'summary') return panel.summary || '';
  if (target.field === 'report.title') return panel.report.title;
  const section = panel.report.sections.find((item) => item.id === target.sectionId);
  if (!section) return undefined;
  if (target.field === 'section.heading') return section.heading;
  const block = target.blockIndex == null ? undefined : section.blocks[target.blockIndex];
  if (!block) return undefined;
  if (target.field === 'block.text' && block.type === 'paragraph') return block.text;
  if (target.field === 'bullet.text' && block.type === 'bullet_list' && target.itemIndex != null) {
    return block.items[target.itemIndex]?.text;
  }
  if (target.field === 'checklist.label' && block.type === 'checklist' && target.itemIndex != null) {
    return block.items[target.itemIndex]?.label;
  }
  if (target.field === 'checklist.detail' && block.type === 'checklist' && target.itemIndex != null) {
    return block.items[target.itemIndex]?.detail || '';
  }
  if (target.field === 'artifact.caption' && block.type === 'artifact_embed') return block.caption || '';
  return undefined;
};

const updateScienceReportText = (
  panel: SciencePanelData,
  target: ScienceReportTextTarget,
  content: string,
  revision: string,
  timestamp: number
): SciencePanelData | undefined => {
  const report: SciencePanelData['report'] = {
    ...panel.report,
    revision,
    sections: panel.report.sections.map((section) => ({ ...section, blocks: [...section.blocks] })),
  };
  if (target.field === 'question') return { ...panel, question: content, report, generatedAt: timestamp };
  if (target.field === 'summary') {
    return { ...panel, summary: content || undefined, report, generatedAt: timestamp };
  }
  if (target.field === 'report.title') {
    report.title = content;
    return { ...panel, report, generatedAt: timestamp };
  }
  const sectionIndex = report.sections.findIndex((item) => item.id === target.sectionId);
  if (sectionIndex < 0) return undefined;
  const section = report.sections[sectionIndex];
  if (target.field === 'section.heading') {
    report.sections[sectionIndex] = { ...section, heading: content };
    return { ...panel, report, generatedAt: timestamp };
  }
  if (target.blockIndex == null || !section.blocks[target.blockIndex]) return undefined;
  const block = section.blocks[target.blockIndex];
  let nextBlock: ScienceReportBlock | undefined;
  if (target.field === 'block.text' && block.type === 'paragraph') nextBlock = { ...block, text: content };
  if (target.field === 'bullet.text' && block.type === 'bullet_list' && target.itemIndex != null) {
    if (!block.items[target.itemIndex]) return undefined;
    const items = block.items.map((item, index) => (index === target.itemIndex ? { ...item, text: content } : item));
    nextBlock = { ...block, items };
  }
  if (
    (target.field === 'checklist.label' || target.field === 'checklist.detail') &&
    block.type === 'checklist' &&
    target.itemIndex != null
  ) {
    if (!block.items[target.itemIndex]) return undefined;
    const items = block.items.map((item, index) => {
      if (index !== target.itemIndex) return item;
      return target.field === 'checklist.label'
        ? { ...item, label: content }
        : { ...item, detail: content || undefined };
    });
    nextBlock = { ...block, items };
  }
  if (target.field === 'artifact.caption' && block.type === 'artifact_embed') {
    nextBlock = { ...block, caption: content || undefined };
  }
  if (!nextBlock) return undefined;
  const blocks = [...section.blocks];
  blocks[target.blockIndex] = nextBlock;
  report.sections[sectionIndex] = { ...section, blocks };
  return { ...panel, report, generatedAt: timestamp };
};

export function editScienceReportText(request: ScienceReportTextEditRequest): ScienceReportTextEditResult {
  const project = ensureScienceArtifactRepo(request.projectRoot);
  if (!project) return { ok: false, error: 'projectRoot is required.' };
  const root = runStateRoot(project, request.runId);
  const statePath = path.join(root, 'state.json');
  const panelPath = path.join(root, 'panel.json');
  const lockPath = path.join(
    project.deepScientistRoot,
    SCIENCE_ARTIFACTS_DIR,
    'locks',
    `${safeSegment(request.runId)}.lock`
  );
  fs.mkdirSync(path.dirname(lockPath), { recursive: true });

  let lockFd: number | undefined;
  try {
    try {
      if (fs.existsSync(lockPath) && now() - fs.statSync(lockPath).mtimeMs > 30_000) fs.unlinkSync(lockPath);
      lockFd = fs.openSync(lockPath, 'wx');
      fs.writeFileSync(lockFd, `${process.pid}\n${now()}\n`, 'utf8');
    } catch {
      return { ok: false, error: 'This Artifact is being updated. Try saving again in a moment.' };
    }

    const state = readJson<JsonRecord>(statePath, {});
    const panel = readJson<SciencePanelData | undefined>(panelPath, undefined);
    if (!panel) return { ok: false, error: `Science run ${request.runId} is unavailable.` };
    const currentText = readScienceReportText(panel, request.target);
    if (currentText === undefined) return { ok: false, error: 'The selected report text no longer exists.' };
    if (request.baseRevision && panel.report.revision && request.baseRevision !== panel.report.revision) {
      return { ok: false, conflict: 'revision', error: 'The report changed after this editor was opened.' };
    }
    if (request.expectedContent !== undefined && request.expectedContent !== currentText) {
      return { ok: false, conflict: 'content', error: 'The report text changed after this editor was opened.' };
    }
    if (request.baseCommit) {
      const history = listScienceArtifactHistory({ projectRoot: project.projectRoot, runId: request.runId, limit: 1 });
      const latestCommit = history.items[0]?.commit;
      if (latestCommit && latestCommit !== request.baseCommit && panel.git?.commit !== request.baseCommit) {
        return { ok: false, conflict: 'commit', error: 'A newer Git snapshot exists for this report.' };
      }
    }
    if (request.content.length > 100_000 || request.content.includes('\0')) {
      return { ok: false, error: 'Report text edits are limited to 100 KB and cannot contain binary data.' };
    }
    if (
      ['question', 'report.title', 'section.heading', 'block.text', 'bullet.text', 'checklist.label'].includes(
        request.target.field
      ) &&
      !request.content.trim()
    ) {
      return { ok: false, error: 'This report field cannot be empty.' };
    }

    const timestamp = now();
    const revision = makeRevision();
    const nextPanel = updateScienceReportText(panel, request.target, request.content, revision, timestamp);
    if (!nextPanel) return { ok: false, error: 'The selected report field is incompatible with this report block.' };
    const label = reportTargetLabel(request.target);
    const memory: ScienceArtifactMemoryEvent = {
      id: `memory_${timestamp.toString(36)}_${crypto.randomBytes(3).toString('hex')}`,
      runId: request.runId,
      actor: request.actor || 'user',
      action: 'edit',
      summary: request.summary || `Edited report ${label}`,
      changedPaths: [`report:${label}`],
      timestamp,
      hidden: true,
    };
    const event: ScienceArtifactEvent = {
      schema: 'deepscientist.science.event.v1',
      eventId: `sci_evt_${timestamp.toString(36)}_${crypto.randomBytes(3).toString('hex')}`,
      runId: request.runId,
      action: 'patch',
      timestamp,
      target: { kind: 'report', id: 'report' },
      baseRevision: panel.report.revision,
      resultingRevision: revision,
      memoryId: memory.id,
    };
    const events = [...readJsonl<ScienceArtifactEvent>(path.join(root, 'events.jsonl')), event];
    const stateMemory = Array.isArray(state.memory) ? state.memory : [];
    const nextState: JsonRecord = {
      ...state,
      updatedAt: timestamp,
      question: nextPanel.question,
      summary: nextPanel.summary,
      report: nextPanel.report,
      memory: [...stateMemory, memory],
    };
    const gitRef = commitScienceArtifactSnapshot({
      projectRoot: project.projectRoot,
      panel: nextPanel,
      state: nextState,
      events,
      event,
      target: event.target,
      message: `Edit report: ${memory.summary}`,
    });
    if (!gitRef.ok) return { ok: false, error: gitRef.error || 'The report Git snapshot failed.' };

    memory.commit = gitRef.commit;
    event.git = gitRef;
    nextPanel.git = gitRef;
    nextState.git = gitRef;
    nextState.memory = [...stateMemory, memory];
    writeJson(panelPath, nextPanel);
    writeJson(statePath, nextState);
    writeJsonl(path.join(root, 'events.jsonl'), events);
    return { ok: true, panel: nextPanel, git: gitRef, memory };
  } catch (error) {
    return { ok: false, error: error instanceof Error ? error.message : String(error) };
  } finally {
    if (lockFd !== undefined) {
      fs.closeSync(lockFd);
      try {
        fs.unlinkSync(lockPath);
      } catch {
        // The lock may already have been removed after a failed acquisition.
      }
    }
  }
}

const readGitJson = <T>(repoPath: string, commit: string, objectPath: string): T | undefined => {
  const raw = gitOutput(repoPath, ['show', `${commit}:${objectPath}`]);
  if (!raw) return undefined;
  try {
    return JSON.parse(raw) as T;
  } catch {
    return undefined;
  }
};

const formatResultSummaryNumber = (value: number): string =>
  new Intl.NumberFormat('en-US', { maximumFractionDigits: 6, useGrouping: false }).format(value);

const formatResultSummaryMetric = (metric: ScienceResultSummaryMetric): string => {
  const value =
    metric.value != null
      ? formatResultSummaryNumber(metric.value)
      : metric.interval
        ? `${formatResultSummaryNumber(metric.interval.lower)}-${formatResultSummaryNumber(metric.interval.upper)}`
        : 'Pending';
  const unit = metric.unit ? ` ${metric.unit}` : '';
  const interval = metric.interval
    ? metric.value != null
      ? ` (${metric.interval.level ? `${Math.round(metric.interval.level * 100)}% ` : ''}${metric.interval.kind}: ${formatResultSummaryNumber(metric.interval.lower)}-${formatResultSummaryNumber(metric.interval.upper)}${metric.interval.method ? `; ${metric.interval.method}` : ''})`
      : ` (${metric.interval.level ? `${Math.round(metric.interval.level * 100)}% ` : ''}${metric.interval.kind}${metric.interval.method ? `; ${metric.interval.method}` : ''})`
    : '';
  return `${value}${unit}${interval}${metric.comparison ? `; ${metric.comparison}` : ''}`;
};

const resultSummaryEvidenceRefs = (ids?: string[]): string =>
  ids?.length ? ` ${ids.map((id) => `[${id}]`).join(' ')}` : '';

const stripInlineBoldMarkers = (value: string): string => value.replace(/\*\*([^*\n]+)\*\*/gu, '$1');

const resultSummaryToMarkdownLines = (block: ScienceResultSummaryBlock): string[] => [
  `### ${stripInlineBoldMarkers(block.title || 'Result summary')}`,
  '',
  `${block.takeaway}${resultSummaryEvidenceRefs(block.evidenceIds)}`,
  '',
  ...block.metrics.map(
    (metric) =>
      `- **${stripInlineBoldMarkers(metric.label)}:** ${formatResultSummaryMetric(metric)} [${metric.basis}; ${metric.role}]${resultSummaryEvidenceRefs(metric.evidenceIds)}`
  ),
  ...(block.metrics.length ? [''] : []),
  ...(block.facts || []).map(
    (fact) => `- **${stripInlineBoldMarkers(fact.label)}:** ${fact.value}${resultSummaryEvidenceRefs(fact.evidenceIds)}`
  ),
  ...(block.facts?.length ? [''] : []),
  ...(block.note ? [`> ${block.note}`, ''] : []),
];

const markdownTableValue = (value: string | number | boolean | null): string =>
  value === null ? '-' : String(value).replace(/\|/gu, '\\|').replace(/\r?\n/gu, ' ');

const structuredCardToMarkdownLines = (card: StructuredReportCard): string[] => {
  const lines = [
    `### ${stripInlineBoldMarkers(card.title)}`,
    '',
    `_${card.lifecycle} · ${card.freshness} · ${card.completeness} · ${card.dataMode} · trading disabled_`,
    '',
  ];
  if (card.kind === 'metric_strip') {
    card.metrics.forEach((metric) => {
      lines.push(
        `- **${stripInlineBoldMarkers(metric.label)}:** ${markdownTableValue(metric.value)}${metric.unit ? ` ${metric.unit}` : ''}`
      );
    });
  } else if (card.kind === 'timeseries') {
    card.series.forEach((series) => {
      lines.push(`- **${stripInlineBoldMarkers(series.label)}${series.unit ? ` (${series.unit})` : ''}**`);
      series.points.forEach((point) =>
        lines.push(`  - ${markdownTableValue(point.x)}: ${markdownTableValue(point.y)}`)
      );
    });
  } else if (card.kind === 'data_table') {
    lines.push(
      `| ${card.columns.map((column) => column.label).join(' | ')} |`,
      `| ${card.columns.map(() => '---').join(' | ')} |`
    );
    card.rows.forEach((row) => {
      lines.push(`| ${card.columns.map((column) => markdownTableValue(row[column.key] ?? null)).join(' | ')} |`);
    });
  } else if (card.kind === 'ranked_list') {
    card.items.forEach((item) => {
      lines.push(
        `${item.rank}. **${stripInlineBoldMarkers(item.label)}**${item.value == null ? '' : `: ${markdownTableValue(item.value)}`}${item.detail ? ` — ${item.detail}` : ''}`
      );
    });
  } else {
    card.items.forEach((item) => {
      lines.push(`- [${item.evidenceId}] **${stripInlineBoldMarkers(item.title)}** — ${item.source} (${item.asOf})`);
      if (item.detail) lines.push(`  - ${item.detail}`);
    });
  }
  lines.push('');
  return lines;
};

const cardReferenceToMarkdownLines = (panel: SciencePanelData, cardId: string): string[] => {
  const card = panel.cards?.find((candidate) => candidate.id === cardId);
  return card
    ? structuredCardToMarkdownLines(card)
    : [`> Report card unavailable: \`${cardId}\` is not present in this panel snapshot.`, ''];
};

const panelToMarkdown = (panel: SciencePanelData, options: { includeHeader?: boolean } = {}): string => {
  const includeHeader = options.includeHeader !== false;
  const lines: string[] = includeHeader
    ? [`# ${panel.report.title || panel.question}`, '', `Run: \`${panel.runId}\``, '']
    : [];
  if (panel.summary) lines.push(panel.summary, '');
  for (const section of panel.report.sections) {
    lines.push(`## ${section.heading}`, '');
    for (const block of section.blocks) {
      if (block.type === 'paragraph') lines.push(block.text, '');
      if (block.type === 'bullet_list') {
        block.items.forEach((item) => lines.push(`- ${item.text}`));
        lines.push('');
      }
      if (block.type === 'checklist') {
        block.items.forEach((item) =>
          lines.push(
            `- [${item.status === 'done' || item.status === 'passed' ? 'x' : ' '}] ${item.label}${item.detail ? `: ${item.detail}` : ''}`
          )
        );
        lines.push('');
      }
      if (block.type === 'result_summary') lines.push(...resultSummaryToMarkdownLines(block));
      if (block.type === 'card_ref') {
        lines.push(...cardReferenceToMarkdownLines(panel, block.cardId));
        continue;
      }
      if (block.type === 'artifact_embed') {
        const artifact = panel.artifacts.find((item) => item.id === block.artifactId);
        const artifactPath = artifact?.previewPath || artifact?.primaryPath || artifact?.thumbnailPath;
        if (artifactPath && artifact?.type === 'figure') {
          lines.push(`![${block.caption || artifact.title}](${artifactPath})`, '');
        } else {
          lines.push(`- Embedded artifact: \`${block.artifactId}\`${block.caption ? ` — ${block.caption}` : ''}`, '');
        }
        continue;
      }
      if ('artifactId' in block) lines.push(`- Artifact: \`${block.artifactId}\``, '');
    }
  }
  if (panel.artifacts.length) {
    lines.push('## Artifacts', '');
    panel.artifacts.forEach((artifact) => {
      lines.push(
        `- \`${artifact.id}\` v${artifact.version}: ${artifact.title}${artifact.primaryPath ? ` (${artifact.primaryPath})` : ''}`
      );
    });
    lines.push('');
  }
  if (panel.evidence.length) {
    lines.push('## Reference Evidence', '');
    panel.evidence.forEach((evidence) => {
      lines.push(
        `- [${evidence.id}] ${evidence.title}${evidence.path ? ` — ${evidence.path}` : evidence.url ? ` — ${evidence.url}` : ''}`
      );
      if (evidence.summary) lines.push(`  - ${evidence.summary}`);
    });
    lines.push('');
  }
  if (panel.graphWarnings?.length) {
    lines.push('## Provenance Warnings', '');
    panel.graphWarnings.forEach((warning) => lines.push(`- ${warning.severity}: ${warning.message}`));
    lines.push('');
  }
  if (panel.cardDiagnostics?.length) {
    lines.push('## Report Card Diagnostics', '');
    panel.cardDiagnostics.forEach((diagnostic) => lines.push(`- ${diagnostic}`));
    lines.push('');
  }
  return `${lines.join('\n').trim()}\n`;
};

const portablePublishedPath = (projectRoot: string, reportDir: string, value?: string): string | undefined => {
  const candidate = String(value || '').trim();
  if (!candidate || !isPlausibleLocalFileReference(candidate)) return undefined;
  const resolved = path.isAbsolute(candidate) ? path.resolve(candidate) : path.resolve(projectRoot, candidate);
  if (!isInside(projectRoot, resolved)) return undefined;
  return toPosix(path.relative(reportDir, resolved));
};

const portablePanelForProjectReport = (
  panel: SciencePanelData,
  projectRoot: string,
  reportDir: string
): SciencePanelData => ({
  ...panel,
  projectRoot: undefined,
  artifacts: panel.artifacts.map((artifact) => ({
    ...artifact,
    primaryPath: portablePublishedPath(projectRoot, reportDir, artifact.primaryPath),
    previewPath: portablePublishedPath(projectRoot, reportDir, artifact.previewPath),
    thumbnailPath: portablePublishedPath(projectRoot, reportDir, artifact.thumbnailPath),
    sourcePaths: artifact.sourcePaths
      ?.map((item) => portablePublishedPath(projectRoot, reportDir, item))
      .filter((item): item is string => Boolean(item)),
    inputPaths: artifact.inputPaths
      ?.map((item) => portablePublishedPath(projectRoot, reportDir, item))
      .filter((item): item is string => Boolean(item)),
    outputPaths: artifact.outputPaths
      ?.map((item) => portablePublishedPath(projectRoot, reportDir, item))
      .filter((item): item is string => Boolean(item)),
  })),
  evidence: panel.evidence.map((evidence) => ({
    ...evidence,
    path: portablePublishedPath(projectRoot, reportDir, evidence.path),
  })),
});

type PublishedFileBackup = { filePath: string; content?: Buffer };

const writeFileAtomic = (filePath: string, content: string): void => {
  fs.mkdirSync(path.dirname(filePath), { recursive: true });
  const temporaryPath = `${filePath}.tmp-${process.pid}-${crypto.randomBytes(4).toString('hex')}`;
  try {
    fs.writeFileSync(temporaryPath, content, 'utf8');
    fs.renameSync(temporaryPath, filePath);
  } finally {
    if (fs.existsSync(temporaryPath)) fs.rmSync(temporaryPath, { force: true });
  }
};

const restorePublishedFiles = (backups: PublishedFileBackup[], reportDir: string): void => {
  for (const backup of backups) {
    if (backup.content) {
      fs.mkdirSync(path.dirname(backup.filePath), { recursive: true });
      fs.writeFileSync(backup.filePath, backup.content);
    } else {
      fs.rmSync(backup.filePath, { force: true });
    }
  }
  try {
    if (fs.existsSync(reportDir) && fs.readdirSync(reportDir).length === 0) fs.rmdirSync(reportDir);
  } catch {
    // A concurrent writer may have added another published file; leave the directory intact.
  }
};

export function publishScienceArtifactReportToProject(
  request: ScienceArtifactProjectPublishRequest
): ScienceArtifactProjectPublishResult {
  const fallback: ScienceArtifactProjectPublishResult = { ok: false, changedFiles: [] };
  const projectRoot = String(request.projectRoot || '').trim();
  const runId = String(request.runId || '').trim();
  if (!projectRoot || !runId) return { ...fallback, error: 'projectRoot and runId are required.' };
  if (request.commit && !/^[a-f0-9]{7,40}$/iu.test(request.commit)) {
    return { ...fallback, error: 'The Artifact commit is invalid.' };
  }

  const repository = discoverProjectGit({ workspace: projectRoot });
  if (!repository.ok || !repository.repository) {
    return { ...fallback, error: 'The selected project is not a Git repository.' };
  }
  const project = ensureScienceArtifactRepo(projectRoot);
  if (!project || !fs.existsSync(path.join(project.artifactRepoPath, '.git'))) {
    return { ...fallback, error: 'Science artifact history is unavailable for this project.' };
  }
  const artifactCommit = request.commit || gitHead(project.artifactRepoPath);
  if (!artifactCommit) return { ...fallback, error: 'No frozen Science report snapshot is available.' };

  const runSegment = safeSegment(runId, 'run');
  const panel = readGitJson<SciencePanelData>(
    project.artifactRepoPath,
    artifactCommit,
    `runs/${runSegment}/panel.json`
  );
  if (!panel) {
    return { ...fallback, error: `Run ${runId} is not available at Artifact commit ${artifactCommit}.` };
  }

  const reportRelativeDir = toPosix(path.join('reports', runSegment));
  const reportDir = path.join(projectRoot, reportRelativeDir);
  const reportRelativePath = toPosix(path.join(reportRelativeDir, 'report.md'));
  const manifestRelativePath = toPosix(path.join(reportRelativeDir, 'report-manifest.json'));
  const reportPath = path.join(projectRoot, reportRelativePath);
  const manifestPath = path.join(projectRoot, manifestRelativePath);
  const portablePanel = portablePanelForProjectReport(panel, projectRoot, reportDir);
  const selectedArtifact = panel.artifacts
    .filter(
      (artifact) =>
        (!request.artifactId || artifact.id === request.artifactId) &&
        (!request.artifactVersion || artifact.version === request.artifactVersion)
    )
    .toSorted((left, right) => right.version - left.version)[0];
  const reportArtifact =
    selectedArtifact ||
    panel.artifacts
      .filter((artifact) => artifact.type === 'report' || String(artifact.type) === 'research_report')
      .toSorted((left, right) => right.version - left.version)[0];
  const artifactRef = {
    runId: panel.runId,
    artifactId: reportArtifact?.id || request.artifactId || 'report',
    version: reportArtifact?.version || request.artifactVersion || 1,
    revision: reportArtifact?.revision || panel.report.revision,
  };
  const reportContent = panelToMarkdown(portablePanel);
  const manifestContent = `${JSON.stringify(
    {
      schema: 'deepscientist.published-report.v1',
      projectId: project.projectId,
      runId: panel.runId,
      conversationId: panel.conversationId,
      title: panel.report.title || panel.question,
      generatedAt: panel.generatedAt,
      reportPath: 'report.md',
      artifact: {
        commit: artifactCommit,
        shortCommit: artifactCommit.slice(0, 7),
        ...artifactRef,
      },
      sourceGit: panel.sourceGit
        ? {
            branch: panel.sourceGit.branch,
            commit: panel.sourceGit.commit,
            shortCommit: panel.sourceGit.shortCommit,
            subject: panel.sourceGit.subject,
            stage: panel.sourceGit.stage,
            domain: panel.sourceGit.domain,
          }
        : undefined,
    },
    null,
    2
  )}\n`;
  const nextFiles = [
    { filePath: reportPath, content: reportContent },
    { filePath: manifestPath, content: manifestContent },
  ];
  const backups = nextFiles.map(({ filePath }) => ({
    filePath,
    content: fs.existsSync(filePath) ? fs.readFileSync(filePath) : undefined,
  }));
  try {
    nextFiles.forEach(({ filePath, content }) => writeFileAtomic(filePath, content));
    const checkpointPaths = [
      reportRelativePath,
      manifestRelativePath,
      '.deepscientist/project.json',
      '.deepscientist/.gitignore',
    ];
    const status = git(projectRoot, ['status', '--porcelain=v1', '--untracked-files=normal', '--', ...checkpointPaths]);
    if (status.status !== 0) {
      restorePublishedFiles(backups, reportDir);
      return { ...fallback, error: String(status.stderr || 'Unable to inspect the published report files.') };
    }
    if (!String(status.stdout || '').trim()) {
      return {
        ok: true,
        status: 'unchanged',
        projectId: project.projectId,
        reportDir,
        reportPath,
        manifestPath,
        artifactCommit,
        projectCommit: repository.repository.head,
        projectShortCommit: repository.repository.head?.slice(0, 7),
        changedFiles: [],
      };
    }
    const checkpoint = createProjectGitCheckpoint({
      workspace: projectRoot,
      message: `publish report ${panel.report.title || panel.question}`,
      stage: 'report',
      includePaths: checkpointPaths,
      verification: [`Artifact snapshot ${artifactCommit.slice(0, 7)}`],
      runId: panel.runId,
      conversationId: panel.conversationId,
      domain: panel.sourceGit?.domain || 'research',
      artifactRef,
    });
    if (!checkpoint.ok || !checkpoint.commit) {
      restorePublishedFiles(backups, reportDir);
      return { ...fallback, error: checkpoint.error || 'The report could not be committed to the project.' };
    }
    return {
      ok: true,
      status: 'committed',
      projectId: project.projectId,
      reportDir,
      reportPath,
      manifestPath,
      artifactCommit,
      projectCommit: checkpoint.commit,
      projectShortCommit: checkpoint.shortCommit,
      changedFiles: checkpoint.changedFiles,
    };
  } catch (error) {
    restorePublishedFiles(backups, reportDir);
    return { ...fallback, error: error instanceof Error ? error.message : String(error) };
  }
}

const escapeHtml = (value: string): string =>
  value.replace(/&/gu, '&amp;').replace(/</gu, '&lt;').replace(/>/gu, '&gt;').replace(/"/gu, '&quot;');

const renderInlineHtml = (value: string): string =>
  escapeHtml(value)
    .replace(/\*\*([^*\n]+)\*\*/gu, '<strong>$1</strong>')
    .replace(/`([^`]+)`/gu, '<code>$1</code>')
    .replace(/\[([A-Za-z]\d+)\]/gu, '<span class="evidence-ref">[$1]</span>');

const sourceTypeLabel = (value: string): string => value.replace(/_/gu, ' ');

const artifactDisplayPath = (artifact?: ScienceArtifact): string | undefined =>
  artifact?.previewPath || artifact?.primaryPath || artifact?.thumbnailPath || artifact?.outputPaths?.[0];

const artifactFileUrl = (filePath?: string): string | undefined => {
  if (!filePath) return undefined;
  if (/^[a-z]+:\/\//iu.test(filePath)) return filePath;
  return path.isAbsolute(filePath) ? pathToFileURL(filePath).toString() : filePath;
};

const structuredCardToHtml = (card: StructuredReportCard): string => {
  let content = '';
  if (card.kind === 'metric_strip') {
    content = `<dl class="result-metrics">${card.metrics
      .map(
        (metric) =>
          `<div><dt>${renderInlineHtml(metric.label)}</dt><dd>${renderInlineHtml(String(metric.value))}${metric.unit ? ` ${escapeHtml(metric.unit)}` : ''}</dd></div>`
      )
      .join('')}</dl>`;
  } else if (card.kind === 'timeseries') {
    content = card.series
      .map(
        (series) =>
          `<div class="table-wrap"><table><caption>${renderInlineHtml(series.label)}</caption><thead><tr><th>Point</th><th>Value${series.unit ? ` (${escapeHtml(series.unit)})` : ''}</th></tr></thead><tbody>${series.points
            .map((point) => `<tr><td>${escapeHtml(String(point.x))}</td><td>${escapeHtml(String(point.y))}</td></tr>`)
            .join('')}</tbody></table></div>`
      )
      .join('');
  } else if (card.kind === 'data_table') {
    content = `<div class="table-wrap"><table><thead><tr>${card.columns
      .map((column) => `<th>${renderInlineHtml(column.label)}</th>`)
      .join('')}</tr></thead><tbody>${card.rows
      .map(
        (row) =>
          `<tr>${card.columns
            .map((column) => `<td>${escapeHtml(row[column.key] == null ? '-' : String(row[column.key]))}</td>`)
            .join('')}</tr>`
      )
      .join('')}</tbody></table></div>`;
  } else if (card.kind === 'ranked_list') {
    content = `<ol class="report-list">${card.items
      .map(
        (item) =>
          `<li value="${item.rank}"><strong>${renderInlineHtml(item.label)}</strong>${item.value == null ? '' : `: ${renderInlineHtml(String(item.value))}`}${item.detail ? ` <span class="muted">${renderInlineHtml(item.detail)}</span>` : ''}</li>`
      )
      .join('')}</ol>`;
  } else {
    content = `<ul class="report-list">${card.items
      .map(
        (item) =>
          `<li><span class="evidence-ref">[${escapeHtml(item.evidenceId)}]</span> <strong>${renderInlineHtml(item.title)}</strong> — ${renderInlineHtml(item.source)} <span class="muted">${escapeHtml(item.asOf)}</span>${item.detail ? `<br><span class="muted">${renderInlineHtml(item.detail)}</span>` : ''}</li>`
      )
      .join('')}</ul>`;
  }
  return [
    '<article class="result-summary report-card">',
    `<header><span>${escapeHtml(card.kind.replace(/_/gu, ' '))}</span><strong>${renderInlineHtml(card.title)}</strong></header>`,
    `<p class="muted">${escapeHtml(`${card.lifecycle} · ${card.freshness} · ${card.completeness} · ${card.dataMode} · trading disabled`)}</p>`,
    content,
    '</article>',
  ].join('\n');
};

const renderReportBlockHtml = (
  panel: SciencePanelData,
  block: SciencePanelData['report']['sections'][number]['blocks'][number]
): string => {
  if (block.type === 'paragraph') return `<p>${renderInlineHtml(block.text)}</p>`;
  if (block.type === 'bullet_list') {
    return [
      '<ul class="report-list">',
      ...block.items.map((item) => `<li>${renderInlineHtml(item.text)}</li>`),
      '</ul>',
    ].join('\n');
  }
  if (block.type === 'checklist') {
    return [
      '<ul class="checklist">',
      ...block.items.map((item) => {
        const done = item.status === 'done' || item.status === 'passed';
        const detail = item.detail ? `<span class="muted"> - ${renderInlineHtml(item.detail)}</span>` : '';
        return `<li><span class="check">${done ? '&#10003;' : ''}</span><span>${renderInlineHtml(item.label)}${detail}</span></li>`;
      }),
      '</ul>',
    ].join('\n');
  }
  if (block.type === 'result_summary') {
    const evidenceHtml = (ids?: string[]): string =>
      ids?.length
        ? ` <span class="result-evidence">${ids
            .map((id) => `<span class="evidence-ref">[${escapeHtml(id)}]</span>`)
            .join(' ')}</span>`
        : '';
    return [
      '<article class="result-summary">',
      `<header><span>Result summary</span><strong>${renderInlineHtml(block.title || 'Result summary')}</strong></header>`,
      `<p class="result-takeaway">${renderInlineHtml(block.takeaway)}${evidenceHtml(block.evidenceIds)}</p>`,
      '<dl class="result-metrics">',
      ...block.metrics.map(
        (metric) =>
          `<div data-basis="${escapeHtml(metric.basis)}" data-role="${escapeHtml(metric.role)}"><dt>${renderInlineHtml(metric.label)}</dt><dd>${renderInlineHtml(formatResultSummaryMetric(metric))}${evidenceHtml(metric.evidenceIds)}</dd><small>${escapeHtml(metric.basis)}</small></div>`
      ),
      '</dl>',
      block.facts?.length
        ? `<dl class="result-facts">${block.facts
            .map(
              (fact) =>
                `<div><dt>${renderInlineHtml(fact.label)}</dt><dd>${renderInlineHtml(fact.value)}${evidenceHtml(fact.evidenceIds)}</dd></div>`
            )
            .join('')}</dl>`
        : '',
      block.note ? `<p class="result-note">${renderInlineHtml(block.note)}</p>` : '',
      '</article>',
    ].join('\n');
  }
  if (block.type === 'card_ref') {
    const card = panel.cards?.find((candidate) => candidate.id === block.cardId);
    return card
      ? structuredCardToHtml(card)
      : `<p class="artifact-ref warning-section">Report card <code>${escapeHtml(block.cardId)}</code> is unavailable in this panel snapshot.</p>`;
  }
  if (block.type === 'artifact_embed') {
    const artifact = panel.artifacts.find((item) => item.id === block.artifactId);
    const artifactPath = artifactDisplayPath(artifact);
    const src = artifactFileUrl(artifactPath);
    const caption = block.caption || artifact?.title || block.artifactId;
    const isImage = Boolean(artifactPath && /\.(png|jpe?g|gif|svg|webp|bmp|tiff?|avif)$/iu.test(artifactPath));
    const media =
      src && isImage
        ? `<img src="${escapeHtml(src)}" alt="${escapeHtml(caption)}" />`
        : `<p class="artifact-ref">Embedded artifact <code>${escapeHtml(block.artifactId)}</code>${artifact ? ` &middot; ${renderInlineHtml(artifact.title)}` : ''}</p>`;
    return [
      '<figure class="artifact-embed">',
      media,
      `<figcaption>${renderInlineHtml(caption)}</figcaption>`,
      '</figure>',
    ].join('\n');
  }
  if ('artifactId' in block) {
    const artifact = panel.artifacts.find((item) => item.id === block.artifactId);
    return `<p class="artifact-ref">Artifact <code>${escapeHtml(block.artifactId)}</code>${artifact ? ` &middot; ${renderInlineHtml(artifact.title)}` : ''}</p>`;
  }
  return '';
};

const panelToHtml = (panel: SciencePanelData): string => {
  const title = panel.report.title || panel.question;
  const body = [
    '<header class="report-header">',
    '<div class="eyebrow">DeepScientist artifact export</div>',
    `<h1>${renderInlineHtml(title)}</h1>`,
    '<div class="meta-grid">',
    `<div><span>Run</span><strong>${escapeHtml(panel.runId)}</strong></div>`,
    `<div><span>Status</span><strong>${escapeHtml(panel.status)}</strong></div>`,
    `<div><span>Artifacts</span><strong>${panel.artifacts.length}</strong></div>`,
    `<div><span>Evidence</span><strong>${panel.evidence.length}</strong></div>`,
    '</div>',
    '</header>',
    panel.summary
      ? `<section class="summary-block"><h2>Summary</h2><p>${renderInlineHtml(panel.summary)}</p></section>`
      : '',
    ...panel.report.sections.map((section) =>
      [
        '<section class="report-section">',
        `<h2>${renderInlineHtml(section.heading)}</h2>`,
        ...section.blocks.map((block) => renderReportBlockHtml(panel, block)),
        '</section>',
      ].join('\n')
    ),
    panel.artifacts.length
      ? [
          '<section class="report-section">',
          '<h2>Artifacts</h2>',
          '<div class="table-wrap"><table>',
          '<thead><tr><th>ID</th><th>Version</th><th>Title</th><th>Primary file</th></tr></thead>',
          '<tbody>',
          ...panel.artifacts.map(
            (artifact) =>
              `<tr><td><code>${escapeHtml(artifact.id)}</code></td><td>v${artifact.version}</td><td>${renderInlineHtml(artifact.title)}</td><td>${artifact.primaryPath ? `<code>${escapeHtml(artifact.primaryPath)}</code>` : '<span class="muted">-</span>'}</td></tr>`
          ),
          '</tbody></table></div>',
          '</section>',
        ].join('\n')
      : '',
    panel.evidence.length
      ? [
          '<section class="report-section">',
          '<h2>Reference Evidence</h2>',
          '<div class="evidence-list">',
          ...panel.evidence.map((evidence) =>
            [
              '<article class="evidence-card">',
              `<div class="evidence-title"><span class="evidence-ref">[${escapeHtml(evidence.id)}]</span><strong>${renderInlineHtml(evidence.title)}</strong></div>`,
              `<div class="evidence-meta">${escapeHtml(sourceTypeLabel(evidence.sourceType))} &middot; ${escapeHtml(evidence.confidence)}${evidence.path ? ` &middot; <code>${escapeHtml(evidence.path)}</code>` : evidence.url ? ` &middot; ${renderInlineHtml(evidence.url)}` : ''}</div>`,
              evidence.summary ? `<p>${renderInlineHtml(evidence.summary)}</p>` : '',
              '</article>',
            ].join('\n')
          ),
          '</div>',
          '</section>',
        ].join('\n')
      : '',
    panel.graphWarnings?.length
      ? [
          '<section class="report-section warning-section">',
          '<h2>Provenance Warnings</h2>',
          '<ul class="report-list">',
          ...panel.graphWarnings.map(
            (warning) =>
              `<li><strong>${escapeHtml(warning.severity)}</strong>: ${renderInlineHtml(warning.message)}</li>`
          ),
          '</ul>',
          '</section>',
        ].join('\n')
      : '',
    panel.cardDiagnostics?.length
      ? [
          '<section class="report-section warning-section">',
          '<h2>Report Card Diagnostics</h2>',
          '<ul class="report-list">',
          ...panel.cardDiagnostics.map((diagnostic) => `<li>${renderInlineHtml(diagnostic)}</li>`),
          '</ul>',
          '</section>',
        ].join('\n')
      : '',
  ].join('\n');
  return [
    '<!doctype html>',
    '<html>',
    '<head>',
    '<meta charset="utf-8" />',
    `<title>${escapeHtml(title)}</title>`,
    '<style>',
    '@page{size:A4;margin:20mm;}',
    '*{box-sizing:border-box;}',
    'html{background:#eef0f2;}',
    'body{font-family:-apple-system,BlinkMacSystemFont,"Segoe UI",Arial,sans-serif;line-height:1.58;color:#20242a;background:#fff;}',
    '@media screen{body{width:210mm;min-height:297mm;margin:24px auto;padding:20mm;box-shadow:0 20px 64px rgba(24,30,38,.12);}}',
    '@media print{html{background:#fff;}body{margin:0;padding:0;box-shadow:none;}}',
    '.report-header{border-bottom:1px solid #d8dde3;padding:0 0 18px;margin:0 0 24px;}',
    '.eyebrow{font-size:11px;letter-spacing:.08em;text-transform:uppercase;color:#68717d;font-weight:700;margin-bottom:8px;}',
    'h1{font-size:30px;line-height:1.16;margin:0 0 18px;font-weight:760;}',
    'h2{font-size:18px;line-height:1.25;margin:0 0 12px;font-weight:720;}',
    'p{margin:0 0 12px;}',
    'code{font-family:"SFMono-Regular","Roboto Mono",Consolas,monospace;background:#f3f5f7;border:1px solid #e4e8ee;border-radius:5px;padding:1px 5px;font-size:.92em;}',
    '.meta-grid{display:grid;grid-template-columns:repeat(4,1fr);gap:10px;}',
    '.meta-grid div{border:1px solid #e3e7ec;border-radius:8px;padding:10px 12px;background:#fafbfc;}',
    '.meta-grid span{display:block;color:#7a8491;font-size:11px;text-transform:uppercase;letter-spacing:.06em;}',
    '.meta-grid strong{display:block;margin-top:4px;font-size:14px;}',
    '.summary-block,.report-section{break-inside:avoid;margin:0 0 24px;}',
    '.report-section{border-top:1px solid #e6e9ee;padding-top:18px;}',
    '.report-list{margin:0 0 12px 18px;padding:0;}',
    '.report-list li{margin:5px 0;}',
    '.checklist{list-style:none;margin:0 0 12px;padding:0;}',
    '.checklist li{display:flex;gap:8px;margin:6px 0;}',
    '.check{width:16px;height:16px;border:1px solid #b8c0ca;border-radius:4px;display:inline-flex;align-items:center;justify-content:center;font-size:11px;font-weight:700;margin-top:3px;}',
    '.result-summary{border:1px solid #dfe4e8;border-radius:7px;background:#fafbfa;padding:16px 17px;margin:0 0 18px;break-inside:avoid;}',
    '.result-summary header{display:flex;justify-content:space-between;gap:12px;align-items:baseline;border-bottom:1px solid #e5e8e6;padding-bottom:9px;}',
    '.result-summary header span,.result-summary small{color:#727b77;font-size:11px;text-transform:uppercase;letter-spacing:.04em;}',
    '.result-takeaway{font-weight:650;margin:12px 0;}',
    '.result-metrics,.result-facts{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));margin:0;}',
    '.result-metrics>div,.result-facts>div{padding:9px 12px;border-left:1px solid #e5e8e6;}',
    '.result-metrics>div:nth-child(odd),.result-facts>div:nth-child(odd){border-left:0;padding-left:0;}',
    '.result-metrics dt,.result-facts dt{color:#727b77;font-size:11px;}',
    '.result-metrics dd,.result-facts dd{margin:3px 0 0;font-weight:680;font-variant-numeric:tabular-nums;}',
    '.result-metrics [data-role="primary"] dd{font-size:22px;}',
    '.result-facts{border-top:1px solid #e5e8e6;margin-top:9px;padding-top:4px;}',
    '.result-note{border-top:1px solid #e5e8e6;color:#68717d;font-size:12px;margin:9px 0 0;padding-top:9px;}',
    '.artifact-ref{border-left:3px solid #6f7b88;padding-left:10px;color:#38414a;}',
    '.artifact-embed{margin:14px 0 18px;padding:0;}',
    '.artifact-embed img{display:block;max-width:100%;height:auto;margin:0 auto;border-top:1px solid #e6e9ee;border-bottom:1px solid #e6e9ee;padding:10px 0;}',
    '.artifact-embed figcaption{margin-top:7px;color:#68717d;font-size:12px;line-height:1.45;}',
    '.table-wrap{overflow:hidden;border:1px solid #e1e5ea;border-radius:8px;}',
    'table{width:100%;border-collapse:collapse;font-size:13px;}',
    'th,td{text-align:left;vertical-align:top;padding:9px 10px;border-bottom:1px solid #edf0f3;}',
    'th{background:#f7f8fa;color:#5e6773;font-size:11px;text-transform:uppercase;letter-spacing:.05em;}',
    'tr:last-child td{border-bottom:none;}',
    '.evidence-list{display:grid;gap:10px;}',
    '.evidence-card{border:1px solid #e1e5ea;border-radius:8px;padding:11px 12px;break-inside:avoid;}',
    '.evidence-title{display:flex;gap:8px;align-items:baseline;margin-bottom:4px;}',
    '.evidence-ref{font-family:"SFMono-Regular","Roboto Mono",Consolas,monospace;color:#2f5f9f;background:#eef4ff;border:1px solid #d7e4fb;border-radius:5px;padding:0 4px;font-size:.9em;}',
    '.evidence-meta,.muted{color:#77818e;}',
    '.warning-section{border-color:#ead6a3;}',
    '</style>',
    '</head>',
    '<body>',
    body,
    '</body>',
    '</html>',
    '',
  ].join('\n');
};

const panelToNotebook = (panel: SciencePanelData): string => {
  const markdownCells = [
    `# ${panel.report.title || panel.question}\n\nRun: \`${panel.runId}\`\n\n${panel.summary || panel.question || ''}`,
    panelToMarkdown(panel, { includeHeader: false }),
  ];
  const artifactCells = panel.artifacts.flatMap((artifact) => {
    const cells: JsonRecord[] = [
      {
        cell_type: 'markdown',
        metadata: {},
        source: [
          `## ${artifact.title}\n\n`,
          `- artifact: \`${artifact.id}\`\n`,
          `- version: v${artifact.version}\n`,
          artifact.primaryPath ? `- primaryPath: \`${artifact.primaryPath}\`\n` : '',
          artifact.execution?.logPath ? `- logPath: \`${artifact.execution.logPath}\`\n` : '',
        ].filter(Boolean),
      },
    ];
    if (artifact.execution?.command || artifact.code?.path) {
      cells.push({
        cell_type: 'code',
        execution_count: null,
        metadata: {},
        outputs: [],
        source: [
          '# Re-run this command in the original project environment when appropriate.\n',
          artifact.code?.path ? `# source: ${artifact.code.path}\n` : '',
          artifact.execution?.command || '',
          '\n',
        ].filter(Boolean),
      });
    }
    return cells;
  });
  const notebook = {
    cells: [
      ...markdownCells.map((source) => ({ cell_type: 'markdown', metadata: {}, source: source.split(/(?<=\n)/u) })),
      ...artifactCells,
    ],
    metadata: {
      kernelspec: {
        display_name: 'Python 3',
        language: 'python',
        name: 'python3',
      },
      deepscientist: {
        runId: panel.runId,
        generatedFrom: 'science artifact git snapshot',
      },
    },
    nbformat: 4,
    nbformat_minor: 5,
  };
  return `${JSON.stringify(notebook, null, 2)}\n`;
};

const escapeLatex = (value: string): string =>
  value
    .replace(/\\/gu, '\\textbackslash{}')
    .replace(/([#$%&_{}])/gu, '\\$1')
    .replace(/~/gu, '\\textasciitilde{}')
    .replace(/\^/gu, '\\textasciicircum{}');

const renderInlineLatex = (value: string): string => {
  const parts: string[] = [];
  const pattern = /\*\*([^*\n]+)\*\*/gu;
  let cursor = 0;
  let match: RegExpExecArray | null;
  while ((match = pattern.exec(value)) !== null) {
    parts.push(escapeLatex(value.slice(cursor, match.index)));
    parts.push(`\\textbf{${escapeLatex(match[1])}}`);
    cursor = match.index + match[0].length;
  }
  parts.push(escapeLatex(value.slice(cursor)));
  return parts.join('');
};

const structuredCardToLatexLines = (card: StructuredReportCard): string[] => {
  const lines = [
    '\\subsection*{' + escapeLatex(stripInlineBoldMarkers(card.title)) + '}',
    '\\noindent\\textit{' +
      escapeLatex(`${card.lifecycle}; ${card.freshness}; ${card.completeness}; ${card.dataMode}; trading disabled`) +
      '}',
    '\\begin{itemize}',
  ];
  if (card.kind === 'metric_strip') {
    card.metrics.forEach((metric) =>
      lines.push(
        '\\item \\textbf{' +
          escapeLatex(stripInlineBoldMarkers(metric.label)) +
          ':} ' +
          escapeLatex(String(metric.value)) +
          (metric.unit ? ' ' + escapeLatex(metric.unit) : '')
      )
    );
  } else if (card.kind === 'timeseries') {
    card.series.forEach((series) => {
      lines.push('\\item \\textbf{' + escapeLatex(series.label) + '}');
      series.points.forEach((point) =>
        lines.push(`\\item[] ${escapeLatex(String(point.x))}: ${escapeLatex(String(point.y))}`)
      );
    });
  } else if (card.kind === 'data_table') {
    card.rows.forEach((row) =>
      lines.push(
        '\\item ' +
          card.columns
            .map(
              (column) =>
                `${escapeLatex(column.label)}=${escapeLatex(row[column.key] == null ? '-' : String(row[column.key]))}`
            )
            .join('; ')
      )
    );
  } else if (card.kind === 'ranked_list') {
    card.items.forEach((item) =>
      lines.push(
        `\\item ${item.rank}. \\textbf{${escapeLatex(stripInlineBoldMarkers(item.label))}}${item.value == null ? '' : `: ${escapeLatex(String(item.value))}`}${item.detail ? `; ${renderInlineLatex(item.detail)}` : ''}`
      )
    );
  } else {
    card.items.forEach((item) =>
      lines.push(
        `\\item [${escapeLatex(item.evidenceId)}] \\textbf{${escapeLatex(stripInlineBoldMarkers(item.title))}}; ${escapeLatex(item.source)}; ${escapeLatex(item.asOf)}${item.detail ? `; ${renderInlineLatex(item.detail)}` : ''}`
      )
    );
  }
  lines.push('\\end{itemize}', '');
  return lines;
};

const panelToLatex = (panel: SciencePanelData): string => {
  const lines: string[] = [
    '\\documentclass[11pt]{article}',
    '\\usepackage[margin=1in]{geometry}',
    '\\usepackage{hyperref}',
    '\\usepackage{longtable}',
    '\\title{' + escapeLatex(stripInlineBoldMarkers(panel.report.title || panel.question)) + '}',
    '\\date{}',
    '\\begin{document}',
    '\\maketitle',
    '\\noindent\\textbf{Run:} \\texttt{' + escapeLatex(panel.runId) + '}',
    '',
  ];
  if (panel.summary) lines.push(renderInlineLatex(panel.summary), '');
  for (const section of panel.report.sections) {
    lines.push('\\section*{' + escapeLatex(stripInlineBoldMarkers(section.heading)) + '}');
    for (const block of section.blocks) {
      if (block.type === 'paragraph') lines.push(renderInlineLatex(block.text), '');
      if (block.type === 'bullet_list') {
        lines.push('\\begin{itemize}');
        block.items.forEach((item) => lines.push('\\item ' + renderInlineLatex(item.text)));
        lines.push('\\end{itemize}', '');
      }
      if (block.type === 'result_summary') {
        lines.push('\\subsection*{' + escapeLatex(stripInlineBoldMarkers(block.title || 'Result summary')) + '}');
        lines.push(
          renderInlineLatex(block.takeaway) +
            (block.evidenceIds?.length ? ' [' + escapeLatex(block.evidenceIds.join(', ')) + ']' : ''),
          '\\begin{itemize}'
        );
        block.metrics.forEach((metric) => {
          lines.push(
            '\\item \\textbf{' +
              escapeLatex(stripInlineBoldMarkers(metric.label)) +
              ':} ' +
              renderInlineLatex(formatResultSummaryMetric(metric)) +
              ' [' +
              escapeLatex(metric.basis) +
              ']' +
              (metric.evidenceIds?.length ? ' [' + escapeLatex(metric.evidenceIds.join(', ')) + ']' : '')
          );
        });
        block.facts?.forEach((fact) => {
          lines.push(
            '\\item \\textbf{' +
              escapeLatex(stripInlineBoldMarkers(fact.label)) +
              ':} ' +
              renderInlineLatex(fact.value) +
              (fact.evidenceIds?.length ? ' [' + escapeLatex(fact.evidenceIds.join(', ')) + ']' : '')
          );
        });
        lines.push('\\end{itemize}');
        if (block.note) lines.push('\\noindent\\textit{' + renderInlineLatex(block.note) + '}', '');
      }
      if (block.type === 'card_ref') {
        const card = panel.cards?.find((candidate) => candidate.id === block.cardId);
        lines.push(
          ...(card
            ? structuredCardToLatexLines(card)
            : ['\\noindent\\textbf{Report card unavailable:} \\texttt{' + escapeLatex(block.cardId) + '}', ''])
        );
        continue;
      }
      if (block.type === 'artifact_embed') {
        lines.push('\\noindent Embedded artifact: \\texttt{' + escapeLatex(block.artifactId) + '}', '');
        if (block.caption) lines.push('\\noindent ' + renderInlineLatex(block.caption), '');
        continue;
      }
      if ('artifactId' in block) lines.push('\\noindent Artifact: \\texttt{' + escapeLatex(block.artifactId) + '}', '');
    }
  }
  if (panel.evidence.length) {
    lines.push('\\section*{Reference Evidence}', '\\begin{itemize}');
    panel.evidence.forEach((evidence) => {
      lines.push('\\item [' + escapeLatex(evidence.id) + '] ' + escapeLatex(evidence.title));
    });
    lines.push('\\end{itemize}');
  }
  if (panel.cardDiagnostics?.length) {
    lines.push('\\section*{Report Card Diagnostics}', '\\begin{itemize}');
    panel.cardDiagnostics.forEach((diagnostic) => lines.push('\\item ' + escapeLatex(diagnostic)));
    lines.push('\\end{itemize}');
  }
  lines.push('\\end{document}', '');
  return lines.join('\n');
};

export function exportScienceArtifactSnapshot(request: ScienceArtifactExportRequest): ScienceArtifactExportResult {
  const project = ensureScienceArtifactRepo(request.projectRoot);
  if (!project || !fs.existsSync(path.join(project.artifactRepoPath, '.git'))) {
    return { ok: false, project, files: [], error: 'Science artifact repository is unavailable.' };
  }
  const sourceCommit = request.commit || gitHead(project.artifactRepoPath);
  if (!sourceCommit) return { ok: false, project, files: [], error: 'No Science artifact commit is available.' };
  const runSegment = safeSegment(request.runId, 'run');
  const panel = readGitJson<SciencePanelData>(project.artifactRepoPath, sourceCommit, `runs/${runSegment}/panel.json`);
  if (!panel)
    return { ok: false, project, files: [], error: `Run ${request.runId} is not available at commit ${sourceCommit}.` };

  const exportId = `export_${Date.now().toString(36)}_${sourceCommit.slice(0, 7)}`;
  const exportDir = path.join(project.deepScientistRoot, 'exports', runSegment, exportId);
  fs.mkdirSync(exportDir, { recursive: true });
  const exportTypes = new Set(request.exportTypes?.length ? request.exportTypes : ['manifest', 'panel', 'markdown']);
  const files: ScienceArtifactExportResult['files'] = [];
  const writeExportFile = (type: string, filePath: string, content: string): void => {
    fs.mkdirSync(path.dirname(filePath), { recursive: true });
    fs.writeFileSync(filePath, content, 'utf8');
    files.push({ type, path: filePath, contentHash: hashText(content) });
  };
  if (exportTypes.has('panel')) {
    writeExportFile('panel', path.join(exportDir, 'panel.json'), `${JSON.stringify(panel, null, 2)}\n`);
  }
  if (exportTypes.has('markdown')) {
    writeExportFile('markdown', path.join(exportDir, 'report.md'), panelToMarkdown(panel));
  }
  if (exportTypes.has('html')) {
    writeExportFile('html', path.join(exportDir, 'report.html'), panelToHtml(panel));
  }
  if (exportTypes.has('notebook')) {
    writeExportFile('notebook', path.join(exportDir, 'analysis.ipynb'), panelToNotebook(panel));
  }
  if (exportTypes.has('latex')) {
    writeExportFile('latex', path.join(exportDir, 'manuscript.tex'), panelToLatex(panel));
  }
  if (exportTypes.has('run_bundle')) {
    const bundlePath = path.join(exportDir, 'run-bundle.zip');
    const bundle = git(project.artifactRepoPath, [
      'archive',
      '--format=zip',
      '--output',
      bundlePath,
      sourceCommit,
      `runs/${runSegment}`,
    ]);
    if (bundle.status !== 0 || !fs.existsSync(bundlePath)) {
      return {
        ok: false,
        project,
        exportId,
        exportDir,
        sourceCommit,
        files,
        error: bundle.stderr || bundle.stdout || 'Failed to create run bundle.',
      };
    }
    files.push({ type: 'run_bundle', path: bundlePath, contentHash: hashFile(bundlePath) });
  }
  if (exportTypes.has('git_bundle') || request.includeGitHistory) {
    const bundlePath = path.join(exportDir, 'artifact-history.bundle');
    const bundle = git(project.artifactRepoPath, ['bundle', 'create', bundlePath, '--all']);
    if (bundle.status !== 0 || !fs.existsSync(bundlePath)) {
      return {
        ok: false,
        project,
        exportId,
        exportDir,
        sourceCommit,
        files,
        error: bundle.stderr || bundle.stdout || 'Failed to create git history bundle.',
      };
    }
    const contentHash = hashFile(bundlePath);
    files.push({ type: 'git_bundle', path: bundlePath, contentHash });
  }
  const manifest = {
    schema: 'deepscientist.science-export.v1',
    projectId: project.projectId,
    projectRoot: project.projectRoot,
    runId: request.runId,
    exportId,
    exportedAt: now(),
    sourceCommit,
    sourcePanelHash: hashText(JSON.stringify(panel)),
    artifactIds: request.artifactIds?.length ? request.artifactIds : panel.artifacts.map((artifact) => artifact.id),
    evidenceIds: panel.evidence.map((evidence) => evidence.id),
    exports: files.map((file) => ({
      type: file.type,
      path: path.relative(exportDir, file.path),
      contentHash: file.contentHash,
    })),
    completeness: exportTypes.has('run_bundle') ? 'complete_with_pointers' : 'partial',
    note: 'This export is generated from a frozen DeepScientist artifact git snapshot. Large files may be represented by pointers in the artifact repo.',
  };
  if (exportTypes.has('manifest')) {
    writeExportFile('manifest', path.join(exportDir, 'export-manifest.json'), `${JSON.stringify(manifest, null, 2)}\n`);
  }
  return {
    ok: true,
    project,
    exportId,
    exportDir,
    sourceCommit,
    files,
  };
}
