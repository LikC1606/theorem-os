/**
 * @license
 * Copyright 2026 DeepScientist (deepscientist.cc)
 * SPDX-License-Identifier: Apache-2.0
 */

import type {
  ProjectGitTargetSummary,
  ProjectGitCheckpointArtifactRef,
  ProjectGitChangedFile,
  ProjectGitCommitSummary,
  ProjectGitDomain,
  ProjectGitFileStatus,
  ProjectGitMetricContext,
  ProjectGitPerformanceMetric,
  ProjectGitResearchStageReceipt,
} from "../common/types/office/preview";
import {
  normalizeProjectGitDirectionDecision,
  normalizeResearchStrategy,
  parseResearchCommitSubject,
} from "../common/chat/researchStrategy";

const RECORD_SEPARATOR = '\x1e';
const FIELD_SEPARATOR = '\x1f';

const PROJECT_GIT_DOMAINS = new Set<ProjectGitDomain>([
  'general',
  'research',
  'medical_evidence',
  'knowledge_deposition',
  'financial',
  'financial_factor',
  'target_discovery',
  'mathematics',
  'challenge',
]);

export const PROJECT_GIT_LOG_FORMAT = ['%H', '%h', '%P', '%s', '%b', '%an', '%ae', '%aI', '%D'].join('%x1f') + '%x1e';

const parsePerformanceMetric = (value: string): ProjectGitPerformanceMetric | undefined => {
  try {
    const candidate = JSON.parse(value) as Record<string, unknown>;
    const name = typeof candidate.name === 'string' ? candidate.name.trim() : '';
    const metricValue = typeof candidate.value === 'number' ? candidate.value : Number.NaN;
    if (!name || !Number.isFinite(metricValue)) return undefined;
    const unit = typeof candidate.unit === 'string' ? candidate.unit.trim() : '';
    const direction =
      candidate.direction === 'maximize' || candidate.direction === 'minimize' ? candidate.direction : undefined;
    return {
      name: name.slice(0, 64),
      value: metricValue,
      ...(unit ? { unit: unit.slice(0, 24) } : {}),
      ...(direction ? { direction } : {}),
    };
  } catch {
    return undefined;
  }
};

const parseMetricContext = (value?: string): ProjectGitMetricContext | undefined => {
  if (!value) return undefined;
  try {
    const candidate = JSON.parse(value) as Record<string, unknown>;
    const contractId = typeof candidate.contractId === 'string' ? candidate.contractId.trim() : '';
    const evaluationId = typeof candidate.evaluationId === 'string' ? candidate.evaluationId.trim() : '';
    const baselineCommit = typeof candidate.baselineCommit === 'string' ? candidate.baselineCommit.trim() : '';
    const evaluationCode =
      candidate.evaluationCode && typeof candidate.evaluationCode === 'object'
        ? (candidate.evaluationCode as Record<string, unknown>)
        : undefined;
    const codePath = typeof evaluationCode?.path === 'string' ? evaluationCode.path.trim() : '';
    const safeCodePath =
      codePath &&
      !codePath.startsWith('/') &&
      !/^[a-z]:[\\/]/iu.test(codePath) &&
      !codePath.split(/[\\/]+/u).includes('..')
        ? codePath.replaceAll('\\', '/').slice(0, 300)
        : '';
    const runtime = ['python', 'node', 'r', 'notebook'].includes(String(evaluationCode?.runtime || ''))
      ? (evaluationCode?.runtime as 'python' | 'node' | 'r' | 'notebook')
      : undefined;
    const entrypoint = typeof evaluationCode?.entrypoint === 'string' ? evaluationCode.entrypoint.trim() : '';
    const sha256 =
      typeof evaluationCode?.sha256 === 'string' && /^[a-f0-9]{64}$/iu.test(evaluationCode.sha256)
        ? evaluationCode.sha256.toLowerCase()
        : '';
    if (!contractId || !evaluationId) return undefined;
    return {
      contractId: contractId.slice(0, 120),
      evaluationId: evaluationId.slice(0, 160),
      ...(baselineCommit ? { baselineCommit: baselineCommit.slice(0, 80) } : {}),
      ...(safeCodePath
        ? {
            evaluationCode: {
              path: safeCodePath,
              ...(runtime ? { runtime } : {}),
              ...(entrypoint ? { entrypoint: entrypoint.slice(0, 160) } : {}),
              ...(sha256 ? { sha256 } : {}),
            },
          }
        : {}),
    };
  } catch {
    return undefined;
  }
};

const parseArtifactRef = (value?: string): ProjectGitCheckpointArtifactRef | undefined => {
  if (!value) return undefined;
  try {
    const candidate = JSON.parse(value) as Record<string, unknown>;
    const runId = typeof candidate.runId === 'string' ? candidate.runId.trim() : '';
    const artifactId = typeof candidate.artifactId === 'string' ? candidate.artifactId.trim() : '';
    const version = typeof candidate.version === 'number' ? candidate.version : Number.NaN;
    const revision = typeof candidate.revision === 'string' ? candidate.revision.trim() : '';
    if (!runId || !artifactId || !Number.isInteger(version) || version < 1) return undefined;
    return { runId, artifactId, version, ...(revision ? { revision } : {}) };
  } catch {
    return undefined;
  }
};

const parseTargetSummary = (value?: string): ProjectGitTargetSummary | undefined => {
  if (!value) return undefined;
  try {
    const candidate = JSON.parse(value) as Record<string, unknown>;
    const numeric = (key: string): number =>
      typeof candidate[key] === 'number' && Number.isFinite(candidate[key]) ? Math.max(0, candidate[key] as number) : 0;
    const leadingCoverage =
      typeof candidate.leadingCoverage === 'number' && Number.isFinite(candidate.leadingCoverage)
        ? Math.max(0, Math.min(1, candidate.leadingCoverage))
        : undefined;
    return {
      candidateCount: numeric('candidateCount'),
      advanceCount: numeric('advanceCount'),
      validationCount: numeric('validationCount'),
      blockerCount: numeric('blockerCount'),
      sourceReadyCount: numeric('sourceReadyCount'),
      sourceCount: numeric('sourceCount'),
      branchCount: numeric('branchCount'),
      ...(leadingCoverage == null ? {} : { leadingCoverage }),
      topTargets: Array.isArray(candidate.topTargets)
        ? candidate.topTargets
            .filter((item): item is string => typeof item === 'string' && Boolean(item.trim()))
            .map((item) => item.trim().slice(0, 32))
            .slice(0, 3)
        : [],
    };
  } catch {
    return undefined;
  }
};

const parseResearchStageReceipt = (value?: string): ProjectGitResearchStageReceipt | undefined => {
  if (!value) return undefined;
  try {
    const candidate = JSON.parse(value) as Record<string, unknown>;
    const stringValue = (key: string, maxLength: number): string | undefined => {
      const item = typeof candidate[key] === 'string' ? candidate[key].trim() : '';
      return item ? item.slice(0, maxLength) : undefined;
    };
    const stringList = (key: string, maxItems = 36): string[] | undefined => {
      if (!Array.isArray(candidate[key])) return undefined;
      const values = (candidate[key] as unknown[])
        .filter((item): item is string => typeof item === 'string' && Boolean(item.trim()))
        .map((item) => item.trim().slice(0, 160))
        .slice(0, maxItems);
      return values.length === (candidate[key] as unknown[]).length ? values : undefined;
    };
    const stageId = stringValue('stageId', 120);
    const objective = stringValue('objective', 500);
    const successCriteria = stringList('successCriteria', 20);
    const failureCriteria = stringList('failureCriteria', 20);
    const priorWorkRefs = stringList('priorWorkRefs');
    const supportingEvidenceIds = stringList('supportingEvidenceIds');
    const refutingEvidenceIds = stringList('refutingEvidenceIds');
    const exhaustionEvidenceIds = candidate.exhaustionEvidenceIds == null ? [] : stringList('exhaustionEvidenceIds');
    const beliefDelta = stringValue('beliefDelta', 500);
    const reflection = stringValue('reflection', 800);
    const nextObjective = stringValue('nextObjective', 500);
    const disposition = candidate.disposition;
    if (
      !stageId ||
      !objective ||
      !successCriteria?.length ||
      !failureCriteria?.length ||
      !priorWorkRefs ||
      !supportingEvidenceIds ||
      !refutingEvidenceIds ||
      !exhaustionEvidenceIds ||
      !beliefDelta ||
      !reflection ||
      !['supported', 'refuted', 'exhausted', 'inconclusive', 'runtime_failed'].includes(String(disposition))
    ) {
      return undefined;
    }
    if (disposition === 'supported' && !supportingEvidenceIds.length) return undefined;
    if (disposition === 'refuted' && !refutingEvidenceIds.length) return undefined;
    if (disposition === 'exhausted' && !exhaustionEvidenceIds.length) return undefined;
    return {
      stageId,
      objective,
      successCriteria,
      failureCriteria,
      priorWorkRefs,
      disposition: disposition as ProjectGitResearchStageReceipt['disposition'],
      supportingEvidenceIds,
      refutingEvidenceIds,
      ...(exhaustionEvidenceIds.length ? { exhaustionEvidenceIds } : {}),
      beliefDelta,
      reflection,
      ...(nextObjective ? { nextObjective } : {}),
    };
  } catch {
    return undefined;
  }
};

export const parseCheckpointMetadata = (value: string): ProjectGitCommitSummary['checkpoint'] | undefined => {
  const trailers = new Map<string, string[]>();
  String(value || '')
    .split(/\r?\n/u)
    .forEach((line) => {
      const match = /^DeepScientist-([A-Za-z]+):\s*(.+)$/u.exec(line.trim());
      if (!match) return;
      const key = match[1].toLowerCase();
      trailers.set(key, [...(trailers.get(key) || []), match[2].trim()]);
    });
  if (trailers.get('checkpoint')?.[0]?.toLowerCase() !== 'true') return undefined;
  const metrics = (trailers.get('metric') || [])
    .map(parsePerformanceMetric)
    .filter((metric): metric is ProjectGitPerformanceMetric => Boolean(metric));
  const rawDomain = trailers.get('domain')?.[0];
  const domain =
    rawDomain && PROJECT_GIT_DOMAINS.has(rawDomain as ProjectGitDomain) ? (rawDomain as ProjectGitDomain) : undefined;
  const artifactRef = parseArtifactRef(trailers.get('artifact')?.[0]);
  const targetSummary = parseTargetSummary(trailers.get('targetsummary')?.[0]);
  const metricContext = parseMetricContext(trailers.get('metriccontext')?.[0]);
  const goalId = trailers.get('goal')?.[0]?.trim();
  const researchStage = parseResearchStageReceipt(trailers.get('researchstage')?.[0]);
  const directionDecision = (() => {
    const serialized = trailers.get('decision')?.[0];
    if (!serialized) return undefined;
    try {
      return normalizeProjectGitDirectionDecision(JSON.parse(serialized));
    } catch {
      return undefined;
    }
  })();
  const researchStrategy = normalizeResearchStrategy(trailers.get('strategy')?.[0]);
  const routeNodeId = trailers.get('routenode')?.[0]?.trim();
  const repairsNodeId = trailers.get('repairsnode')?.[0]?.trim();
  return {
    stage: trailers.get('stage')?.[0] || 'checkpoint',
    ...(researchStrategy ? { researchStrategy } : {}),
    ...(routeNodeId ? { routeNodeId: routeNodeId.slice(0, 120) } : {}),
    ...(repairsNodeId ? { repairsNodeId: repairsNodeId.slice(0, 120) } : {}),
    runId: trailers.get('run')?.[0],
    conversationId: trailers.get('conversation')?.[0],
    ...(domain ? { domain } : {}),
    ...(artifactRef ? { artifactRef } : {}),
    ...(targetSummary ? { targetSummary } : {}),
    ...(metricContext ? { metricContext } : {}),
    ...(goalId ? { goalId } : {}),
    ...(researchStage ? { researchStage } : {}),
    ...(directionDecision ? { directionDecision } : {}),
    verification: trailers.get('verification') || [],
    ...(metrics.length ? { metrics } : {}),
  };
};

export const mapGitStatus = (value: string): ProjectGitFileStatus => {
  const code = value.trim().charAt(0).toUpperCase();
  if (code === 'A' || code === '?') return 'added';
  if (code === 'M') return 'modified';
  if (code === 'D') return 'deleted';
  if (code === 'R') return 'renamed';
  if (code === 'C') return 'copied';
  if (code === 'U') return 'unmerged';
  return 'unknown';
};

export const parseGitLog = (value: string): ProjectGitCommitSummary[] =>
  value
    .split(RECORD_SEPARATOR)
    .map((record) => record.trim())
    .filter(Boolean)
    .map((record) => {
      const [sha, shortSha, parents, subject, body, authorName, authorEmail, authoredAt, decorations] =
        record.split(FIELD_SEPARATOR);
      const checkpoint = parseCheckpointMetadata(String(body || ''));
      const parsedSubject = parseResearchCommitSubject(String(subject || ''));
      const bodyPreview =
        String(body || '')
          .split(/\r?\n/u)
          .filter((line) => !/^DeepScientist-[A-Za-z]+:/u.test(line.trim()))
          .join(' ')
          .replace(/\s+/gu, ' ')
          .trim()
          .slice(0, 240) || undefined;
      return Object.assign(
        {
          sha: String(sha || '').trim(),
          shortSha: String(shortSha || '').trim(),
          parents: String(parents || '')
            .split(/\s+/u)
            .filter(Boolean),
          subject: String(subject || '').trim(),
          bodyPreview,
          authorName: String(authorName || '').trim() || undefined,
          authorEmail: String(authorEmail || '').trim() || undefined,
          authoredAt: String(authoredAt || '').trim() || undefined,
          refs: String(decorations || '')
            .split(',')
            .map((item) => item.trim())
            .filter(Boolean),
          changedFileCount: 0,
          additions: 0,
          deletions: 0,
          checkpoint,
        },
        checkpoint?.researchStrategy || parsedSubject.researchStrategy
          ? { researchStrategy: checkpoint?.researchStrategy || parsedSubject.researchStrategy }
          : {}
      );
    })
    .filter((commit) => /^[a-f0-9]{40}$/u.test(commit.sha));

export const parseNumstat = (
  value: string
): Map<string, { additions?: number; deletions?: number; binary: boolean }> => {
  const result = new Map<string, { additions?: number; deletions?: number; binary: boolean }>();
  value.split(/\r?\n/u).forEach((line) => {
    if (!line) return;
    const [added, deleted, ...pathParts] = line.split('\t');
    const rawPath = pathParts.join('\t').trim();
    const path =
      rawPath.includes('{') && rawPath.includes(' => ')
        ? rawPath.replace(/\{[^{}]* => ([^{}]*)\}/gu, '$1')
        : rawPath.includes(' => ')
          ? rawPath.split(' => ').at(-1)?.trim() || rawPath
          : rawPath;
    if (!path) return;
    const binary = added === '-' || deleted === '-';
    result.set(path, {
      additions: binary ? undefined : Number.parseInt(added, 10) || 0,
      deletions: binary ? undefined : Number.parseInt(deleted, 10) || 0,
      binary,
    });
  });
  return result;
};

export const parseNameStatus = (value: string, numstat?: ReturnType<typeof parseNumstat>): ProjectGitChangedFile[] => {
  const files: ProjectGitChangedFile[] = [];
  value.split(/\r?\n/u).forEach((line) => {
    if (!line) return;
    const [rawStatus, ...rawPaths] = line.split('\t');
    const status = mapGitStatus(rawStatus);
    const renamed = status === 'renamed' || status === 'copied';
    const oldPath = renamed ? rawPaths[0]?.trim() : undefined;
    const filePath = (renamed ? rawPaths[1] : rawPaths[0])?.trim();
    if (!filePath) return;
    const stats = numstat?.get(filePath) || (oldPath ? numstat?.get(oldPath) : undefined);
    files.push({
      path: filePath,
      oldPath,
      status,
      additions: stats?.additions,
      deletions: stats?.deletions,
      binary: stats?.binary === true,
    });
  });
  return files;
};

export const summarizeNumstat = (
  value: string
): Pick<ProjectGitCommitSummary, 'changedFileCount' | 'additions' | 'deletions'> => {
  let changedFileCount = 0;
  let additions = 0;
  let deletions = 0;
  value.split(/\r?\n/u).forEach((line) => {
    if (!line) return;
    const [added, deleted, ...pathParts] = line.split('\t');
    if (!pathParts.length) return;
    changedFileCount += 1;
    if (added !== '-') additions += Number.parseInt(added, 10) || 0;
    if (deleted !== '-') deletions += Number.parseInt(deleted, 10) || 0;
  });
  return { changedFileCount, additions, deletions };
};

export const parseLogNumstats = (
  value: string
): Map<string, Pick<ProjectGitCommitSummary, 'changedFileCount' | 'additions' | 'deletions'>> => {
  const result = new Map<string, Pick<ProjectGitCommitSummary, 'changedFileCount' | 'additions' | 'deletions'>>();
  value.split(RECORD_SEPARATOR).forEach((record) => {
    const [rawSha, ...lines] = record.replace(/^\s+/u, '').split(/\r?\n/u);
    const sha = rawSha.trim();
    if (!/^[a-f0-9]{40}$/u.test(sha)) return;
    result.set(sha, summarizeNumstat(lines.join('\n')));
  });
  return result;
};

export const parsePorcelainStatus = (value: string): ProjectGitChangedFile[] =>
  value
    .split(/\r?\n/u)
    .filter(Boolean)
    .map((line) => {
      const code = line.slice(0, 2);
      const rawPath = line.slice(3).trim();
      const renameParts = rawPath.split(' -> ');
      const path = renameParts.at(-1) || rawPath;
      return {
        path,
        oldPath: renameParts.length > 1 ? renameParts[0] : undefined,
        status: mapGitStatus(code.includes('?') ? '?' : code.replace(/\s/gu, '')),
        binary: false,
      };
    });
