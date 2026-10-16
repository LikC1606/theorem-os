import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import { z } from 'zod';
import type { ArchiveCatalog, ArchiveRecord, ArchiveSource } from './types';

const identifier = z.string().regex(/^[a-z0-9_]+$/);
const digest = z.string().regex(/^[a-f0-9]{64}$/);
const commit = z.string().regex(/^[a-f0-9]{40}$/);
const date = z.string().datetime({ offset: true });
const httpsUrl = z.string().url().refine(value => new URL(value).protocol === 'https:');
const acceptedSchema = z.array(z.object({
  problem_id: identifier,
  directory: identifier,
  statement_revision: z.number().int().positive(),
  model: z.string().min(1),
  status: z.literal('official_accepted'),
  submission_url: httpsUrl,
  result_url: httpsUrl,
  result_reported_at: date,
  result_body: z.string(),
  original_source_url: httpsUrl,
  original_source_commit: commit,
  source_sha256: z.record(digest),
}));
const snapshotSchema = z.object({
  schema: z.literal('lean-eval.in-progress-snapshot.v1'),
  status: z.literal('in_progress_not_officially_accepted'),
  captureFinishedAt: date,
  problems: z.array(z.object({
    problemId: identifier,
    directory: identifier,
    runId: z.string().uuid(),
    phase: z.string(),
    turns: z.number().int().nonnegative(),
    workers: z.number().int().positive(),
  })),
});
const manifestSchema = z.object({
  problemId: identifier,
  runId: z.string().uuid(),
  status: z.literal('in_progress_not_officially_accepted'),
  capturedAt: date,
  model: z.string().min(1),
  projectRelative: z.string().regex(/^generated\/[a-z0-9_]+$/),
  taskStatuses: z.record(z.number().int().nonnegative()),
  files: z.array(z.object({ file: z.string(), sha256: digest })),
});
const legacyLocalSchema = z.object({
  problem_id: identifier,
  source_proof_commit: commit.optional(),
  source_sha256: z.record(digest).default({}),
  local_evaluation: z.object({
    status: z.string(),
    kernel_verified: z.boolean(),
    official_comparator: z.string().optional(),
    kernel_receipt: z.string().optional(),
    axioms: z.array(z.string()).default([]),
  }),
  production: z.object({
    mode: z.string(),
    human_direction: z.string().optional(),
    fresh_from_zero: z.boolean().optional(),
  }).optional(),
});
const publishedFilesSchema = z.record(z.object({ sha256: digest, bytes: z.number().int().nonnegative() }));
const publishedEvidenceSchema = z.object({
  schema: z.literal('theorem-os.leaneval.submission-evidence.v1'),
  problem_id: identifier,
  candidate_commit: commit,
  files: publishedFilesSchema,
  kernel_acceptance: z.array(z.string()),
  local_official_comparator: z.object({ status: z.string(), exitCode: z.number().int() }),
}).transform(evidence => ({
  problem_id: evidence.problem_id,
  source_proof_commit: evidence.candidate_commit,
  source_sha256: Object.fromEntries(Object.entries(evidence.files).map(([file, value]) => [file, value.sha256])),
  local_evaluation: {
    status: evidence.local_official_comparator.status,
    kernel_verified: evidence.local_official_comparator.status === 'official_verified' &&
      evidence.local_official_comparator.exitCode === 0 && evidence.kernel_acceptance.includes('nanoda') &&
      evidence.kernel_acceptance.includes('Lean default kernel'),
    official_comparator: evidence.local_official_comparator.status,
    axioms: [],
  },
}));
const submissionProvenanceSchema = z.object({
  schema: z.literal('theoremos.lean-eval-submission-provenance.v1'),
  problem: z.object({
    problemId: identifier,
    solverCommit: commit,
    files: publishedFilesSchema,
    localOfficialReceipt: z.object({
      problemId: identifier, proofHash: digest, receiptId: z.string().min(1),
      status: z.string(), verifier: z.string(), exitCode: z.number().int(), timedOut: z.boolean(),
    }),
  }).refine(problem => problem.localOfficialReceipt.problemId === problem.problemId &&
    problem.localOfficialReceipt.proofHash === problem.files['Submission.lean']?.sha256,
  'Local receipt does not match the published problem and proof'),
}).transform(({ problem }) => ({
  problem_id: problem.problemId,
  source_proof_commit: problem.solverCommit,
  source_sha256: Object.fromEntries(Object.entries(problem.files).map(([file, value]) => [file, value.sha256])),
  local_evaluation: {
    status: problem.localOfficialReceipt.status,
    kernel_verified: problem.localOfficialReceipt.status === 'official_verified' &&
      problem.localOfficialReceipt.verifier === 'official-comparator' &&
      problem.localOfficialReceipt.exitCode === 0 && !problem.localOfficialReceipt.timedOut,
    official_comparator: problem.localOfficialReceipt.status,
    kernel_receipt: problem.localOfficialReceipt.receiptId,
    axioms: [],
  },
}));
// Normalize published evidence for display; retain every original evidence file unchanged.
const localSchema = z.union([legacyLocalSchema, publishedEvidenceSchema, submissionProvenanceSchema])
  .pipe(legacyLocalSchema);

const descriptions: Record<string, Pick<ArchiveRecord, 'title' | 'subtitle' | 'area' | 'summary' | 'declaration'>> = {
  annals_equiangular_lines_fixed_angle: {
    title: 'Equiangular lines', subtitle: '固定夹角等角线', area: '离散几何',
    summary: '关于固定夹角下等角线数量与谱半径阶的渐近关系。档案保留原始提交包及其官方验收结果。',
    declaration: 'theorem theorem_1_2',
  },
  annals_rademacher_enflo_type: {
    title: 'Rademacher & Enflo type', subtitle: 'Rademacher 型与 Enflo 型的一致性', area: '泛函分析',
    summary: '在 1 ≤ p ≤ 2 时，比较 Banach 空间的 Rademacher 型与 Enflo 型常数，同时证明两侧常数界。对应原题 theorem_1_1。',
    declaration: 'theorem theorem_1_1',
  },
  annals_unit_conjecture: {
    title: 'Unit conjecture', subtitle: '群环单位猜想', area: '代数',
    summary: '构造无挠群中的群环非平凡单位，对应原题 theorem_A。原始结果归属于 DeepScientist + GPT-5.6。',
    declaration: 'theorem theorem_A',
  },
  annals_fractional_expectation_thresholds: {
    title: 'Fractional expectation thresholds', subtitle: '分数期望阈值', area: '概率组合',
    summary: '证明上闭集合族的分数期望阈值界，包括通用常数 K 和原题 theorem_1_1。档案保留完整提交包及官方验收记录。',
    declaration: 'theorem theorem_1_1',
  },
  dimitrov: {
    title: 'Dimitrov', subtitle: '代数整数的 house 下界', area: '数论',
    summary: '证明非零且非单位根代数整数的 house 下界。档案保留最终提交包及官方验收记录。',
    declaration: 'theorem dimitrov',
  },
  hopf_rinow: {
    title: 'Hopf–Rinow', subtitle: '测地完备与度量完备', area: '微分几何',
    summary: '在原题的黎曼流形条件下，证明测地完备与度量完备的等价性。档案保留最终提交包及官方验收记录。',
    declaration: 'theorem hopf_rinow',
  },
  szemeredi: {
    title: 'Szemerédi', subtitle: '正上密度集合中的等差数列', area: '组合数学',
    summary: '正上密度的自然数集合包含任意长等差数列。当前档案记录研究过程，尚未获得官方验收。',
    declaration: 'theorem szemeredi',
  },
};

function description(id: string) {
  return descriptions[id] ?? {
    title: id.replaceAll('_', ' '), subtitle: id, area: '数学', summary: 'Lean-Eval 证明档案。',
  };
}

function readJson(root: string, relative: string): unknown {
  return JSON.parse(fs.readFileSync(path.join(root, relative), 'utf8'));
}

function checkedFile(root: string, relative: string, expected: string): Buffer {
  const location = path.resolve(root, relative);
  if (!location.startsWith(path.resolve(root) + path.sep)) throw new Error(`Invalid archive path: ${relative}`);
  const bytes = fs.readFileSync(location);
  if (crypto.createHash('sha256').update(bytes).digest('hex') !== expected) {
    throw new Error(`Archive checksum mismatch: ${relative}`);
  }
  return bytes;
}

export function buildSiteCatalog(root: string, archiveRevision: string): ArchiveCatalog {
  commit.parse(archiveRevision);
  const repository = 'https://github.com/LikC1606/theorem-os';
  const sourceUrl = (relative: string) => `${repository}/blob/${archiveRevision}/${relative}`;
  const source = (relative: string, name: string, expected: string): ArchiveSource => {
    const code = checkedFile(root, relative, expected).toString('utf8');
    return { name, path: relative, url: sourceUrl(relative), sha256: expected,
      lines: code.split('\n').length - Number(code.endsWith('\n')), code };
  };
  const accepted = acceptedSchema.parse(readJson(root, 'accepted/accepted.json'));
  const snapshot = snapshotSchema.parse(readJson(root, 'in-progress/snapshot.json'));
  const records: ArchiveRecord[] = accepted.map(entry => {
    if (entry.directory !== entry.problem_id) throw new Error(`Archive identity mismatch: ${entry.problem_id}`);
    const base = `accepted/${entry.directory}`;
    for (const [file, expected] of Object.entries(entry.source_sha256)) checkedFile(root, `${base}/${file}`, expected);
    const sources = Object.entries(entry.source_sha256)
      .filter(([file]) => file.endsWith('.lean'))
      .map(([file, expected]) => source(`${base}/${file}`, file, expected));
    if (!sources.some(file => file.name === 'Submission.lean')) throw new Error(`Missing proof source: ${entry.problem_id}`);
    const record: ArchiveRecord = {
      id: entry.problem_id, ...description(entry.problem_id), status: entry.status, model: entry.model,
      updatedAt: entry.result_reported_at, archiveUrl: `${repository}/tree/${archiveRevision}/${base}`, sources,
      official: {
        statementRevision: entry.statement_revision, submissionUrl: entry.submission_url,
        resultUrl: entry.result_url, resultBody: entry.result_body,
        sourceUrl: entry.original_source_url, sourceCommit: entry.original_source_commit,
        checksums: entry.source_sha256,
      },
    };
    if (entry.source_sha256['verification.json']) {
      const local = localSchema.parse(readJson(root, `${base}/verification.json`));
      if (local.problem_id !== entry.problem_id) throw new Error(`Evaluation identity mismatch: ${entry.problem_id}`);
      record.local = {
        status: local.local_evaluation.status, kernelVerified: local.local_evaluation.kernel_verified,
        comparator: local.local_evaluation.official_comparator, receipt: local.local_evaluation.kernel_receipt,
        sourceProofCommit: local.source_proof_commit,
        sourceBinding: !Object.keys(local.source_sha256).length ? 'unrecorded' :
          Object.entries(local.source_sha256).every(([file, hash]) => entry.source_sha256[file] === hash) ? 'matches' : 'differs',
        axioms: local.local_evaluation.axioms, url: sourceUrl(`${base}/verification.json`),
        production: local.production ? {
          mode: local.production.mode, humanDirection: local.production.human_direction,
          freshFromZero: local.production.fresh_from_zero,
        } : undefined,
      };
    }
    return record;
  });
  const acceptedIds = new Set(accepted.map(entry => entry.problem_id));
  for (const entry of snapshot.problems) {
    // Historical snapshots remain intact after their final proofs receive acceptance.
    if (acceptedIds.has(entry.problemId)) continue;
    const base = `in-progress/${entry.directory}`;
    const manifest = manifestSchema.parse(readJson(root, `${base}/manifest.json`));
    if (entry.problemId !== entry.directory || manifest.problemId !== entry.problemId || manifest.runId !== entry.runId) {
      throw new Error(`Snapshot identity mismatch: ${entry.problemId}`);
    }
    const project = `workers/solver/${manifest.projectRelative}`;
    const selected = ['Submission.lean', 'Challenge.lean', 'Submission/Helpers.lean'];
    const sources = selected.flatMap(name => {
      const file = manifest.files.find(item => item.file === `${project}/${name}`);
      return file ? [source(`${base}/${file.file}`, name, file.sha256)] : [];
    });
    if (!sources.length) throw new Error(`Missing snapshot source: ${entry.problemId}`);
    records.push({
      id: entry.problemId, ...description(entry.problemId), status: snapshot.status, model: manifest.model,
      updatedAt: manifest.capturedAt, archiveUrl: `${repository}/tree/${archiveRevision}/${base}`, sources,
      snapshot: {
        runId: entry.runId, phase: entry.phase, turns: entry.turns, workers: entry.workers,
        taskStatuses: manifest.taskStatuses,
      },
    });
  }
  if (new Set(records.map(record => record.id)).size !== records.length) throw new Error('Duplicate archive problem');
  return {
    schema: 'theoremos.public-archive.v1', repository, archiveRevision,
    snapshotAt: snapshot.captureFinishedAt, records: records.sort((a, b) => b.updatedAt.localeCompare(a.updatedAt)),
  };
}
