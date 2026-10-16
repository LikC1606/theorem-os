import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import { spawnSync } from 'node:child_process';
import { gunzipSync } from 'node:zlib';
import { z } from 'zod';
import { canonicalMathJson, mathDigest, writeMathJsonDurable } from '../math/mathRuntimeIo';
import { projectMathematicsRuntimeEnvironment } from '../math/mathRuntimeEnvironment';
import { bindLeanPackages } from '../math/leanDiagnostics';
import { resolveMathematicsLakePackagesCache } from '../math/verifier';
import { readSolverRunState, writeSolverRunState, type SolverRunState } from './archive';
import { assertSolverSources, git, type SolverProblem } from './problem';
import { checkTaskProofs, projectTaskSources, type TaskProof, type TaskProofRequest } from './cooperativeProof';
import { taskVersion, type TaskRecord } from './tasks';

const oid = /^[a-f0-9]{40,64}$/u;
const hash = z.string().regex(/^[a-f0-9]{64}$/u);
const manifestSchema = z.object({
  schema: z.literal('lean-eval.problem-snapshot.v1'), problemId: z.string(), runId: z.string(),
  projectRelative: z.string(), originalBaseCommit: z.string().regex(oid),
  workers: z.array(z.object({ id: z.string().regex(/^[a-zA-Z0-9_-]{1,64}$/u), sourceHeadAfter: z.string().regex(oid) })),
  files: z.array(z.object({ file: z.string(), bytes: z.number().int().nonnegative(), sha256: hash })),
});

const relative = (value: string) => Boolean(value && !value.includes('\\') && !value.includes('\0') &&
  !path.posix.isAbsolute(value) && value.split('/').every(part => part && part !== '.' && part !== '..'));
const protectedPath = (value: string) => value.split('/').some(part => part === 'Solution.lean' || part === '.git');
const newCanonicalPath = (value: string) => {
  let existing = path.resolve(value);
  const suffix: string[] = [];
  while (!fs.lstatSync(existing, { throwIfNoEntry: false })) { suffix.unshift(path.basename(existing)); existing = path.dirname(existing); }
  return path.join(fs.realpathSync(existing), ...suffix);
};

function snapshotFiles(snapshot: string) {
  const root = fs.realpathSync(snapshot);
  const manifest = manifestSchema.parse(JSON.parse(fs.readFileSync(path.join(root, 'manifest.json'), 'utf8')));
  const files = new Map<string, Buffer>();
  for (const file of manifest.files) {
    if (!relative(file.file) || protectedPath(file.file) || files.has(file.file)) throw new Error('math_recovery_invalid_snapshot_path');
    const target = path.join(root, file.file);
    if (fs.realpathSync(target) !== target || !fs.lstatSync(target).isFile()) throw new Error('math_recovery_snapshot_symlink');
    const bytes = fs.readFileSync(target);
    if (bytes.length !== file.bytes || mathDigest(bytes) !== file.sha256) throw new Error(`math_recovery_snapshot_changed:${file.file}`);
    files.set(file.file, bytes);
  }
  if (!files.has('state.json') || !files.has('history.fast-export.gz')) throw new Error('math_recovery_snapshot_incomplete');
  const state = readSolverRunState(path.join(root, 'state.json'));
  if (state.runId !== manifest.runId || state.problem.projectRelative !== manifest.projectRelative ||
      state.problem.contract.problemId !== manifest.problemId || state.problem.baseCommit !== manifest.originalBaseCommit ||
      !relative(state.problem.projectRelative)) throw new Error('math_recovery_snapshot_identity_changed');
  const sourceFiles = [...state.problem.ownedFiles, ...Object.keys(state.problem.trustedFiles)];
  if (sourceFiles.some(file => !relative(file) || protectedPath(file))) throw new Error('math_recovery_invalid_source_path');
  return { root, manifest, files, state };
}

/** Skip byte-counted data: prose in RESEARCH.md is never parsed as Git commands. */
function exportCommits(bytes: Buffer, allowed: ReadonlySet<string>) {
  const commits = new Map<string, string>();
  let offset = 0, commit = false, mark: string | undefined;
  while (offset < bytes.length) {
    const end = bytes.indexOf(10, offset);
    if (end < 0) throw new Error('math_recovery_invalid_export');
    const line = bytes.toString('utf8', offset, end); offset = end + 1;
    if (line.startsWith('data ')) {
      if (!/^data [0-9]+$/u.test(line)) throw new Error('math_recovery_invalid_export');
      offset += Number(line.slice(5));
      if (offset > bytes.length) throw new Error('math_recovery_invalid_export');
      continue;
    }
    if (line === 'blob' || line.startsWith('reset ') || line.startsWith('commit ')) {
      commit = line.startsWith('commit '); mark = undefined;
    } else if (/^mark :[0-9]+$/u.test(line)) mark = line.slice(5);
    else if (line.startsWith('original-oid ')) {
      const original = line.slice(13);
      if (!oid.test(original)) throw new Error('math_recovery_invalid_export');
      if (commit && mark) commits.set(original, mark);
    } else if (line.startsWith('M ') || line.startsWith('D ')) {
      const match = /^(?:M (?:100644|100755) :[0-9]+ |D )(.+)$/u.exec(line);
      if (!match || !allowed.has(match[1]!)) throw new Error('math_recovery_export_outside_ownership');
    } else if (line && line !== 'done' && line !== 'deleteall' &&
        !/^(?:author |committer |encoding |from :[0-9]+$|merge :[0-9]+$)/u.test(line))
      throw new Error('math_recovery_invalid_export');
  }
  if (!commits.size) throw new Error('math_recovery_empty_export');
  return commits;
}

function gitInput(root: string, args: string[], input?: Buffer | string) {
  const result = spawnSync('git', ['-C', root, ...args], { input, timeout: 120_000, maxBuffer: 8 * 1024 * 1024 });
  if (result.error || result.status !== 0) throw new Error(`math_recovery_git_failed:${args[0]}`);
  return result.stdout;
}
const gitFile = (root: string, commit: string, file: string) => gitInput(root, ['show', `${commit}:${file}`]);
const tryGitFile = (root: string, commit: string, file: string) => {
  try { return gitFile(root, commit, file); } catch { return undefined; }
};

export type SnapshotRecovery = {
  schema: 'theorem-os.snapshot-recovery.v1'; runId: string; originalRunId: string; snapshot: string;
  manifestDigest: string; stateFile: string; workspace: string; history: string;
  originalToImported: Record<string, string>; originalToMaterialized: Record<string, string>;
  missingCommitReferences: { commit: string; fields: string[] }[];
  candidates: string[]; workerCommits: Record<string, string>; workerSourceErrors: Record<string, string>; canonicalCommit: string;
  verification: 'not-run' | 'checking' | 'finished' | 'interrupted';
  evidence: 'recovered-sources-require-recheck' | 'fresh-helper-receipts';
  resumable: false;
};

/** Rebuild sources in a new repository; original receipts remain in the hashed snapshot. */
export function recoverMathSnapshot(options: { snapshot: string; output: string; sourceRepository?: string }): SnapshotRecovery {
  const { root, manifest, files, state: archived } = snapshotFiles(options.snapshot);
  const output = newCanonicalPath(options.output);
  if (fs.existsSync(output)) throw new Error('math_recovery_output_exists');
  if (output === root || output.startsWith(root + path.sep)) throw new Error('math_recovery_output_inside_snapshot');
  const allowed = new Set(['RESEARCH.md', ...[...archived.problem.ownedFiles, ...Object.keys(archived.problem.trustedFiles)]
    .map(file => `${manifest.projectRelative}/${file}`)]);
  const stream = gunzipSync(files.get('history.fast-export.gz')!, { maxOutputLength: 256 * 1024 * 1024 });
  const originalMarks = exportCommits(stream, allowed);
  fs.mkdirSync(output, { recursive: true, mode: 0o700 });
  const history = path.join(output, 'history'); fs.mkdirSync(history);
  git(history, ['init', '--quiet', '--bare']);
  const marksFile = path.join(output, 'imported-marks');
  gitInput(history, ['fast-import', '--quiet', '--force', `--export-marks=${marksFile}`], stream);
  const importedMarks = new Map(fs.readFileSync(marksFile, 'utf8').trim().split('\n').map(line => line.split(' ') as [string, string]));
  const originalToImported = Object.fromEntries([...originalMarks].map(([original, mark]) => [original, importedMarks.get(mark)!]));
  const importedBase = originalToImported[archived.problem.baseCommit];
  if (!importedBase) throw new Error('math_recovery_base_missing');
  const originalCanonical = archived.cooperation?.canonicalCommit;
  const importedCanonical = originalCanonical && originalToImported[originalCanonical];
  if (!importedCanonical) throw new Error('math_recovery_canonical_missing');
  const workspace = path.join(output, 'workspace'); fs.mkdirSync(workspace);
  git(workspace, ['init', '--quiet']);
  const project = path.join(workspace, manifest.projectRelative); fs.mkdirSync(project, { recursive: true });
  const writeSource = (file: string, bytes: Buffer) => {
    const target = path.join(project, file); fs.mkdirSync(path.dirname(target), { recursive: true }); fs.writeFileSync(target, bytes);
  };
  const officialCommit = archived.problem.contract.officialManifestId?.split(':').at(-1);
  for (const [file, expected] of Object.entries(archived.problem.trustedFiles)) {
    let bytes = tryGitFile(history, importedBase, `${manifest.projectRelative}/${file}`) ??
      files.get(`workers/solver/${manifest.projectRelative}/${file}`);
    if ((!bytes || mathDigest(bytes) !== expected) && options.sourceRepository && officialCommit && oid.test(officialCommit))
      bytes = tryGitFile(options.sourceRepository, officialCommit, `${manifest.projectRelative}/${file}`);
    if (!bytes || mathDigest(bytes) !== expected) throw new Error(`math_recovery_trusted_file_missing:${file}`);
    writeSource(file, bytes);
  }
  // The historical bootstrap can predate the required target stub. The canonical
  // source has the frozen declarations and must still pass all current policies.
  for (const file of archived.problem.ownedFiles) writeSource(file, gitFile(history, importedCanonical, `${manifest.projectRelative}/${file}`));
  const canonicalNotes = tryGitFile(history, importedCanonical, 'RESEARCH.md');
  if (canonicalNotes) fs.writeFileSync(path.join(workspace, 'RESEARCH.md'), canonicalNotes);
  git(workspace, ['add', '--', '.']);
  git(workspace, ['-c', 'user.name=TheoremOS Recovery', '-c', 'user.email=recovery@localhost',
    'commit', '--quiet', '--no-gpg-sign', '-m', 'Recover frozen problem sources']);
  const baseCommit = git(workspace, ['rev-parse', 'HEAD']);
  const problem: SolverProblem = { ...archived.problem, workspace, baseCommit,
    activeProblemPath: path.join(root, 'state.json'), sourceRepository: options.sourceRepository };
  assertSolverSources(problem, workspace);
  const originalToMaterialized: Record<string, string> = { [originalCanonical!]: baseCommit };
  const checkpoint = (checkout: string) => {
    const sources = problem.ownedFiles.map(file => `${problem.projectRelative}/${file}`);
    if (fs.existsSync(path.join(checkout, 'RESEARCH.md'))) sources.push('RESEARCH.md');
    git(checkout, ['add', '--', ...sources]);
    if (git(checkout, ['diff', '--cached', '--name-only'])) git(checkout, ['-c', 'user.name=TheoremOS Recovery',
      '-c', 'user.email=recovery@localhost', 'commit', '--quiet', '--no-gpg-sign', '-m', 'Recover worker proof sources']);
    return git(checkout, ['rev-parse', 'HEAD']);
  };
  const materialize = (original: string) => {
    if (originalToMaterialized[original]) return originalToMaterialized[original]!;
    const imported = originalToImported[original];
    if (!imported) throw new Error(`math_recovery_source_commit_missing:${original}`);
    git(workspace, ['reset', '--quiet', '--hard', baseCommit]);
    for (const file of problem.ownedFiles) writeSource(file, gitFile(history, imported, `${problem.projectRelative}/${file}`));
    const notes = tryGitFile(history, imported, 'RESEARCH.md');
    if (notes) fs.writeFileSync(path.join(workspace, 'RESEARCH.md'), notes);
    const commit = checkpoint(workspace);
    git(workspace, ['update-ref', `refs/recovery/original/${original}`, commit]);
    originalToMaterialized[original] = commit;
    return commit;
  };
  const references = new Map<string, string[]>();
  const collect = (value: unknown, field: string) => {
    if (!value || typeof value !== 'object') return;
    for (const [key, child] of Object.entries(value)) {
      const location = `${field}.${key}`;
      if (['commit', 'targetCommit', 'seedCommit', 'canonicalCommit'].includes(key) && typeof child === 'string' && oid.test(child)) {
        const fields = references.get(child) ?? []; fields.push(location); references.set(child, fields);
      } else if (typeof child === 'object') collect(child, location);
    }
  };
  collect(archived.cooperation?.tasks, 'tasks');
  const canonicalCommit = materialize(archived.cooperation!.canonicalCommit!);
  const workerCommits: Record<string, string> = {}, workerSourceErrors: Record<string, string> = {};
  const runId = crypto.randomUUID();
  for (const worker of manifest.workers) {
    const workerRoot = path.join(output, 'workers', worker.id);
    const head = materialize(worker.sourceHeadAfter);
    git(workspace, ['worktree', 'add', '--quiet', '--detach', workerRoot, head]);
    for (const [file, bytes] of files) if (file.startsWith(`workers/${worker.id}/`)) {
      const target = path.join(workerRoot, file.slice(`workers/${worker.id}/`.length));
      fs.mkdirSync(path.dirname(target), { recursive: true }); fs.writeFileSync(target, bytes);
    }
    workerCommits[worker.id] = checkpoint(workerRoot);
    try { assertSolverSources(problem, workerRoot); }
    catch (error) { workerSourceErrors[worker.id] = error instanceof Error ? error.message : 'math_recovery_worker_source_invalid'; }
    git(workspace, ['update-ref', `refs/math/${runId}/workers/${worker.id}`, workerCommits[worker.id]!]);
  }
  git(workspace, ['reset', '--quiet', '--hard', canonicalCommit]);
  assertSolverSources(problem, workspace);
  const tasks: TaskRecord[] = (archived.cooperation?.tasks ?? []).map(node => ({ task: node.task, attempts: 0,
    status: ['research', 'sketch'].includes(node.task.kind) && node.status === 'completed' ? 'completed' : 'pending', finding: node.finding }));
  const candidates = (archived.cooperation?.tasks ?? []).filter(node => node.proof?.passed || node.integratedCheck?.passed).map(node => node.task.id);
  const taskFile = [...files].find(([file, bytes]) => file.startsWith('task') && file.endsWith('.md') && mathDigest(bytes) === archived.taskDigest);
  if (!taskFile) throw new Error('math_recovery_task_missing');
  fs.writeFileSync(path.join(output, 'task.md'), taskFile[1]);
  const stateFile = path.join(output, 'state.json');
  const state: SolverRunState = { schema: 'deepscientist.math.solver.v1', runId, problem, worktree: workspace,
    taskDigest: archived.taskDigest, buildDigest: 'snapshot-recovery-not-an-execution-run', environmentDigest: '',
    evaluatorDigest: 'not-evaluated', model: 'none', effort: 'none', phase: 'prepared', turns: 0,
    cooperation: { ...archived.cooperation!, canonicalCommit, tasks, deliveries: [], history: [], statementReviews: [], review: undefined,
      edits: [], recheck: undefined, error: undefined } };
  writeSolverRunState(stateFile, state);
  const report: SnapshotRecovery = { schema: 'theorem-os.snapshot-recovery.v1', runId, originalRunId: archived.runId,
    snapshot: root, manifestDigest: mathDigest(fs.readFileSync(path.join(root, 'manifest.json'))), stateFile, workspace, history,
    originalToImported, originalToMaterialized, candidates, workerCommits, workerSourceErrors, canonicalCommit,
    missingCommitReferences: [...references].filter(([commit]) => !originalToImported[commit]).map(([commit, fields]) => ({ commit, fields })),
    verification: 'not-run', evidence: 'recovered-sources-require-recheck', resumable: false };
  writeMathJsonDurable(path.join(output, 'recovery.json'), report);
  return report;
}

/** Recheck formerly passed helpers, including tasks damaged by historical cancellation. No model sessions. */
export async function recheckMathSnapshot(output: string, options: { env: NodeJS.ProcessEnv; signal: AbortSignal; timeoutMs?: number;
  onProgress?: (taskIds: string[]) => void }) {
  const directory = fs.realpathSync(output), reportFile = path.join(directory, 'recovery.json');
  const report = JSON.parse(fs.readFileSync(reportFile, 'utf8')) as SnapshotRecovery;
  if (report.schema !== 'theorem-os.snapshot-recovery.v1' || report.stateFile !== path.join(directory, 'state.json') ||
      report.workspace !== path.join(directory, 'workspace')) throw new Error('math_recovery_identity_changed');
  const snapshot = snapshotFiles(report.snapshot);
  if (mathDigest(fs.readFileSync(path.join(snapshot.root, 'manifest.json'))) !== report.manifestDigest)
    throw new Error('math_recovery_snapshot_changed');
  const state = readSolverRunState(report.stateFile), worktree = report.workspace;
  if (state.runId !== report.runId || state.problem.workspace !== worktree) throw new Error('math_recovery_identity_changed');
  const frozen = (problem: SolverProblem) => {
    const { workspace: _workspace, baseCommit: _base, activeProblemPath: _active, sourceRepository: _source, ...identity } = problem;
    return identity;
  };
  const originalTasks = snapshot.state.cooperation!.tasks;
  const expectedCandidates = originalTasks.filter(node => node.proof?.passed || node.integratedCheck?.passed).map(node => node.task.id);
  const tasks = state.cooperation?.tasks;
  if (canonicalMathJson(frozen(state.problem)) !== canonicalMathJson(frozen(snapshot.state.problem)) ||
      state.problem.baseCommit !== report.canonicalCommit || !oid.test(report.canonicalCommit) ||
      canonicalMathJson(report.candidates) !== canonicalMathJson(expectedCandidates) || tasks?.length !== originalTasks.length ||
      tasks.some((node, index) => taskVersion(node.task) !== taskVersion(originalTasks[index]!.task)))
    throw new Error('math_recovery_identity_changed');
  const originalCanonical = snapshot.state.cooperation!.canonicalCommit!;
  const importedCanonical = report.originalToImported[originalCanonical];
  if (!importedCanonical || !oid.test(importedCanonical) || state.problem.ownedFiles.some(file =>
    !gitFile(report.history, importedCanonical, `${state.problem.projectRelative}/${file}`).equals(
      gitFile(worktree, report.canonicalCommit, `${state.problem.projectRelative}/${file}`))))
    throw new Error('math_recovery_canonical_changed');
  // Lake caches/build products were excluded on the original host, outside the filtered export.
  const exclude = path.resolve(worktree, git(worktree, ['rev-parse', '--git-path', 'info/exclude']));
  const rule = `/${state.problem.projectRelative}/.lake/`;
  if (!fs.readFileSync(exclude, 'utf8').split('\n').includes(rule)) fs.appendFileSync(exclude, `\n${rule}\n`);
  const packages = resolveMathematicsLakePackagesCache(path.join(worktree, state.problem.projectRelative), options.env);
  if (!packages) throw new Error('math_lake_packages_unavailable');
  bindLeanPackages(path.join(worktree, state.problem.projectRelative), packages);
  state.environmentDigest = mathDigest(canonicalMathJson(projectMathematicsRuntimeEnvironment(options.env)));
  state.phase = 'checking'; report.verification = 'checking';
  const save = () => {
    report.evidence = state.cooperation!.tasks.some(node => report.candidates.includes(node.task.id) &&
      node.integratedCheck?.verification.results.some(result => result.status === 'kernel_verified' && result.receiptId))
      ? 'fresh-helper-receipts' : 'recovered-sources-require-recheck';
    writeSolverRunState(report.stateFile, state); writeMathJsonDurable(reportFile, report);
  };
  const pin = (proof: TaskProof) => {
    for (const commit of [proof.commit, proof.verification.targetCommit]) if (commit) {
      if (!oid.test(commit)) throw new Error('math_recovery_invalid_receipt_commit');
      git(worktree, ['update-ref', `refs/math/${state.runId}/evidence/${commit}`, commit]);
    }
  };
  const nodes = state.cooperation!.tasks.filter(node => report.candidates.includes(node.task.id));
  for (const node of nodes) { node.status = 'pending'; node.proof = undefined; node.integratedCheck = undefined; node.feedback = undefined; }
  const pending = [...nodes];
  state.cooperation!.recheck = { canonicalCommit: report.canonicalCommit, total: nodes.length, completed: 0 };
  save();
  try {
    while (pending.length) {
      options.signal.throwIfAborted();
      const node = pending.shift()!, group = [node];
      state.cooperation!.recheck!.taskId = node.task.id; save();
      try {
        const projection = canonicalMathJson([...projectTaskSources(state.problem, worktree, report.canonicalCommit, node.task, [])]);
        for (const other of pending) {
          if (group.length === 32) break;
          try {
            if (canonicalMathJson([...projectTaskSources(state.problem, worktree, report.canonicalCommit, other.task, [])]) === projection) group.push(other);
          } catch { /* The single-task path records its own projection failure. */ }
        }
        options.onProgress?.(group.map(item => item.task.id));
        const check = () => {
          const requests: TaskProofRequest[] = group.map(item => ({ task: item.task, retainedGoals: [], assignment: {
            taskId: item.task.id, taskDigest: taskVersion(item.task), workerId: 'recovery', seedCommit: report.canonicalCommit } }));
          return checkTaskProofs(state.problem, worktree, report.canonicalCommit, requests, options.env,
            options.signal, options.timeoutMs ?? 180_000, state.environmentDigest);
        };
        let proofs: TaskProof[];
        try { proofs = await check(); }
        catch (error) {
          options.signal.throwIfAborted();
          if (group.length === 1) throw error;
          group.splice(1); proofs = await check();
        }
        if (group.length > 1 && proofs.some(proof => !proof.passed)) {
          options.signal.throwIfAborted(); group.splice(1); proofs = await check();
        }
        options.signal.throwIfAborted();
        for (let index = 0; index < group.length; index++) {
          const item = group[index]!, proof = proofs[index]!; pin(proof);
          item.integratedCheck = proof; item.status = proof.passed ? 'integrated' : 'blocked';
          item.feedback = proof.passed ? undefined : proof.verification.results.map(result => result.error).filter(Boolean).join('\n') || proof.verification.status;
        }
      } catch (error) {
        options.signal.throwIfAborted();
        for (const item of group) { item.status = 'blocked'; item.feedback = error instanceof Error ? error.message : 'math_recovery_check_failed'; }
      }
      for (const item of group) { const index = pending.indexOf(item); if (index >= 0) pending.splice(index, 1); }
      state.cooperation!.recheck!.completed += group.length; state.cooperation!.recheck!.taskId = undefined; save();
    }
    state.phase = 'prepared'; report.verification = 'finished'; save();
  } catch (error) {
    report.verification = 'interrupted'; save(); throw error;
  }
  return { report, state };
}
