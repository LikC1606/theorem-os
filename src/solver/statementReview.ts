import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import { canonicalMathJson, mathDigest, writeMathJsonDurable } from '../math/mathRuntimeIo';
import { bindLeanPackages, prepareLeanDiagnosticOverrides, runLeanDiagnostics } from '../math/leanDiagnostics';
import { leanStatementContextCommands, parseLeanStatementContexts, type LeanStatementContext } from '../math/leanStatementContext';
import { maskLeanComments } from '../math/leanSyntax';
import { inspectLeanDeclarationRegions } from '../math/leanSource';
import { assertMathCanonicalPath } from '../math/paths';
import { committedSource, withSolverWorktree } from './problem';
import { advisoryEvidenceRefs } from './deliveries';
import { taskProofContractVersion, taskVersion, type CooperativeTask } from './tasks';
import type { SolverProblem } from './problem';
import { captureProofReferences, type ProofReferences } from './proofReferences';

export type Backtranslation = { mathematics: string; assumptions: string[]; definitions: string[]; evidenceRefs: string[] };
export type StatementReview = {
  id: string; taskId: string; taskDigest: string; snapshotDigest: string; environmentDigest: string; commit: string;
  leanStatement: string; intendedStatement: string; premises: readonly string[]; dependencies: { taskId: string; taskDigest: string }[];
  workspace: string; files: { path: string; digest: string }[];
  status: 'pending' | 'translating' | 'translated' | 'reviewing' | 'accepted' | 'changes_requested' | 'superseded';
  workerId?: string; assignmentId?: string; translation?: Backtranslation; summary?: string;
  references?: ProofReferences;
};
export type StatementAction = { kind: 'backtranslate' | 'statement-review'; reviewId: string; taskId: string; taskDigest: string;
  snapshotDigest: string; seedCommit: string; workspace: string; assignmentId?: string };
export const isStatementAction = (action: { kind: string }): action is StatementAction =>
  action.kind === 'backtranslate' || action.kind === 'statement-review';

export function resetStatementReview(review: StatementReview): void {
  if (review.status === 'translating') review.status = 'pending';
  if (review.status === 'reviewing') review.status = 'translated';
  review.workerId = undefined;
}

export function statementReviewSummary({ workspace: _workspace, files: _files, references, ...review }: StatementReview) {
  return { ...review, actualReferences: references };
}

/** The blind view contains formal context and definitions, with no comments, proof bodies or journals. */
export function statementSnapshot(problem: SolverProblem, task: CooperativeTask, worktree: string, commit: string,
  environmentDigest: string, dependencies: readonly { task: CooperativeTask; taskDigest: string }[], elaboration?: LeanStatementContext) {
  const leanStatement = task.kind === 'lemma' ? `theorem ${task.theoremName} : ${task.type}` :
    'theorem ' + problem.declarations[task.proofPath!]!.find(item => item.name.split('.').at(-1) === task.theoremName!.split('.').at(-1))!.header;
  const sources = [...new Set([...Object.keys(problem.trustedFiles), ...problem.ownedFiles])].filter(file => file.endsWith('.lean'));
  let bytes = 0;
  const definitions = sources.map(file => {
    let source = maskLeanComments(committedSource(worktree, commit, `${problem.projectRelative}/${file}`));
    for (const region of inspectLeanDeclarationRegions(source).reverse()) if (/^(?:theorem|lemma)\s/u.test(source.slice(region.startOffset, region.bodyOffset))) {
      const target = task.kind === 'goal' && file === task.proofPath && region.name.split('.').at(-1) === task.theoremName!.split('.').at(-1);
      source = source.slice(0, region.startOffset) + (target ? 'theorem ' + region.declarationType + '\n' : '') + source.slice(region.endOffset);
    }
    bytes += Buffer.byteLength(source);
    if (bytes > 4_000_000) throw new Error('math_statement_snapshot_too_large');
    return { file, source };
  });
  // Goal reviews certify the fixed original declaration. Helper task revisions do
  // not change that declaration and must not force the same review to restart.
  const snapshotDependencies = task.kind === 'goal' ? [] : dependencies;
  const input = { leanStatement: maskLeanComments(leanStatement), theoremName: task.theoremName, proofPath: task.proofPath, environmentDigest,
    ...(elaboration ? { elaboration } : {}),
    dependencies: snapshotDependencies.map(({ task: dependency, taskDigest }) => ({ taskId: dependency.id, taskDigest,
      theoremName: dependency.theoremName, leanType: dependency.type && maskLeanComments(dependency.type) })),
    definitions: definitions.map((definition, index) => ({ originalFile: definition.file, path: `definitions/${index}.lean` })) };
  // Keep full task versions in the audit input; only mathematical contracts bind review reuse.
  const snapshotDigest = mathDigest(canonicalMathJson({ input: { ...input,
    dependencies: input.dependencies.map((dependency, index) => ({ ...dependency,
      taskDigest: taskProofContractVersion(snapshotDependencies[index]!.task) })) }, definitions }));
  const references = elaboration?.references && captureProofReferences(problem, worktree, commit,
    { name: task.theoremName!, file: task.proofPath! }, elaboration.references, environmentDigest, 'statement',
    task.kind === 'lemma' ? task.type : undefined);
  return { input, definitions, snapshotDigest, ...(references ? { references } : {}) };
}

/** Elaborate all requested types together in a disposable, proof-erased projection. This is not proof evidence. */
export async function captureStatementContexts(problem: SolverProblem, tasks: readonly CooperativeTask[], worktree: string,
  commit: string, env: NodeJS.ProcessEnv, signal?: AbortSignal, timeoutMs = 180_000): Promise<Map<string, LeanStatementContext>> {
  return withSolverWorktree(worktree, commit, async checkout => {
    const project = path.join(checkout, problem.projectRelative);
    const sources = [...new Set([...Object.keys(problem.trustedFiles), ...problem.ownedFiles])].filter(file => file.endsWith('.lean'));
    for (const file of sources) {
      let source = committedSource(worktree, commit, `${problem.projectRelative}/${file}`);
      for (const region of inspectLeanDeclarationRegions(source).reverse())
        if (/^(?:theorem|lemma)\s/u.test(source.slice(region.startOffset, region.bodyOffset)))
          source = source.slice(0, region.bodyOffset) + ' by sorry\n' + source.slice(region.endOffset);
      fs.writeFileSync(path.join(project, file), source);
    }
    const moduleName = (file: string) => file.replace(/\.lean$/u, '').replaceAll('/', '.');
    const id = crypto.randomUUID().replaceAll('-', '');
    const query = `StatementContext${id}.lean`, output = `.lake/statement-context-${id}.json`;
    const roots = tasks.map((task, index) => ({ id: task.id, name: task.kind === 'lemma' ? `statementContext${id}_${index}` : task.theoremName! }));
    const commands = ['import Lean', ...[...new Set(tasks.map(task => moduleName(task.proofPath!)))].map(module => `import ${module}`),
      'set_option autoImplicit false',
      ...tasks.flatMap((task, index) => task.kind === 'lemma' ? [`axiom ${roots[index].name} : ${task.type}`] : []),
      leanStatementContextCommands(roots, sources.map(file => ({ module: moduleName(file), file })), output)].join('\n');
    fs.writeFileSync(path.join(project, query), commands + '\n');
    const packages = path.join(worktree, problem.projectRelative, '.lake', 'packages');
    if (fs.existsSync(packages)) bindLeanPackages(project, packages);
    prepareLeanDiagnosticOverrides(project);
    let result: Awaited<ReturnType<typeof runLeanDiagnostics>> | undefined;
    try {
      result = await runLeanDiagnostics({ projectRoot: project, files: [query], env, signal, timeoutMs, outputLimit: 1_000_000 });
      const report = path.join(project, output);
      if (result.exitCode !== 0 || result.timedOut || !fs.existsSync(report)) {
        const diagnostics = [result.stdout, result.stderr].filter(Boolean).join('\n');
        const firstError = /^.*\berror:/mu.exec(diagnostics)?.index;
        const detail = firstError === undefined ? diagnostics : diagnostics.slice(firstError);
        throw new Error('math_statement_elaboration_failed\n' + (detail || 'Lean did not export statement context.').slice(0, 2000));
      }
      const stat = fs.lstatSync(report);
      if (!stat.isFile() || stat.nlink !== 1 || stat.size > 4_000_000) throw new Error('math_statement_elaboration_invalid');
      return parseLeanStatementContexts(fs.readFileSync(report, 'utf8'), tasks.map(task => task.id));
    } catch (error) {
      // Keep the actual proof-erased inputs and full diagnostics before the disposable
      // checkout is released. A projection containing sorry is never proof evidence.
      const directory = path.join(path.dirname(worktree), 'statement-diagnostics', id);
      assertMathCanonicalPath(directory);
      fs.mkdirSync(path.join(directory, 'project'), { recursive: true, mode: 0o700 });
      const files = [...new Set([...sources, ...Object.keys(problem.trustedFiles), ...problem.ownedFiles, query])].map(file => {
        const source = fs.readFileSync(path.join(project, file));
        const target = path.join(directory, 'project', file);
        assertMathCanonicalPath(target);
        fs.mkdirSync(path.dirname(target), { recursive: true, mode: 0o700 });
        fs.writeFileSync(target, source, { mode: 0o600 });
        return { path: `project/${file}`, digest: mathDigest(source) };
      });
      const reason = error instanceof Error ? error.message : 'math_statement_elaboration_failed';
      fs.writeFileSync(path.join(directory, 'stdout.log'), result?.stdout ?? '', { mode: 0o600 });
      fs.writeFileSync(path.join(directory, 'stderr.log'), result?.stderr ?? reason, { mode: 0o600 });
      writeMathJsonDurable(path.join(directory, 'manifest.json'), {
        schema: 'theorem-os.statement-projection-diagnostic.v1', status: 'advisory-unverified',
        problemReceiptDigest: problem.receiptDigest, commit, query, files,
        tasks: tasks.map(task => ({ id: task.id, taskDigest: taskVersion(task) })),
        exitCode: result?.exitCode ?? null, timedOut: result?.timedOut ?? false, aborted: signal?.aborted ?? false,
        outputCaptureLimitBytes: 1_000_000, reason,
      });
      throw new Error(`${reason}\nProjection diagnostics: ${directory}`, { cause: error });
    }
  });
}

export function writeStatementSnapshot(workspace: string, snapshot: ReturnType<typeof statementSnapshot>): StatementReview['files'] {
  fs.mkdirSync(path.join(workspace, 'definitions'), { recursive: true });
  writeMathJsonDurable(path.join(workspace, 'STATEMENT.json'), { ...snapshot.input, snapshotDigest: snapshot.snapshotDigest });
  snapshot.definitions.forEach((definition, index) => fs.writeFileSync(path.join(workspace, `definitions/${index}.lean`), definition.source));
  return ['STATEMENT.json', ...snapshot.input.definitions.map(definition => definition.path)].map(file =>
    ({ path: file, digest: mathDigest(fs.readFileSync(path.join(workspace, file))) }));
}

/** A review cannot rewrite the statement or definitions it claims to have translated. */
export function assertStatementSnapshot(review: StatementReview): void {
  if (!fs.lstatSync(review.workspace).isDirectory()) throw new Error('math_statement_snapshot_changed');
  const allowed = new Set(review.files.map(file => file.path).concat('RESEARCH.md'));
  const visit = (directory: string) => {
    for (const entry of fs.readdirSync(path.join(review.workspace, directory), { withFileTypes: true })) {
      const relative = directory ? `${directory}/${entry.name}` : entry.name;
      // Session sandboxes can materialize empty metadata mount points beside the fixed inputs.
      if (!directory && entry.isDirectory() && ['.git', '.codex', '.agents', '.aws'].includes(entry.name) &&
          fs.readdirSync(path.join(review.workspace, relative)).length === 0) continue;
      if (entry.isDirectory() && [...allowed].some(file => file.startsWith(relative + '/'))) visit(relative);
      else if (!entry.isFile() || !allowed.has(relative)) throw new Error('math_statement_snapshot_changed');
    }
  };
  visit('');
  for (const file of review.files) {
    const absolute = path.join(review.workspace, file.path);
    const stat = fs.lstatSync(absolute);
    if (!stat.isFile() || stat.nlink !== 1 || stat.size > 4_100_000 || mathDigest(fs.readFileSync(absolute)) !== file.digest)
      throw new Error('math_statement_snapshot_changed');
  }
}

export function readBacktranslation(value: any): Backtranslation {
  value = value && { assumptions: [], definitions: [], evidenceRefs: [], ...value };
  const strings = (items: unknown) => Array.isArray(items) && items.every(item => typeof item === 'string');
  if (!value || typeof value.mathematics !== 'string' || !value.mathematics.trim() ||
      !strings(value.assumptions) || !strings(value.definitions))
    throw new Error('math_backtranslation_invalid');
  return { mathematics: value.mathematics, assumptions: value.assumptions, definitions: value.definitions, evidenceRefs: advisoryEvidenceRefs(value.evidenceRefs) };
}
