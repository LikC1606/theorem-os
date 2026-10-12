import fs from 'node:fs';
import path from 'node:path';
import { canonicalMathJson, mathDigest, writeMathJsonDurable } from '../math/mathRuntimeIo';
import { maskLeanComments } from '../math/leanSyntax';
import { inspectLeanDeclarationRegions } from '../math/verifier';
import { committedSource } from './problem';
import type { CooperativeTask } from './tasks';
import type { SolverProblem } from './problem';
import type { ProofReferences } from './proofReferences';

export type Backtranslation = { mathematics: string; assumptions: string[]; definitions: string[]; evidenceRefs: string[] };
export type StatementReview = {
  id: string; taskId: string; taskDigest: string; snapshotDigest: string; environmentDigest: string; commit: string;
  leanStatement: string; intendedStatement: string; premises: readonly string[]; dependencies: { taskId: string; taskDigest: string }[];
  workspace: string; files: { path: string; digest: string }[];
  status: 'pending' | 'translating' | 'translated' | 'reviewing' | 'accepted' | 'changes_requested' | 'superseded';
  workerId?: string; translation?: Backtranslation; summary?: string;
  references?: ProofReferences;
};
export type StatementAction = { kind: 'backtranslate' | 'statement-review'; reviewId: string; taskId: string; taskDigest: string;
  snapshotDigest: string; seedCommit: string; workspace: string };
export const isStatementAction = (action: { kind: string }): action is StatementAction =>
  action.kind === 'backtranslate' || action.kind === 'statement-review';

/** The blind view contains formal context and definitions, with no comments, proof bodies or journals. */
export function statementSnapshot(problem: SolverProblem, task: CooperativeTask, worktree: string, commit: string,
  environmentDigest: string, dependencies: readonly { task: CooperativeTask; taskDigest: string }[]) {
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
  const input = { leanStatement: maskLeanComments(leanStatement), theoremName: task.theoremName, proofPath: task.proofPath, environmentDigest,
    dependencies: dependencies.map(({ task: dependency, taskDigest }) => ({ taskId: dependency.id, taskDigest,
      theoremName: dependency.theoremName, leanType: dependency.type && maskLeanComments(dependency.type) })),
    definitions: definitions.map((definition, index) => ({ originalFile: definition.file, path: `definitions/${index}.lean` })) };
  const snapshotDigest = mathDigest(canonicalMathJson({ input, definitions }));
  return { input, definitions, snapshotDigest };
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
  const strings = (items: unknown, count: number, length: number) => Array.isArray(items) && items.length <= count &&
    items.every(item => typeof item === 'string' && item.length <= length);
  if (!value || typeof value.mathematics !== 'string' || !value.mathematics.trim() || value.mathematics.length > 8000 ||
      !strings(value.assumptions, 32, 2000) || !strings(value.definitions, 32, 2000) || !strings(value.evidenceRefs, 16, 1000))
    throw new Error('math_backtranslation_invalid');
  return { mathematics: value.mathematics, assumptions: value.assumptions, definitions: value.definitions, evidenceRefs: value.evidenceRefs };
}
