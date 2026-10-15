import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { mathGitBytes, mathGitText } from '../math/mathGit';
import { readImo2026BootstrapReceipt, verifyImo2026BootstrapReceipt, theoremQualifiedNamesFromSource } from '../math/imo2026Adapter';
import { readLeanEvalBootstrapReceipt } from '../math/leanEvalBootstrap';
import { resolveLeanEvalSubmissionName } from '../math/leanEvalSubmission';
import { canonicalMathJson, mathDigest, readMathJson } from '../math/mathRuntimeIo';
import { assertMathCanonicalPath, isMathPathWithin } from '../math/paths';
import { hashMathFormalSourceDeclaration, inspectLeanDeclarationRegions, inspectLeanDeclarations } from '../math/leanSource';
import { mathConstructionImports } from '../math/mathConstructionSources';
import type { MathProblemContract } from '../math/contracts';
import { readLocalExampleReceipt } from '../math/localExample';

export function committedSource(worktree: string, commit: string, file: string): string {
  return mathGitBytes(worktree, ['show', `${commit}:${file}`],
    { timeout: 30_000, maxBuffer: 1024 * 1024, errorMessage: 'math_task_source_unavailable' }).toString('utf8');
}

export type ProofTarget = Readonly<{ proofPath: string; theoremName: string; declarationHash: string }>;
export class SolverSourceError extends Error {
  constructor(readonly proofPath: string, reason: 'math_original_declaration_changed' | 'math_original_context_changed',
    readonly declarationName?: string) {
    super(reason);
  }
  get recovery(): string {
    return this.message === 'math_original_context_changed'
      ? 'Restore the original imports, namespace/section placement, variables, opens, scopes and options from the seed commit. ' +
        'Keep new helpers; move helper-specific scopes and instances inside their proofs. Only explicit Mathlib.* imports may be added.'
      : `Restore the original name, parameters, type and any frozen definition body${this.declarationName ? ` of ${this.declarationName}` : ''} from the seed commit. Preserve new proof work.`;
  }
}
export type SolverProblem = Readonly<{
  kind: 'imo2026' | 'lean-eval' | 'example';
  workspace: string;
  projectRelative: string;
  baseCommit: string;
  receiptDigest: string;
  contract: MathProblemContract;
  targets: readonly ProofTarget[];
  trustedFiles: Readonly<Record<string, string>>;
  ownedFiles: readonly string[];
  activeProblemPath: string;
  sourceRepository?: string;
  declarations: Readonly<Record<string, readonly { name: string; header: string; body?: string }[]>>;
  sourceStructure: Readonly<Record<string, string>>;
  sourceImports?: Readonly<Record<string, readonly string[]>>;
}>;

export function git(root: string, args: string[]): string {
  return mathGitText(root, args, { timeout: 30_000, maxBuffer: 1024 * 1024, errorMessage: `math_git_failed:${args[0]}` });
}

/** Journals guide research but never become inputs to a projected proof. */
export function commitSolverProjection(problem: SolverProblem, worktree: string, message: string): string {
  git(worktree, ['rm', '--quiet', '--force', '--ignore-unmatch', '--', 'RESEARCH.md']);
  git(worktree, ['add', '--', ...problem.ownedFiles.map(file => path.join(problem.projectRelative, file))]);
  git(worktree, ['-c', 'user.name=DeepScientist Math', '-c', 'user.email=math@localhost', 'commit',
    '--allow-empty', '--no-gpg-sign', '--quiet', '-m', message]);
  return git(worktree, ['rev-parse', 'HEAD']);
}

export type SolverSourceConstraints = Pick<SolverProblem, 'trustedFiles' | 'declarations' | 'sourceStructure' | 'sourceImports'>;

/** Only explicit modules from the pinned Mathlib package may extend proof imports. */
export function solverMathlibImports(source: string): string[] {
  return mathConstructionImports(source).filter(module => /^Mathlib(?:\.[A-Za-z_][A-Za-z0-9_']*)+$/u.test(module));
}

/** Read-only instance queries allow simple names or balanced parenthesized types. */
function isInstanceQuery(line: string): boolean {
  const query = /^#synth[ \t]+[\p{L}_][\p{L}\p{M}\p{N}_'.]*(.*)$/u.exec(line);
  if (!query || /["`#;]/u.test(query[1])) return false;
  let depth = 0;
  let bare = '';
  const validBare = () => !bare || /^[\p{L}_][\p{L}\p{M}\p{N}_'.]*$|^[0-9]+$/u.test(bare) &&
    !/^(?:import|public|private|meta|namespace|section|end|theorem|lemma|def|example|abbrev|opaque|instance|inductive|structure|class|axiom|constant|variable|universe|open|export|set_option|attribute|noncomputable|unsafe|syntax|macro|elab|notation|infix|infixl|infixr|prefix|postfix|initialize|builtin_initialize)$/u.test(bare);
  for (const character of query[1]) {
    if (character === '(') { if (!depth && !validBare()) return false; bare = ''; depth++; }
    else if (character === ')') { if (--depth < 0) return false; }
    else if (!depth) {
      if (character === ' ' || character === '\t') { if (!validBare()) return false; bare = ''; }
      else bare += character;
    }
  }
  return depth === 0 && validBare();
}

function sourceStructure(source: string, originalNames: ReadonlySet<string>, originalImports?: readonly string[]): string {
  const addedImports = new Set(originalImports === undefined ? [] :
    solverMathlibImports(source).filter(module => !originalImports.includes(module)));
  const regions = inspectLeanDeclarationRegions(source);
  let frozen = '';
  let cursor = 0;
  for (const region of regions) {
    const context = source.slice(cursor, region.startOffset);
    frozen += originalNames.has(region.name) ? context : context.replace(/\bnoncomputable[ \t]+$/u, '');
    if (originalNames.has(region.name)) frozen += `${region.declarationType}\n`;
    cursor = region.endOffset;
  }
  frozen += source.slice(cursor);
  // Read-only name and instance queries leave the original proof context intact.
  return mathDigest(frozen.split('\n').map(line => line.trim()).filter(line => line &&
    !addedImports.has(/^import[ \t]+([^ \t]+)$/u.exec(line)?.[1] ?? '') &&
    !/^#check[ \t]+[\p{L}_][\p{L}\p{M}\p{N}_'.]*$/u.test(line) && !isInstanceQuery(line)).join('\n'));
}

export function readSolverProblem(workspacePath: string, receiptFile: string): SolverProblem {
  const workspace = fs.realpathSync(workspacePath);
  assertMathCanonicalPath(workspace);
  const raw = readMathJson(receiptFile) as { schema?: string; receipt?: unknown };
  const value = raw.schema === 'deepscientist.mathematics.lean-eval-held-out-bootstrap.v1' ? raw.receipt : raw;
  const receipt = (value as { schema?: string }).schema === 'theorem-os.local-example.v1'
    ? readLocalExampleReceipt(receiptFile)
    : (value as { schema?: string }).schema === 'deepscientist.mathematics.imo2026-bootstrap-receipt.v1'
    ? readImo2026BootstrapReceipt(receiptFile)
    : readLeanEvalBootstrapReceipt((value as { activeProblemPath: string }).activeProblemPath);
  if (receipt.schema === 'deepscientist.mathematics.imo2026-bootstrap-receipt.v1') verifyImo2026BootstrapReceipt(receipt);
  if (fs.realpathSync(receipt.workspaceRoot) !== workspace) throw new Error('math_problem_workspace_mismatch');
  assertMathCanonicalPath(receipt.projectRoot);
  if (!isMathPathWithin(workspace, receipt.projectRoot) || workspace === receipt.projectRoot)
    throw new Error('math_problem_project_outside_workspace');
  const projectRelative = path.relative(workspace, receipt.projectRoot);
  const trustedFiles = Object.fromEntries(receipt.trustedFiles.map(relative => {
    const target = path.resolve(receipt.projectRoot, relative);
    assertMathCanonicalPath(target);
    if (!isMathPathWithin(receipt.projectRoot, target) || !fs.statSync(target).isFile()) throw new Error('math_problem_trusted_path');
    return [relative, mathDigest(fs.readFileSync(target))];
  }));
  const publicObligations = 'publicObligations' in receipt ? receipt.publicObligations : undefined;
  const names = publicObligations?.map(item => item.name) || theoremQualifiedNamesFromSource(receipt.contract.formalStatement);
  if (!names.length) throw new Error('math_problem_targets_missing');
  const targets = names.map(theoremName => {
    const declarationHash = publicObligations?.find(item => item.name === theoremName)?.declarationHash ||
      hashMathFormalSourceDeclaration(receipt.contract.formalStatement, theoremName);
    if (!declarationHash) throw new Error('math_problem_declaration_missing');
    const files = receipt.solverOwnedFiles.filter(relative => relative.endsWith('.lean') &&
      hashMathFormalSourceDeclaration(fs.readFileSync(path.join(receipt.projectRoot, relative), 'utf8'), theoremName) === declarationHash);
    if (files.length !== 1) throw new Error('math_problem_target_file_ambiguous');
    const candidateName = publicObligations && receipt.schema !== 'theorem-os.local-example.v1' ? resolveLeanEvalSubmissionName(theoremName,
      fs.readFileSync(path.join(receipt.projectRoot, files[0]!), 'utf8')) : theoremName;
    return { theoremName: candidateName, declarationHash, proofPath: files[0]! };
  });
  const targetNames = new Set(targets.map(target => target.theoremName.split('.').at(-1)));
  const declarations = Object.fromEntries(receipt.solverOwnedFiles.filter(file => file.endsWith('.lean')).map(file => {
    const source = fs.readFileSync(path.join(receipt.projectRoot, file), 'utf8');
    const kinds = new Map(inspectLeanDeclarations(source).map(item => [item.name, item.kind]));
    return [file, inspectLeanDeclarationRegions(source).map(item => ({ name: item.name, header: item.declarationType,
      ...(kinds.get(item.name) !== 'theorem' && !targetNames.has(item.name.split('.').at(-1))
        ? { body: mathDigest(source.slice(item.bodyOffset, item.endOffset).trim()) } : {}) }))];
  }));
  const structures = Object.fromEntries(Object.entries(declarations).map(([file, originals]) =>
    [file, sourceStructure(fs.readFileSync(path.join(receipt.projectRoot, file), 'utf8'), new Set(originals.map(item => item.name)))]));
  const sourceImports = Object.fromEntries(Object.keys(declarations).map(file =>
    [file, mathConstructionImports(fs.readFileSync(path.join(receipt.projectRoot, file), 'utf8'))]));
  return { kind: receipt.schema === 'theorem-os.local-example.v1' ? 'example' : receipt.schema.includes('imo2026') ? 'imo2026' : 'lean-eval', workspace, projectRelative,
    baseCommit: git(workspace, ['rev-parse', 'HEAD']), receiptDigest: mathDigest(canonicalMathJson(receipt)),
    contract: receipt.contract, targets, trustedFiles, ownedFiles: receipt.solverOwnedFiles,
    declarations, sourceStructure: structures, sourceImports, activeProblemPath: receipt.activeProblemPath,
    ...('sourceProjectRoot' in receipt ? { sourceRepository: receipt.sourceProjectRoot } : {}) };
}

/** Shared source preflight; diagnostic copies remain advisory, host checks use the frozen state. */
export function assertSolverProjectSources(problem: SolverSourceConstraints, project: string): void {
  for (const [relative, digest] of Object.entries(problem.trustedFiles)) {
    const target = path.join(project, relative);
    assertMathCanonicalPath(target);
    if (mathDigest(fs.readFileSync(target)) !== digest) throw new Error('math_trusted_source_changed');
  }
  for (const [relative, originals] of Object.entries(problem.declarations)) {
    const file = path.join(project, relative);
    assertMathCanonicalPath(file);
    const source = fs.readFileSync(file, 'utf8');
    const regions = inspectLeanDeclarationRegions(source);
    for (const original of originals) {
      const matches = regions.filter(item => item.name === original.name);
      const current = matches[0];
      if (matches.length !== 1 || current.declarationType !== original.header ||
          (original.body && mathDigest(source.slice(current.bodyOffset, current.endOffset).trim()) !== original.body))
        throw new SolverSourceError(relative, 'math_original_declaration_changed', original.name);
    }
    if (sourceStructure(source, new Set(originals.map(item => item.name)), problem.sourceImports?.[relative]) !== problem.sourceStructure[relative])
      throw new SolverSourceError(relative, 'math_original_context_changed');
  }
}

export function assertSolverSources(problem: SolverProblem, worktree: string): void {
  const project = path.join(worktree, problem.projectRelative);
  assertSolverProjectSources(problem, project);
  git(worktree, ['merge-base', '--is-ancestor', problem.baseCommit, 'HEAD']);
  const changed = [...git(worktree, ['diff', '--name-only', problem.baseCommit]).split('\n'),
    ...git(worktree, ['ls-files', '--others', '--exclude-standard']).split('\n')].filter(Boolean);
  const allowed = new Set([...problem.ownedFiles.map(relative => path.join(problem.projectRelative, relative)), 'RESEARCH.md', 'DELIVERIES.jsonl', 'COOPERATION.json']);
  for (const relative of changed) if (!allowed.has(relative) && !/^DELIVERIES-[a-f0-9]{64}\.jsonl$/u.test(relative)) throw new Error('math_source_outside_ownership');
  for (const target of problem.targets) {
    const file = path.join(project, target.proofPath);
    if (hashMathFormalSourceDeclaration(fs.readFileSync(file, 'utf8'), target.theoremName) !== target.declarationHash)
      throw new SolverSourceError(target.proofPath, 'math_original_declaration_changed');
  }
}

export function commitSolverSources(problem: SolverProblem, worktree: string): string {
  assertSolverSources(problem, worktree);
  // Host journals change independently of frozen proof commits. Ignore only their allowed root paths.
  const exclude = path.resolve(worktree, git(worktree, ['rev-parse', '--git-path', 'info/exclude']));
  const existing = fs.existsSync(exclude) ? fs.readFileSync(exclude, 'utf8').split('\n') : [];
  const missing = ['/COOPERATION.json', '/DELIVERIES.jsonl', `/DELIVERIES-${'[a-f0-9]'.repeat(64)}.jsonl`]
    .filter(rule => !existing.includes(rule));
  if (missing.length) {
    fs.mkdirSync(path.dirname(exclude), { recursive: true });
    fs.appendFileSync(exclude, `\n${missing.join('\n')}\n`);
  }
  const files = problem.ownedFiles.map(relative => path.join(problem.projectRelative, relative));
  if (fs.existsSync(path.join(worktree, 'RESEARCH.md'))) files.push('RESEARCH.md');
  git(worktree, ['add', '--', ...files]);
  if (git(worktree, ['diff', '--cached', '--name-only']))
    git(worktree, ['-c', 'user.name=DeepScientist Math', '-c', 'user.email=math@localhost', 'commit', '--no-gpg-sign', '--quiet', '-m', 'Checkpoint mathematical proof']);
  return git(worktree, ['rev-parse', 'HEAD']);
}

/** Use a disposable checkout of a fixed commit and release it on every exit path. */
export async function withSolverWorktree<T>(worktree: string, commit: string, run: (checkout: string) => Promise<T>): Promise<T> {
  const directory = fs.mkdtempSync(path.join(os.tmpdir(), 'math-check-'));
  const checkout = path.join(directory, 'worktree');
  let added = false;
  try {
    git(worktree, ['worktree', 'add', '--quiet', '--detach', checkout, commit]); added = true;
    return await run(checkout);
  } finally {
    try { if (added) git(worktree, ['worktree', 'remove', '--force', checkout]); }
    finally { fs.rmSync(directory, { recursive: true, force: true }); }
  }
}
