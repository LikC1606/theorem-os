import fs from 'node:fs';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import { readImo2026BootstrapReceipt, verifyImo2026BootstrapReceipt, theoremQualifiedNamesFromSource } from '../math/imo2026Adapter';
import { readLeanEvalBootstrapReceipt } from '../math/leanEvalBootstrap';
import { resolveLeanEvalSubmissionName } from '../math/leanEvalSubmission';
import { canonicalMathJson, mathDigest, readMathJson } from '../math/mathRuntimeIo';
import { assertMathCanonicalPath, isMathPathWithin } from '../math/paths';
import { hashMathFormalSourceDeclaration, inspectLeanDeclarationRegions, inspectLeanDeclarations } from '../math/verifier';
import type { MathProblemContract } from '../math/contracts';

export type ProofTarget = Readonly<{ proofPath: string; theoremName: string; declarationHash: string }>;
export class SolverSourceError extends Error {
  constructor(readonly proofPath: string, reason: 'math_original_declaration_changed' | 'math_original_context_changed') {
    super(reason);
  }
}
export type SolverProblem = Readonly<{
  kind: 'imo2026' | 'lean-eval';
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
}>;

export function git(root: string, args: string[]): string {
  const result = spawnSync('git', args, { cwd: root, encoding: 'utf8', timeout: 30_000, maxBuffer: 1024 * 1024 });
  if (result.error || result.status !== 0) throw new Error(`math_git_failed:${args[0]}`);
  return result.stdout.trim();
}

export type SolverSourceConstraints = Pick<SolverProblem, 'trustedFiles' | 'declarations' | 'sourceStructure'>;

function sourceStructure(source: string, originalNames: ReadonlySet<string>): string {
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
  return mathDigest(frozen.split('\n').map(line => line.trim()).filter(Boolean).join('\n'));
}

export function readSolverProblem(workspacePath: string, receiptFile: string): SolverProblem {
  const workspace = fs.realpathSync(workspacePath);
  assertMathCanonicalPath(workspace);
  const raw = readMathJson(receiptFile) as { schema?: string; receipt?: unknown };
  const value = raw.schema === 'deepscientist.mathematics.lean-eval-held-out-bootstrap.v1' ? raw.receipt : raw;
  const receipt = (value as { schema?: string }).schema === 'deepscientist.mathematics.imo2026-bootstrap-receipt.v1'
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
    const candidateName = publicObligations ? resolveLeanEvalSubmissionName(theoremName,
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
  return { kind: receipt.schema.includes('imo2026') ? 'imo2026' : 'lean-eval', workspace, projectRelative,
    baseCommit: git(workspace, ['rev-parse', 'HEAD']), receiptDigest: mathDigest(canonicalMathJson(receipt)),
    contract: receipt.contract, targets, trustedFiles, ownedFiles: receipt.solverOwnedFiles,
    declarations, sourceStructure: structures, activeProblemPath: receipt.activeProblemPath,
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
        throw new SolverSourceError(relative, 'math_original_declaration_changed');
    }
    if (sourceStructure(source, new Set(originals.map(item => item.name))) !== problem.sourceStructure[relative])
      throw new SolverSourceError(relative, 'math_original_context_changed');
  }
}

export function assertSolverSources(problem: SolverProblem, worktree: string): void {
  const project = path.join(worktree, problem.projectRelative);
  assertSolverProjectSources(problem, project);
  git(worktree, ['merge-base', '--is-ancestor', problem.baseCommit, 'HEAD']);
  const changed = [...git(worktree, ['diff', '--name-only', problem.baseCommit]).split('\n'),
    ...git(worktree, ['ls-files', '--others', '--exclude-standard']).split('\n')].filter(Boolean);
  const allowed = new Set([...problem.ownedFiles.map(relative => path.join(problem.projectRelative, relative)), 'RESEARCH.md']);
  for (const relative of changed) if (!allowed.has(relative)) throw new Error('math_source_outside_ownership');
  for (const target of problem.targets) {
    const file = path.join(project, target.proofPath);
    if (hashMathFormalSourceDeclaration(fs.readFileSync(file, 'utf8'), target.theoremName) !== target.declarationHash)
      throw new SolverSourceError(target.proofPath, 'math_original_declaration_changed');
  }
}

export function commitSolverSources(problem: SolverProblem, worktree: string): string {
  assertSolverSources(problem, worktree);
  const files = problem.ownedFiles.map(relative => path.join(problem.projectRelative, relative));
  if (fs.existsSync(path.join(worktree, 'RESEARCH.md'))) files.push('RESEARCH.md');
  git(worktree, ['add', '--', ...files]);
  if (git(worktree, ['diff', '--cached', '--name-only']))
    git(worktree, ['-c', 'user.name=DeepScientist Math', '-c', 'user.email=math@localhost', 'commit', '--no-gpg-sign', '--quiet', '-m', 'Checkpoint mathematical proof']);
  return git(worktree, ['rev-parse', 'HEAD']);
}
