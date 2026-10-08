import crypto from 'node:crypto';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { execFileSync } from 'node:child_process';
import { assertMathCanonicalPath } from "./mathRunBinding";
import { isAllowedMathProofSource } from "./mathProofSourcePolicy";
import {
  hashMathFormalSourceDeclaration,
  inspectLeanDeclarations,
  inspectLeanDeclarationRegions,
  stripLeanComments,
  checkManyFormalVerifications,
  type MathematicsVerifierExecutionOptions,
  type MathematicsVerifierResult,
} from "./verifier";

import {
  generateLeanPremiseActionCandidates,
  generateLeanProofActionCandidates,
  type LeanProofActionCandidate,
} from "./leanProofActionSearch";

const digest = (value: string) => crypto.createHash('sha256').update(value).digest('hex');
export type MathProofBlockScope = Readonly<{
  runId: string;
  assignmentId: string;
  artifactRef: string;
  environmentId: string;
}>;
export type CheckedMathProofBlock = Readonly<{
  id: string;
  scope: MathProofBlockScope;
  proofPath: string;
  source: string;
  sourceHash: string;
  declarationName: string;
  elaboratedDeclaration: string;
  declarationHash: string;
  /** Actual kernel dependency attribution for the named declarations in this frozen file. */
  localDependencies: readonly string[];
  axioms: readonly string[];
  receipt: MathematicsVerifierResult;
}>;
const checkedBlocks = new WeakSet<object>();
export function assertCheckedMathProofBlock(block: CheckedMathProofBlock): void {
  if (!checkedBlocks.has(block))
    throw new Error('Proof block must be rebuilt from frozen source and actual verification.');
}

export type MathProofBlockRequest = Readonly<{
  projectRoot: string;
  proofPath: string;
  source: string;
  theoremName: string;
  scope: MathProofBlockScope;
  /** Only already authorized frozen files, never peer working directories. */
  supportingSources?: Readonly<Record<string, string>>;
  deadlineAt: number;
  signal?: AbortSignal;
  env?: NodeJS.ProcessEnv;
  verifierOptions?: Pick<MathematicsVerifierExecutionOptions, 'trustedLakePackagesRoots' | 'verifierCommandPath'>;
}>;

function sourcePath(file: string): string {
  if (
    path.isAbsolute(file) ||
    file.split(/[\\/]/u).some((part) => !part || part === '.' || part === '..') ||
    !isAllowedMathProofSource(file)
  )
    throw new Error('Proof block requires an authorized relative Lean source.');
  return file;
}

export type MathProofBlockResult = Readonly<{
  block?: CheckedMathProofBlock;
  verification?: MathematicsVerifierResult;
  reason?: string;
}>;

/** Preserve the single-target boundary while sharing the exact batch implementation. */
export async function verifyMathProofBlock(request: MathProofBlockRequest): Promise<MathProofBlockResult> {
  return (await verifyMathProofBlocks({ ...request, theoremNames: [request.theoremName] })).get(request.theoremName)!;
}

/** One full frozen-file kernel check, with independently bound evidence for every declaration.
 * No cross-request reuse: authorization and actual environment preparation remain fresh. */
export async function verifyMathProofBlocks(
  request: Omit<MathProofBlockRequest, 'theoremName'> & { theoremNames: readonly string[] }
): Promise<ReadonlyMap<string, MathProofBlockResult>> {
  const checkpoint = () => {
    request.signal?.throwIfAborted();
    if (Date.now() >= request.deadlineAt) throw new Error('Proof block verification deadline exceeded.');
  };
  checkpoint();
  if (Object.values(request.scope).some((value) => !value.trim())) throw new Error('Proof block scope is incomplete.');
  const proofPath = sourcePath(request.proofPath);
  const names = [...new Set(request.theoremNames)];
  if (!names.length || names.length > 32) throw new Error('Proof block batch requires 1 to 32 declarations.');
  const results = new Map<string, MathProofBlockResult>();
  const declarations = inspectLeanDeclarations(request.source);
  if (declarations.length > 32)
    return new Map(
      names.map((name) => [name, { reason: 'Frozen proof block exceeds the bounded declaration attribution scope.' }])
    );
  const sourceHashes = new Map<string, string>();
  for (const name of names) {
    const hash = hashMathFormalSourceDeclaration(request.source, name);
    if (hash) sourceHashes.set(name, hash);
    else results.set(name, { reason: 'No complete named declaration in frozen source.' });
  }
  if (!sourceHashes.size) return results;
  const root = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'math-checked-block-')));
  const git = (...args: string[]) =>
    execFileSync('git', ['-C', root, ...args], {
      encoding: 'utf8',
      timeout: Math.max(1, Math.min(10_000, request.deadlineAt - Date.now())),
      stdio: ['ignore', 'pipe', 'pipe'],
    }).trim();
  try {
    // Preserve exact project configuration. Dependencies are resolved by the existing verifier,
    // using the pinned run configuration; no Lake downloads or package rewriting here.
    for (const file of [
      'lean-toolchain',
      'lakefile.toml',
      'lakefile.lean',
      'lake-manifest.json',
      '.lake/package-overrides.json',
    ]) {
      const from = path.join(request.projectRoot, file);
      if (!fs.existsSync(from)) continue;
      assertMathCanonicalPath(from);
      if (!fs.statSync(from).isFile()) throw new Error('Invalid proof environment configuration.');
      const bytes = fs.readFileSync(from);
      fs.mkdirSync(path.dirname(path.join(root, file)), { recursive: true });
      fs.writeFileSync(path.join(root, file), bytes);
      if (!bytes.equals(fs.readFileSync(from))) throw new Error('Proof environment changed during preparation.');
    }
    for (const [file, source] of Object.entries({ ...request.supportingSources, [proofPath]: request.source })) {
      const target = path.join(root, sourcePath(file));
      fs.mkdirSync(path.dirname(target), { recursive: true });
      fs.writeFileSync(target, source, 'utf8');
    }
    checkpoint();
    git('init', '-q');
    git('add', '-f', '.');
    git(
      '-c',
      'user.name=Proof block verifier',
      '-c',
      'user.email=proof-block@localhost',
      '-c',
      'core.hooksPath=/dev/null',
      'commit',
      '-q',
      '-m',
      'Frozen authorized proof block'
    );
    const targetCommit = git('rev-parse', 'HEAD');
    const sourceHash = digest(request.source);
    const remainingMs = Math.max(1, request.deadlineAt - Date.now());
    const batch = await checkManyFormalVerifications(
      {
        projectRoot: root,
        items: [...sourceHashes].map(([theoremName, sourceDeclarationHash]) => ({
          id: theoremName,
          proofPath,
          theoremName,
          statementHash: sourceDeclarationHash,
          expectedSourceDeclarationHash: sourceDeclarationHash,
        })),
        targetCommit,
        timeoutMs: remainingMs,
        batchTimeoutMs: remainingMs,
      },
      {
        ...request.verifierOptions,
        env: request.env,
        signal: request.signal,
        prepareLocalDependencies: true,
        dependencyCandidates: declarations.map((declaration) => declaration.name),
      }
    );
    checkpoint();
    for (const [theoremName, sourceDeclarationHash] of sourceHashes) {
      const matches = batch.results.filter((result) => result.theoremName === theoremName);
      if (matches.length !== 1) throw new Error('Proof block batch returned ambiguous declaration evidence.');
      const verification = { ...matches[0]!, events: batch.events };
      if (
        verification.status !== 'kernel_verified' ||
        verification.verifier !== 'lean-kernel' ||
        verification.goalsRemaining !== 0 ||
        verification.sorryCount !== 0 ||
        verification.admitCount !== 0 ||
        verification.proofHash !== sourceHash ||
        verification.sourceDeclarationHash !== sourceDeclarationHash ||
        verification.targetCommit !== targetCommit ||
        !verification.elaboratedDeclarationType ||
        !verification.theoremDeclarationHash ||
        !verification.usedDeclarationDependencies
      ) {
        results.set(theoremName, {
          verification,
          reason: verification.error ?? 'Frozen source has no complete bound kernel declaration evidence.',
        });
        continue;
      }
      const scope = Object.freeze({ ...request.scope });
      const block: CheckedMathProofBlock = Object.freeze({
        id: digest(JSON.stringify([scope, proofPath, sourceHash, verification.theoremDeclarationHash])),
        scope,
        proofPath,
        source: request.source,
        sourceHash,
        declarationName: theoremName,
        elaboratedDeclaration: verification.elaboratedDeclarationType,
        declarationHash: verification.theoremDeclarationHash,
        localDependencies: Object.freeze([...verification.usedDeclarationDependencies]),
        axioms: Object.freeze([...verification.axioms]),
        receipt: Object.freeze(verification),
      });
      checkedBlocks.add(block);
      results.set(theoremName, { block, verification });
    }
    return results;
  } finally {
    fs.rmSync(root, { recursive: true, force: true });
  }
}

/** Shared conservative insertion for single facts and locally composed connections.
 * This is only source assembly; the returned source carries no proof authority. */
export function planMathProofBlockInsertion(
  input: Parameters<typeof generateLeanPremiseActionCandidates>[0],
  blocks: readonly CheckedMathProofBlock[]
): { offset: number; text: string } | undefined {
  const currentRegions = inspectLeanDeclarationRegions(input.source);
  const imports = (source: string) =>
    [...stripLeanComments(source).matchAll(/^\s*import\s+([^\n\r]+)/gmu)].flatMap((match) =>
      match[1]!.trim().split(/\s+/u)
    );
  const currentImports = new Set(imports(input.source));
  const additions = new Map<string, string>();
  let dependencyEnd = 0;
  for (const block of blocks) {
    assertCheckedMathProofBlock(block);
    if (imports(block.source).some((name) => !currentImports.has(name))) return undefined;
    const regions = inspectLeanDeclarationRegions(block.source);
    let remainder = block.source;
    for (const region of regions.toReversed())
      remainder = remainder.slice(0, region.startOffset) + remainder.slice(region.endOffset);
    if (
      stripLeanComments(remainder)
        .replace(/^\s*import[^\n\r]*/gmu, '')
        .trim()
    )
      return undefined;
    for (const region of regions) {
      const bytes = block.source.slice(region.startOffset, region.endOffset).trim();
      const existing = currentRegions.filter((item) => item.name === region.name);
      if (
        existing.length > 1 ||
        (existing.length === 1 &&
          input.source.slice(existing[0]!.startOffset, existing[0]!.endOffset).trim() !== bytes) ||
        (additions.has(region.name) && additions.get(region.name) !== bytes)
      )
        return undefined;
      if (!existing.length) additions.set(region.name, bytes);
      else dependencyEnd = Math.max(dependencyEnd, existing[0]!.endOffset);
    }
  }
  const offset = currentRegions.length ? Math.max(currentRegions[0]!.startOffset, dependencyEnd) : undefined;
  const goalLine = input.targetRange?.start.line ?? input.targetLine;
  const goalOffset =
    goalLine === undefined
      ? undefined
      : input.source
          .split('\n')
          .slice(0, goalLine - 1)
          .join('\n').length + (goalLine > 1 ? 1 : 0);
  if (additions.size && (offset === undefined || (goalOffset !== undefined && offset > goalOffset))) return undefined;
  return { offset: offset ?? 0, text: additions.size ? [...additions.values()].join('\n\n') + '\n\n' : '' };
}

/** Conservative lexical insertion only; every generated instance still goes through Lean.
 * Namespace/section commands and unequal declarations require an explicit mathematical edit. */
export function buildMathProofBlockCandidates(
  input: Parameters<typeof generateLeanPremiseActionCandidates>[0],
  blocks: readonly CheckedMathProofBlock[]
): readonly LeanProofActionCandidate[] {
  const candidates: LeanProofActionCandidate[] = [];
  for (const block of blocks) {
    const insertion = planMathProofBlockInsertion(input, [block]);
    if (!insertion) continue;
    const instances = [
      ...generateLeanPremiseActionCandidates({
        ...input,
        premises: [{ name: block.declarationName, type: block.elaboratedDeclaration }],
      }),
    ];
    // A checked equation may solve a target under a constructor or function,
    // even when its conclusion cannot be applied directly. Keep the rewrite
    // inside a complete proof term: unmet conditions must still be discharged
    // by Lean, and no incomplete rewrite prefix becomes an adopted fact.
    if (/^[\p{L}_][\p{L}\p{N}_'.]*$/u.test(block.declarationName) && /[=↔]/u.test(block.elaboratedDeclaration)) {
      const tactic = `exact (by simp_all only [${block.declarationName}])`;
      const rewritten = generateLeanProofActionCandidates({ ...input, preferredTactic: tactic }).find(
        (candidate) => candidate.payload === tactic
      );
      if (rewritten) instances.push(rewritten);
    }
    for (const candidate of instances) {
      const source = insertion.text
        ? candidate.source.slice(0, insertion.offset) + insertion.text + candidate.source.slice(insertion.offset)
        : candidate.source;
      candidates.push(
        Object.freeze({
          ...candidate,
          source,
          helperProduced: true,
          provenance: Object.freeze({
            source: 'local' as const,
            declarationName: block.declarationName,
            declarationType: block.elaboratedDeclaration,
            sourceFile: block.proofPath,
          }),
        })
      );
    }
  }
  return Object.freeze(candidates);
}
