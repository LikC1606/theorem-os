/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

import crypto from 'node:crypto';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import type { MathFeasibilitySignals, MathPlanNode } from "../common/types/team/mathematicsTeam";
import type { LeanEvalCatalogProblem } from "./leanEvalCatalogAdapter";
import { assertLeanEvalHoleDagAcyclic, scheduleLeanEvalHoles, type LeanEvalHoleSchedule } from "./leanEvalHoleDag";
import {
  inspectLeanDeclarations,
  resolveMathematicsLakePackagesCache,
  runMathematicsSandboxedCommand,
} from "./verifier";
import { runLeanEvalLeanProbe } from "./leanEvalLeanProbe";
import { resolveMathematicsRuntimeEnvironment } from "./mathRuntimeEnvironment";

export type LeanEvalAnalyzedHole = Readonly<{
  name: string;
  basename: string;
  kind: 'theorem' | 'definition' | 'instance' | 'unknown';
  declarationBody: string;
  dependsOn: readonly string[];
}>;

export type LeanEvalProblemAnalysis = Readonly<{
  problemId: string;
  benchmarkCommit: string;
  challengePath: string;
  challengeSha256: string;
  imports: readonly string[];
  challengeDependencyDeclarations: readonly string[];
  /** Declaration references inferred from public ChallengeDeps/Lean syntax. */
  holeDependencyDeclarations?: Readonly<Record<string, readonly string[]>>;
  holes: readonly LeanEvalAnalyzedHole[];
  holeDag: readonly MathPlanNode[];
  holeSchedule: LeanEvalHoleSchedule;
  noncomputableDeclarationCount: number;
  formalDegeneracySignals: readonly string[];
  firstCompileProbe: Readonly<{ attempted: boolean; ok?: boolean; error?: string }>;
  /** Optional real elaborator probe over public Challenge declarations. */
  elaborationProbe?: Readonly<{
    attempted: boolean;
    ok?: boolean;
    checkedDeclarationCount?: number;
    declarationDependencies?: Readonly<Record<string, readonly string[]>>;
    error?: string;
  }>;
  feasibility: MathFeasibilitySignals;
}>;

export type LeanEvalProblemAnalysisOptions = Readonly<{
  repositoryRoot: string;
  benchmarkCommit: string;
  compileProbe?: (
    problemRoot: string
  ) => Promise<Readonly<{ ok: boolean; error?: string }>> | Readonly<{ ok: boolean; error?: string }>;
  elaborationProbe?: (
    problemRoot: string,
    declarations: readonly string[],
    dependencyTargets: readonly string[]
  ) =>
    | Promise<
        Readonly<{
          ok: boolean;
          checkedDeclarationCount?: number;
          declarationDependencies?: Readonly<Record<string, readonly string[]>>;
          error?: string;
        }>
      >
    | Readonly<{
        ok: boolean;
        checkedDeclarationCount?: number;
        declarationDependencies?: Readonly<Record<string, readonly string[]>>;
        error?: string;
      }>;
  supportedToolchains?: readonly string[];
  historicalOutcomes?: Readonly<{ attempts: number; successes: number }>;
}>;

const sha256 = (value: string): string => crypto.createHash('sha256').update(value, 'utf8').digest('hex');
const text = (value: unknown): string | undefined =>
  typeof value === 'string' && value.trim() ? value.trim() : undefined;
const record = (value: unknown): Record<string, unknown> | undefined =>
  value !== null && typeof value === 'object' && !Array.isArray(value) ? (value as Record<string, unknown>) : undefined;
const bounded = (value: number): number => Math.max(0, Math.min(1, value));
const escapeRegExp = (value: string): string => value.replace(/[.*+?^${}()|[\]\\]/gu, '\\$&');
const leanEnvironment = (): NodeJS.ProcessEnv => resolveMathematicsRuntimeEnvironment();
const holeNodeId = (name: string): string => {
  const encoded = `hole:${Array.from(name)
    .map((character) => character.codePointAt(0)!.toString(16))
    .join('_')}`;
  return encoded.length <= 120 ? encoded : `${encoded.slice(0, 55)}:${sha256(name)}`;
};

const read = (root: string, relativePath: string): string => fs.readFileSync(path.join(root, relativePath), 'utf8');

type CachedProblemAnalysis = Readonly<{
  challengeSha256: string;
  depsSha256: string;
  value: LeanEvalProblemAnalysis;
}>;
const problemAnalysisCache = new Map<string, CachedProblemAnalysis>();
const MAX_PROBLEM_ANALYSIS_CACHE = 64;

const removeTemporaryTree = (target: string): void => {
  try {
    fs.rmSync(target, { recursive: true, force: true });
  } catch {
    // Docker may create a mount parent as root when a package target is
    // missing. Probe cleanup is best-effort; the target is already disposable.
  }
};

/** Resolve the Lean repository root without mistaking a generated problem's
 * own `lean-toolchain` for the checkout root. */
const leanRepositoryRoot = (resolvedProblemRoot: string): string => {
  let candidate = resolvedProblemRoot;
  let fallback: string | undefined;
  while (candidate !== path.dirname(candidate)) {
    if (fs.existsSync(path.join(candidate, 'lakefile.toml')) && fs.existsSync(path.join(candidate, 'lean-toolchain'))) {
      fallback ??= candidate;
    }
    if (fs.existsSync(path.join(candidate, '.git'))) return candidate;
    candidate = path.dirname(candidate);
  }
  return fallback ?? resolvedProblemRoot;
};

const stripLeanTrivia = (source: string): string => {
  let result = '';
  let blockDepth = 0;
  let lineComment = false;
  let quote = false;
  let escaped = false;
  for (let index = 0; index < source.length; index += 1) {
    const current = source[index]!;
    const next = source[index + 1];
    if (lineComment) {
      if (current === '\n') {
        lineComment = false;
        result += '\n';
      }
      continue;
    }
    if (blockDepth > 0) {
      if (current === '/' && next === '-') {
        blockDepth += 1;
        index += 1;
      } else if (current === '-' && next === '/') {
        blockDepth -= 1;
        index += 1;
      }
      continue;
    }
    if (quote) {
      if (escaped) escaped = false;
      else if (current === '\\') escaped = true;
      else if (current === '"') quote = false;
      result += ' ';
      continue;
    }
    if (current === '-' && next === '-') {
      lineComment = true;
      index += 1;
    } else if (current === '/' && next === '-') {
      blockDepth = 1;
      index += 1;
    } else if (current === '"') {
      quote = true;
      result += ' ';
    } else result += current;
  }
  return result;
};

const isInstanceDeclaration = (body: string): boolean =>
  /(?:^|\n)\s*(?:noncomputable\s+)?instance\b/u.test(body) ||
  /(?:^|\n)\s*@\[[^\]\n]*\binstance\b[^\]\n]*\]/u.test(body);

const importsFrom = (source: string): readonly string[] =>
  Object.freeze([
    ...new Set([...source.matchAll(/^\s*import\s+([^\s-]+)/gmu)].flatMap((match) => (match[1] ? [match[1]] : []))),
  ]);

const declarationNamesFrom = (source: string): readonly string[] =>
  Object.freeze([
    ...new Set(
      [
        ...source.matchAll(
          /(?:^|\n)\s*(?:noncomputable\s+)?(?:def|abbrev|theorem|lemma|instance|class|structure|inductive)\s+([A-Za-z_][A-Za-z0-9_'.]*)/g
        ),
      ].flatMap((match) => (match[1] ? [match[1]] : []))
    ),
  ]);

const namespaceNamesFrom = (source: string): readonly string[] =>
  Object.freeze([
    ...new Set(
      [...source.matchAll(/(?:^|\n)\s*namespace\s+([A-Za-z_][A-Za-z0-9_'.]*)/g)].flatMap((match) =>
        match[1] ? [match[1]] : []
      )
    ),
  ]);

const parseHoleBodies = (
  root: string,
  problem: LeanEvalCatalogProblem
): readonly { name: string; basename: string; kind: LeanEvalAnalyzedHole['kind']; declarationBody: string }[] => {
  const relativePath = `${problem.generatedPath}/holes.json`;
  const parsed = JSON.parse(read(root, relativePath)) as unknown;
  const holes = record(parsed)?.holes;
  if (!Array.isArray(holes)) return Object.freeze([]);
  return Object.freeze(
    holes.flatMap((value) => {
      const hole = record(value);
      const name = text(hole?.name);
      const basename = text(hole?.basename) ?? name?.split('.').at(-1);
      const declarationBody = text(hole?.body);
      if (!name || !basename || !declarationBody) return [];
      const rawKind = text(hole?.kind)?.toLowerCase();
      const kind: LeanEvalAnalyzedHole['kind'] =
        rawKind === 'instance' || (rawKind === 'def' && isInstanceDeclaration(declarationBody))
          ? 'instance'
          : rawKind === 'def' || rawKind === 'definition'
            ? 'definition'
            : rawKind === 'theorem'
              ? 'theorem'
              : 'unknown';
      return [{ name, basename, kind, declarationBody }];
    })
  );
};

const deriveHoles = (
  holes: readonly { name: string; basename: string; kind: LeanEvalAnalyzedHole['kind']; declarationBody: string }[]
): readonly LeanEvalAnalyzedHole[] => {
  const basenames = new Set(holes.map((hole) => hole.basename));
  return Object.freeze(
    holes.map((hole) =>
      Object.freeze({
        ...hole,
        dependsOn: Object.freeze(
          [...basenames].filter((candidate: string) => {
            if (candidate === hole.basename) return false;
            const body = stripLeanTrivia(hole.declarationBody);
            return /^[A-Za-z0-9_]+$/u.test(candidate)
              ? new RegExp(`\\b${escapeRegExp(candidate)}\\b`, 'u').test(body)
              : body.includes(candidate);
          })
        ),
      })
    )
  );
};

/** Convert the official hole ordering/dependencies into a scheduler-ready DAG. */
export function buildLeanEvalHoleDag(holes: readonly LeanEvalAnalyzedHole[]): readonly MathPlanNode[] {
  if (!holes.length) return Object.freeze([]);
  const goal = holes.at(-1)!;
  return Object.freeze(
    holes.map((hole, index) =>
      Object.freeze({
        id: holeNodeId(hole.name),
        informalClaim: `${hole.kind} ${hole.name}`,
        provisionalLeanStatement: hole.declarationBody,
        dependsOn: Object.freeze(
          hole.dependsOn.map((dependency) =>
            holeNodeId(holes.find((candidate) => candidate.basename === dependency)?.name ?? dependency)
          )
        ),
        role:
          hole.name === goal.name
            ? 'goal'
            : hole.kind === 'definition' || hole.kind === 'instance'
              ? 'auxiliary'
              : 'reduction',
        status: 'proposed',
        evidenceRefs: Object.freeze([`lean-eval:${hole.name}`]),
        kind: hole.kind === 'definition' ? 'definition' : hole.kind === 'instance' ? 'api_bridge' : 'theorem',
        estimatedEffort: hole.kind === 'theorem' ? Math.min(5, 2 + index / Math.max(1, holes.length)) : 1,
      })
    )
  );
}

const degeneracySignals = (source: string): readonly string[] => {
  const signals: string[] = [];
  if (/\bTrue\b/u.test(source)) signals.push('contains_true_proposition');
  if (/:=\s*by\s*(?:simp|rfl|trivial)\b/u.test(source)) signals.push('trivial_proof_shape');
  if (/\bNonempty\b|\bInhabited\b/u.test(source)) signals.push('inhabited_or_nonempty_assumption');
  if (/\baxiom\b/u.test(source)) signals.push('declares_axiom');
  return Object.freeze(signals);
};

const toolchainValue = (root: string, problem: LeanEvalCatalogProblem): string | undefined => {
  try {
    return text(read(root, `${problem.generatedPath}/lean-toolchain`));
  } catch {
    return undefined;
  }
};

const dependencyCriticalPath = (holes: readonly LeanEvalAnalyzedHole[]): number => {
  const byName = new Map(holes.map((hole) => [hole.basename, hole]));
  const memo = new Map<string, number>();
  const depth = (name: string, seen = new Set<string>()): number => {
    if (memo.has(name)) return memo.get(name)!;
    if (seen.has(name)) return 0;
    const hole = byName.get(name);
    if (!hole) return 0;
    const next = new Set(seen).add(name);
    const value = 1 + Math.max(0, ...hole.dependsOn.map((dependency) => depth(dependency, next)));
    memo.set(name, value);
    return value;
  };
  return Math.max(0, ...holes.map((hole) => depth(hole.basename)));
};

/** Compile only the public Challenge target; this never loads Solution.lean. */
export async function runLeanEvalCompileProbe(
  problemRoot: string,
  timeoutMs = 30_000
): Promise<Readonly<{ ok: boolean; error?: string }>> {
  return runLeanEvalSandboxedCompileProbe(problemRoot, timeoutMs);
}

/**
 * Compile the public Challenge in a disposable, filtered checkout.  The
 * benchmark checkout is never used as the process cwd and Solution.lean is
 * intentionally excluded from the staged tree.
 */
export async function runLeanEvalSandboxedCompileProbe(
  problemRoot: string,
  timeoutMs = 30_000
): Promise<Readonly<{ ok: boolean; error?: string }>> {
  const resolvedProblemRoot = fs.realpathSync(path.resolve(problemRoot));
  const repositoryRoot = leanRepositoryRoot(resolvedProblemRoot);
  const projectRelative = path.relative(repositoryRoot, resolvedProblemRoot).replaceAll(path.sep, '/');
  if (projectRelative.startsWith('../') || path.isAbsolute(projectRelative)) {
    return Object.freeze({ ok: false, error: 'compile probe problem root is outside the Lean repository' });
  }
  const temporaryRoot = fs.mkdtempSync(path.join(os.tmpdir(), 'deepscientist-lean-probe-'));
  const copyTree = (source: string, destination: string, skipSolution = false, skipLakePackages = false): void => {
    const stat = fs.lstatSync(source);
    if (stat.isSymbolicLink()) throw new Error(`compile probe source contains a symlink: ${source}`);
    if (stat.isDirectory()) {
      // The verifier mounts the trusted package cache read-only. Copying it
      // into every disposable probe and mounting it again doubles startup I/O
      // for Mathlib-sized projects.
      if (skipLakePackages && path.basename(source) === 'packages' && path.basename(path.dirname(source)) === '.lake') {
        return;
      }
      fs.mkdirSync(destination, { recursive: true, mode: 0o700 });
      for (const entry of fs.readdirSync(source).toSorted())
        copyTree(path.join(source, entry), path.join(destination, entry), skipSolution, skipLakePackages);
      return;
    }
    if (!stat.isFile()) return;
    if (skipSolution && path.basename(source) === 'Solution.lean') return;
    fs.mkdirSync(path.dirname(destination), { recursive: true, mode: 0o700 });
    fs.copyFileSync(source, destination);
  };
  try {
    for (const file of ['lean-toolchain', 'lakefile.toml', 'lakefile.lean', 'lake-manifest.json']) {
      const source = path.join(repositoryRoot, file);
      if (fs.existsSync(source)) copyTree(source, path.join(temporaryRoot, file));
    }
    copyTree(resolvedProblemRoot, path.join(temporaryRoot, projectRelative), true, true);
    // Generated Lean-Eval projects do not carry their own manifest. Reuse the
    // pinned benchmark manifest so Lake resolves the mounted package cache
    // instead of attempting a network clone during the probe.
    const temporaryProblemRoot = path.join(temporaryRoot, projectRelative);
    const temporaryManifest = path.join(temporaryProblemRoot, 'lake-manifest.json');
    const repositoryManifest = path.join(repositoryRoot, 'lake-manifest.json');
    if (!fs.existsSync(temporaryManifest) && fs.existsSync(repositoryManifest)) {
      copyTree(repositoryManifest, temporaryManifest);
    }
    const packageCache = (() => {
      const candidate = path.join(repositoryRoot, '.lake', 'packages');
      try {
        if (fs.lstatSync(candidate).isDirectory()) return candidate;
      } catch {
        // Fall through to the pinned runtime cache used by the verifier.
      }
      return resolveMathematicsLakePackagesCache(temporaryProblemRoot, leanEnvironment());
    })();
    fs.mkdirSync(path.join(temporaryRoot, projectRelative, '.lake', 'packages'), { recursive: true, mode: 0o700 });
    const result = await runMathematicsSandboxedCommand({
      checkoutRoot: temporaryRoot,
      projectRelative,
      // Build the Lake target first so local modules such as ChallengeDeps
      // are elaborated into the disposable checkout before the public
      // Challenge target is checked.  Running `lean Challenge.lean` directly
      // would fail with unknown-module errors in a fresh checkout.
      command: 'lake',
      args: ['build', 'Challenge'],
      timeoutMs: Math.max(1_000, Math.min(timeoutMs, 120_000)),
      env: { ...leanEnvironment(), CI: '1' },
      ...(packageCache ? { lakePackagesPath: packageCache } : {}),
    });
    return Object.freeze({
      ok: result.started && result.exitCode === 0 && !result.timedOut && !result.aborted,
      ...(result.started && result.exitCode === 0
        ? {}
        : { error: String(result.stderr || result.errorMessage || 'compile probe failed').slice(0, 4_000) }),
    });
  } catch (error) {
    return Object.freeze({ ok: false, error: error instanceof Error ? error.message : String(error) });
  } finally {
    removeTemporaryTree(temporaryRoot);
  }
}

/**
 * Run a genuine Lean elaborator pass over public Challenge declarations in a
 * disposable filtered checkout.  This complements static declaration
 * inspection without ever materializing or reading Solution.lean.
 */
export async function runLeanEvalSandboxedElaborationProbe(
  problemRoot: string,
  declarations: readonly string[],
  timeoutMs = 30_000,
  dependencyTargets: readonly string[] = []
): Promise<
  Readonly<{
    ok: boolean;
    checkedDeclarationCount?: number;
    declarationDependencies?: Readonly<Record<string, readonly string[]>>;
    error?: string;
  }>
> {
  const resolvedProblemRoot = fs.realpathSync(path.resolve(problemRoot));
  const repositoryRoot = leanRepositoryRoot(resolvedProblemRoot);
  const projectRelative = path.relative(repositoryRoot, resolvedProblemRoot).replaceAll(path.sep, '/');
  if (projectRelative.startsWith('../') || path.isAbsolute(projectRelative)) {
    return Object.freeze({ ok: false, error: 'elaboration probe problem root is outside the Lean repository' });
  }
  const selectedDeclarations = [...new Set(declarations)]
    .filter((name) => /^[\p{L}_][\p{L}\p{M}\p{N}_'.]*$/u.test(name))
    .slice(0, 256);
  if (!selectedDeclarations.length) return Object.freeze({ ok: true, checkedDeclarationCount: 0 });
  const selectedDeclarationSet = new Set(selectedDeclarations);
  const selectedDependencyTargets = [...new Set(dependencyTargets)]
    .filter((name) => selectedDeclarationSet.has(name))
    .slice(0, 64);
  const temporaryRoot = fs.mkdtempSync(path.join(os.tmpdir(), 'deepscientist-lean-elab-'));
  const copyTree = (source: string, destination: string, skipSolution = false, skipLakePackages = false): void => {
    const stat = fs.lstatSync(source);
    if (stat.isSymbolicLink()) throw new Error(`elaboration probe source contains a symlink: ${source}`);
    if (stat.isDirectory()) {
      // See the compile probe above: package sources are mounted by the
      // verifier and should not be copied into every temporary checkout.
      if (skipLakePackages && path.basename(source) === 'packages' && path.basename(path.dirname(source)) === '.lake') {
        return;
      }
      fs.mkdirSync(destination, { recursive: true, mode: 0o700 });
      for (const entry of fs.readdirSync(source).toSorted()) {
        copyTree(path.join(source, entry), path.join(destination, entry), skipSolution, skipLakePackages);
      }
      return;
    }
    if (!stat.isFile() || (skipSolution && path.basename(source) === 'Solution.lean')) return;
    fs.mkdirSync(path.dirname(destination), { recursive: true, mode: 0o700 });
    fs.copyFileSync(source, destination);
  };
  try {
    for (const file of ['lean-toolchain', 'lakefile.toml', 'lakefile.lean', 'lake-manifest.json']) {
      const source = path.join(repositoryRoot, file);
      if (fs.existsSync(source)) copyTree(source, path.join(temporaryRoot, file));
    }
    const temporaryProblemRoot = path.join(temporaryRoot, projectRelative);
    copyTree(resolvedProblemRoot, temporaryProblemRoot, true, true);
    const temporaryManifest = path.join(temporaryProblemRoot, 'lake-manifest.json');
    const repositoryManifest = path.join(repositoryRoot, 'lake-manifest.json');
    if (!fs.existsSync(temporaryManifest) && fs.existsSync(repositoryManifest)) {
      copyTree(repositoryManifest, temporaryManifest);
    }
    const packageCache = (() => {
      const candidate = path.join(repositoryRoot, '.lake', 'packages');
      try {
        if (fs.lstatSync(candidate).isDirectory()) return candidate;
      } catch {
        // Fall through to the pinned runtime cache used by the verifier.
      }
      return resolveMathematicsLakePackagesCache(temporaryProblemRoot, leanEnvironment());
    })();
    fs.mkdirSync(path.join(temporaryProblemRoot, '.lake', 'packages'), { recursive: true, mode: 0o700 });
    const buildResult = await runMathematicsSandboxedCommand({
      checkoutRoot: temporaryRoot,
      projectRelative,
      command: 'lake',
      args: ['build', 'Challenge'],
      timeoutMs: Math.max(1_000, Math.min(timeoutMs, 120_000)),
      env: { ...leanEnvironment(), CI: '1' },
      ...(packageCache ? { lakePackagesPath: packageCache } : {}),
    });
    const buildOk = buildResult.started && buildResult.exitCode === 0 && !buildResult.timedOut && !buildResult.aborted;
    if (!buildOk) {
      return Object.freeze({
        ok: false,
        checkedDeclarationCount: 0,
        error: String(
          buildResult.stderr || buildResult.errorMessage || 'elaboration probe dependency build failed'
        ).slice(0, 4_000),
      });
    }
    const challengeSource = fs.readFileSync(path.join(resolvedProblemRoot, 'Challenge.lean'), 'utf8');
    const depsSource = fs.existsSync(path.join(resolvedProblemRoot, 'ChallengeDeps.lean'))
      ? fs.readFileSync(path.join(resolvedProblemRoot, 'ChallengeDeps.lean'), 'utf8')
      : '';
    const imports = ['import Challenge', 'import Lean'];
    if (fs.existsSync(path.join(resolvedProblemRoot, 'ChallengeDeps.lean'))) imports.push('import ChallengeDeps');
    const namespaceOpens = namespaceNamesFrom(`${depsSource}\n${challengeSource}`).map((name) => `open ${name}`);
    const dependencyCommand = selectedDependencyTargets.length
      ? `
open Lean Elab Command

elab "#deepscientist_deps " declaration:ident : command => do
  let name ← resolveGlobalConstNoOverload declaration
  let info ← getConstInfo name
  let mut dependencies := info.type.getUsedConstants
  if let some value := info.value? (allowOpaque := true) then
    dependencies := dependencies ++ value.getUsedConstants
  let names := dependencies.toList.map (·.toString) |>.mergeSort |>.eraseDups
  logInfo m!"DEEPSCIENTIST_DEPS_BEGIN:{name}\\n{String.intercalate "\\n" names}\\nDEEPSCIENTIST_DEPS_END:{name}"
`
      : '';
    const probeSource = `${imports.join('\n')}\n${namespaceOpens.join('\n')}\n${dependencyCommand}\n${selectedDeclarations
      .map((name) => `#check ${name}`)
      .join('\n')}\n${selectedDependencyTargets.map((name) => `#deepscientist_deps ${name}`).join('\n')}\n`;
    fs.writeFileSync(path.join(temporaryProblemRoot, 'ElaborationProbe.lean'), probeSource, {
      encoding: 'utf8',
      mode: 0o600,
    });
    const result = await runMathematicsSandboxedCommand({
      checkoutRoot: temporaryRoot,
      projectRelative,
      command: 'lake',
      args: ['env', 'lean', 'ElaborationProbe.lean'],
      timeoutMs: Math.max(1_000, Math.min(timeoutMs, 120_000)),
      env: { ...leanEnvironment(), CI: '1' },
      ...(packageCache ? { lakePackagesPath: packageCache } : {}),
    });
    const commandOk = result.started && result.exitCode === 0 && !result.timedOut && !result.aborted;
    const declarationDependencies = commandOk
      ? parseLeanElaborationDependencies(result.stdout, selectedDependencyTargets.length)
      : undefined;
    const dependencyOutputOk = selectedDependencyTargets.length === 0 || declarationDependencies !== undefined;
    const ok = commandOk && dependencyOutputOk;
    return Object.freeze({
      ok,
      checkedDeclarationCount: commandOk ? selectedDeclarations.length : 0,
      ...(declarationDependencies ? { declarationDependencies } : {}),
      ...(!dependencyOutputOk
        ? { error: 'Lean elaboration probe returned an incomplete dependency report' }
        : result.started && result.exitCode === 0
          ? {}
          : { error: String(result.stderr || result.errorMessage || 'elaboration probe failed').slice(0, 4_000) }),
    });
  } catch (error) {
    return Object.freeze({ ok: false, error: error instanceof Error ? error.message : String(error) });
  } finally {
    removeTemporaryTree(temporaryRoot);
  }
}

const parseLeanElaborationDependencies = (
  stdout: string,
  expectedCount: number
): Readonly<Record<string, readonly string[]>> | undefined => {
  if (expectedCount === 0) return Object.freeze({});
  const lines = stdout.split(/\r?\n/u);
  const result: Record<string, readonly string[]> = {};
  for (let index = 0; index < lines.length; index += 1) {
    const begin = /^DEEPSCIENTIST_DEPS_BEGIN:(.+)$/u.exec(lines[index]!.trim());
    if (!begin?.[1]) continue;
    const name = begin[1].trim();
    const dependencies: string[] = [];
    let closed = false;
    for (index += 1; index < lines.length; index += 1) {
      const line = lines[index]!.trim();
      if (line === `DEEPSCIENTIST_DEPS_END:${name}`) {
        closed = true;
        break;
      }
      if (line && /^[\p{L}_][\p{L}\p{M}\p{N}_'.]*$/u.test(line) && line !== name && line !== 'sorryAx') {
        dependencies.push(line);
      }
    }
    if (!closed || Object.hasOwn(result, name)) return undefined;
    result[name] = Object.freeze([...new Set(dependencies)]);
  }
  return Object.keys(result).length === expectedCount ? Object.freeze(result) : undefined;
};

export type LeanEvalStagedCompileProbe = Readonly<{
  attempted: boolean;
  ok: boolean;
  files: readonly Readonly<{ file: string; ok: boolean; error?: string; durationMs: number }>[];
}>;

/** Compile solver-owned files in dependency order and retain per-stage diagnostics. */
export async function runLeanEvalStagedCompileProbe(
  problemRoot: string,
  files: readonly string[] = ['Challenge.lean', 'Submission.lean'],
  timeoutMs = 30_000
): Promise<LeanEvalStagedCompileProbe> {
  const stages: Array<LeanEvalStagedCompileProbe['files'][number]> = [];
  for (const file of files.slice(0, 16)) {
    if (!file || path.posix.isAbsolute(file) || file.split(/[\\/]/u).some((part) => part === '..')) {
      stages.push(
        Object.freeze({ file, ok: false, error: 'compile probe file must be workspace-relative', durationMs: 0 })
      );
      continue;
    }
    const startedAt = Date.now();
    const result = await runLeanEvalLeanProbe({
      workspaceRoot: problemRoot,
      sourceFile: file,
      mode: 'compile',
      timeoutMs: Math.max(1_000, Math.min(timeoutMs, 120_000)),
    });
    stages.push(
      Object.freeze({
        file,
        ok: result.status === 'passed',
        ...(result.status === 'passed'
          ? {}
          : {
              error: String(result.error || result.diagnostics || 'compile probe failed').slice(0, 4_000),
            }),
        durationMs: result.durationMs || Date.now() - startedAt,
      })
    );
  }
  return Object.freeze({
    attempted: stages.length > 0,
    ok: stages.every((stage) => stage.ok),
    files: Object.freeze(stages),
  });
}

/** Analyze a problem using public Challenge/metadata files; Solution.lean is never read. */
export async function analyzeLeanEvalProblem(
  problem: LeanEvalCatalogProblem,
  options: LeanEvalProblemAnalysisOptions
): Promise<LeanEvalProblemAnalysis> {
  const root = fs.realpathSync(path.resolve(options.repositoryRoot));
  const challengePath = `${problem.generatedPath}/Challenge.lean`;
  const challengeSource = read(root, challengePath);
  const depsSource = (() => {
    try {
      return read(root, `${problem.generatedPath}/ChallengeDeps.lean`);
    } catch {
      return '';
    }
  })();
  const challengeSha256 = sha256(challengeSource);
  const depsSha256 = sha256(depsSource);
  const cacheKey = `${root}\0${problem.id}\0${options.benchmarkCommit}`;
  // Custom probes and historical outcomes are caller-specific. Cache only the
  // deterministic public-source analysis and invalidate it by content identity.
  if (!options.compileProbe && !options.elaborationProbe && !options.historicalOutcomes) {
    const cached = problemAnalysisCache.get(cacheKey);
    if (cached && cached.challengeSha256 === challengeSha256 && cached.depsSha256 === depsSha256) {
      problemAnalysisCache.delete(cacheKey);
      problemAnalysisCache.set(cacheKey, cached);
      return cached.value;
    }
    if (cached) problemAnalysisCache.delete(cacheKey);
  }
  const publicSource = `${depsSource}\n${challengeSource}`;
  const imports = importsFrom(publicSource);
  const staticHoles = deriveHoles(parseHoleBodies(root, problem));
  const challengeDeclarations = inspectLeanDeclarations(challengeSource).map((declaration) => declaration.name);
  const dependencyDeclarations = [
    ...new Set([
      ...inspectLeanDeclarations(depsSource).map((declaration) => declaration.name),
      ...declarationNamesFrom(depsSource),
    ]),
  ];
  const staticHoleDependencyDeclarations = Object.freeze(
    Object.fromEntries(
      staticHoles.map((hole) => {
        const body = stripLeanTrivia(hole.declarationBody);
        const references = dependencyDeclarations.filter((declaration) => {
          const basename = declaration.split('.').at(-1) ?? declaration;
          return new RegExp(`\\b${escapeRegExp(basename)}\\b`, 'u').test(body);
        });
        return [hole.name, Object.freeze(references)];
      })
    )
  ) as Readonly<Record<string, readonly string[]>>;
  const noncomputableDeclarationCount = (challengeSource.match(/\bnoncomputable\s+(?:def|instance)/gu) ?? []).length;
  const formalDegeneracySignals = degeneracySignals(challengeSource);
  const toolchain = toolchainValue(root, problem);
  const supported = options.supportedToolchains ?? ['leanprover/lean4:v4.33.0'];
  const toolchainCompatibility =
    toolchain && supported.some((candidate) => toolchain === candidate || toolchain.includes(candidate))
      ? 1
      : toolchain
        ? 0.35
        : 0;
  const compileProbeResult = options.compileProbe
    ? await options.compileProbe(path.join(root, problem.generatedPath))
    : undefined;
  const firstCompileProbe = Object.freeze({
    attempted: Boolean(options.compileProbe),
    ...(compileProbeResult
      ? { ok: compileProbeResult.ok, ...(compileProbeResult.error ? { error: compileProbeResult.error } : {}) }
      : {}),
  });
  const elaborationProbeResult = options.elaborationProbe
    ? await options.elaborationProbe(
        path.join(root, problem.generatedPath),
        [...dependencyDeclarations, ...challengeDeclarations],
        challengeDeclarations
      )
    : undefined;
  const elaborationProbe = options.elaborationProbe
    ? Object.freeze({
        attempted: true,
        ok: elaborationProbeResult?.ok,
        ...(elaborationProbeResult?.checkedDeclarationCount !== undefined
          ? { checkedDeclarationCount: elaborationProbeResult.checkedDeclarationCount }
          : {}),
        ...(elaborationProbeResult?.declarationDependencies
          ? { declarationDependencies: elaborationProbeResult.declarationDependencies }
          : {}),
        ...(elaborationProbeResult?.error ? { error: elaborationProbeResult.error } : {}),
      })
    : undefined;
  const elaboratedDependencies = elaborationProbeResult?.declarationDependencies;
  const dependenciesForHole = (hole: LeanEvalAnalyzedHole): readonly string[] | undefined => {
    if (!elaboratedDependencies) return undefined;
    return Object.entries(elaboratedDependencies).find(
      ([name]) => name === hole.name || name === hole.basename || name.endsWith(`.${hole.basename}`)
    )?.[1];
  };
  const holes = Object.freeze(
    staticHoles.map((hole) => {
      const dependencies = dependenciesForHole(hole);
      if (!dependencies) return hole;
      const dependsOn = staticHoles.flatMap((candidate) =>
        candidate.name === hole.name
          ? []
          : dependencies.some(
                (name) =>
                  name === candidate.name || name === candidate.basename || name.endsWith(`.${candidate.basename}`)
              )
            ? [candidate.basename]
            : []
      );
      return Object.freeze({ ...hole, dependsOn: Object.freeze([...new Set(dependsOn)]) });
    })
  );
  const dependencyDeclarationSet = new Set(dependencyDeclarations);
  const dependencyDeclarationsByBasename = new Map<string, string[]>();
  for (const declaration of dependencyDeclarations) {
    const basename = declaration.split('.').at(-1) ?? declaration;
    const entries = dependencyDeclarationsByBasename.get(basename) ?? [];
    entries.push(declaration);
    dependencyDeclarationsByBasename.set(basename, entries);
  }
  const canonicalDependencyReference = (name: string): string | undefined => {
    if (dependencyDeclarationSet.has(name)) return name;
    const matches = dependencyDeclarationsByBasename.get(name.split('.').at(-1) ?? name);
    return matches?.length === 1 ? matches[0] : undefined;
  };
  const holeDependencyDeclarations = Object.freeze(
    Object.fromEntries(
      holes.map((hole) => {
        const dependencies = dependenciesForHole(hole);
        const references = dependencies
          ? dependencies.flatMap((name) => {
              const canonical = canonicalDependencyReference(name);
              return canonical ? [canonical] : [];
            })
          : (staticHoleDependencyDeclarations[hole.name] ?? []);
        return [hole.name, Object.freeze([...new Set(references)])];
      })
    )
  ) as Readonly<Record<string, readonly string[]>>;
  assertLeanEvalHoleDagAcyclic(
    holes.map((hole) => ({ name: hole.name, basename: hole.basename, kind: hole.kind, dependsOn: hole.dependsOn }))
  );
  const definitions = holes.filter((hole) => hole.kind === 'definition' || hole.kind === 'instance').length;
  const sourceAvailability = Number(Boolean(problem.source || problem.notes || problem.informalSolution));
  const relatedAvailability = imports.filter((item) => item.startsWith('Mathlib.')).length > 0 ? 0.65 : 0.2;
  const declarationCount = inspectLeanDeclarations(publicSource).length;
  const quantifierDepth = Math.min(12, (publicSource.match(/(?:\u2200|\bforall\b|\bexists\b)/gu) ?? []).length);
  const typeclassDepth = (publicSource.match(/\[[^\]\n]{1,200}\]/gu) ?? []).length;
  const mathlibApiCoverage = imports.length
    ? bounded(imports.filter((item) => item.startsWith('Mathlib')).length / imports.length)
    : 0;
  const feasibility: MathFeasibilitySignals = Object.freeze({
    candidateId: problem.id,
    acceptedCreditCount: problem.acceptedCreditCount,
    holeCount: holes.length,
    importCoverage: bounded(
      imports.length === 0
        ? 0
        : Math.min(
            1,
            imports.filter((item) => item.startsWith('Mathlib')).length / Math.max(1, Math.min(8, imports.length))
          )
    ),
    literatureAvailability: sourceAvailability,
    relatedFormalizationAvailability: relatedAvailability,
    definitionSurface: bounded(definitions / Math.max(1, holes.length)),
    missingFoundationDepth: bounded(1 - Math.min(1, imports.length / 8)),
    formalDegeneracyPotential: bounded(formalDegeneracySignals.length / 3),
    firstMilestoneCost: bounded((holes.length + definitions * 2) / 20),
    toolchainCompatibility,
    benchmarkCommit: options.benchmarkCommit,
    statementRevision: problem.statementRevision,
    active: problem.status === 'active',
    visible: problem.visible,
    inV1: problem.activeV1,
    evidenceSource:
      'lean-eval:public-catalog+source-syntax; import/foundation/related-formalization values are uncalibrated proxies, not verified coverage',
    evidenceFreshAt: problem.catalogEvidence.generatedAt,
    declarationCount,
    declarationSize: challengeSource.length,
    quantifierDepth,
    typeclassDepth,
    dependencyCriticalPath: dependencyCriticalPath(holes),
    mathlibApiCoverage,
    ...(options.historicalOutcomes
      ? {
          historicalAttempts: options.historicalOutcomes.attempts,
          historicalSuccesses: options.historicalOutcomes.successes,
        }
      : {}),
  });
  const analysis = Object.freeze({
    problemId: problem.id,
    benchmarkCommit: options.benchmarkCommit,
    challengePath,
    challengeSha256,
    imports,
    challengeDependencyDeclarations: Object.freeze(dependencyDeclarations),
    holeDependencyDeclarations,
    holes,
    holeDag: buildLeanEvalHoleDag(holes),
    holeSchedule: scheduleLeanEvalHoles(
      holes.map((hole) => ({ name: hole.name, basename: hole.basename, kind: hole.kind, dependsOn: hole.dependsOn }))
    ),
    noncomputableDeclarationCount,
    formalDegeneracySignals,
    firstCompileProbe,
    ...(elaborationProbe ? { elaborationProbe } : {}),
    feasibility,
  });
  if (!options.compileProbe && !options.elaborationProbe && !options.historicalOutcomes) {
    problemAnalysisCache.set(cacheKey, { challengeSha256, depsSha256, value: analysis });
    while (problemAnalysisCache.size > MAX_PROBLEM_ANALYSIS_CACHE) {
      const oldest = problemAnalysisCache.keys().next().value;
      if (oldest === undefined) break;
      problemAnalysisCache.delete(oldest);
    }
  }
  return analysis;
}
