/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

import crypto from 'node:crypto';
import { resolveMathRunHistory } from "./mathRunHistory";
import { inspectLeanDeclarationRegions, inspectLeanDeclarations, stripLeanComments } from "./verifier";
import type { LeanEvalLeanProbeResult } from "./leanEvalLeanProbe";
import type { MathProofActionKind, MathProofState } from "../common/types/team/mathematicsTeam";
import type {
  MathematicsLeanProofSession,
  MathematicsLeanSessionActionResult,
  MathematicsLeanSessionSnapshot,
} from "./leanInteractiveSession";
import {
  actionContextKey,
  appendLeanEvalActionRecords,
  leanGoalShape,
  readLeanEvalActionPerformance,
  type LeanEvalActionRecordInput,
  type LeanEvalActionPerformanceSummary,
} from "./leanEvalActionLedger";
import { scoreInstalledPremiseForGoal } from "./installedPackageSearch";

const DEFAULT_BEAM_WIDTH = 2;
const MAX_BEAM_WIDTH = 4;
const splitLeanSourceLines = (value: string): string[] => value.split(/\r\n|\n|\r/u);

export type LeanProofActionCandidate = Readonly<{
  kind: MathProofActionKind;
  payload: string;
  source: string;
  file?: string;
  /** Optional runtime hint used only as a tie-breaker. */
  helperProduced?: boolean;
  candidateId?: string;
  provenance?: Readonly<{
    source: 'frozen-corpus' | 'local';
    declarationName: string;
    declarationType: string;
    packageName?: string;
    packageRevision?: string;
    sourceModule?: string;
    sourceFile?: string;
    providerRank?: number;
    corpusDigest?: string;
  }>;
}>;

export type LeanProofActionBranch = Readonly<{
  candidate: LeanProofActionCandidate;
  result: MathematicsLeanSessionActionResult;
  state?: MathProofState;
  score: number;
  retained: boolean;
}>;

export type LeanProofExecutedAttempt = Readonly<{
  startedAt: string;
  recordedAt: string;
  candidate: LeanProofActionCandidate;
  result: MathematicsLeanSessionActionResult;
  baseState: MathProofState;
  goalIndex: number;
  goalFingerprint: string;
}>;

export type LeanProofRecoveredAttempt = Readonly<{
  candidate: LeanProofActionCandidate;
  preconditionSourceHash: string;
  preconditionGoalFingerprint: string;
  outcome: string;
  snapshot?: MathematicsLeanSessionSnapshot;
  capabilityAdded?: boolean;
}>;

export type LeanProofActionSearchResult = Readonly<{
  localClosure?: import("./mathLocalClosure").MathLocalClosureDiagnostic;
  status: 'completed' | 'unavailable' | 'no_candidates';
  executionDisposition: LeanEvalLeanProbeResult['executionDisposition'];
  batchComplete: boolean;
  nextCandidateIndex: number;
  baseState: MathProofState;
  branches: readonly LeanProofActionBranch[];
  executedAttempts: readonly LeanProofExecutedAttempt[];
  best?: LeanProofActionBranch;
  durationMs: number;
}>;

export function classifyLeanProofDiagnostic(diagnostics: string): string {
  if (/unknown (?:identifier|constant)|unknown namespace/iu.test(diagnostics)) return 'unknown_identifier';
  if (/type mismatch|application type mismatch/iu.test(diagnostics)) return 'type_mismatch';
  if (/failed to synthesize|synthesiz.*instance/iu.test(diagnostics)) return 'instance_synthesis_failed';
  if (/unsolved goals/iu.test(diagnostics)) return 'unsolved_goals';
  return diagnostics.trim() ? 'compiler_error' : 'none';
}

/** linarith (and nlinarith) proves a plain relation target or refutes
 * relational hypotheses, which closes any target but a trivial `True`. */
export function linarithCanUseGoal(goal: string): boolean {
  const parts = goal.split(/⊢|\|-/u);
  const target = parts.at(-1)?.trim() ?? '';
  const relation = /[=≠≤≥<>]/u;
  if (relation.test(target) && !/∀|∃|∧|∨|↔|→|->|\b(?:Exists|And|Or|Iff)\b/u.test(target)) return true;
  return target !== 'True' && relation.test(parts.slice(0, -1).join('\n'));
}

/**
 * Produce conservative local actions when no external structured-search
 * backend is available. These are deliberately generic; Lean probe decides
 * whether any action is useful for the current goal.
 */
type LeanProofCandidateGenerationInput = Readonly<{
  source: string;
  openGoal?: string;
  failureCategory?: string;
  preferredTactic?: string;
  /** Lean's one-based diagnostic line for the active proof. */
  targetLine?: number;
  targetRange?: LeanEvalLeanProbeResult['sourceRange'];
  premises?: readonly Readonly<{ name: string; type: string }>[];
  excludedPremiseNames?: readonly string[];
  /** Batch pagination never discards the remaining candidate pool. */
  candidateOffset?: number;
  candidateBatchSize?: number;
  goalIndex?: number;
  diagnostics?: string;
}>;

function generateLeanProofCandidates(
  input: Readonly<{
    source: string;
    openGoal?: string;
    failureCategory?: string;
    preferredTactic?: string;
    /** Lean's one-based diagnostic line for the active proof. */
    targetLine?: number;
    targetRange?: LeanEvalLeanProbeResult['sourceRange'];
    premises?: readonly Readonly<{ name: string; type: string }>[];
    excludedPremiseNames?: readonly string[];
    /** Batch pagination never discards the remaining candidate pool. */
    candidateOffset?: number;
    candidateBatchSize?: number;
    goalIndex?: number;
    diagnostics?: string;
  }>,
  mode: 'generic' | 'premises'
): readonly LeanProofActionCandidate[] {
  const newline = input.source.includes('\r\n') ? '\r\n' : input.source.includes('\r') ? '\r' : '\n';
  if (!input.openGoal?.trim()) {
    const lines = splitLeanSourceLines(input.source);
    const index = (input.targetLine ?? input.targetRange?.start.line ?? 0) - 1;
    const line = lines[index];
    if (!line || !input.diagnostics?.trim()) return Object.freeze([]);
    // Repair only a failing proof tactic, never a declaration's statement or imports.
    const tacticLine =
      /^(\s+)(?:exact\?|exact|apply|rw|simp|simpa|aesop|refine|assumption|norm_num|omega|linarith|nlinarith|ring_nf|positivity)\b/u.exec(
        line
      );
    const inline =
      /(:=\s*by)\s+(?:exact\?|exact|apply|rw|simp|simpa|aesop|refine|assumption|norm_num|omega|linarith|nlinarith|ring_nf|positivity)\b/u.exec(
        line
      );
    const prefix = tacticLine?.[1] ?? (inline ? line.slice(0, inline.index + inline[1]!.length) + ' ' : undefined);
    if (prefix === undefined) return Object.freeze([]);
    const repairs = [
      ...new Set(
        mode === 'premises'
          ? (input.premises ?? []).map((premise) => `exact ${premise.name}`)
          : ['assumption', 'rfl', 'simp', 'aesop']
      ),
    ];
    return Object.freeze(
      repairs.map((payload) => ({
        kind: 'tactic' as const,
        payload,
        source: [...lines.slice(0, index), `${prefix}${payload}`, ...lines.slice(index + 1)].join(newline),
      }))
    );
  }
  const tactics = new Set<string>();
  if (mode === 'generic' && input.preferredTactic?.trim()) tactics.add(input.preferredTactic.trim());
  const goal = input.openGoal;
  const target =
    goal
      .split(/(?:⊢|\|-)/u)
      .at(-1)
      ?.trim() ?? goal;
  const locals = goal.split('\n').flatMap((line) => {
    const match = /^\s*([\p{L}\p{N}_' ]+)\s*:\s*(.+)$/u.exec(line);
    return match
      ? match[1]!
          .trim()
          .split(/\s+/u)
          .map((name) => ({ name, type: match[2]!.trim() }))
      : [];
  });
  const contextual = new Set<string>();
  for (const local of mode === 'generic' ? locals : []) {
    if (local.type.replace(/\s+/gu, '') === target.replace(/\s+/gu, '')) contextual.add(`exact ${local.name}`);
    if (/=|↔/u.test(local.type)) {
      contextual.add(`rw [${local.name}]`);
      contextual.add(`rw [← ${local.name}]`);
    }
    if (/∨|\bOr\b|∧|\bAnd\b/u.test(local.type)) contextual.add(`cases ${local.name}`);
    if (/→|->|∀/u.test(local.type)) contextual.add(`apply ${local.name}`);
    if (/^(?:Nat|ℕ)$/u.test(local.type)) contextual.add(`induction ${local.name}`);
    if (/^(?:∃|Exists\b)/u.test(target)) contextual.add(`refine ⟨${local.name}, ?_⟩`);
  }
  if (mode === 'generic' && /^(?:∀|.*(?:→|->))/u.test(target)) contextual.add('intro');
  if (mode === 'generic' && /\bAnd\b|∧/u.test(target)) contextual.add('constructor');
  if (mode === 'generic' && /\bExists\b|∃/u.test(target)) tactics.add('constructor');
  // Offer polynomial normalization only for an equality with arithmetic structure
  // and an existing import known to provide ring. Lean still decides applicability.
  const importedModules = [...stripLeanComments(input.source).matchAll(/^[ \t]*import[ \t]+([^\r\n]+)/gmu)].flatMap(
    ([, modules]) => modules!.split(/\s+/u)
  );
  const hasRingImport = importedModules.some((module) =>
    /^(?:Mathlib|Mathlib\.Tactic|Mathlib\.Tactic\.Ring(?:\..+)?)$/u.test(module)
  );
  if (mode === 'generic' && hasRingImport && /=/u.test(target) && /[+*^-]/u.test(target)) tactics.add('ring');
  const hasLinarithImport = importedModules.some((module) =>
    /^(?:Mathlib|Mathlib\.Tactic|Mathlib\.Tactic\.Linarith(?:\.Frontend)?)$/u.test(module)
  );
  const relationTarget = /[=≠≤≥<>]/u.test(target) && !/∀|∃|∧|∨|↔|→|->|\b(?:Exists|And|Or|Iff)\b/u.test(target);
  // Arithmetic closure can combine hypotheses that simplification cannot. Try
  // it before general search when the existing imports provide the tactic; the
  // generic pool below still offers it later for other arithmetic goals.
  // nlinarith only adds products and squares of hypotheses, so it can succeed
  // where linarith fails only when the goal context has a nonlinear term.
  // Multiplication by a constant can also trigger it; Lean decides whether
  // its stronger arithmetic procedure is useful, without changing the statement.
  const nonlinearContext = /[*^/]|⁻¹/u.test(goal);
  if (mode === 'generic' && hasLinarithImport && relationTarget) {
    tactics.add('linarith');
    if (nonlinearContext) tactics.add('nlinarith');
  }
  if (mode === 'generic' && /=|\u2260|\u003c|\u003e|\u2264|\u2265|[+*^\-/]/u.test(goal)) {
    tactics.add('simp');
    // Keep the cheap closed-arithmetic pass in the generic pool. The
    // failure-category fallback may not run when a structured route is absent.
    // Imports only order the tier above: indirect imports can still provide it.
    tactics.add('norm_num');
    if (linarithCanUseGoal(goal)) {
      tactics.add('linarith');
      if (nonlinearContext) tactics.add('nlinarith');
    }
    tactics.add('ring_nf');
  }
  if (mode === 'generic' && /\u003c|\u003e|\u2264|\u2265/u.test(goal)) tactics.add('positivity');
  if (mode === 'generic' && /\b(?:Nat|Int)\b|ℕ|ℤ/u.test(goal)) tactics.add('omega');
  if (mode === 'generic' && /\/|⁻¹|\b(?:Inv|Div)\b/u.test(goal)) tactics.add('field_simp');
  // Propositional closure is deterministic and kernel-checked, so expose it
  // to the bounded fallback beside constructor/intro actions.
  if (mode === 'generic' && /(?:→|->|↔|\bIff\b|∧|\bAnd\b|∨|\bOr\b|¬|\bNot\b)/u.test(goal)) tactics.add('tauto');
  if (mode === 'generic' && /(?:\bFalse\b|⊥)/u.test(goal)) tactics.add('contradiction');
  switch (mode === 'generic' ? input.failureCategory : undefined) {
    case 'unknown_identifier':
    case 'instance_synthesis_failed':
      tactics.add('simp');
      tactics.add('aesop');
      break;
    case 'type_mismatch':
      tactics.add('simpa');
      tactics.add('exact?');
      break;
    case 'unsolved_goals':
      tactics.add('aesop');
      tactics.add('norm_num');
      tactics.add('omega');
      break;
    default:
      tactics.add('simp');
      tactics.add('aesop');
  }
  if (mode === 'generic') {
    tactics.add('simp_all');
    tactics.add('assumption');
    tactics.add('rfl');
  }
  const source = /(?:\r\n|\n|\r)$/u.test(input.source) ? input.source : `${input.source}${newline}`;
  const lines = splitLeanSourceLines(source);
  const targetLine = input.targetRange?.start.line ?? input.targetLine;
  const start = targetLine === undefined ? undefined : targetLine - 1;
  // Insert into the reported declaration's tactic block, before a following
  // declaration or namespace end. Without a location, only use the legacy EOF.
  const proofStart =
    start !== undefined && start >= 0 && start < lines.length
      ? lines.findLastIndex((line, index) => index <= start && /\bby\b/u.test(line.split('--')[0]!))
      : -1;
  let insertion = lines.length - 1;
  let indent = '  ';
  if (proofStart >= 0) {
    const baseIndent = lines[proofStart]!.match(/^\s*/u)?.[0].length ?? 0;
    const declarationColumn = [
      ...lines[proofStart]!.matchAll(/\b(?:theorem|lemma|example|def|abbrev|instance)\b/gu),
    ].at(-1)?.index;
    // Lean's offside rule uses the declaration token, which can follow an
    // inline block comment. Indenting from column zero would emit a command
    // instead of a tactic in that case.
    indent = ' '.repeat(Math.max(baseIndent + 2, declarationColumn === undefined ? 0 : declarationColumn + 2));
    for (let index = proofStart + 1; index < lines.length; index += 1) {
      if (lines[index]!.trim() && (lines[index]!.match(/^\s*/u)?.[0].length ?? 0) <= baseIndent) {
        insertion = index;
        break;
      }
    }
  }
  // A nested `have ... := by` or a multiline header makes the nearest `by`
  // occur inside the active declaration. Retrieve only declarations preceding
  // that declaration, rather than treating its unfinished statement as a fact.
  const targetColumn = input.targetRange?.start.column;
  const targetOffset =
    start !== undefined && start >= 0 && start < lines.length
      ? lines.slice(0, start).reduce((offset, line) => offset + line.length + newline.length, 0) +
        (targetColumn !== undefined && targetColumn >= 0 && targetColumn <= lines[start]!.length
          ? targetColumn
          : lines[start]!.length)
      : undefined;
  const activeDeclaration =
    targetOffset === undefined
      ? undefined
      : inspectLeanDeclarationRegions(source).findLast(
          (declaration) => declaration.startOffset <= targetOffset && targetOffset < declaration.endOffset
        );
  const prefix = activeDeclaration
    ? source.slice(0, activeDeclaration.startOffset)
    : lines.slice(0, Math.max(0, proofStart)).join(newline);
  const excluded = new Set((input.excludedPremiseNames ?? []).flatMap((name) => [name, name.split('.').at(-1)!]));
  const goalTokens = new Set(target.match(/[\p{L}\p{N}_]+/gu) ?? []);
  const premises = [
    ...(input.premises ?? []).map((premise) => ({ name: premise.name, type: premise.type, priority: 0 })),
    ...(mode === 'generic'
      ? inspectLeanDeclarations(prefix).map((declaration) => ({
          name: declaration.name,
          type: declaration.declarationType,
          // Definitions can contain proof values, so retain them after named
          // theorems instead of guessing propositionhood from a type string.
          priority: declaration.kind === 'theorem' ? 1 : 2,
        }))
      : []),
  ]
    .filter(
      (premise) =>
        /^[\p{L}_][\p{L}\p{N}_'.]*$/u.test(premise.name) &&
        !excluded.has(premise.name) &&
        !excluded.has(premise.name.split('.').at(-1)!)
    )
    .map((premise) => ({
      name: premise.name,
      type: premise.type,
      priority: premise.priority,
      score:
        scoreInstalledPremiseForGoal({ declarationName: premise.name, declarationType: premise.type }, target) +
        (premise.type.match(/[\p{L}\p{N}_]+/gu) ?? []).filter((token) => goalTokens.has(token)).length,
    }))
    .toSorted((a, b) => a.priority - b.priority || b.score - a.score);
  const premiseActions = new Set<string>();
  const fallbackPremiseActions = new Set<string>();
  for (const premise of premises) {
    const actions = premise.priority === 2 ? fallbackPremiseActions : premiseActions;
    actions.add(`exact ${premise.name}`);
    actions.add(`apply ${premise.name}`);
  }
  const rangedEnd = input.targetRange?.end;
  const rangeLine = rangedEnd ? lines[rangedEnd.line - 1] : undefined;
  const rangeOffset =
    rangedEnd && rangeLine !== undefined && rangedEnd.column >= 0 && rangedEnd.column <= rangeLine.length
      ? lines.slice(0, rangedEnd.line - 1).reduce((sum, line) => sum + line.length + newline.length, 0) +
        rangedEnd.column
      : undefined;
  const groups = mode === 'premises' ? [[...premiseActions]] : [[...contextual], [...tactics], [...premiseActions]];
  const diverse: string[] = [];
  for (let index = 0; groups.some((group) => index < group.length); index += 1) {
    for (const group of groups) {
      const action = group[index];
      if (action && !diverse.includes(action)) diverse.push(action);
    }
  }
  // Automatically indexed data declarations must not crowd out ordinary
  // closure tactics. Keep every fallback available to subsequent pages.
  for (const action of fallbackPremiseActions) {
    if (!diverse.includes(action)) diverse.push(action);
  }
  const offset = input.candidateOffset ?? 0;
  const candidates = diverse.slice(
    offset,
    input.candidateBatchSize === undefined ? undefined : offset + input.candidateBatchSize
  );
  return Object.freeze(
    candidates.map((tactic) =>
      Object.freeze({
        kind: (tactic.startsWith('rw ')
          ? 'rewrite'
          : tactic.startsWith('induction ')
            ? 'induction'
            : tactic.startsWith('exact ') || tactic.startsWith('apply ')
              ? 'premise'
              : 'tactic') as MathProofActionKind,
        payload: tactic,
        source: (() => {
          const action = input.goalIndex ? `rotate_left ${input.goalIndex}${newline}${indent}${tactic}` : tactic;
          return rangeOffset !== undefined
            ? `${source.slice(0, rangeOffset)}${newline}${indent}${action}${newline}${source.slice(rangeOffset)}`
            : [...lines.slice(0, insertion), `${indent}${action}`, ...lines.slice(insertion)].join(newline);
        })(),
        file: 'Submission.lean',
      })
    )
  );
}

export function generateLeanProofActionCandidates(
  input: LeanProofCandidateGenerationInput
): readonly LeanProofActionCandidate[] {
  return generateLeanProofCandidates(input, 'generic');
}

/** Build only exact/apply instances for host-retrieved premises using the shared source insertion path. */
export function generateLeanPremiseActionCandidates(
  input: LeanProofCandidateGenerationInput & {
    premises: readonly Readonly<{ name: string; type: string }>[];
  }
): readonly LeanProofActionCandidate[] {
  const premiseByName = new Map<string, Readonly<{ name: string; type: string }>>();
  for (const premise of input.premises) {
    if (!premiseByName.has(premise.name)) premiseByName.set(premise.name, premise);
  }
  return Object.freeze(
    generateLeanProofCandidates(input, 'premises').map((candidate) => {
      const declarationName = /^(?:exact|apply)\s+(.+)$/u.exec(candidate.payload)?.[1];
      const premise = declarationName ? premiseByName.get(declarationName) : undefined;
      return premise
        ? Object.freeze({
            ...candidate,
            provenance: Object.freeze({
              source: 'frozen-corpus' as const,
              declarationName: premise.name,
              declarationType: premise.type,
              ...('packageName' in premise && typeof premise.packageName === 'string'
                ? { packageName: premise.packageName }
                : {}),
              ...('packageRevision' in premise && typeof premise.packageRevision === 'string'
                ? { packageRevision: premise.packageRevision }
                : {}),
              ...('sourceModule' in premise && typeof premise.sourceModule === 'string'
                ? { sourceModule: premise.sourceModule }
                : {}),
              ...('sourceFile' in premise && typeof premise.sourceFile === 'string'
                ? { sourceFile: premise.sourceFile }
                : {}),
              ...('providerRank' in premise && typeof premise.providerRank === 'number'
                ? { providerRank: premise.providerRank }
                : {}),
              ...('corpusDigest' in premise && typeof premise.corpusDigest === 'string'
                ? { corpusDigest: premise.corpusDigest }
                : {}),
            }),
          })
        : candidate;
    })
  );
}

type BranchMutable = {
  candidate: LeanProofActionCandidate;
  result: MathematicsLeanSessionActionResult;
  state?: MathProofState;
  score: number;
  retained: boolean;
  usable: boolean;
  snapshot: MathematicsLeanSessionSnapshot;
};

type ActionMethod =
  | 'runTactic'
  | 'applyPremise'
  | 'rewrite'
  | 'construct'
  | 'cases'
  | 'induction'
  | 'helper'
  | 'importModule';

const methodFor = (kind: MathProofActionKind): ActionMethod => {
  switch (kind) {
    case 'premise':
      return 'applyPremise';
    case 'rewrite':
      return 'rewrite';
    case 'constructor':
      return 'construct';
    case 'cases':
      return 'cases';
    case 'induction':
      return 'induction';
    case 'helper':
      return 'helper';
    case 'import':
      return 'importModule';
    case 'tactic':
    default:
      return 'runTactic';
  }
};

const candidateKey = (state: MathProofState, candidate: LeanProofActionCandidate): string =>
  `${state.sourceHash}\u0000${state.goalFingerprint}\u0000${candidate.kind}\u0000${candidate.payload.trim()}\u0000${crypto.createHash('sha256').update(candidate.source).digest('hex')}`;

/** Candidate evidence is usable only when source, state, feedback, scope, and environment agree. */
export function isUsableCandidateResult(
  session: MathematicsLeanProofSession,
  base: MathProofState,
  candidate: LeanProofActionCandidate,
  result: MathematicsLeanSessionActionResult
): boolean {
  const outcome = result.underlyingStatus ?? result.status;
  if (
    result.executionDisposition === 'aborted' ||
    result.executionDisposition === 'timed_out' ||
    result.executionDisposition === 'unavailable' ||
    outcome === 'unavailable' ||
    outcome === 'invalid' ||
    outcome === 'failed' ||
    (result.status === 'duplicate' && !result.cacheHit)
  )
    return false;
  const state = result.state;
  if (!state || state.status === 'failed') return false;
  const candidateSourceHash = crypto.createHash('sha256').update(candidate.source).digest('hex');
  if (
    state.sourceHash !== candidateSourceHash ||
    state.statementHash !== base.statementHash ||
    state.routeFingerprint !== base.routeFingerprint ||
    state.sourceFile !== base.sourceFile
  )
    return false;
  const feedback = session.readStateFeedback(state.stateId);
  return Boolean(
    feedback &&
    feedback.state.stateId === state.stateId &&
    feedback.state.sourceHash === candidateSourceHash &&
    feedback.sourceText === candidate.source &&
    feedback.environmentFingerprint &&
    session.environmentFingerprint &&
    feedback.environmentFingerprint === session.environmentFingerprint
  );
}

const scoreBranch = (
  base: MathProofState,
  candidate: LeanProofActionCandidate,
  result: MathematicsLeanSessionActionResult,
  history: LeanEvalActionPerformanceSummary | undefined,
  failureCategory: string | undefined,
  goalIndex = 0,
  usable = true
): number => {
  if (!usable) return -10_000;
  const state = result.state;
  if (!state) return -5_000;
  if ((result.underlyingStatus ?? result.status) === 'failed' || state.status === 'failed') return -1_000;
  let score = 0;
  if ((result.underlyingStatus ?? result.status) === 'advanced') score += 100;
  if (state.status === 'closed') score += 10_000;
  if (state.openGoals.length < base.openGoals.length)
    score += 100 * Math.log2(1 + base.openGoals.length - state.openGoals.length);
  if ((result.underlyingStatus ?? result.status) === 'advanced' && state.goalFingerprint !== base.goalFingerprint)
    score += 100;
  if (candidate.helperProduced || candidate.kind === 'helper') score += 25;
  if (result.capabilityAdded) score += 25;
  // Historical action performance is deliberately a small tie-break. Lean's
  // current kernel result remains authoritative, and unseen actions retain a
  // neutral score so exploration is never disabled by stale history.
  if (history) {
    const tactic = candidate.payload.trim();
    const context =
      history.byContext[actionContextKey(leanGoalShape(base.openGoals[goalIndex]), failureCategory, tactic)];
    const global = history.byTactic[tactic];
    const bucket = context?.attempts ? context : global;
    if (bucket) {
      const posterior = (bucket.advances + 1) / (bucket.attempts + 2);
      const reductionRate = Math.min(1, bucket.goalReductions / Math.max(1, bucket.attempts));
      const errorRate = Math.min(1, bucket.errorImprovements / Math.max(1, bucket.attempts));
      score += (posterior - 0.5) * 8 + reductionRate * 2 + errorRate;
    }
  }
  // Prefer smaller source changes when semantic progress ties.
  score -= Math.min(100, Math.floor(Buffer.byteLength(candidate.source, 'utf8') / 1024));
  return score;
};

const historicalPriority = (
  base: MathProofState,
  candidate: LeanProofActionCandidate,
  history: LeanEvalActionPerformanceSummary | undefined,
  failureCategory: string | undefined,
  goalIndex = 0
): number => {
  if (!history) return 0;
  const tactic = candidate.payload.trim();
  const context =
    history.byContext[actionContextKey(leanGoalShape(base.openGoals[goalIndex]), failureCategory, tactic)];
  const global = history.byTactic[tactic];
  const bucket = context?.attempts ? context : global;
  if (!bucket) return 0;
  const posterior = (bucket.advances + 1) / (bucket.attempts + 2);
  const reductionRate = Math.min(1, bucket.goalReductions / Math.max(1, bucket.attempts));
  const errorRate = Math.min(1, bucket.errorImprovements / Math.max(1, bucket.attempts));
  return (posterior - 0.5) * 8 + reductionRate * 2 + errorRate;
};

const invoke = async (
  session: MathematicsLeanProofSession,
  candidate: LeanProofActionCandidate,
  signal?: AbortSignal,
  timeoutMs?: number
): Promise<MathematicsLeanSessionActionResult> => {
  const method = methodFor(candidate.kind);
  return session[method](candidate.payload, candidate.source, signal, timeoutMs);
};

/**
 * Evaluate a bounded action beam from one source-backed state. Every branch is
 * restored to the same base snapshot before execution; only the best retained
 * branch is left current when the search returns.
 */
export async function searchLeanProofActions(
  input: Readonly<{
    session: MathematicsLeanProofSession;
    candidates: readonly LeanProofActionCandidate[];
    beamWidth?: number;
    /** Keep the session at its base state when the caller will commit the best action itself. */
    commitBest?: boolean;
    signal?: AbortSignal;
    /** One shared deadline for synchronization, replay, and candidate probes. */
    timeoutMs?: number;
    /** Optional persistent action-feedback context. Telemetry is best-effort. */
    performanceRoot?: string;
    episodeId?: string;
    problemId?: string;
    failureCategory?: string;
    goalIndex?: number;
    /** One resumable lookahead wave; callers may continue any retained branch. */
    lookahead?: boolean;
    /** Explicit candidates retain caller order instead of advisory history ordering. */
    preserveOrder?: boolean;
    onAttempt?: (attempt: LeanProofExecutedAttempt) => void;
    recoveredAttempts?: readonly LeanProofRecoveredAttempt[];
    retainForOperation?: (stateId: string) => void;
  }>
): Promise<LeanProofActionSearchResult> {
  const deadlineAt = input.timeoutMs === undefined ? undefined : performance.now() + Math.max(0, input.timeoutMs);
  const remainingTimeoutMs = (): number | undefined =>
    deadlineAt === undefined ? undefined : Math.max(0, deadlineAt - performance.now());
  const refreshed = await input.session.synchronizeSource(
    input.session.snapshot().sourceText,
    input.signal,
    remainingTimeoutMs()
  );
  const baseSnapshot = input.session.snapshot();
  const baseState = baseSnapshot.state;
  const goalIndex = input.goalIndex ?? 0;
  const selectedGoal = baseState.openGoals[goalIndex];
  const originalLocation = input.session.goalLocation(goalIndex) ?? { line: input.session.goalLine };
  const goalFingerprint = selectedGoal
    ? crypto.createHash('sha256').update(selectedGoal).digest('hex')
    : baseState.goalFingerprint;
  const executedAttempts: LeanProofExecutedAttempt[] = [];
  if (refreshed.status === 'invalid' || refreshed.status === 'unavailable')
    return Object.freeze({
      status: 'unavailable',
      executionDisposition: refreshed.executionDisposition ?? 'unavailable',
      batchComplete: false,
      nextCandidateIndex: 0,
      baseState,
      branches: Object.freeze([]),
      executedAttempts: Object.freeze([]),
      durationMs: refreshed.durationMs ?? 0,
    });
  const historyScope = input.performanceRoot
    ? resolveMathRunHistory(input.performanceRoot, input.problemId)
    : undefined;
  const performanceRoot = historyScope?.root;
  const recordScope = historyScope?.runIdentity
    ? { runIdentity: historyScope.runIdentity, problemId: input.problemId! }
    : undefined;
  if (!input.candidates.length) {
    return Object.freeze({
      status: 'no_candidates',
      executionDisposition: 'completed',
      batchComplete: true,
      nextCandidateIndex: 0,
      baseState,
      branches: Object.freeze([]),
      executedAttempts: Object.freeze([]),
      durationMs: refreshed.durationMs ?? 0,
    });
  }
  const releaseBaseState = input.session.retainState(baseState.stateId);
  input.retainForOperation?.(baseState.stateId);
  const releaseCandidateStates: Array<() => void> = [];
  const releaseSearchPins = (): void => {
    for (const release of releaseCandidateStates.splice(0)) release();
    releaseBaseState();
  };
  const beamWidth = Math.max(DEFAULT_BEAM_WIDTH, Math.min(MAX_BEAM_WIDTH, input.beamWidth ?? DEFAULT_BEAM_WIDTH));
  const seen = new Set<string>();
  const branches: BranchMutable[] = [];
  // Index journal entries once. The search may evaluate dozens of candidates,
  // and scanning the full recovered-attempt list (including a fresh reversed
  // copy) for every candidate turns resume into O(candidates * journal).
  // Iterating in source order and overwriting preserves the previous
  // toReversed().find semantics: the latest matching entry wins.
  const recoveredByKey = new Map<string, LeanProofRecoveredAttempt>();
  for (const attempt of input.recoveredAttempts ?? []) {
    if (
      attempt.preconditionSourceHash !== baseState.sourceHash ||
      attempt.preconditionGoalFingerprint !== baseState.goalFingerprint
    )
      continue;
    recoveredByKey.set(candidateKey(baseState, attempt.candidate), attempt);
  }
  let durationMs = refreshed.durationMs ?? 0;
  let history: LeanEvalActionPerformanceSummary | undefined;
  if (performanceRoot) {
    try {
      history = readLeanEvalActionPerformance(performanceRoot, recordScope);
    } catch {
      // A damaged optional telemetry ledger must never prevent proof search.
    }
  }
  const candidates = input.preserveOrder
    ? [...input.candidates]
    : input.candidates.toSorted(
        (left, right) =>
          historicalPriority(baseState, right, history, input.failureCategory, goalIndex) -
          historicalPriority(baseState, left, history, input.failureCategory, goalIndex)
      );
  const performanceRecords: LeanEvalActionRecordInput[] = [];
  let executionDisposition: LeanEvalLeanProbeResult['executionDisposition'] = 'completed';
  let nextCandidateIndex = 0;
  const flushPerformanceRecords = (): void => {
    if (!performanceRoot || !performanceRecords.length) return;
    try {
      appendLeanEvalActionRecords(performanceRoot, performanceRecords);
      performanceRecords.length = 0;
    } catch {
      // Action telemetry is advisory and cannot alter proof semantics.
    }
  };
  for (let candidateIndex = 0; candidateIndex < candidates.length; candidateIndex += 1) {
    const candidate = candidates[candidateIndex]!;
    const remainingBeforeCandidate = remainingTimeoutMs();
    if (input.signal?.aborted || remainingBeforeCandidate === 0) {
      executionDisposition = input.signal?.aborted ? 'aborted' : 'timed_out';
      nextCandidateIndex = candidateIndex;
      break;
    }
    const key = candidateKey(baseState, candidate);
    if (seen.has(key)) {
      nextCandidateIndex = candidateIndex + 1;
      continue;
    }
    seen.add(key);
    const previous = recoveredByKey.get(key);
    if (previous && ['failed', 'invalid'].includes(previous.outcome)) {
      nextCandidateIndex = candidateIndex + 1;
      continue;
    }
    const restored = input.session.restore(baseSnapshot);
    if (restored.status === 'invalid') {
      flushPerformanceRecords();
      releaseSearchPins();
      return Object.freeze({
        status: 'unavailable',
        executionDisposition: 'invalid',
        batchComplete: false,
        nextCandidateIndex: candidateIndex,
        baseState,
        branches: Object.freeze(branches),
        executedAttempts: Object.freeze(executedAttempts),
        durationMs,
      });
    }
    const startedAt = new Date().toISOString();
    const attemptedAt = performance.now();
    // eslint-disable-next-line no-await-in-loop
    const result = await (async (): Promise<MathematicsLeanSessionActionResult> => {
      let replayMs = 0;
      if (previous?.snapshot) {
        const retained = input.session.restore(previous.snapshot);
        if (retained.status === 'restored' && retained.state)
          return {
            ...retained,
            status: 'duplicate' as const,
            underlyingStatus:
              previous.outcome === 'advanced' || previous.outcome === 'unchanged' ? previous.outcome : undefined,
            capabilityAdded: previous.capabilityAdded,
            recoveredFromJournal: true,
            cacheHit: true,
            reuseKind: 'hot' as const,
            durationMs: 0,
          };
        const replayed = await input.session.replay(previous.snapshot, input.signal, remainingBeforeCandidate);
        replayMs = replayed.durationMs ?? 0;
        if (replayed.status === 'restored' && replayed.state)
          return {
            ...replayed,
            status:
              replayed.state.status === 'closed' || replayed.state.goalFingerprint !== baseState.goalFingerprint
                ? 'advanced'
                : 'unchanged',
            capabilityAdded: previous.capabilityAdded,
            recoveredFromJournal: true,
            reuseKind: 'replayed' as const,
          };
        if (input.signal?.aborted) return replayed;
      }
      const remainingBeforeInvoke = remainingTimeoutMs();
      if (input.signal?.aborted || remainingBeforeInvoke === 0)
        return {
          status: 'unavailable',
          state: input.session.state,
          diagnostics: input.signal?.aborted
            ? 'Lean proof action search was aborted after replay'
            : 'Lean proof action search timed out after replay',
          executionDisposition: input.signal?.aborted ? 'aborted' : 'timed_out',
          durationMs: replayMs,
        };
      const invoked = await invoke(input.session, candidate, input.signal, remainingBeforeInvoke);
      return {
        ...invoked,
        durationMs: replayMs + (invoked.durationMs ?? 0),
        ...(invoked.action
          ? {
              action: {
                ...invoked.action,
                runtime: { ...invoked.action.runtime, durationMs: replayMs + invoked.action.runtime.durationMs },
              },
            }
          : {}),
      };
    })().catch(
      (error: unknown): MathematicsLeanSessionActionResult => ({
        status: 'unavailable',
        state: input.session.state,
        diagnostics: String(error),
        executionDisposition: 'unavailable',
        durationMs: performance.now() - attemptedAt,
      })
    );
    const attempt = {
      startedAt,
      recordedAt: new Date().toISOString(),
      candidate,
      result,
      baseState,
      goalIndex,
      goalFingerprint,
    };
    executedAttempts.push(attempt);
    try {
      input.onAttempt?.(attempt);
    } catch (error) {
      releaseSearchPins();
      throw error;
    }
    durationMs += result.reuseKind === 'hot' ? 0 : (result.action?.runtime.durationMs ?? result.durationMs ?? 0);
    const usable = isUsableCandidateResult(input.session, baseState, candidate, result);
    if (usable && result.state) {
      releaseCandidateStates.push(input.session.retainState(result.state.stateId));
    }
    const score = scoreBranch(baseState, candidate, result, history, input.failureCategory, goalIndex, usable);
    if (input.performanceRoot && input.episodeId) {
      const nextState = result.state;
      performanceRecords.push({
        ...(recordScope ? { runIdentity: recordScope.runIdentity } : {}),
        episodeId: input.episodeId,
        problemId: input.problemId || 'unknown',
        goalFingerprint,
        goalShape: leanGoalShape(selectedGoal),
        ...(input.failureCategory ? { failureCategory: input.failureCategory } : {}),
        tactic: candidate.payload.trim(),
        actionKind: candidate.kind,
        outcome:
          result.status === 'advanced' ||
          result.status === 'unchanged' ||
          result.status === 'failed' ||
          result.status === 'unavailable' ||
          result.status === 'invalid' ||
          result.status === 'duplicate'
            ? result.status
            : 'failed',
        openGoalsBefore: baseState.openGoals.length,
        openGoalsAfter: nextState?.openGoals.length ?? baseState.openGoals.length,
        firstErrorImproved: result.status === 'advanced',
        leanMs: Math.max(0, Math.round(result.action?.runtime.durationMs ?? result.durationMs ?? 0)),
      });
    }
    branches.push({
      candidate,
      result,
      ...(result.state ? { state: result.state } : {}),
      score,
      retained: false,
      usable,
      snapshot: input.session.snapshot(),
    });
    nextCandidateIndex = candidateIndex + 1;
    if (result.executionDisposition === 'timed_out' || result.executionDisposition === 'aborted') {
      executionDisposition = result.executionDisposition;
      nextCandidateIndex = candidateIndex;
      break;
    }
    if (result.status === 'unavailable') {
      executionDisposition = result.executionDisposition ?? 'unavailable';
      nextCandidateIndex = candidateIndex;
      break;
    }
    // A kernel-closed state dominates every other branch. Avoid spending
    // additional Lean probes once a complete proof is available.
    if (usable && result.state?.status === 'closed') {
      nextCandidateIndex = candidates.length;
      break;
    }
  }
  flushPerformanceRecords();
  const lookaheadPending =
    input.lookahead &&
    executionDisposition === 'completed' &&
    !branches.some((branch) => branch.usable && branch.state?.status === 'closed');
  if (lookaheadPending && (input.signal?.aborted || remainingTimeoutMs() === 0)) {
    executionDisposition = input.signal?.aborted ? 'aborted' : 'timed_out';
  } else if (lookaheadPending) {
    const promising = branches
      .filter(
        (branch) =>
          branch.usable &&
          ((branch.result.underlyingStatus ?? branch.result.status) === 'advanced' || branch.result.capabilityAdded) &&
          branch.state
      )
      .toSorted((left, right) => right.score - left.score)
      .slice(0, beamWidth);
    // Declaration inspection is pure but parses the source prefix. Lookahead
    // checks the same base declaration for every retained branch and often
    // revisits identical branch sources while locating sibling goals. Cache
    // the bounded source/line pairs for this search wave.
    const declarationCache = new Map<string, string | undefined>();
    const declarationAt = (source: string, line: number | undefined) => {
      if (line === undefined) return undefined;
      const key = `${line}\u0000${source}`;
      if (declarationCache.has(key)) return declarationCache.get(key);
      const declaration = inspectLeanDeclarations(source.split('\n').slice(0, line).join('\n')).at(-1)?.name;
      declarationCache.set(key, declaration);
      return declaration;
    };
    const originalDeclaration = declarationAt(baseSnapshot.sourceText, originalLocation?.line);
    for (const branch of promising) {
      const remainingBeforeLookahead = remainingTimeoutMs();
      if (input.signal?.aborted || remainingBeforeLookahead === 0) {
        executionDisposition = input.signal?.aborted ? 'aborted' : 'timed_out';
        break;
      }
      if (input.session.restore(branch.snapshot).status === 'invalid') continue;
      const siblingGoals = new Set(baseState.openGoals.filter((_, index) => index !== goalIndex));
      const locations = branch
        .state!.openGoals.map((goal, index) => ({
          goal,
          index,
          location:
            input.session.goalLocation(index) ??
            (index === 0 ? { line: input.session.goalLine, range: input.session.goalRange, localIndex: 0 } : undefined),
        }))
        .filter(
          ({ location }) =>
            !originalDeclaration || declarationAt(branch.snapshot.sourceText, location?.line) === originalDeclaration
        );
      const continuation =
        locations.find(({ goal }) => !siblingGoals.has(goal)) ?? locations.find(({ goal }) => goal === selectedGoal);
      if (!continuation) continue;
      const followups = generateLeanProofActionCandidates({
        source: branch.snapshot.sourceText,
        openGoal: continuation.goal,
        goalIndex: continuation.location?.localIndex ?? 0,
        targetLine: continuation.location?.line,
        targetRange: continuation.location?.range,
      });
      let continued: Awaited<ReturnType<typeof searchLeanProofActions>>;
      try {
        // eslint-disable-next-line no-await-in-loop -- Continuations share a mutable Lean session.
        const { runMathLocalClosure } = await import("./mathLocalClosure");
        // eslint-disable-next-line no-await-in-loop -- Continuations share a mutable Lean session.
        continued = await runMathLocalClosure({
          ...input,
          candidates: followups,
          maxTrials: Math.max(0, 16 - executedAttempts.length),
          maxTransitions: 7,
          goalIndex: continuation.index,
          failureCategory: classifyLeanProofDiagnostic(input.session.diagnostics),
          lookahead: false,
          commitBest: true,
          timeoutMs: remainingBeforeLookahead,
        });
      } catch (error) {
        releaseSearchPins();
        throw error;
      }
      durationMs += continued.durationMs;
      executedAttempts.push(...continued.executedAttempts);
      if (continued.executionDisposition !== 'completed') {
        executionDisposition = continued.executionDisposition;
        break;
      }
      const next = continued.best;
      if (
        !next?.state ||
        ((next.result.underlyingStatus ?? next.result.status) !== 'advanced' && next.state.status !== 'closed')
      )
        continue;
      const candidate = { ...next.candidate, payload: `${branch.candidate.payload}\n${next.candidate.payload}` };
      branches.push({
        candidate,
        result: next.result,
        state: next.state,
        score: scoreBranch(baseState, candidate, next.result, history, input.failureCategory, goalIndex, true),
        retained: false,
        usable: true,
        snapshot: input.session.snapshot(),
      });
      releaseCandidateStates.push(input.session.retainState(next.state.stateId));
      if (next.state.status === 'closed') break;
    }
  }
  const ranked = branches
    .filter((branch) => branch.usable)
    .toSorted(
      (left, right) => right.score - left.score || left.candidate.payload.localeCompare(right.candidate.payload)
    );
  const retained = new Set(ranked.slice(0, beamWidth));
  const normalizedBranches = branches.map((branch) => Object.freeze({ ...branch, retained: retained.has(branch) }));
  const best = ranked[0] ? Object.freeze({ ...ranked[0], retained: true }) : undefined;
  if (best?.state) input.retainForOperation?.(best.state.stateId);
  if (
    best &&
    executionDisposition === 'completed' &&
    input.commitBest !== false &&
    ((best.result.underlyingStatus ?? best.result.status) === 'advanced' ||
      best.result.capabilityAdded ||
      best.state?.status === 'closed')
  ) {
    const restored = best.state ? input.session.restoreState(best.state.stateId) : input.session.restore(best.snapshot);
    if (restored.status === 'invalid') input.session.restore(baseSnapshot);
  } else {
    input.session.restore(baseSnapshot);
  }
  releaseSearchPins();
  return Object.freeze({
    status: executionDisposition === 'completed' ? 'completed' : 'unavailable',
    executionDisposition,
    batchComplete: executionDisposition === 'completed',
    nextCandidateIndex,
    baseState,
    durationMs,
    branches: Object.freeze(
      normalizedBranches.map(({ snapshot: _snapshot, usable: _usable, ...branch }) => Object.freeze(branch))
    ),
    executedAttempts: Object.freeze(executedAttempts),
    ...(best
      ? {
          best: Object.freeze({
            candidate: best.candidate,
            result: best.result,
            ...(best.state ? { state: best.state } : {}),
            score: best.score,
            retained: true,
          }),
        }
      : {}),
  });
}
