/** Bounded routine proof work. Source adoption belongs exclusively to the caller. */
import crypto from 'node:crypto';
import {
  classifyLeanProofDiagnostic,
  generateLeanProofActionCandidates,
  linarithCanUseGoal,
  searchLeanProofActions,
  type LeanProofActionBranch,
  type LeanProofActionCandidate,
  type LeanProofActionSearchResult,
  type LeanProofExecutedAttempt,
} from "./leanProofActionSearch";

import { inspectLeanDeclarations } from "./verifier";

type ClosureInput = Parameters<typeof searchLeanProofActions>[0] & {
  maxTrials?: number;
  maxTransitions?: number;
  allowChoices?: boolean;
};
export type MathLocalClosureDiagnostic = Readonly<{
  transitions: number;
  trials: number;
  stopReason: 'closed' | 'open' | 'slice_exhausted' | 'interrupted' | 'location_unavailable';
}>;

/** Only these actions may retain an incomplete prefix. Lean still checks every action. */
export function isRoutineMathClosureAction(candidate: LeanProofActionCandidate, goal: string): boolean {
  const action = candidate.payload.trim();
  if (/^(?:assumption|rfl|simp|simp_all|simpa|aesop|intro)$/u.test(action)) return true;
  // The generic generator emits Lean's bounded local search tactic for
  // type-mismatch recovery. Keep that recovery path executable.
  if (action === 'exact?') return true;
  if (/^exact\s+/u.test(action)) return true;
  const target = goal.split(/⊢|\|-/u).at(-1) ?? '';
  if (action === 'constructor') return /∧|\bAnd\b/u.test(target) && !/∃|\bExists\b|∨|\bOr\b/u.test(target);
  // Contradictory relational hypotheses close any target, not only False.
  if (/^(?:linarith|nlinarith)$/u.test(action)) return linarithCanUseGoal(goal);
  if (action === 'omega') return /\bNat\b|\bInt\b|ℕ|ℤ/u.test(goal);
  if (action === 'tauto') return /(?:→|->|↔|\bIff\b|∧|\bAnd\b|∨|\bOr\b|¬|\bNot\b)/u.test(goal);
  if (action === 'contradiction') return /(?:\bFalse\b|⊥)/u.test(goal);
  if (action === 'field_simp') return /\/|⁻¹|\b(?:Inv|Div)\b/u.test(goal);
  if (/^(?:norm_num|ring|ring_nf|positivity)$/u.test(action))
    return /[=≤≥<>+*^\-/]|\b(?:Nat|Int|Rat|Real|Ring|Field)\b|ℕ|ℤ|ℚ|ℝ/u.test(goal);
  return false;
}

/**
 * One session, one deadline and at most 8 state transitions / 16 actual trials.
 * Mathematical choices (apply, witnesses, induction, rewrite) are never retained
 * just because the printed goal count improved. Explicit provided searches keep
 * their own semantics and do not enter this routine executor.
 */
export async function runMathLocalClosure(input: ClosureInput): Promise<LeanProofActionSearchResult> {
  const started = performance.now();
  const deadline = input.timeoutMs === undefined ? undefined : started + Math.max(0, input.timeoutMs);
  const remaining = () => (deadline === undefined ? undefined : Math.max(0, deadline - performance.now()));
  const session = input.session;
  const maxTransitions = Math.max(0, Math.min(8, input.maxTransitions ?? 8));
  const maxTrials = Math.max(0, Math.min(16, input.maxTrials ?? 16));
  const base = session.snapshot();
  const releaseBase = session.retainState(base.state.stateId);
  const declarationCache = new Map<string, Map<number, string | undefined>>();
  const declarationCountCache = new Map<string, number>();
  const declarationAt = (source: string, line: number | undefined) => {
    if (line === undefined) return undefined;
    const byLine = declarationCache.get(source);
    if (byLine?.has(line)) return byLine.get(line);
    const declaration = inspectLeanDeclarations(source.split('\n').slice(0, line).join('\n')).at(-1)?.name;
    const entries = byLine ?? new Map<number, string | undefined>();
    entries.set(line, declaration);
    if (!byLine) declarationCache.set(source, entries);
    return declaration;
  };
  const declarationCount = (source: string): number => {
    const cached = declarationCountCache.get(source);
    if (cached !== undefined) return cached;
    const count = inspectLeanDeclarations(source).length;
    declarationCountCache.set(source, count);
    return count;
  };
  const originalDeclaration = declarationAt(
    base.sourceText,
    session.goalLocation(input.goalIndex ?? 0)?.line ?? session.goalLine
  );
  const selectedDeclarationClosed = (): boolean => {
    if (session.state.status === 'closed') return true;
    if (!originalDeclaration || session.state.status === 'failed') return false;
    const source = session.snapshot().sourceText;
    return (
      session.state.openGoals.length > 0 &&
      session.state.openGoals.every((_, index) => {
        const located = declarationAt(source, session.goalLocation(index)?.line);
        return located !== undefined && located !== originalDeclaration;
      })
    );
  };
  const releases: Array<() => void> = [];
  const branches: LeanProofActionBranch[] = [];
  const attempts: LeanProofExecutedAttempt[] = [];
  const visited = new Set<string>();
  let best: LeanProofActionBranch | undefined;
  let transitions = 0;
  let trials = 0;
  let stopReason: MathLocalClosureDiagnostic['stopReason'] = 'open';
  let executionDisposition: LeanProofActionSearchResult['executionDisposition'] = 'completed';
  try {
    while (transitions < maxTransitions && trials < maxTrials) {
      if (input.signal?.aborted || remaining() === 0) {
        executionDisposition = input.signal?.aborted ? 'aborted' : 'timed_out';
        stopReason = 'interrupted';
        break;
      }
      const current = session.snapshot();
      if (current.state.status === 'closed') {
        stopReason = 'closed';
        break;
      }
      // Full hypotheses/instances are part of openGoals. Source also binds local
      // declarations and imports; no success cache is keyed by printed conclusion.
      const identity = crypto
        .createHash('sha256')
        .update(
          JSON.stringify([
            session.environmentFingerprint,
            current.state.statementHash,
            current.state.routeFingerprint,
            current.state.sourceHash,
            current.state.openGoals,
          ])
        )
        .digest('hex');
      if (visited.has(identity)) break;
      visited.add(identity);
      const goalIndex =
        transitions === 0
          ? (input.goalIndex ?? 0)
          : originalDeclaration
            ? current.state.openGoals.findIndex(
                (_, index) =>
                  declarationAt(current.sourceText, session.goalLocation(index)?.line) === originalDeclaration
              )
            : 0;
      if (goalIndex < 0) {
        if (selectedDeclarationClosed()) stopReason = 'closed';
        break;
      }
      const goal = current.state.openGoals[goalIndex] ?? '';
      const location = session.goalLocation(goalIndex);
      const line = location?.line ?? session.goalLine;
      if (line === undefined && (transitions > 0 || declarationCount(current.sourceText) !== 1)) {
        stopReason = 'location_unavailable';
        break;
      }
      const generated =
        transitions === 0
          ? input.candidates
          : generateLeanProofActionCandidates({
              source: current.sourceText,
              openGoal: goal,
              targetLine: line,
              targetRange: location?.range ?? session.goalRange,
              goalIndex: location?.localIndex ?? 0,
              diagnostics: session.diagnostics,
              failureCategory: classifyLeanProofDiagnostic(session.diagnostics),
            });
      const candidates = generated.filter((candidate) => isRoutineMathClosureAction(candidate, goal));
      let advanced = false;
      for (const candidate of candidates) {
        if (trials >= maxTrials) break;
        // eslint-disable-next-line no-await-in-loop -- Candidates share one versioned Lean session.
        const result = await searchLeanProofActions({
          ...input,
          candidates: [candidate],
          goalIndex,
          commitBest: false,
          preserveOrder: true,
          lookahead: false,
          timeoutMs: remaining(),
        });
        attempts.push(...result.executedAttempts);
        trials += result.executedAttempts.length;
        branches.push(...result.branches);
        if (result.executionDisposition !== 'completed') {
          executionDisposition = result.executionDisposition;
          stopReason = 'interrupted';
          break;
        }
        const next = result.best;
        if (!next?.state) continue;
        // A new source hash alone is never mathematical progress. Unchanged
        // simp/aesop attempts cannot grow a useless source forever.
        if (
          next.state.status !== 'closed' &&
          ((next.result.underlyingStatus ?? next.result.status) !== 'advanced' ||
            next.state.goalFingerprint === current.state.goalFingerprint ||
            JSON.stringify(next.state.openGoals) === JSON.stringify(current.state.openGoals))
        )
          continue;
        if (session.restoreState(next.state.stateId).status !== 'restored') continue;
        // Checked-block exact terms promise a complete consumer proof. Lean can
        // still expose goals inside an unfinished `by` term; following that
        // prefix would discard the remaining independent helper candidates.
        // A different original declaration may remain open in the same file.
        if (candidate.helperProduced && /^exact\s/u.test(candidate.payload.trim()) && !selectedDeclarationClosed()) {
          session.restore(current);
          continue;
        }
        releases.push(session.retainState(next.state.stateId));
        input.retainForOperation?.(next.state.stateId);
        best = next;
        transitions += 1;
        advanced = true;
        if (next.state.status === 'closed') stopReason = 'closed';
        break;
      }
      if (!advanced && input.allowChoices !== false && executionDisposition === 'completed' && trials < maxTrials) {
        // Apply is a mathematical choice. Keep its recovery branch, but only
        // return it for adoption if a bounded routine suffix closes everything.
        const choices = generated.filter((candidate) => /^apply\s+/u.test(candidate.payload)).slice(0, 2);
        for (const choice of choices) {
          if (trials >= maxTrials || transitions >= maxTransitions) break;
          session.restore(current);
          // eslint-disable-next-line no-await-in-loop -- Restore and try one branch at a time.
          const chosen = await searchLeanProofActions({
            ...input,
            candidates: [choice],
            goalIndex,
            commitBest: false,
            lookahead: false,
            preserveOrder: true,
            timeoutMs: remaining(),
          });
          trials += chosen.executedAttempts.length;
          attempts.push(...chosen.executedAttempts);
          branches.push(...chosen.branches);
          if (chosen.executionDisposition !== 'completed') {
            executionDisposition = chosen.executionDisposition;
            stopReason = 'interrupted';
            break;
          }
          const branch = chosen.best;
          if (!branch?.state || session.restoreState(branch.state.stateId).status !== 'restored') continue;
          input.retainForOperation?.(branch.state.stateId);
          let closed = selectedDeclarationClosed() ? branch : undefined;
          if (!closed && branch.state.goalFingerprint !== current.state.goalFingerprint) {
            const nextIndex = originalDeclaration
              ? session.state.openGoals.findIndex(
                  (_, index) =>
                    declarationAt(session.snapshot().sourceText, session.goalLocation(index)?.line) ===
                    originalDeclaration
                )
              : 0;
            const nextLocation = session.goalLocation(nextIndex);
            if (nextLocation?.line !== undefined) {
              // eslint-disable-next-line no-await-in-loop -- The suffix consumes this branch's state.
              const suffix = await runMathLocalClosure({
                ...input,
                candidates: generateLeanProofActionCandidates({
                  source: session.snapshot().sourceText,
                  openGoal: session.state.openGoals[nextIndex],
                  targetLine: nextLocation.line,
                  targetRange: nextLocation.range,
                  goalIndex: nextLocation.localIndex ?? 0,
                  diagnostics: session.diagnostics,
                }),
                goalIndex: nextIndex,
                commitBest: false,
                lookahead: false,
                allowChoices: false,
                maxTrials: maxTrials - trials,
                maxTransitions: maxTransitions - transitions - 1,
                timeoutMs: remaining(),
              });
              trials += suffix.executedAttempts.length;
              attempts.push(...suffix.executedAttempts);
              branches.push(...suffix.branches);
              if (suffix.executionDisposition !== 'completed') {
                executionDisposition = suffix.executionDisposition;
                stopReason = 'interrupted';
                break;
              }
              if (
                suffix.best?.state &&
                (suffix.best.state.status === 'closed' || suffix.localClosure?.stopReason === 'closed')
              ) {
                closed = suffix.best;
                transitions += suffix.localClosure?.transitions ?? 0;
              }
            }
          }
          if (closed?.state) {
            best = closed;
            transitions += 1;
            input.retainForOperation?.(closed.state.stateId);
            releases.push(session.retainState(closed.state.stateId));
            session.restoreState(closed.state.stateId);
            stopReason = 'closed';
            advanced = true;
            break;
          }
          session.restore(current);
        }
      }
      if (executionDisposition !== 'completed' || stopReason === 'closed' || !advanced) break;
    }
    if (stopReason === 'open' && (transitions === maxTransitions || trials >= maxTrials))
      stopReason = 'slice_exhausted';
    if (input.commitBest === false || executionDisposition !== 'completed') session.restore(base);
    else if (best?.state) session.restoreState(best.state.stateId);
    else session.restore(base);
    return {
      status: executionDisposition === 'completed' ? 'completed' : 'unavailable',
      executionDisposition,
      batchComplete: executionDisposition === 'completed',
      nextCandidateIndex: input.candidates.length,
      baseState: base.state,
      branches,
      executedAttempts: attempts,
      best,
      durationMs: performance.now() - started,
      localClosure: { transitions, trials, stopReason },
    };
  } finally {
    for (const release of releases) release();
    releaseBase();
  }
}
