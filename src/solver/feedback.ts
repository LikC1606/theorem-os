import path from 'node:path';
import type { ProofCheck } from './modules/evidence';
import { assertSolverSources, SolverSourceError, type SolverProblem } from './problem';
import { mathDigest } from '../math/mathRuntimeIo';
import { parseLeanDiagnosticOutput, renderLeanDiagnosticMessage } from '../math/leanDiagnosticMessages';

const MAX_FEEDBACK_BYTES = 16_000;

function bounded(text: string, bytes: number): string {
  if (Buffer.byteLength(text) <= bytes) return text;
  const suffix = '\n[truncated; run a local Lean check for the full diagnostics]';
  return Buffer.from(text).subarray(0, bytes - Buffer.byteLength(suffix)).toString('utf8').replace(/\uFFFD$/u, '') + suffix;
}

function leanErrorBlocks(output = ''): string[] {
  return parseLeanDiagnosticOutput(output).messages.filter(message => message.severity === 'error').map(renderLeanDiagnosticMessage);
}

/** Compare errors and goals, ignoring locations that move when a proof is edited. */
function failureSignature(check: ProofCheck): string | undefined {
  if (check.passed || check.verification.status !== 'failed' || !check.verification.results.some(result => result.status === 'failed')) return;
  const targets: string[] = [];
  for (const result of check.verification.results) {
    const target = [result.proofPath, result.theoremName, result.status];
    if (result.status === 'kernel_verified') {
      targets.push(JSON.stringify(target));
      continue;
    }
    if (result.status !== 'failed') return;
    const errors = [...new Set([result.stdoutPreview, result.stderrPreview].flatMap(output => leanErrorBlocks(output))
      .map(block => block.replace(/^(.+):\d+:\d+:\s*(error(?:\([^\n)]*\))?):/gmu, '$1: $2:').replace(/[ \t]+$/gmu, '')))].sort();
    // Generic host failures or absent diagnostics cannot establish stalled proof work.
    if (!errors.length) return;
    targets.push(JSON.stringify([...target, errors]));
  }
  return targets.sort().join('\n');
}

export type SolverFailure = Readonly<{ signature: string; sourceDigest: string; attempts: number }>;

/** Run-local hints only: history cannot suppress a check or establish proof acceptance. */
export function rememberSolverFailure(check: ProofCheck, history: readonly SolverFailure[] = []): SolverFailure[] {
  const signature = failureSignature(check);
  if (!signature) return history.slice(-32);
  const digest = mathDigest(signature);
  const previous = history.find(item => item.signature === digest);
  return [...history.filter(item => item.signature !== digest).slice(-31),
    { signature: digest, sourceDigest: check.sourceDigest, attempts: (previous?.attempts ?? 0) + 1 }];
}

export function solverSourceFeedback(problem: SolverProblem, worktree: string): string | undefined {
  try {
    assertSolverSources(problem, worktree);
  } catch (error) {
    if (!(error instanceof SolverSourceError)) throw error;
    if (error.message === 'math_source_outside_ownership')
      return `Host rejected the edited source before committing or checking it in Lean.\nFile: ${error.proofPath}\nError: ${error.message}\n${error.recovery}\nRepository root: ${worktree}\nProject directory: ${path.join(worktree, problem.projectRelative)}\nOwned proof files (repository-relative): ${problem.ownedFiles.map(file => path.join(problem.projectRelative, file)).join(', ')}\nAdvisory scratch must remain untracked regular files under .scratch/ at the repository root or ${path.join(problem.projectRelative, '.scratch')}/ at the project root. Check pwd before writing: when already in the project directory, use .scratch/ directly instead of repeating ${problem.projectRelative}/. Correct the location manually while preserving its contents; do not reset or discard the worktree. All source checks must pass before committing or Lean acceptance.`;
    return `Host rejected the edited source before committing or checking it in Lean.\nFile: ${problem.projectRelative}/${error.proofPath}\nError: ${error.message}\n${error.recovery}\nCompare this file with baseline commit ${problem.baseCommit} using git show. Edit only the allowed files; do not reset or discard the worktree. The original source checks must pass before Lean acceptance.`;
  }
}

/** Only host source inspection, not a provider's error text, supplies this feedback. */
export function isSolverSourceOwnershipFeedback(feedback: string): boolean {
  return feedback.startsWith('Host rejected the edited source before committing or checking it in Lean.\n') &&
    feedback.includes('\nError: math_source_outside_ownership\n');
}

/** Keep Lean's goal/context blocks, without repeating a file's output for each target. */
export function solverProofFeedback(check: ProofCheck, previous?: ProofCheck, history: readonly SolverFailure[] = []): string {
  const files = new Map<string, { targets: string[]; errors: Set<string>; output: Set<string> }>();
  for (const result of check.verification.results) {
    if (result.status === 'kernel_verified') continue;
    let file = files.get(result.proofPath);
    if (!file) {
      file = { targets: [], errors: new Set(), output: new Set() };
      files.set(result.proofPath, file);
    }
    file.targets.push(`${result.theoremName || '(unnamed)'}: ${result.status}`);
    if (result.error) file.errors.add(result.error);
    for (const output of [result.stdoutPreview, result.stderrPreview]) {
      if (!output?.trim()) continue;
      const errors = leanErrorBlocks(output);
      for (const block of errors.length ? errors : [output]) file.output.add(block.trim());
    }
  }
  const sections = [
    'Continue the original proof. The frozen commit failed host acceptance.',
    'Repair the earliest blocking error and check the relevant lemma in Lean before expanding the proof. Preserve already checked lemmas and all original statements.',
  ];
  const firstBlocking = check.verification.results.flatMap(result => [result.stdoutPreview, result.stderrPreview]
    .flatMap(output => parseLeanDiagnosticOutput(output ?? '').messages)).find(message => message.severity === 'error');
  if (firstBlocking) sections.push('First blocking Lean message:\n' +
    bounded(renderLeanDiagnosticMessage({ ...firstBlocking, message: '' }).trimEnd(), 3000) +
    '\nRead its goal and hypotheses in the file diagnostics below.');
  const signature = failureSignature(check);
  if (previous && !previous.passed && previous.sourceDigest === check.sourceDigest) {
    sections.push('The proof source is unchanged since the previous failed check. Re-examine the blocking mathematical step or choose another route before submitting again.');
  } else if (previous) {
    if (signature && signature === failureSignature(previous)) {
      sections.push('The proof source changed, but the same Lean errors and goal contexts remain for the same targets. Re-examine the blocking lemma and test a different local argument or supply the missing assumption before retrying. Preserve checked lemmas; reconsider the overall route if its key step appears false or too strong.');
    }
  }
  const recurring = signature && history.find(item => item.signature === mathDigest(signature));
  if (recurring) {
    sections.push(`This Lean failure has already occurred ${recurring.attempts} time(s) in this run. ${recurring.sourceDigest === check.sourceDigest ? 'The same proof source was previously rejected. ' : ''}Review the failed arguments in RESEARCH.md and test a different local argument or supply the missing premise. Retry an earlier argument when its relevant source, assumptions or instantiation have changed; this history is advisory.`);
  }
  for (const [file, diagnostics] of files) {
    sections.push(`File: ${file}\nTargets: ${diagnostics.targets.join(', ')}\nHost: ${[...diagnostics.errors].join('; ')}\n${bounded([...diagnostics.output].join('\n\n'), 6_000)}`);
  }
  const output = [...files.values()].flatMap(file => [...file.output]).join('\n');
  if (/positivity|linarith failed/u.test(output)) {
    sections.splice(2, 0, 'For positivity/arithmetic failures, expose subtype .property facts, sign/nonzero assumptions and cast identities explicitly before retrying the tactic.');
  }
  if (!files.size) sections.push(`Host verification status: ${check.verification.status}. Lean output alone does not establish acceptance.`);
  return bounded(sections.join('\n\n'), MAX_FEEDBACK_BYTES);
}
