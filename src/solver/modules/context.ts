import path from 'node:path';
import { mathematicsRuntimeInstruction } from '../../math/mathRuntimeEnvironment';
import type { SolverRunState } from '../archive';
import type { SolverProblem } from '../problem';
import type { ProofCheck } from './evidence';
import { solverProofFeedback, type SolverFailure } from '../feedback';
import type { ResearchOperation } from './value';

export type ContextAccess = Readonly<{
  root: string;
  worktree: string;
  environment: NodeJS.ProcessEnv;
  taskText: string;
  corpusFile?: string;
  retrievalRoot: string;
  sourceFeedback?: string;
  previousCheck?: ProofCheck;
  previousFailures?: readonly SolverFailure[];
  operation?: ResearchOperation;
}>;
export type ContextBundle = Readonly<{
  instructions: string;
  message: string;
  scope: 'original-problem-and-allowed-library';
  sources: Readonly<{ problemReceiptDigest: string; checkCommit?: string; retrievalDigest?: string }>;
}>;

/** M5 selects instructions and feedback without promoting retrieved or generated hints to evidence. */
export function buildResearchContext(task: SolverProblem, state: Readonly<SolverRunState>, access: ContextAccess): ContextBundle {
  const instructions = `You prove the original mathematical problem in Lean. Work only in this isolated worktree.\nEdit only ${task.ownedFiles.map(file => path.join(task.projectRelative, file)).join(', ')} and RESEARCH.md.\nPreserve every original declaration, definition and assumption. Do not use sorry, admit, native_decide, unsafe or new axioms in a completed proof. Do not read external candidate solutions.\nFor a difficult problem, briefly compare plausible routes and test the key bridge lemma before expanding a long proof. Prefer routes supported by installed library lemmas.\nBatch independent library searches and source reads in one tool call. Read only relevant declaration ranges; reuse known definitions and checked lemmas instead of rereading entire proof files. Bound tool output in bytes before returning it; show only the earliest Lean errors with their goal contexts.\nUse lake env lean on the changed proof file for diagnostics. Check a coherent local proof change, repair its earliest error, and avoid rebuilding dependencies or repeating a successful check without relevant edits.\nThe host independently checks the frozen commit after each turn. Keep RESEARCH.md concise: checked lemmas, failed arguments with their Lean goal/context, remaining obligations, current route and latest blocking error. End a turn when ready for a host check.\n${access.corpusFile ? `For library lookup, run bun ${shellArgument(path.join(access.root, 'bin/math.ts'))} search-lean --workspace ${shellArgument(access.retrievalRoot)} --corpus ${shellArgument(access.corpusFile)} --sha256 ${shellArgument(access.environment.DEEPSCIENTIST_MATH_RETRIEVAL_CORPUS_SHA256!)} --query 'KEYWORDS' --query 'OTHER_KEYWORDS'. Repeat --query up to 8 times to share one verified library scan. Use short library keywords; add --goal 'LEAN_GOAL_AND_CONTEXT' to rank results by the current target and available types. Keep local variable names in --goal rather than requiring them in --query. Ranking is a hint; test shortlisted premises at the actual proof position. Results include qualified names, source headers and active variable/open context; use Lean #check to confirm the full type. Check a known declaration name in Lean before searching: generated declarations and Lean core lemmas may have no explicit Mathlib source header.\n` : ''}${mathematicsRuntimeInstruction(access.environment.DEEPSCIENTIST_MATH_ENV_FILE)}`;
  const diagnostics = `\nFor local diagnostics, run bun ${shellArgument(path.join(access.root, 'bin/math.ts'))} check-lean --workspace ${shellArgument(path.join(access.worktree, task.projectRelative))} --file 'OWNED_FILE.lean' --timeout-seconds 90. This compiles local imports with pinned packages and preserves failures. Do not pipe compiler output through head; the command already bounds output. A timeout is inconclusive: reduce the change or check the key bridge separately, then return for host feedback.\nWork in short turns: test one key bridge or complete one coherent proof step, save files and return. The host may interrupt a long turn to check saved sources and resume with diagnostics.\nBefore expanding a route, list every original obligation and the needed library lemmas, constructions and bridge proofs. A route addressing only one conjunct is incomplete. Verify the hardest missing bridge first. Check that optional computational tools are installed before depending on them; generated calculations still need Lean verification.\n`;
  let message = access.sourceFeedback || (state.check && !state.check.passed
    ? solverProofFeedback(state.check, access.previousCheck, access.previousFailures ?? state.failures)
    : `${access.taskText}\n\nOriginal problem:\n${task.contract.formalStatement}\n\nOnly the instructions above and host Lean checks determine acceptance.`);
  if (access.operation && access.operation !== 'direct' && !access.sourceFeedback) {
    const research = state.lemmaResearch;
    message += `\n\nResearch operation: ${access.operation}.\n` +
      'Propose one new ordinary theorem before one original target in the same owned Lean file. Use its unqualified name in the target proof. Its full closed type must include all original assumptions and parameters, using qualified library names. Keep every original declaration unchanged.\n' +
      'Keep exactly one fenced math-lemma JSON block in RESEARCH.md: {"proofPath":"owned/file.lean","target":"Original.qualifiedTarget","lemma":"Original.helper","type":"FULL_CLOSED_LEAN_TYPE"}.\n' +
      'For decompose/bridge, write the concrete target proof using the helper; the helper may remain a draft. The host checks the connection with the helper as an explicit parameter, in a disposable projection. For prove-lemma, prove the helper without the original target. For integrate-lemma, apply the proven helper to close the original targets. All operations share the run budget.\n' +
      'Conditional bridge evidence does not prove the original problem. The host separately checks the helper closed type and finally rechecks every unchanged original target. Do not depend on other original theorem drafts in the helper; the host removes original theorem declarations when checking it.\n' +
      `Current plan: ${JSON.stringify(research?.plan ?? null)}\nProposal error: ${research?.error ?? 'none'}\n` +
      `Conditional bridge: ${research?.bridge?.passed ? 'checked under the explicit lemma premise' : 'unverified'}\nLemma: ${research?.lemma?.passed ? 'checked at the recorded source version' : 'unverified'}\n`;
    for (const receipt of [research?.bridge, research?.lemma]) {
      if (receipt && !receipt.passed) message += `\n${receipt.obligation} obligation feedback:\n${solverProofFeedback(receipt)}\n`;
      if (receipt && !receipt.passed && receipt.unchangedFailures >= 2)
        message += `\nThe ${receipt.obligation} obligation failed ${receipt.unchangedFailures} consecutive checks with unchanged proof inputs. Reconsider the candidate lemma or its connection, and test a revised route before resubmitting. Preserve useful proved helpers.\n`;
    }
  }
  return { instructions: instructions.replace('Use lake env lean on the changed proof file for diagnostics.',
    'Use the bounded check-lean command below on the changed proof file for diagnostics.') + diagnostics +
    '\nReuse existing public imports. Add narrowly scoped library imports for new lemmas instead of importing all of Mathlib for a small proof change.\n',
    message, scope: 'original-problem-and-allowed-library',
    sources: { problemReceiptDigest: task.receiptDigest, checkCommit: state.check?.commit,
      retrievalDigest: access.environment.DEEPSCIENTIST_MATH_RETRIEVAL_CORPUS_SHA256 } };
}

function shellArgument(value: string): string {
  return "'" + value.replaceAll("'", "'\\''") + "'";
}
