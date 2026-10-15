import path from 'node:path';
import fs from 'node:fs';
import { readMathText } from '../../math/mathRuntimeIo';
import { assertMathCanonicalPath } from '../../math/paths';
import { mathematicsRuntimeInstruction } from '../../math/mathRuntimeEnvironment';
import { limitMathOutput } from '../../math/mathProcess';
import type { SolverRunState } from '../archive';
import type { SolverProblem } from '../problem';
import type { ProofCheck } from './evidence';
import { solverProofFeedback, type SolverFailure } from '../feedback';
import type { ResearchOperation } from './value';
import { taskGroup, assignmentDeliveryFile, type CooperativeAction } from '../tasks';
import type { CooperationState } from '../cooperation';
import { statementReviewSummary, type StatementAction, type StatementReview } from '../statementReview';

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
  assignment?: CooperativeAction;
}>;
export type ContextBundle = Readonly<{
  assignment?: CooperativeAction;
  instructions: string;
  message: string;
  scope: 'original-problem-and-allowed-library' | 'fixed-statement';
  sources: Readonly<{ problemReceiptDigest: string }>;
}>;

/** Backtranslation is built from the formal snapshot alone, in a fresh session. */
export function buildStatementReviewContext(review: StatementReview, action: StatementAction, problemReceiptDigest: string): ContextBundle {
  const blind = action.kind === 'backtranslate';
  const instructions = 'You are the Independent Reviewer of one fixed Lean declaration. Read only STATEMENT.json and the supplied definitions in this workspace. ' +
    'Do not read parent directories, other workspaces, git history, task journals or external candidate solutions. Leave all snapshot inputs unchanged; write only RESEARCH.md. ' +
    'Use the Lean-exported elaboration in STATEMENT.json to resolve names, coercions and imported definitions. Flag relevant ambiguous or unavailable definitions instead of guessing. ' +
    'A translation or review is advisory and grants no Lean proof acceptance. Bound tool output in bytes.\n' + (blind
      ? 'Translate the Lean statement into mathematics using its formal context only. State all quantifiers, assumptions and relevant definitions explicitly. ' +
        'The intended mathematical explanation is deliberately withheld. Write the translation as ordinary Markdown in RESEARCH.md.\n'
      : 'Compare the saved independent backtranslation with the intended mathematics and premises below. Check missing hypotheses, changed quantifiers and changes of meaning. ' +
        'Write one JSON object in RESEARCH.md: {"verdict":"accepted|changes_requested"}. Optional summary and evidenceRefs explain the decision. ' +
        'Plain JSON or a math/json fence is accepted. The host binds your response to the fixed snapshot.\n');
  return { instructions, scope: 'fixed-statement', sources: { problemReceiptDigest },
    message: 'Cooperative assignment:\n' + JSON.stringify(action) + '\n\nRead the fixed formal snapshot in STATEMENT.json.\n' + (blind ? '' :
      '\nIntended mathematics:\n' + review.intendedStatement + '\nPremises:\n' + JSON.stringify(review.premises) +
      '\nSaved independent backtranslation:\n' + JSON.stringify(review.translation)) };
}

/** M4 builds prompts from the host's scoped cooperation view; hints remain advisory. */
export function buildResearchContext(task: SolverProblem, state: Readonly<SolverRunState>, access: ContextAccess): ContextBundle {
  const command = `bun ${shellArgument(path.join(access.root, 'bin/math.ts'))}`;
  const taskRules = access.assignment?.kind === 'task' && access.assignment.task.kind === 'lemma'
    ? `This is a lemma task for ${access.assignment.task.theoremName}. You may repair solver-created lemma proofs and add newly named helpers in owned Lean files. Preserve existing helper statements, definition bodies and original goal proofs.\n`
    : '';
  const instructions = `You prove the original mathematical problem in Lean. Work only in this isolated worktree.
Edit only ${task.ownedFiles.map(file => path.join(task.projectRelative, file)).join(', ')}, RESEARCH.md${access.assignment?.kind === 'task' ? ', the assigned delivery log' : ''}.
Preserve original declarations, definitions, assumptions, existing imports, options and namespace/section context. You may add explicit Mathlib.* imports at the top of owned Lean files from the pinned installed library; do not edit trusted problem or package files. Completed proofs must not use sorry, admit, native_decide, unsafe or new axioms. Do not read external candidate solutions.
${taskRules}Use installed library lemmas and test uncertain bridges early. Batch independent searches and reads, reuse results, bound output in bytes and show the earliest Lean error and goal. The host launches the cooperative agents; do not spawn agents inside this session. Lead planning saves a task graph and returns promptly; assigned workers investigate and prove it.
For diagnostics, run ${command} check-lean --workspace ${shellArgument(path.join(access.worktree, task.projectRelative))} --file 'OWNED_FILE.lean' --timeout-seconds 0. It compiles saved sources with pinned imports and bounded output. Poll a returned process ID. A timeout is inconclusive. Repair the earliest error; avoid rebuilding dependencies or repeating unchanged checks. For math_original_context_changed or math_original_declaration_changed, use the reported file and recovery instructions to restore the offending context or declaration from the seed commit while preserving new proof work, then retry the saved-file check. Keep helper-specific scopes and instances inside their proofs. If the environment is unavailable or the same startup error remains after a repair, report it and return.
Add helpers in owned modules; definitions may be noncomputable. For type lookup, add single-name #check commands such as #check Finset.sum_eq_single in the existing namespace. For instance lookup, use #synth MeasureSpace ℝ or parenthesize complex types, such as #synth Fintype (Fin 2). If a known library declaration is unavailable, find its module in the installed corpus and import that explicit Mathlib.* module in the owned file; an unknown name alone does not establish a missing library theorem. Check the actual saved file, remove probes before delivery, and save checked helpers, gaps and next steps in RESEARCH.md. Keep this file as a concise current checkpoint; replace obsolete status instead of appending transcripts. Earlier committed notes remain in git history. Then return for independent host checking. Turns may be checkpointed and resumed. Verify computational results in Lean.
${access.corpusFile ? `For library lookup, run ${command} search-lean --workspace ${shellArgument(access.retrievalRoot)} --corpus ${shellArgument(access.corpusFile)} --sha256 ${shellArgument(access.environment.DEEPSCIENTIST_MATH_RETRIEVAL_CORPUS_SHA256!)} --query 'KEYWORDS' --query 'OTHER_KEYWORDS'. Batch up to 8 short queries; use --goal 'LEAN_GOAL_AND_CONTEXT' for local variables and types. Ranking is advisory. Confirm types and known names with Lean #check before expanding a search: generated and core declarations may have no Mathlib source header.\n` : ''}${mathematicsRuntimeInstruction(access.environment.DEEPSCIENTIST_MATH_ENV_FILE)}`;
  const originalProblem = `${access.taskText}\n\nOriginal problem:\n${task.contract.formalStatement}`;
  let message = access.sourceFeedback || (state.check && !state.check.passed
    ? solverProofFeedback(state.check, access.previousCheck, access.previousFailures ?? state.failures)
    : originalProblem);
  const cooperation = state.cooperation;
  if (cooperation) {
    const work = access.assignment?.kind === 'task' ? access.assignment.task : undefined;
    const references = [...(cooperation.deliveries ?? [])]
      .sort((a, b) => Number(work?.dependsOn.includes(a.taskId ?? '')) - Number(work?.dependsOn.includes(b.taskId ?? '')))
      .slice(-8).map(({ evidence: _evidence, ...record }) => record);
    message += '\n\nCurrent-version deliveries selected for this task (retain unproved obligations):\n' +
      bounded(JSON.stringify(references), 12000);
  }
  if (!state.threadId && state.previousThreadIds?.length) {
    if (message !== originalProblem) message = `${originalProblem}\n\n${message}`;
    const notes = path.join(access.worktree, 'RESEARCH.md');
    if (fs.existsSync(notes)) {
      assertMathCanonicalPath(notes);
      message += `\n\nCurrent research checkpoint (advisory; recheck claims in Lean):\n${readMathText(notes, 6000, { headOnly: true })}`;
    }
  }
  if (!state.cooperation && access.operation && access.operation !== 'direct' && !access.sourceFeedback) {
    const research = state.lemmaResearch;
    message += `\n\nResearch operation: ${access.operation}.\n` +
      'Add a helper before an original target in the same owned file; use its unqualified name in the target proof. Give its full closed Lean type with all parameters and hypotheses.\n' +
      'Write one JSON object in RESEARCH.md (plain JSON or a math/json fence): {"proofPath":"owned/file.lean","target":"Original.qualifiedTarget","lemma":"Original.helper","type":"FULL_CLOSED_LEAN_TYPE"}.\n' +
      'For decompose/bridge, prove the target using the draft helper; the host tests this connection under an explicit helper premise. For prove-lemma, prove the helper independently: original theorem drafts are removed during checking. For integrate-lemma, use checked helpers to close all original targets. These checks share the run budget; a conditional bridge alone is not a solution.\n' +
      `Current plan: ${JSON.stringify(research?.plan ?? null)}\nProposal error: ${research?.error ?? 'none'}\n` +
      `Conditional bridge: ${research?.bridge?.passed ? 'checked under the explicit lemma premise' : 'unverified'}\nLemma: ${research?.lemma?.passed ? 'checked at the recorded source version' : 'unverified'}\n`;
    for (const receipt of [research?.bridge, research?.lemma]) {
      if (receipt && !receipt.passed) message += `\n${receipt.obligation} obligation feedback:\n${solverProofFeedback(receipt)}\n`;
      if (receipt && !receipt.passed && receipt.unchangedFailures >= 2)
        message += `\nThe ${receipt.obligation} obligation failed ${receipt.unchangedFailures} consecutive checks with unchanged proof inputs. Reconsider the candidate lemma or its connection, and test a revised route before resubmitting. Preserve useful proved helpers.\n`;
    }
  }
  const bundle: ContextBundle = { instructions,
    message, scope: 'original-problem-and-allowed-library',
    sources: { problemReceiptDigest: task.receiptDigest } };
  return access.assignment && cooperation ? buildCooperativeContext(task, cooperation, bundle, access.assignment, access.operation ?? 'direct') : bundle;
}

function shellArgument(value: string): string {
  return "'" + value.replaceAll("'", "'\\''") + "'";
}

/** Add role prompts and a bounded summary of the scoped cooperation view. */
const bounded = (text: string, bytes: number) => limitMathOutput(text, bytes, 'head');
function buildCooperativeContext(problem: SolverProblem, cooperation: CooperationState, context: ContextBundle,
  action: CooperativeAction, operation: ResearchOperation): ContextBundle {
  const summary = cooperation.tasks.map(node => ({
    ...(action.kind === 'task' && node.task.id === action.task.id ? { id: node.task.id } : node.task),
    status: node.status, attempts: node.attempts,
    groupId: taskGroup(node.task), producer: node.assignment?.workerId, sharing: node.task.sharing ?? 'problem',
    feedback: node.feedback && bounded(node.feedback, 2500), finding: node.finding,
    integratedCommit: node.integratedCheck?.commit, checkedSourceDigest: node.integratedCheck?.sourceDigest,
    actualReferences: (node.integratedCheck ?? node.proof)?.references }));
  const rules = action.kind === 'review'
    ? 'You are the Independent Reviewer. Leave Lean sources unchanged. Check this fixed proof against the original question, assumptions and Lean evidence. Write one JSON object in RESEARCH.md: {"verdict":"accepted|changes_requested"}. Optional summary and evidenceRefs explain the decision.\n'
    : action.kind === 'solve'
    ? 'You are the Primary Solver. Start proving the entire original problem immediately and retain your proof context across turns. Continue solving while peers work. Prove small supporting lemmas locally. Request help only for a concrete independent bottleneck by writing one JSON object in RESEARCH.md, plain or in a math-help fence: {"requests":[{"id":"helper","kind":"lemma","objective":"...","theoremName":"Namespace.helper","type":"ACTUAL_CLOSED_LEAN_TYPE","proofPath":"owned/file.lean"}]}. Use actual names and a full closed type in the frozen original context, with every parameter and hypothesis explicit. An untyped research request is advisory and must leave Lean sources unchanged. Request at most one task per peer; optional dependsOn may name other requests. Never delegate original goals. Keep request ids and revisions stable while work is useful; revise or remove requests to replace work. Helpers have isolated worktrees and do not edit your sources. COOPERATION.json reports checked deliveries and their commits; inspect the saved sources with git show COMMIT:PROJECT_RELATIVE_PATH and selectively copy useful checked helpers, preserving your current proofs. Claims and notifications alone are not proof evidence. Ordinary notes are allowed when no help is needed. The host checks every original target and obtains an independent review of the fixed complete proof.\n'
    : action.kind !== 'task'
    ? `You are the Lead. Choose routes and delegate independent work to researchers and the engineer. Save the initial task graph and return before running Lean diagnostics or investigating proofs; delegate uncertain connections and consistency checks to researchers; leave Lean sources unchanged during planning. Write one JSON object in RESEARCH.md: {"tasks":[{"id":"helper","kind":"lemma","objective":"...","proofPath":${JSON.stringify(problem.ownedFiles.find(file => file.endsWith('.lean')))},"theoremName":"Namespace.helper","type":"∀ (P : Prop), P → P"},{"id":"goal","kind":"goal","objective":"...","theoremName":"Original.target","dependsOn":["helper"]}]}. Include every original target once. This example shows the schema only: replace its names, objectives and sample type with actual tasks and full closed Lean types, including all parameters and hypotheses. Never copy placeholder types. If no exact helper proposition is known, use an untyped research/sketch task. Choose proofPath from ${JSON.stringify(problem.ownedFiles.filter(file => file.endsWith('.lean')))}; goals infer it from theoremName, and lemmas may omit it only when one Lean file is owned. Use lemma tasks whenever workers should save proofs; research/sketch tasks without an exact typed target only return advisory findings and restore temporary probes. Typed research tasks are normalized to lemma tasks. dependsOn defaults to []; revision to 0. Change objectives, dependencies or revision to retry a route. conditional:true allows fixed typed lemma premises. statementReview:true with informalStatement requests meaning review. Optional groups set ownership, sharing and budgets.\n`
    : ['research', 'sketch'].includes(action.task.kind)
    ? 'You are a Mathematical Researcher. Explore the assigned question, report evidence and unresolved gaps, and leave Lean sources unchanged. Write ordinary Markdown findings in RESEARCH.md. Optionally use JSON {"summary":"findings and evidence","needsDecision":true} to request a route change. Optional conclusion is supporting, refuted or inconclusive; findings remain advisory.\n'
    : 'Prove the assigned Lean declaration with its exact requested type. Add newly named supporting helpers in owned Lean files as needed. You may repair proof bodies of solver-created lemmas while preserving their names, parameters, types and placement. Preserve original declarations, other original goals and definition bodies. Conditional tasks may reference fixed dependency lemmas; do not add stubs or extra assumptions. Check the complete saved target file and its local imports before delivery; a Helpers-only check does not check Submission. Save concise notes in RESEARCH.md and return for host checking and integration.\n';
  const sharing = action.kind === 'task'
    ? `To share before returning, append a JSON line to ${assignmentDeliveryFile(action.assignment)}: {"summary":"progress or gap"}. For a ready proof, save the allowed sources and notes, then return. Git metadata is managed by the host; do not run git add or git commit. The host freezes the saved sources and independently checks and integrates them after your turn ends. Do not truncate the delivery log. Progress reports remain advisory.\n`
      : '';
  return { ...context, assignment: action, instructions: context.instructions + '\n' + rules +
    'Original declarations retain the frozen source order shown below. A goal cannot depend on a later original goal in the same file. Extract their shared argument into a newly named lemma before both goals; preserve every other original proof and declaration placement.\n' +
    'COOPERATION.json contains live peer work, gaps and checked results; never edit it. Structured responses use one JSON object, plain or in a math/json fence, replacing old responses. The host manages versions, receipts and budgets, and independently checks all original targets. Unproved dependencies and reviews remain advisory.\n',
    message: context.message + '\n\nCooperative assignment:\n' + JSON.stringify(action) +
      '\n\nLead task graph and host feedback:\n' + bounded(JSON.stringify(summary), 14000) +
      '\n\nRoute groups and budgets:\n' + bounded(JSON.stringify(cooperation.groups ?? []), 6000) +
      `\nPlan error: ${cooperation.error ?? 'none'}\nReview: ${JSON.stringify(cooperation.review ?? null)}` +
      '\nStatement reviews: ' + bounded(JSON.stringify(cooperation.statementReviews?.filter(review => review.status !== 'superseded')
        .map(statementReviewSummary) ?? []), 16000) +
      '\nFrozen declaration order by file: ' + bounded(JSON.stringify(Object.fromEntries(Object.entries(problem.declarations)
        .map(([file, declarations]) => [file, declarations.map(declaration => declaration.name)]))), 4000) +
      `\nOriginal targets: ${JSON.stringify(problem.targets)}\nYour role: ${action.kind === 'review' ? 'reviewer' : action.kind === 'solve' ? 'primary solver' : action.kind === 'task' ? action.task.kind === 'goal' ? 'engineer' : 'researcher' : 'lead'}` + '\n' + sharing +
      (operation === 'direct' ? '' : `Research operation: ${operation}.\n`) };
}
