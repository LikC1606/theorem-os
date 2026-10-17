import path from 'node:path';
import fs from 'node:fs';
import { readMathText } from '../../math/mathRuntimeIo';
import { assertMathCanonicalPath } from '../../math/paths';
import { mathematicsRuntimeInstruction } from '../../math/mathRuntimeEnvironment';
import type { SolverRunState } from '../archive';
import { committedSource, type SolverProblem } from '../problem';
import type { ProofCheck } from './evidence';
import { solverProofFeedback, type SolverFailure } from '../feedback';
import type { ResearchOperation } from './value';
import { assignmentDeliveryFile, type CooperativeAction } from '../tasks';
import type { CooperationState } from '../cooperation';
import { statementReviewSummary, type StatementAction, type StatementReview } from '../statementReview';
import { buildProofContinuation } from '../progress';
import { compileTaskContext, frozenSourceContext, TaskContextError,
  type ContextManifest, type ContextSection, type TaskContextInput } from '../contextCompiler';

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
  /** Prompt byte allowance only; this does not limit solving time or turns. */
  maxContextBytes?: number;
  /** Pure fixture context; real frozen problems always load their committed source. */
  frozenContexts?: Readonly<Record<string, string>>;
}>;
export type ContextBundle = Readonly<{
  assignment?: CooperativeAction;
  instructions: string;
  message: string;
  scope: 'original-problem-and-allowed-library' | 'fixed-statement';
  sources: Readonly<{ problemReceiptDigest: string }>;
  manifest?: ContextManifest;
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
Edit only ${task.ownedFiles.map(file => path.join(access.worktree, task.projectRelative, file)).join(', ')}, ${path.join(access.worktree, 'RESEARCH.md')}${access.assignment?.kind === 'task' ? `, ${path.join(access.worktree, assignmentDeliveryFile(access.assignment.assignment))}` : ''}.
Save RESEARCH.md and delivery logs at these exact worktree-root paths, including when a diagnostic command runs inside the Lean project subdirectory.
Preserve original declaration kinds, names, parameters, types, assumptions, existing imports, options and namespace/section context. Original goals may include def declarations whose bodies must be filled; retain all other original definition bodies. You may add explicit Mathlib.* imports from the pinned library or frozen local modules already imported by the original owned files, without import cycles; do not edit trusted problem or package files. Completed proofs must not use sorry, admit, native_decide, unsafe or new axioms. Do not read external candidate solutions.
${taskRules}Use installed library lemmas and test uncertain bridges early. Batch independent searches and reads, reuse results, bound output in bytes and show the earliest Lean error and goal. The host launches the cooperative agents; do not spawn agents inside this session. Lead planning saves a task graph and returns promptly; assigned workers investigate and prove it.
For diagnostics, run ${command} check-lean --workspace ${shellArgument(path.join(access.worktree, task.projectRelative))} --file 'OWNED_FILE.lean' --timeout-seconds 0. It compiles saved sources with pinned imports and bounded output. Poll a returned process ID. A timeout is inconclusive. Repair the earliest error; avoid rebuilding dependencies or repeating unchanged checks. For math_original_context_changed or math_original_declaration_changed, use the reported file and recovery instructions to restore the offending context or declaration from the seed commit while preserving new proof work, then retry the saved-file check. Keep helper-specific scopes and instances inside their proofs. If the environment is unavailable or the same startup error remains after a repair, report it and return.
Add helpers in owned modules; definitions may be noncomputable. For type lookup, add single-name #check commands such as #check Finset.sum_eq_single in the existing namespace. For instance lookup, use #synth MeasureSpace ℝ or parenthesize complex types, such as #synth Fintype (Fin 2). If a known library declaration is unavailable, find its module in the installed corpus and import that explicit Mathlib.* module in the owned file; an unknown name alone does not establish a missing library theorem. Check the actual saved file, remove probes before delivery, and save checked helpers, gaps and next steps in RESEARCH.md. Keep this file as a concise current checkpoint; replace obsolete status instead of appending transcripts. Earlier committed notes remain in git history. Then return for independent host checking. Turns may be checkpointed and resumed. Verify computational results in Lean.
${access.corpusFile ? `For library lookup, run ${command} search-lean --workspace ${shellArgument(access.retrievalRoot)} --corpus ${shellArgument(access.corpusFile)} --sha256 ${shellArgument(access.environment.DEEPSCIENTIST_MATH_RETRIEVAL_CORPUS_SHA256!)} --query 'KEYWORDS' --query 'OTHER_KEYWORDS'. Batch up to 8 short queries; use --goal 'LEAN_GOAL_AND_CONTEXT' for local variables and types. Ranking is advisory. Confirm types and known names with Lean #check before expanding a search: generated and core declarations may have no Mathlib source header.\n` : ''}${mathematicsRuntimeInstruction(access.environment.DEEPSCIENTIST_MATH_ENV_FILE)}`;
  const originalProblem = `${access.taskText}\n\nOriginal problem:\n${task.contract.formalStatement}`;
  let message = access.sourceFeedback || (state.check && !state.check.passed
    ? solverProofFeedback(state.check, access.previousCheck, access.previousFailures ?? state.failures)
    : originalProblem);
  const cooperation = state.cooperation;
  let checkpoint: string | undefined;
  if (!state.threadId && state.previousThreadIds?.length) {
    const notes = path.join(access.worktree, 'RESEARCH.md');
    if (fs.existsSync(notes)) {
      assertMathCanonicalPath(notes);
      // A checkpoint is optional. Its full text is either selected or explicitly omitted by the compiler.
      checkpoint = readMathText(notes, 1_000_000);
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
  const compilation = { problem: task, cooperation, action: access.assignment, taskText: access.taskText,
    feedback: message.startsWith(originalProblem) ? message.slice(originalProblem.length).trim() || undefined : message, checkpoint,
    frozenContexts: readFrozenContexts(task, access),
    maxContextBytes: access.maxContextBytes, environmentDigest: state.environmentDigest };
  return access.assignment && cooperation ? buildCooperativeContext(task, cooperation, bundle, access.assignment,
    access.operation ?? 'direct', compilation) : { ...bundle, ...compileTaskContext({ ...compilation, instructions }) };
}

function shellArgument(value: string): string {
  return "'" + value.replaceAll("'", "'\\''") + "'";
}

const frozenContextCache = new Map<string, Readonly<Record<string, string>>>();
function readFrozenContexts(problem: SolverProblem, access: ContextAccess): Readonly<Record<string, string>> {
  if (!problem.workspace && access.frozenContexts) return access.frozenContexts;
  const key = JSON.stringify([problem.receiptDigest, problem.baseCommit, access.worktree, problem.workspace]);
  const cached = frozenContextCache.get(key);
  if (cached) return cached;
  const contexts = Object.fromEntries(problem.ownedFiles.filter(file => file.endsWith('.lean')).map(file => {
    if (path.posix.basename(file) === 'Solution.lean') throw new TaskContextError('math_context_missing_required', `forbidden-source:${file}`);
    let source: string | undefined;
    for (const repository of [...new Set([access.worktree, problem.workspace].filter(Boolean))]) {
      try { source = committedSource(repository, problem.baseCommit, path.posix.join(problem.projectRelative, file)); break; }
      catch { /* A newly prepared fixture may expose the frozen object only in its source repository. */ }
    }
    if (source === undefined) throw new TaskContextError('math_context_missing_required', `frozen-source:${file}`);
    return [file, frozenSourceContext(problem, file, source)];
  }));
  frozenContextCache.set(key, contexts);
  if (frozenContextCache.size > 16) frozenContextCache.delete(frozenContextCache.keys().next().value!);
  return contexts;
}

/** Add role rules; the compiler selects a scoped, versioned mathematical context for dispatch. */
function buildCooperativeContext(problem: SolverProblem, cooperation: CooperationState, context: ContextBundle,
  action: CooperativeAction, operation: ResearchOperation, compilation: Omit<TaskContextInput, 'instructions'>): ContextBundle {
  const rules = action.kind === 'review'
    ? 'You are the Independent Reviewer. Leave Lean sources unchanged. Check this fixed proof against the original question, assumptions and Lean evidence. Write one JSON object in RESEARCH.md: {"verdict":"accepted|changes_requested"}. Optional summary and evidenceRefs explain the decision.\n'
    : action.kind === 'solve'
    ? 'You are the Primary Solver. Start proving the entire original problem immediately and retain your proof context across turns. Continue solving while peers work. Prove small supporting lemmas locally. Request help only for a concrete independent bottleneck by writing one JSON object in RESEARCH.md, plain or in a math-help fence: {"requests":[{"id":"helper","kind":"lemma","objective":"...","theoremName":"Namespace.helper","type":"ACTUAL_CLOSED_LEAN_TYPE","proofPath":"owned/file.lean"}]}. Use actual names and a full closed type in the frozen original context, with every parameter and hypothesis explicit. An untyped research request is advisory and must leave Lean sources unchanged. Request at most one task per peer; optional dependsOn may name other requests. Never delegate original goals. Keep request ids and revisions stable while work is useful; revise or remove requests to replace work. Helpers have isolated worktrees and do not edit your sources. COOPERATION.json reports checked deliveries and their commits; inspect the saved sources with git show COMMIT:PROJECT_RELATIVE_PATH and selectively copy useful checked helpers, preserving your current proofs. Claims and notifications alone are not proof evidence. Ordinary notes are allowed when no help is needed. The host checks every original target and obtains an independent review of the fixed complete proof.\n'
    : action.kind !== 'task'
    ? `You are the Lead. Choose routes and delegate independent work to researchers and the engineer. Save the initial task graph and return before running Lean diagnostics or investigating proofs; delegate uncertain connections and consistency checks to researchers; leave Lean sources unchanged during planning. Write one JSON object in RESEARCH.md: {"tasks":[{"id":"helper","kind":"lemma","objective":"...","proofPath":${JSON.stringify(problem.ownedFiles.find(file => file.endsWith('.lean')))},"theoremName":"Namespace.helper","type":"∀ (P : Prop), P → P"},{"id":"goal","kind":"goal","objective":"...","theoremName":"Original.target","dependsOn":["helper"]}]}. Include every original target once. This example shows the schema only: replace its names, objectives and sample type with actual tasks and full closed Lean types, including all parameters and hypotheses. Never copy placeholder types. If no exact helper proposition is known, use an untyped research/sketch task. Choose proofPath from ${JSON.stringify(problem.ownedFiles.filter(file => file.endsWith('.lean')))}; goals infer it from theoremName, and lemmas may omit it only when one Lean file is owned. Use lemma tasks whenever workers should save proofs; research/sketch tasks without an exact typed target only return advisory findings and restore temporary probes. Typed research tasks are normalized to lemma tasks. dependsOn defaults to []; revision to 0. Keep accepted task definitions stable; record progress in notes rather than rewriting objectives, which invalidates their checked deliveries. Revise a mathematical contract to change a route; changing only prose or revision does not resolve a recorded blocker. conditional:true allows fixed typed lemma premises. statementReview:true with informalStatement requests meaning review. Optional groups set ownership, sharing and budgets.\n`
    : ['research', 'sketch'].includes(action.task.kind)
    ? 'You are a Mathematical Researcher. Explore the assigned question, report evidence and unresolved gaps, and leave Lean sources unchanged. Replace inherited RESEARCH.md with findings for this assignment before returning; ordinary Markdown is supported. Timed checkpoints preserve progress and resume the same assignment without completing it. Optionally use JSON {"summary":"findings and evidence","needsDecision":true} to request a route change. Optional conclusion is supporting, refuted or inconclusive; findings remain advisory. To turn a useful bridge into proof work, add lemmaRequests:[{id,kind:"lemma",objective,theoremName,type,proofPath,dependsOn:[]}]. Supply new ids and full closed Lean types in your own route group. The host validates these proposals and presents them to Lead; adoption creates a separate typed assignment whose proof requires independent checking. A proposal does not authorize edits to Lean sources.\n'
    : 'Prove the assigned Lean declaration with its exact requested type. An original goal may be a def: fill only its body, retaining its frozen declaration kind, name, parameters, type and placement. Helper proof targets must be theorems or lemmas. Add newly named supporting helpers in owned Lean files as needed. You may repair proof bodies of solver-created lemmas while preserving their names, parameters, types and placement. Preserve other original goals and every other existing definition body. Conditional tasks may reference fixed dependency lemmas; do not add stubs or extra assumptions. Check the complete saved target file and its local imports before delivery; a Helpers-only check does not check Submission. Save concise notes in RESEARCH.md and return for host checking and integration.\n';
  const sharing = action.kind === 'task'
    ? `To share before returning, append a JSON line to ${assignmentDeliveryFile(action.assignment)}: {"summary":"progress or gap"}. For a ready proof, save the allowed sources and notes, then return. Git metadata is managed by the host; do not run git add or git commit. The host freezes the saved sources and independently checks and integrates them after your turn ends. Do not truncate the delivery log. Progress reports remain advisory.\n`
      : '';
  const continuation = buildProofContinuation(cooperation.tasks, { groups: cooperation.groups, environmentDigest: compilation.environmentDigest });
  const roleText = `Your role: ${action.kind === 'review' ? 'reviewer' : action.kind === 'solve' ? 'primary solver' : action.kind === 'task' ? action.task.kind === 'goal' ? 'engineer' : 'researcher' : 'lead'}` + '\n' + sharing +
    (operation === 'direct' ? '' : `Research operation: ${operation}.\n`);
  const routeRules = 'Report a stable local obstruction in a research/sketch response or progress delivery with blockers:[{mechanism:"stable local mechanism",scope:"exact affected inference",evidenceRefs:[],reopenOn:[{kind:"contract-changed"},{kind:"environment-changed"},{kind:"dependency-checked",taskId:"ACTUAL_DECLARED_DEPENDENCY_ID"}]}]. Use actual declared dependency ids; reopenOn may be omitted for the host default. A blocker is advisory and applies only to its stated inference. Repeating the same local premises, evidence and environment twice parks the affected task; it does not establish that the original theorem is false or impose a solving deadline. Preserve useful proofs and state an explicit reopening condition.\n';
  const leadRouteRules = action.kind === 'lead' ?
    'When the original-goal frontier is stalled, use new findings to split the substantive missing argument into independently provable exact lemma tasks and a closing consumer. Changing notation or assuming the original bound in a wrapper does not reduce that gap. A paper theorem is a route reference; assign every unproved analytic premise explicitly. Preserve existing checked task contracts. If the available inputs give no further concrete step, retain the blockers and explain the specific new input needed to resume. The host will reconsider unchanged mathematical input only once, including across restarts.\n' +
    'For a parked task, assign a targeted feasibility check or a discriminating experiment, or change a relevant mathematical input. A revision number, reworded objective or unrelated helper does not resolve the recorded obstruction. You may declare alternative proofRoutes:[{id:"route_id",targetTaskId:"original_goal_task_id",prerequisiteTaskIds:["typed_lemma_task_id"],closingTaskId:"typed_closing_lemma_task_id"}]. Replace schema ids with actual task ids. Every route input must be a typed lemma with its full exact closed type; the closing lemma dependsOn must cover all route prerequisites. All prerequisites within one route are required together; routes for one target are alternatives. The target\'s ordinary dependsOn remain additional requirements. A checked closing lemma enables an original-goal attempt. A route is closed only after the original goal passes its strict host check and its Lean proof actually references that closing lemma; advisory findings and a conditional bridge never supply formal acceptance.\n' : '';
  const attemptRules = action.kind === 'task' ?
    'Before continuing, read the current task feedback and relevant saved results. Identify the unresolved inference, its intended consumer, and the cheapest check that can distinguish your next hypothesis from an already failed approach. Reuse checked declarations and exact library signatures. Save the new evidence, failed approach or reusable draft in a concise checkpoint. If nothing relevant changed and no new discriminating check is available, report the specific missing input instead of repeating searches, submitting identical files or creating a renamed equivalent task. New research evidence can be useful before any theorem is proved.\n' : '';
  const instructions = context.instructions + '\n' + rules + attemptRules +
    (action.kind === 'lead' ? 'Use the proof-continuation snapshot to identify the original goal\'s current mathematical frontier. Prefer consuming relevant checked lemmas before creating more auxiliary work; give each new helper an intended consumer and explicitly assign every substantive missing premise. Keep useful alternative routes visible. A lemma without a recorded consumer may still be useful; investigate its connection rather than deleting it. Planned dependencies, actual Lean proof references and conditional references are reported separately. Do not count auxiliary lemma totals as completion of the original problem. The host obtains fixed-candidate review after the complete proof is checked; mark any advisory final-candidate task with reviewScope:"final-candidate" so it waits for freshly checked original goals. Use a distinct task with reviewScope:"feasibility" for independent mathematical route checks before a complete candidate exists. Inspect validated lemmaRequests in deliveries and adopt useful exact proposals as separate lemma tasks; proposals and their local checks are advisory. Advisory research may start before its planned dependencies are proved; use typed proof tasks when a consumer must wait for checked premises.\n' :
      action.kind === 'task' && ['lemma', 'goal'].includes(action.task.kind) ? 'Inspect relevant checked inputs and their exact declarations before reconstructing an argument. Save the concrete consumer application and discharge every premise; report the remaining original-goal obstacle in RESEARCH.md.\n' : '') +
    (action.kind === 'task' && ['research', 'sketch'].includes(action.task.kind)
      ? 'Before restoring a temporary Lean probe, retain its complete reusable code, namespace/context, exact declaration names and proposed consumer in a lean fence in worktree-root RESEARCH.md. A prose claim that Lean passed is not a recoverable proof. To report a successful local check explicitly, use leanChecks:[{status:"passed",path:"RESEARCH.md",declarations:["Qualified.name"]}] in the single JSON response and keep the complete code outside that JSON in a lean fence. The host binds retained artifacts to this problem, assignment and commit; every local check remains advisory until a separate typed host check passes.\n' : '') +
    routeRules + leadRouteRules +
    'Original declarations retain the frozen source order shown below. A goal cannot depend on a later original goal in the same file. Extract their shared argument into a newly named lemma before both goals; preserve every other original proof and declaration placement.\n' +
    'COOPERATION.json contains scoped live peer work, findings, gaps and checked results; leave it and CONTEXT-MANIFEST.json unchanged. The context compilation manifest identifies included and omitted material and why it was omitted. Exact mathematical interfaces and original assumptions are mandatory; retrieve full proof sources and context using their immutable commit/path references. Structured responses use one JSON object, plain or in a math/json fence, replacing old responses. The host manages versions, receipts and budgets, and independently checks all original targets. Unproved dependencies and reviews remain advisory.\n' +
    roleText;
  const optional: ContextSection[] = [
    { id: 'plan-feedback', kind: 'feedback', text: `Review: ${JSON.stringify(cooperation.review ?? null)}` },
    { id: 'proof-continuation', kind: 'continuation', text: '\nProof continuation (stored evidence, not replayed; planned use and actual proof use are separate):\n' + JSON.stringify(continuation) },
    { id: 'statement-reviews', kind: 'statement-review', text: 'Statement reviews: ' + JSON.stringify(cooperation.statementReviews?.filter(review => review.status !== 'superseded')
      .map(statementReviewSummary) ?? []) },
  ];
  return { ...context, assignment: action, instructions,
    ...compileTaskContext({ ...compilation, instructions, optional,
      mandatory: [{ id: 'assignment-policy', kind: 'assignment', text: roleText }] }) };
}
