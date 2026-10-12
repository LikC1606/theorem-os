import path from 'node:path';
import fs from 'node:fs';
import { assertMathCanonicalPath } from '../../math/paths';
import { mathematicsRuntimeInstruction } from '../../math/mathRuntimeEnvironment';
import type { SolverRunState } from '../archive';
import type { SolverProblem } from '../problem';
import type { ProofCheck } from './evidence';
import { solverProofFeedback, type SolverFailure } from '../feedback';
import type { ResearchOperation } from './value';
import { taskGroup, taskVersion, assignmentDeliveryFile, type CooperativeAction } from '../tasks';
import type { CooperationState } from '../cooperation';
import type { StatementAction, StatementReview } from '../statementReview';

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
  sources: Readonly<{ problemReceiptDigest: string; checkCommit?: string; retrievalDigest?: string }>;
}>;

/** Backtranslation is built from the formal snapshot alone, in a fresh session. */
export function buildStatementReviewContext(review: StatementReview, action: StatementAction, problemReceiptDigest: string): ContextBundle {
  const blind = action.kind === 'backtranslate';
  const instructions = 'You are the Independent Reviewer of one fixed Lean declaration. Read only STATEMENT.json and the supplied definitions in this workspace. ' +
    'Do not read parent directories, other workspaces, git history, task journals or external candidate solutions. Leave all snapshot inputs unchanged; write only RESEARCH.md. ' +
    'State all quantifiers, assumptions and relevant definitions explicitly. Flag ambiguous or unavailable definitions instead of guessing. ' +
    'A translation or review is advisory and grants no Lean proof acceptance. Bound tool output in bytes.\n' + (blind
      ? 'Translate the Lean statement into mathematics using its formal context only. The intended mathematical explanation is deliberately withheld. ' +
        'Write one math JSON block in RESEARCH.md: {"mathematics":"the statement, assumptions and relevant definitions"}. Optional assumptions, definitions and evidenceRefs are lists.\n'
      : 'Compare the saved independent backtranslation with the intended mathematics and premises below. Check missing hypotheses, changed quantifiers and changes of meaning. ' +
        'Write one math JSON block in RESEARCH.md: {"verdict":"accepted|changes_requested","summary":"findings and evidence"}. The host binds your response to the fixed snapshot.\n');
  return { instructions, scope: 'fixed-statement', sources: { problemReceiptDigest },
    message: 'Cooperative assignment:\n' + JSON.stringify(action) + '\n\nRead the fixed formal snapshot in STATEMENT.json.\n' + (blind ? '' :
      '\nIntended mathematics:\n' + review.intendedStatement + '\nPremises:\n' + JSON.stringify(review.premises) +
      '\nSaved independent backtranslation:\n' + JSON.stringify(review.translation)) };
}

/** M4 selects instructions and feedback without promoting retrieved or generated hints to evidence. */
export function buildResearchContext(task: SolverProblem, state: Readonly<SolverRunState>, access: ContextAccess): ContextBundle {
  const instructions = `You prove the original mathematical problem in Lean. Work only in this isolated worktree.\nEdit only ${task.ownedFiles.map(file => path.join(task.projectRelative, file)).join(', ')} and RESEARCH.md.\nPreserve every original declaration, definition and assumption. Do not use sorry, admit, native_decide, unsafe or new axioms in a completed proof. Do not read external candidate solutions.\nFor a difficult problem, briefly compare plausible routes and test the key bridge lemma before expanding a long proof. Prefer routes supported by installed library lemmas.\nBatch independent library searches and source reads in one tool call. Read only relevant declaration ranges; reuse known definitions and checked lemmas instead of rereading entire proof files. Bound tool output in bytes before returning it; show only the earliest Lean errors with their goal contexts.\nUse lake env lean on the changed proof file for diagnostics. Check a coherent local proof change, repair its earliest error, and avoid rebuilding dependencies or repeating a successful check without relevant edits.\nThe host independently checks the frozen commit after each turn. Keep RESEARCH.md concise: checked lemmas, failed arguments with their Lean goal/context, remaining obligations, current route and latest blocking error. End a turn when ready for a host check.\n${access.corpusFile ? `For library lookup, run bun ${shellArgument(path.join(access.root, 'bin/math.ts'))} search-lean --workspace ${shellArgument(access.retrievalRoot)} --corpus ${shellArgument(access.corpusFile)} --sha256 ${shellArgument(access.environment.DEEPSCIENTIST_MATH_RETRIEVAL_CORPUS_SHA256!)} --query 'KEYWORDS' --query 'OTHER_KEYWORDS'. Repeat --query up to 8 times to share one verified library scan. Use short library keywords; add --goal 'LEAN_GOAL_AND_CONTEXT' to rank results by the current target and available types. Keep local variable names in --goal rather than requiring them in --query. Ranking is a hint; test shortlisted premises at the actual proof position. Results include qualified names, source headers and active variable/open context; use Lean #check to confirm the full type. Check a known declaration name in Lean before searching: generated declarations and Lean core lemmas may have no explicit Mathlib source header.\n` : ''}${mathematicsRuntimeInstruction(access.environment.DEEPSCIENTIST_MATH_ENV_FILE)}`;
  const diagnostics = `\nFor local diagnostics, run bun ${shellArgument(path.join(access.root, 'bin/math.ts'))} check-lean --workspace ${shellArgument(path.join(access.worktree, task.projectRelative))} --file 'OWNED_FILE.lean' --timeout-seconds 0. This preflights original source constraints and compiles the saved file with pinned imports, waiting for completion. Do not pipe output through head; output is already bounded. If the command yields a process ID, poll that process rather than restarting the check. A timeout is inconclusive.\nWork in short turns: test one key bridge or complete one coherent proof step, save files and return. The host may interrupt a long turn to check saved sources and resume with diagnostics.\nBefore expanding a route, list every original obligation and the needed library lemmas, constructions and bridge proofs. A route addressing only one conjunct is incomplete. Verify the hardest missing bridge first. Check that optional computational tools are installed before depending on them; generated calculations still need Lean verification.\n`;
  let message = access.sourceFeedback || (state.check && !state.check.passed
    ? solverProofFeedback(state.check, access.previousCheck, access.previousFailures ?? state.failures)
    : `${access.taskText}\n\nOriginal problem:\n${task.contract.formalStatement}\n\nOnly the instructions above and host Lean checks determine acceptance.`);
  const cooperation = state.cooperation;
  if (cooperation) {
    const worker = state.workers?.find(record => record.worktree === access.worktree);
    const work = cooperation.tasks.find(node => node.assignment?.workerId === worker?.id && node.status === 'running')?.task;
    const selected = (cooperation.deliveries ?? []).filter(record => {
      if (record.status === 'superseded') return false;
      if (!record.taskId) return !work;
      const producer = cooperation.tasks.find(node => node.task.id === record.taskId && taskVersion(node.task) === record.taskDigest);
      return producer && (!work || taskGroup(work) === taskGroup(producer.task) || producer.task.sharing !== 'group') &&
        record.dependencies.every(dependency => cooperation.tasks.some(node => node.task.id === dependency.taskId && taskVersion(node.task) === dependency.taskDigest));
    }).sort((a, b) => Number(work?.dependsOn.includes(a.taskId ?? '')) - Number(work?.dependsOn.includes(b.taskId ?? ''))).slice(-8);
    const references = selected.map(({ evidence: _evidence, ...record }) => record);
    message += '\n\nCurrent-version deliveries selected for this task (retain unproved obligations):\n' +
      Buffer.from(JSON.stringify(references)).subarray(0, 12000).toString('utf8').replace(/\uFFFD$/u, '');
  }
  if (!state.threadId && state.previousThreadIds?.length) {
    message = `${access.taskText}\n\nOriginal problem:\n${task.contract.formalStatement}\n\n${message}`;
    const notes = path.join(access.worktree, 'RESEARCH.md');
    if (fs.existsSync(notes)) {
      assertMathCanonicalPath(notes);
      const fd = fs.openSync(notes, fs.constants.O_RDONLY | fs.constants.O_NOFOLLOW);
      try {
        const stat = fs.fstatSync(fd);
        if (!stat.isFile() || stat.nlink !== 1) throw new Error('math_research_notes_invalid');
        const text = Buffer.alloc(6000), count = fs.readSync(fd, text, 0, text.length, 0);
        message += `\n\nCurrent research checkpoint (advisory; recheck claims in Lean):\n${text.subarray(0, count).toString('utf8')}`;
      } finally { fs.closeSync(fd); }
    }
  }
  if (!state.cooperation && access.operation && access.operation !== 'direct' && !access.sourceFeedback) {
    const research = state.lemmaResearch;
    message += `\n\nResearch operation: ${access.operation}.\n` +
      'Propose one new ordinary theorem before one original target in the same owned Lean file. Use its unqualified name in the target proof. Its full closed type must include all original assumptions and parameters, using qualified library names. Keep every original declaration unchanged.\n' +
      'Keep one math JSON block in RESEARCH.md: {"proofPath":"owned/file.lean","target":"Original.qualifiedTarget","lemma":"Original.helper","type":"FULL_CLOSED_LEAN_TYPE"}.\n' +
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
  const bundle: ContextBundle = { instructions: instructions.replace('Use lake env lean on the changed proof file for diagnostics.',
    'Use the bounded check-lean command below on the changed proof file for diagnostics.') + diagnostics +
    '\nPreserve original imports, options, namespace and section context. Add ordinary helpers in existing owned modules; a new helper definition may be noncomputable. Keep proved helpers in the existing imported helper module when available so unchanged imports can be reused.\n' +
    'Before expanding a proof, confirm that the provided checker starts and returns Lean diagnostics. If it reports SANDBOX_UNAVAILABLE or a startup error, save the exact blocker and return; do not keep retrying it or expand an unverified construction.\n' +
    'A complete local check must compile the actual saved owned file. Never add a noncomputable section, extra assumptions, imports or options to a temporary copy and report that as a successful check of the submission. Focused fragments only verify those fragments.\n' +
    'Keep RESEARCH.md within 6000 bytes, recording checked helper names, failed arguments and their missing premises, remaining obligations and the next concrete step. Update it before returning; a fresh context continues from these notes and the saved sources.\n',
    message, scope: 'original-problem-and-allowed-library',
    sources: { problemReceiptDigest: task.receiptDigest, checkCommit: state.check?.commit,
      retrievalDigest: access.environment.DEEPSCIENTIST_MATH_RETRIEVAL_CORPUS_SHA256 } };
  return access.assignment && cooperation ? buildCooperativeContext(task, cooperation, bundle, access.assignment, access.operation ?? 'direct') : bundle;
}

function shellArgument(value: string): string {
  return "'" + value.replaceAll("'", "'\\''") + "'";
}

/** M4 owns role prompts and selects the allowed cooperation records. */
const bounded = (text: string, bytes: number) => Buffer.from(text).subarray(0, bytes).toString('utf8').replace(/\uFFFD$/u, '');
function buildCooperativeContext(problem: SolverProblem, cooperation: CooperationState, context: ContextBundle,
  action: CooperativeAction, operation: ResearchOperation): ContextBundle {
  const records = cooperation.tasks;
  const summary = records.map(node => ({ ...node.task, status: node.status, attempts: node.attempts,
    groupId: taskGroup(node.task), producer: node.assignment?.workerId, sharing: node.task.sharing ?? 'problem',
    feedback: node.feedback && bounded(node.feedback, 2500), finding: node.finding,
    integratedCommit: node.integratedCheck?.commit, checkedSourceDigest: node.integratedCheck?.sourceDigest,
    actualReferences: (node.integratedCheck ?? node.proof)?.references }));
  const rules = action.kind === 'review'
    ? 'You are the Independent Reviewer. Leave Lean sources unchanged. Check this fixed proof against the original question, assumptions and Lean evidence. Write one math JSON block in RESEARCH.md: {"verdict":"accepted|changes_requested","summary":"findings and concrete evidence"}.\n'
    : action.kind !== 'task'
    ? 'You are the Lead. Choose a route and split independent work among researchers and the engineer. Write one math JSON block in RESEARCH.md: {"tasks":[{"id":"helper","kind":"lemma","objective":"...","theoremName":"Namespace.helper","type":"FULL_CLOSED_LEAN_TYPE"},{"id":"goal","kind":"goal","objective":"...","theoremName":"Original.target","dependsOn":["helper"]}]}. Include every original target once. Use kind="research" for open questions and kind="sketch" for unproved arguments. dependsOn defaults to []; revision defaults to 0. proofPath is inferred for original goals or a single owned Lean file; specify it otherwise. Revise the objective, dependencies or revision to change a route or retry blocked work. Optional conditional:true permits a parent proof using fixed typed lemma dependencies; statementReview:true with informalStatement requests independent meaning review. Optional groups set route ownership, sharing and budgets.\n'
    : ['research', 'sketch'].includes(action.task.kind)
    ? 'You are a Mathematical Researcher. Explore the assigned question, report evidence and unresolved gaps, and leave Lean sources unchanged. Write one math JSON block in RESEARCH.md: {"summary":"findings and evidence"}. Add needsDecision:true when the Lead must change the route or assumptions. Optional conclusion is supporting, refuted or inconclusive; findings remain advisory.\n'
    : 'You are proving one assigned Lean declaration. Change only its proof and ordinary supporting helpers in the assigned file; preserve other declarations and the exact requested type. Save the proof, leave concise notes in RESEARCH.md and return. The host checks and integrates it. For a conditional task, reference the fixed dependency lemmas in the ordinary proof; never add stubs, sorry, axioms or extra assumptions.\n';
  const sharing = action.kind === 'task'
    ? `To share before returning, append a JSON line to ${assignmentDeliveryFile(action.assignment)}: {"summary":"progress or gap"}. For a ready proof, commit allowed sources and notes, then append {"kind":"proof","commit":"full git commit","summary":"result"}. Do not truncate this log. The host binds messages to this assignment and checks proofs; keep a delivered proof fixed.\n`
    : '';
  const strategy = operation === 'direct' ? '' : `Research operation: ${operation}.\n` + (action.kind === 'lead'
    ? 'Choose a small graph of typed bridge lemmas. Test the hardest connection first, then let independent researchers prove the helpers while the engineer constructs conditional parent proofs. Use the task graph format above; keep all original targets.\n'
    : operation === 'prove-lemma' ? 'Prove the assigned closed helper independently. Test its key library premises first; leave unrelated original goals to the engineer.\n'
    : operation === 'bridge' ? 'Test the assigned parent connection using only the fixed dependency statements. Report any missing or overly strong hypothesis before investing in the helper proofs.\n'
    : 'Reuse the checked assigned dependencies to close this original goal. Check their exact types and versions before expanding another proof.\n');
  return { ...context, assignment: action, instructions: context.instructions.replace('Keep RESEARCH.md within 6000 bytes', 'Keep RESEARCH.md within 64000 bytes')
    .replace('and RESEARCH.md.', 'and RESEARCH.md; you may also append to the assigned delivery log.') + '\n' + rules +
    'Read the host-maintained COOPERATION.json for peer work, gaps and checked results. Never edit it. Replace the response block rather than adding another; optional evidenceRefs lists sources. Assignment identities, dependency versions, Lean receipts and budgets are managed by the host. Unproved dependencies and reviews never establish the original proof; final acceptance checks the original targets independently.\n',
    message: context.message + '\n\nCooperative assignment:\n' + JSON.stringify(action) +
      '\n\nLead task graph and host feedback:\n' + bounded(JSON.stringify(summary), 14000) +
      '\n\nRoute groups and budgets:\n' + bounded(JSON.stringify(cooperation.groups ?? []), 6000) +
      `\nPlan error: ${cooperation.error ?? 'none'}\nReview: ${JSON.stringify(cooperation.review ?? null)}` +
      '\nStatement reviews: ' + bounded(JSON.stringify(cooperation.statementReviews?.filter(review => review.status !== 'superseded')
        .map(({ workspace: _workspace, files: _files, ...review }) => review) ?? []), 16000) +
      `\nOriginal targets: ${JSON.stringify(problem.targets)}\nYour role: ${action.kind === 'review' ? 'reviewer' : action.kind === 'task' ? action.task.kind === 'goal' ? 'engineer' : 'researcher' : 'lead'}` + '\n' + sharing + strategy };
}
