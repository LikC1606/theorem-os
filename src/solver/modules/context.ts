import path from 'node:path';
import fs from 'node:fs';
import { mathDigest, canonicalMathJson, readMathText } from '../../math/mathRuntimeIo';
import { assertMathCanonicalPath } from '../../math/paths';
import { readLeanResidualGoalSnapshot } from '../../math/leanResidualGoals';
import { mathematicsRuntimeInstruction } from '../../math/mathRuntimeEnvironment';
import type { SolverRunState } from '../archive';
import { committedSource, type SolverProblem } from '../problem';
import type { ProofCheck } from './evidence';
import { solverProofFeedback, type SolverFailure } from '../feedback';
import type { ResearchOperation } from './value';
import { assignmentDeliveryFile, initialPlanDeliveryFile, isFeasibilityReview, taskGroup, taskVersion, type CooperativeAction } from '../tasks';
import type { CooperationState } from '../cooperation';
import { statementReviewSummary, type StatementAction, type StatementReview } from '../statementReview';
import { buildProofContinuation } from '../progress';
import { researchHandoffs } from '../researchHandoffs';
import { originalGoalTaskFocus, originalGoalFrontierSnapshot } from './search';
import { createProofRoutePriorityIndex, selectProofRoutePriorityContext } from '../routePriority';
import { cooperativeWorkContract } from './contracts';
import { knowledgeContextConsumers, knowledgeContextSections, type KnowledgeContextSnapshot, type KnowledgeRetrieval } from '../knowledgeContext';
import { continuationContextSection, readContinuationSnapshot, type ContinuationSnapshot } from '../continuationInput';
import { knowledgeApplicationContextSections } from '../knowledgeApplications';
import { compileTaskContext, frozenSourceContext, TaskContextError,
  type ContextManifest, type ContextSection, type TaskContextInput } from '../contextCompiler';
import type { CustomResearchModule, ResearchModuleSlot } from './policy';

export type ContextAccess = Readonly<{
  root: string;
  worktree: string;
  environment: NodeJS.ProcessEnv;
  taskText: string;
  continuation?: ContinuationSnapshot;
  corpusFile?: string;
  knowledgeFile?: string;
  knowledgeDigest?: string;
  knowledgeSnapshot?: KnowledgeContextSnapshot;
  retrievalRoot: string;
  sourceFeedback?: string;
  previousCheck?: ProofCheck;
  previousFailures?: readonly SolverFailure[];
  operation?: ResearchOperation;
  assignment?: CooperativeAction;
  /** Prompt byte allowance only; this does not limit solving time or turns. */
  maxContextBytes?: number;
  maxOptionalContextBytes?: number;
  customModuleRules?: readonly CustomResearchModule[];
  /** Pure fixture context; real frozen problems always load their committed source. */
  frozenContexts?: Readonly<Record<string, string>>;
}>;
export type ContextBundle = Readonly<{
  assignment?: CooperativeAction;
  workContract?: ReturnType<typeof cooperativeWorkContract>;
  instructions: string;
  message: string;
  scope: 'original-problem-and-allowed-library' | 'fixed-statement';
  sources: Readonly<{ problemReceiptDigest: string }>;
  manifest?: ContextManifest;
  knowledgeRetrievals?: readonly (KnowledgeRetrieval & { included: boolean; omissionReason?: string })[];
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
  if (Boolean(access.continuation) !== Boolean(state.continuationDigest)) throw new Error('math_continuation_identity_missing');
  if (access.continuation && access.continuation.digest !== state.continuationDigest)
    throw new Error('math_continuation_identity_changed');
  const continuation = access.continuation && readContinuationSnapshot(access.continuation.file, access.continuation.digest,
    { taskDigest: state.taskDigest, problemReceiptDigest: task.receiptDigest });
  if (Boolean(access.knowledgeFile) !== Boolean(access.knowledgeDigest)) throw new Error('math_knowledge_identity_missing');
  if (access.knowledgeSnapshot && (!access.knowledgeFile || access.knowledgeSnapshot.digest !== access.knowledgeDigest ||
      (state.knowledgeDigest && state.knowledgeDigest !== access.knowledgeSnapshot.digest)))
    throw new Error('math_knowledge_identity_changed');
  const knowledgeRules = access.knowledgeFile ?
    `Before developing a new proof or repeating a search, consult the saved theorem knowledge base: ${command} knowledge search --catalog ${shellArgument(access.knowledgeFile)} --sha256 ${shellArgument(access.knowledgeDigest!)} --environment ${shellArgument(state.environmentDigest)} --problem-receipt ${shellArgument(state.problem.receiptDigest)} --query 'MATHEMATICAL_KEYWORDS' --goal 'EXACT_LEAN_GOAL_AND_CONTEXT'. Batch up to eight --query arguments to share one search index. You may omit --query to search only the exact goal; goal shape and version compatibility labels are advisory. ` +
    `Inspect a hit with ${command} knowledge get --catalog ${shellArgument(access.knowledgeFile)} --sha256 ${shellArgument(access.knowledgeDigest!)} --id 'THEOREM_ID' --metadata --max-bytes 16000. Deferred fields have complete:false and a read handle; they are not empty or complete interfaces. Rerun the same metadata command with --field 'FIELD_NAME' --offset OFFSET, starting at read.startOffset and then following nextOffset until truncated:false. Concatenate text pages exactly; parse JSON fields only after all pages are joined. Read the complete type and premises before applying a candidate. ` +
    `Inspect recorded dependencies with ${command} knowledge dependencies --catalog ${shellArgument(access.knowledgeFile)} --sha256 ${shellArgument(access.knowledgeDigest!)} --id 'THEOREM_ID' --depth 2. Missing coverage is unknown. ` +
    `Inspect historical consumers with ${command} knowledge consumers --catalog ${shellArgument(access.knowledgeFile)} --sha256 ${shellArgument(access.knowledgeDigest!)} --id 'THEOREM_ID' --max-bytes 16000; follow nextOffset with --offset to continue. These are same-context local reference closures, not instantiated applications. Read each consumer's complete type, elaboration and source with its handles, then check the proposed application and remaining premises in the current problem. ` +
    `Read a dependency or definition in bounded excerpts with ${command} knowledge source --catalog ${shellArgument(access.knowledgeFile)} --sha256 ${shellArgument(access.knowledgeDigest!)} --id 'THEOREM_ID' --file 'ARCHIVED_FILE' --name 'QUALIFIED_DECLARATION' --max-bytes 16000; use --start-line 1 to inspect file context, or --offset NEXT_OFFSET to continue a truncated excerpt without repeating text. Excerpts do not establish complete context. ` +
    'Saved route findings are advisory research records with exact scopes, not accepted theorems. Search with --include-findings and inspect one with knowledge finding --catalog CATALOG --sha256 DIGEST --id FINDING_ID; follow its pagination to read the complete record. Recheck its assumptions, counterexample and reopening conditions against the current problem. ' +
    'When you try a saved theorem, optionally add knowledgeUses:[{id:"THEOREM_ID",catalogDigest:"PINNED_DIGEST",declaration:{name:"Qualified.adaptedHelper",file:"Owned/File.lean"}}] to the same JSON research/proof response in RESEARCH.md. The host records this as a reported origin and separately checks actual Lean references; a citation alone is not proof acceptance. ' +
    'For a specific application, add application:{expression:"CLOSED_LEAN_TERM",expectedType:"CLOSED_EXPECTED_TYPE",context:{file:"Owned/File.lean",declaration:"ASSIGNED_THEOREM"},arguments:[{parameter:"PARAMETER",value:"ACTUAL_ARGUMENT"}],additionalPremises:[],typeclassIssues:[],adaptationSteps:[],remainingGoals:[],reconsiderWhen:[]} inside that knowledgeUses item. Close local variables with explicit binders and lambdas. The host checks up to four selected expressions in isolated proof-erased snapshots and retains scoped successes and failures. This checks the requested type only: it does not establish that the type closes the original consumer, or accept any erased helper proof. Changed inputs require a fresh check. ' +
    `You may inspect one expression beforehand with ${command} check-lean --workspace ${shellArgument(path.join(access.worktree, task.projectRelative))} --file 'Owned/File.lean' --context 'ASSIGNED_THEOREM' --type 'CLOSED_EXPECTED_TYPE' --expression 'CLOSED_LEAN_TERM'. Do not scan all catalog entries with application checks. ` +
    'The task context may include bounded saved-theorem candidates already searched by the host for this exact assignment or the original-goal frontier. Inspect these candidates before repeating the same search; the manifest records hints omitted for context budget. An input-not-searched status or zero lexical matches does not establish that no useful theorem exists. ' +
    'Inspect the complete type, all premises and statement/proof dependencies before reuse. source-header types require the archived context and are not closed types. Search is lexical and a missing hit does not establish a missing theorem. These are historical checked sources, not declarations installed in this problem. Adapt only needed declarations into owned files, respect the frozen problem and allowed imports, then check their actual application with Lean and return for independent host acceptance. Never copy an entire archived Submission over current goals or inherit historical receipts. Record the knowledge theorem id and the consumer in RESEARCH.md.\n' : '';
  const taskRules = access.assignment?.kind === 'task' && access.assignment.task.kind === 'lemma'
    ? `This is a lemma task for ${access.assignment.task.theoremName}. You may repair solver-created lemma proofs and add newly named helpers in owned Lean files. Preserve existing helper statements, definition bodies and original goal proofs.\n`
    : '';
  const instructions = `You prove the original mathematical problem in Lean. Work only in this isolated worktree.
Edit only ${task.ownedFiles.map(file => path.join(access.worktree, task.projectRelative, file)).join(', ')}, ${path.join(access.worktree, 'RESEARCH.md')}${access.assignment?.kind === 'task' ? `, ${path.join(access.worktree, assignmentDeliveryFile(access.assignment.assignment))}` : ''}.
Save RESEARCH.md and delivery logs at these exact worktree-root paths, including when a diagnostic command runs inside the Lean project subdirectory.
Preserve original declaration kinds, names, parameters, types, assumptions, existing imports, options and namespace/section context. Original goals may include def declarations whose bodies must be filled; retain all other original definition bodies. You may add explicit Mathlib.* imports from the pinned library or frozen local modules already imported by the original owned files, without import cycles; do not edit trusted problem or package files. Completed proofs must not use sorry, admit, native_decide, unsafe or new axioms. Do not read external candidate solutions.
${taskRules}${knowledgeRules}${strategyAdvice(access, 'M1', 'Use installed library lemmas and test uncertain bridges early. Batch independent searches and reads, reuse results, bound output in bytes and show the earliest Lean error and goal.')} The host launches the cooperative agents; do not spawn agents inside this session. ${strategyAdvice(access, 'M5', 'Lead planning saves a task graph and returns promptly; assigned workers investigate and prove it.', Boolean(state.cooperation))}
For diagnostics, run ${command} check-lean --workspace ${shellArgument(path.join(access.worktree, task.projectRelative))} --file 'OWNED_FILE.lean' --timeout-seconds 0. It compiles saved sources with pinned imports and bounded output. Read firstBlocking and its exact position; follow diagnosticArtifacts for captured messages, local hypotheses and goals when previews are incomplete. Source/environment digests identify the checked inputs; inspect captureComplete before treating captured output as complete. To preflight an uncertain closed task type, add --type 'CLOSED_LEAN_TYPE' --context 'EXISTING_QUALIFIED_DECLARATION' with exactly one --file. This elaborates a type in a disposable proof-erased snapshot using that declaration's scopes; it does not check a proof or make future helper names available. Keep unavailable future dependencies explicit and revise an invalid interface before sending workers to prove it. Poll a returned process ID. A timeout is inconclusive. ${strategyAdvice(access, 'M3', 'Repair the earliest error; avoid rebuilding dependencies or repeating unchanged checks.')} For math_original_context_changed or math_original_declaration_changed, use the reported file and recovery instructions to restore the offending context or declaration from the seed commit while preserving new proof work, then retry the saved-file check. Keep helper-specific scopes and instances inside their proofs. If the environment is unavailable or the same startup error remains after a repair, report it and return.
For a finite Boolean inference, use ${command} check-finite --json 'JSON' --witnesses 16. Supply {"schema":"theorem-os.finite-boolean-cnf.v1","variables":["A"],"fixed":[],"clauses":[[{"variable":"A","value":true}]]}. Each clause is a disjunction of matching literals and all clauses must hold. Preserve the exact input data and returned digests, satisfyingCount and complete witnesses in your research evidence. A satisfying assignment can refute only a claimed contradiction of those constraints; it does not refute their geometric construction or the original theorem. Size-unsupported results are inconclusive. Enumeration and its translation remain advisory and must be formalized for proof acceptance.
Add helpers in owned modules; definitions may be noncomputable. For type lookup, add single-name #check commands such as #check Finset.sum_eq_single in the existing namespace. For instance lookup, use #synth MeasureSpace ℝ or parenthesize complex types, such as #synth Fintype (Fin 2). If a known library declaration is unavailable, find its module in the installed corpus and import that explicit Mathlib.* module in the owned file; an unknown name alone does not establish a missing library theorem. Check the actual saved file, remove probes before delivery, and save checked helpers, gaps and next steps in RESEARCH.md. ${strategyAdvice(access, 'M4', 'Keep this file as a concise current checkpoint; replace obsolete status instead of appending transcripts. Earlier committed notes remain in git history.')} Then return for independent host checking. Turns may be checkpointed and resumed. Verify computational results in Lean.
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
  const residualSnapshot = readLeanResidualGoalSnapshot({ projectRoot: path.join(access.worktree, task.projectRelative), env: access.environment,
    consumers: knowledgeContextConsumers(task, cooperation, access.assignment, state.environmentDigest) });
  const residualGoals = residualSnapshot.goals;
  const residualSections: ContextSection[] = residualGoals.map(goal => ({
    id: `residual-goal:${mathDigest(canonicalMathJson(goal))}`, kind: 'feedback', priority: 6,
    text: 'Current residual goal from complete, source-matched Lean diagnostics (advisory; not proof acceptance):\n' +
      JSON.stringify({ ...goal, goalText: undefined }) + '\n' + goal.goalText,
  }));
  if (residualSnapshot.omissions.length) residualSections.push({ id: 'residual-goals:reader-omissions', kind: 'feedback', priority: 6,
    text: 'Additional source-matched residual diagnostics were omitted by the bounded reader. Inspect the current diagnostic artifacts before treating these goals as fully covered:\n' +
      JSON.stringify(residualSnapshot.omissions) });
  const knowledgeSections = access.knowledgeSnapshot ? knowledgeContextSections({ problem: task, cooperation, action: access.assignment,
    knowledge: access.knowledgeSnapshot, environmentDigest: state.environmentDigest, residualGoals,
    residualOmissions: residualSnapshot.omissions }) : [];
  const applicationSections = access.knowledgeSnapshot ? knowledgeApplicationContextSections({
    uses: cooperation ? cooperation.deliveries?.flatMap(delivery => delivery.knowledgeUses ?? []) ?? [] : state.knowledgeUses ?? [],
    projectRoot: path.join(access.worktree, task.projectRelative), env: access.environment,
    environmentDigest: state.environmentDigest, catalogDigest: access.knowledgeSnapshot.digest,
    tasks: cooperation?.tasks.map(node => node.task) ?? task.targets.map((target, index) => ({ id: `original_goal_${index + 1}`,
      kind: 'goal' as const, revision: 0, objective: `Prove ${target.theoremName}`, dependsOn: [], ...target })),
  }) : [];
  const compilation = { problem: task, cooperation, action: access.assignment, taskText: access.taskText,
    feedback: message.startsWith(originalProblem) ? message.slice(originalProblem.length).trim() || undefined : message, checkpoint,
    frozenContexts: readFrozenContexts(task, access),
    maxContextBytes: access.maxContextBytes, maxOptionalContextBytes: access.maxOptionalContextBytes,
    environmentDigest: state.environmentDigest,
    ...(continuation ? { mandatory: [continuationContextSection(continuation, command, task.projectRelative)] } : {}),
    optional: [...residualSections, ...knowledgeSections, ...applicationSections] };
  const compiled = access.assignment && cooperation ? buildCooperativeContext(task, cooperation, bundle, access.assignment,
    access.operation ?? 'direct', compilation) : { ...bundle, ...compileTaskContext({ ...compilation, instructions }) };
  return { ...compiled, ...(access.knowledgeSnapshot ? { knowledgeRetrievals: knowledgeSections.map(section => ({
    ...section.knowledge, included: compiled.manifest?.included.some(item => item.id === section.id) ?? false,
    omissionReason: compiled.manifest?.omitted.find(item => item.id === section.id)?.reason })) } : {}) };
}

function strategyAdvice(access: ContextAccess, slot: ResearchModuleSlot, fallback: string, applicable = true): string {
  const rules = applicable ? access.customModuleRules?.filter(module => module.enabled && module.slot === slot) ?? [] : [];
  if (!rules.length) return fallback;
  const fixed = 'Configurable strategy advice cannot override the frozen problem, source boundaries, required mathematical interfaces, Lean checks, or the current role and output protocol.';
  return (rules.some(module => module.mode === 'replace') ? '' : fallback + '\n') + fixed + '\n' +
    rules.map(module => `Strategy ${slot} ${module.mode} ${JSON.stringify({ id: module.id, name: module.name })}:\n${module.instructions}`).join('\n\n') + '\n';
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
  const workContract = cooperativeWorkContract(action, cooperation.tasks, cooperation);
  const feasibilityRules = action.kind === 'task' && isFeasibilityReview(action.task)
    ? 'This is an early mathematical feasibility review. Independently challenge the exact dependency interfaces and their proposed original-goal application before their proofs are complete. Identify the hardest missing construction or estimate and whether its difficulty has merely moved into a helper or assumption. Check quantifier order, uniform constants, quantitative strength, boundary cases and applicability of cited results. First test whether the proposed inputs would actually suffice for the consumer; then test the most doubtful input with a counterexample, tractable special case, weaker statement or alternative construction. Choose a discriminating check that can change the route decision, rather than repeating an unchanged search. Keep a complete useful argument, exact remaining gap and reproducible evidence in RESEARCH.md. Use the existing research response with conclusion supporting, refuted or inconclusive; distinguish an invalid route from a false original theorem. Supporting evidence and local Lean probes remain advisory. Leave Lean sources unchanged on delivery.\n'
    : '';
  const earlyRouteRules = action.kind === 'lead'
    ? 'Before expanding an uncertain decomposition, identify its hardest substantive inference and test that the proposed inputs suffice for their actual consumer. For a typed consumer with unproved lemma inputs, arrange an early conditional:true proof using those fixed inputs; for proofRoutes, do this on the route closing lemma while the original target still waits for a checked route. A conditional receipt checks sufficiency only, not the truth or feasibility of its premises. Request a distinct untyped research/sketch task with reviewScope:"feasibility" to challenge a doubtful core input, with dependsOn naming the consumer and core tasks it must inspect. Advisory dependencies are inspection inputs and do not wait for proofs. Keep the consumer independent of the advisory review in its proof dependencies to avoid a cycle. Give the review a specific mathematical question and discriminating check; an ordinary direct proof does not require a review task. A fresh reviewer session and author exclusion support an independent check; if no independent peer is eligible, keep useful proof work executable and state the missing review.\n'
    : '';
  const connectionRules = action.kind === 'task' && action.assignment.connectionCheck
    ? 'This is a host-dispatched consumer connection check. First prove the assigned consumer from the exact typed inputs fixed in assignment.connectionCheck; their sufficiency is the current mathematical question. You may reference those dependency lemma names without proving them or adding stubs, axioms or extra assumptions. The host supplies only those fixed inputs as assumptions in a disposable projection. Full-file diagnostics may still report absent unproved input declarations; preserve that distinction and return the consumer proof for the host conditional check. A conditional success does not prove any input or accept the original target. Independent useful proof work continues while inputs are proved.\n'
    : '';
  const initialPlanningRules = action.kind === 'lead' && cooperation.tasks.length === 0
    ? 'Initial planning shares the proof budget. Batch a focused inspection and save the smallest useful task graph promptly; delegate unresolved mathematical questions as research tasks. Save useful route notes early so a host planning checkpoint can hand work to peers.\n'
    : '';
  const rules = action.kind === 'review'
    ? 'You are the Independent Reviewer. Leave Lean sources unchanged. Check this fixed proof against the original question, assumptions and Lean evidence. Write one JSON object in RESEARCH.md: {"verdict":"accepted|changes_requested"}. Optional summary and evidenceRefs explain the decision.\n'
    : action.kind !== 'task'
    ? `You are the Lead. Develop a mathematically plausible route from the exact original statement, definitions and relevant saved findings before choosing a task graph. Identify the central construction or estimate and how it would close each target. Save a concise mathematical route justification as Markdown before a single math-plan JSON fence in RESEARCH.md; include each new task's intended inference and consumer in its objective. Keep direct original-goal proof work when decomposition adds no mathematical benefit. Delegate a specific uncertain inference as research instead of inventing a helper proposition. Return the plan without running Lean diagnostics; leave Lean sources unchanged during planning. Write one JSON object in RESEARCH.md: {"tasks":[{"id":"helper","kind":"lemma","objective":"...","proofPath":${JSON.stringify(problem.ownedFiles.find(file => file.endsWith('.lean')))},"theoremName":"Namespace.helper","type":"∀ (P : Prop), P → P"},{"id":"goal","kind":"goal","objective":"...","theoremName":"Original.target","dependsOn":["helper"]}]}. Include every original target once. This example shows the schema only: replace its names, objectives and sample type with actual tasks and full closed Lean types, including all parameters and hypotheses. Never copy placeholder types. If no exact helper proposition is known, use an untyped research/sketch task. Choose proofPath from ${JSON.stringify(problem.ownedFiles.filter(file => file.endsWith('.lean')))}; goals infer it from theoremName, and lemmas may omit it only when one Lean file is owned. Use lemma tasks whenever workers should save proofs; research/sketch tasks without an exact typed target only return advisory findings and restore temporary probes. Typed research tasks are normalized to lemma tasks. dependsOn defaults to []; revision to 0. Keep accepted task definitions stable; record progress in notes rather than rewriting objectives, which invalidates their checked deliveries. Revise a mathematical contract to change a route; changing only prose or revision does not resolve a recorded blocker. conditional:true allows fixed typed lemma premises. statementReview:true with informalStatement requests meaning review. Optional groups set ownership, sharing and budgets.\n`
    : ['research', 'sketch'].includes(action.task.kind)
    ? 'You are a Mathematical Researcher. Explore the assigned mathematical question and leave Lean sources unchanged. Deliver a concise mathematical argument or counterexample with its exact assumptions, unresolved inference and intended original-goal application, so another solver can continue the work. Use library searches to resolve specific uncertainties in that argument. Replace inherited RESEARCH.md with findings for this assignment before returning; ordinary Markdown is supported. Timed checkpoints preserve progress and resume the same assignment without completing it. Optionally use JSON {"summary":"findings and evidence","needsDecision":true} to request a route change. Optional conclusion is supporting, refuted or inconclusive; findings remain advisory. To turn a useful bridge into proof work, add lemmaRequests:[{id,kind:"lemma",objective,theoremName,type,proofPath,dependsOn:[]}]. Supply new ids and full closed Lean types in your own route group. The host validates these proposals and presents them to Lead; adoption creates a separate typed assignment whose proof requires independent checking. A proposal does not authorize edits to Lean sources.\n'
    : 'Prove the assigned Lean declaration with its exact requested type. Develop a complete mathematical argument and use Lean to validate its steps. When a check fails, distinguish a missing mathematical inference from a library-name, type or tactic issue; preserve the useful argument and exact remaining goal in RESEARCH.md. An original goal may be a def: fill only its body, retaining its frozen declaration kind, name, parameters, type and placement. Helper proof targets must be theorems or lemmas. Add newly named supporting helpers in owned Lean files as needed. You may repair proof bodies of solver-created lemmas while preserving their names, parameters, types and placement. Preserve other original goals and every other existing definition body. Conditional tasks may reference fixed dependency lemmas; do not add stubs or extra assumptions. Check the complete saved target file and its local imports before delivery; a Helpers-only check does not check Submission. Save concise notes in RESEARCH.md and return for host checking and integration.\n';
  const sharing = action.kind === 'task'
    ? `To share before returning, append a JSON line to ${assignmentDeliveryFile(action.assignment)}: {"summary":"progress or gap"}. To publish a complete research finding while continuing proof work, append {"kind":"research","finding":{"summary":"complete argument, exact assumptions and gap","conclusion":"supporting|refuted|inconclusive","needsDecision":true,"evidenceRefs":[],"lemmaRequests":[]}}. Inline the complete finding; the host freezes this event in its own immutable notes commit without touching your live files. An optional commit must be a fixed descendant of your assignment seed and identifies supporting saved sources. Each finding is retained separately and stays advisory; publishing does not finish or park your proof task. For a ready proof, save the allowed sources and notes, then return. Git metadata is managed by the host; do not run git add or git commit. The host freezes the saved sources and independently checks and integrates them after your turn ends. Do not truncate the delivery log. Progress reports remain advisory.\n`
      : initialPlanDeliveryFile(action) ? `Once a minimal executable initial plan is ready, you may publish it while continuing planning: append one complete JSON line to ${initialPlanDeliveryFile(action)}. ` +
        `Use {"kind":"plan","baseVersion":${JSON.stringify(action.kind === 'lead' ? action.planVersion : '')},"summary":"mathematical route and intended consumers","tasks":[...],"groups":[...],"proofRoutes":[...]}. ` +
        'Inline the complete valid graph covering every original target exactly once; optional groups and proofRoutes may be omitted. The host freezes the line and can start peers before you return. ' +
        'Only the first valid initial publication is accepted. A partial line, ordinary RESEARCH.md save, or an external file reference does not publish a plan. Do not truncate the log. ' +
        'Continue planning with the accepted graph in COOPERATION.json and retain it in your final response. Later plan revisions use the normal final response, not another early event.\n' : '';
  const visibleIds = new Set(cooperation.tasks.map(node => node.task.id));
  const proofRoutes = (cooperation.proofRoutes ?? cooperation.tasks.flatMap(node => node.alternativeRoutes ?? []))
    .filter(route => visibleIds.has(route.targetTaskId) &&
      [route.closingTaskId, ...route.prerequisiteTaskIds].every(id => visibleIds.has(id)));
  const routeTasks = cooperation.tasks.map(node => ({ ...node,
    alternativeRoutes: proofRoutes.filter(route => route.targetTaskId === node.task.id) }));
  const continuation = buildProofContinuation(routeTasks, { groups: cooperation.groups,
    environmentDigest: compilation.environmentDigest, proofRoutes, researchHandoffs: researchHandoffs(cooperation) });
  const focus = originalGoalTaskFocus(routeTasks, cooperation.groups, compilation.environmentDigest);
  const frontierSnapshot = originalGoalFrontierSnapshot(focus);
  const routeIndex = createProofRoutePriorityIndex(routeTasks, {
    groups: cooperation.groups, environmentDigest: compilation.environmentDigest, proofRoutes });
  const routeContext = selectProofRoutePriorityContext(routeIndex, action.kind === 'task' ? {
    assignedRouteId: action.assignment.routeId,
    relatedRouteIds: proofRoutes.filter(route => route.targetTaskId === action.task.id ||
      route.closingTaskId === action.task.id || route.prerequisiteTaskIds.includes(action.task.id)).map(route => route.id),
  } : {});
  const localFrontier = new Set(routeContext.routes.flatMap(route => route.frontierTaskIds).filter(id => focus.frontier.has(id)));
  if (action.kind === 'task' && focus.frontier.has(action.task.id)) localFrontier.add(action.task.id);
  const boundedFrontier = action.kind === 'task' && proofRoutes.length > 0;
  const focusRules = action.kind === 'lead' || action.kind === 'task' ?
    'Prioritize a ready typed step proving a substantive missing construction or quantitative estimate on the original-goal frontier. Record the actual consumer with explicit dependsOn or proofRoutes and show the concrete application. For advisory research, dependsOn may identify the unresolved frontier being investigated; it does not prove that premise. State which missing argument was discharged and which premises remain. A conditional wrapper, an assumed original estimate or more auxiliary lemmas does not close the original goal. Preserve useful checked contracts and independent investigations. When substantive inputs are ready, let the authorized consumer perform short algebra or glue directly; create a separate helper only when it adds a reusable mathematical result or independent investigation. Divide uncertain core work into a proof attempt, a quantifier/strength or counterexample audit, and a specific library adaptation when these are independent questions.\n' : '';
  const gapRules = ['lead', 'task'].includes(action.kind) ?
    'Keep the true mathematical gap across route revisions in COOPERATION.json mathematicalGaps. In an existing research/progress JSON response, optionally add mathematicalGap:{consumer:{taskId:"ORIGINAL_ID",taskDigest:"EXACT_DIGEST"},previousDeliveryId:"PRIOR_GAP_DELIVERY_IF_ANY",previousGap:"previous unresolved inference",reduced:"what this work actually established",remaining:"exact quantifiers, quantitative strength, nondegeneracy and uniformity still needed",evidenceScope:"assumptions and scope of checked results or counterexamples",reconsiderWhen:["new exact inputs or evidence worth retrying"]}. Omit previousDeliveryId for the first report. Bind an original consumer visible to this assignment. Renaming a route or proving a weaker bound does not establish the missing stronger inference. Historical gaps and failed routes remain advisory and may be reconsidered with new inputs; conditional connections establish sufficiency only.\n' : '';
  const focusPacket = {
    goalTaskIds: continuation.goals.filter(goal => goal.status !== 'integrated' || goal.recordedProof !== 'checked').map(goal => goal.taskId),
    frontierTaskIds: boundedFrontier ? [...localFrontier] : [...focus.frontier],
    ...(proofRoutes.length ? {
      preferredFrontierTaskIds: boundedFrontier ? [...localFrontier].filter(id => focus.preferred.frontier.has(id)) : [...focus.preferred.frontier],
      routePriority: routeContext,
      ...(boundedFrontier ? { frontierSet: { count: frontierSnapshot.count, digest: frontierSnapshot.digest,
        reference: { path: 'COOPERATION.json', field: 'frontierFocus.taskIds' } } } : {}),
    } : {}),
    ...(action.kind === 'task' ? { assignedTaskId: action.task.id,
      relationship: focus.proofPath.has(action.task.id) ? 'proof-path' : focus.targetedResearch.has(action.task.id) ?
        'targeted-investigation' : focus.support.has(action.task.id) ? 'frontier-support' : 'independent-exploration',
      plannedConsumers: workContract.plannedConsumers } : {}),
  };
  const parallelQuestions = cooperation.parallelQuestions ?? cooperation.tasks.filter(node => node.status === 'running' &&
    node.task.id !== (action.kind === 'task' ? action.task.id : undefined) &&
    (action.kind !== 'task' || taskGroup(node.task) === taskGroup(action.task) || node.task.sharing !== 'group'))
    .map(node => ({ taskId: node.task.id, taskDigest: taskVersion(node.task), kind: node.task.kind, objective: node.task.objective,
      theoremName: node.task.theoremName, workerId: node.assignment?.workerId, routeId: node.assignment?.routeId }));
  const roleText = `Your role: ${action.kind === 'review' || action.kind === 'task' && isFeasibilityReview(action.task) ? 'reviewer' : action.kind === 'task' ? action.task.kind === 'goal' ? 'engineer' : 'researcher' : 'lead'}` + '\n' +
    (operation === 'direct' ? '' : `Research operation: ${operation}.\n`);
  const routeRules = 'Report a stable local obstruction in a research/sketch response or progress delivery with blockers:[{mechanism:"stable local mechanism",scope:"exact affected inference",evidenceRefs:[],reopenOn:[{kind:"contract-changed"},{kind:"environment-changed"},{kind:"dependency-checked",taskId:"ACTUAL_DECLARED_DEPENDENCY_ID"}]}]. When reporting an existing obstruction in different words, optionally include blockerId:"EXISTING_BLOCKER_ID" from this task and route to keep its history; use a new entry for a distinct obstruction. Use actual declared dependency ids; reopenOn may be omitted for the host default. A blocker is advisory and applies only to its stated inference. Repeating the same local premises, evidence and environment twice parks the affected task; it does not establish that the original theorem is false or impose a solving deadline. Preserve useful proofs and state an explicit reopening condition.\n';
  const handoffRules = action.kind === 'lead' ?
    'Research challenges are required advisory inputs even when optional research excerpts are omitted. For every shown challenge id, include ' +
    'challengeDecisions:[{id:"SHOWN_CHALLENGE_ID",status:"revised|disputed|deferred",reason:"specific mathematical response"}] in the same plan response. ' +
    'For revised, change the affected mathematical route or explain the concrete repair. For disputed, provide nonempty evidenceRefs for the counterargument. ' +
    'For deferred, specify waitsOn:["PROOF_TASK_ID"] with exact current proof contracts or a concrete reopenOn condition. ' +
    'A checked waiting input reopens the challenge; a model refutation never proves the original theorem false or authorizes acceptance. ' +
    'Preserve queued challenge sources and inputs until their dispatch; also preserve the source, versioned inputs and waiting targets of deferred waitsOn decisions. ' +
    'Read researchChallenges in COOPERATION.json to explicitly replace a still-deferred decision by its id when revising the route or waiting contract.\n' +
    'Pending research-handoffs are required inputs, independent of the optional delivery excerpts. For each shown id, adopt its exact typed target in ' +
    'the complete task graph, or include handoffDecisions:[{id:"SHOWN_HANDOFF_ID",status:"rejected|deferred",reason:"specific mathematical reason or missing input"}]. Adoption only schedules a new proof obligation. Do not mark an unproved proposal as checked. ' +
    'For a deferred proposal waiting on concrete proof tasks, add waitsOn:["ACTUAL_PROOF_TASK_ID"] to its decision. Use nonempty unique ids from the current proposed plan. The host pins their exact contracts and reopens the proposal only after all have fresh unconditional acceptance. Preserve waiting proposals, their sources and required inputs. All already checked inputs cannot justify another wait. You may explicitly replace or reject a still-waiting decision by its id when changing that route. A deferred decision without waitsOn has no automatic wakeup. Reopened proposals carry a previous decision and checked-prerequisites reason; decide their current activation instead of repeating a stale response. ' +
    'The host dispatches bounded dependency-first batches. Preserve a proposal id when other queued proposals depend on it. ' +
    'Queued proposals and late arrivals are handled by subsequent decisions; retain their source tasks, exact prerequisites and group mathematics until then. ' +
    'Inspect continuation.adoptedResearch in COOPERATION.json for adopted targets, their planned original-goal paths and recorded Lean consumers. Investigate useful adopted results without a connection or recorded use; incomplete reference coverage remains unknown. Adoption does not prove a target or require every exploratory proposal to have a consumer immediately. ' +
    '\n' : '';
  const leadRouteRules = action.kind === 'lead' ?
    'When the original-goal frontier is stalled, use new findings to split the substantive missing argument into independently provable exact lemma tasks and a closing consumer. Changing notation or assuming the original bound in a wrapper does not reduce that gap. A paper theorem is a route reference; assign every unproved analytic premise explicitly. Preserve existing checked task contracts. If the available inputs give no further concrete step, retain the blockers and explain the specific new input needed to resume. The host will reconsider unchanged mathematical input only once, including across restarts.\n' +
    'For a parked task, assign a targeted feasibility check or a discriminating experiment, or change a relevant mathematical input. A revision number, reworded objective or unrelated helper does not resolve the recorded obstruction. You may declare alternative proofRoutes:[{id:"route_id",targetTaskId:"original_goal_task_id",prerequisiteTaskIds:["typed_lemma_task_id"],closingTaskId:"typed_closing_lemma_task_id"}]. Replace schema ids with actual task ids. Every route input must be a typed lemma with its full exact closed type; the closing lemma dependsOn must cover all route prerequisites. All prerequisites within one route are required together; routes for one target are alternatives. The target\'s ordinary dependsOn remain additional requirements. A checked closing lemma enables an original-goal attempt. A route is closed only after the original goal passes its strict host check and its Lean proof actually references that closing lemma; advisory findings and a conditional bridge never supply formal acceptance.\n' +
    'A Saved Lead draft pending integration delivery preserves interrupted source work that could not be safely merged. Inspect its fixed commit with git show COMMIT:PROJECT_RELATIVE_PATH and recover useful declarations through typed tasks against current canonical sources. Preserve other workers\' integrated proofs. A saved draft is advisory and must pass the normal host checks before use.\n' : '';
  const attemptRules = action.kind === 'task' ?
    'Before continuing, read the current task feedback and relevant saved results. Identify the unresolved inference, its intended consumer, and the cheapest check that can distinguish your next hypothesis from an already failed approach. Reuse checked declarations and exact library signatures. Save the new evidence, failed approach or reusable draft in a concise checkpoint. If nothing relevant changed and no new discriminating check is available, report the specific missing input instead of repeating searches, submitting identical files or creating a renamed equivalent task. New research evidence can be useful before any theorem is proved.\n' : '';
  const recoveryRules = action.kind === 'lead' && action.recovery ?
    'This is a targeted recovery decision after actual failed work, not another ordinary plan recap. Inspect the failed frontier, its feedback and saved deliveries, and the declared pending tasks whose upstream helpers remain blocked. Adopt retained code through separately typed, host-checked tasks. Connect useful supporting tasks explicitly to the missing argument; an objective mentioning a consumer is not a dependency edge. Preserve checked contracts and scoped blockers. Return the complete math-plan JSON with recovery:{status:"planned",taskIds:["ACTUAL_READY_TASK_ID"]}. The named tasks must be executable now and either connect to an unfinished original goal or be an independent research/sketch investigation depending on the failed frontier. Split a missing construction, repair an unattempted prerequisite, or choose a different concrete inference; merely retrying the same failed target or changing its revision, name or prose is insufficient. Advisory research may investigate blocked inputs but grants no proof acceptance. If there is no concrete discriminating step, use recovery:{status:"awaiting-input",reason:"the specific mathematical input still needed"}. An unchanged recovery decision is durable and will not be repeated just because the process restarts.\n' : '';
  const instructions = context.instructions + '\n' + rules + initialPlanningRules + feasibilityRules + earlyRouteRules + connectionRules + attemptRules + recoveryRules + focusRules + gapRules +
    (action.kind === 'lead' || action.kind === 'task' && !isFeasibilityReview(action.task)
      ? 'For parallel work, give each assignment a distinct mathematical question or concrete product: the main missing proof, a specified counterexample or feasibility test, an exact library connection, or a consumer application. Inspect the current in-flight questions before requesting related work. Reuse their retained results and avoid assigning the same unchanged question to another worker. Keep a useful backup route when it tests a different inference. Leave a slot waiting for input when no independent actionable question is available; do not manufacture helpers to fill it. Route priority reflects recorded inputs and obstructions, not a prediction that a route is easy.\n' : '') +
    (action.kind === 'lead' ? 'Use the proof-continuation snapshot to identify the original goal\'s current mathematical frontier. Prefer consuming relevant checked lemmas before creating more auxiliary work; give each new helper an intended consumer and explicitly assign every substantive missing premise. Keep useful alternative routes visible. A lemma without a recorded consumer may still be useful; investigate its connection rather than deleting it. Planned dependencies, actual Lean proof references and conditional references are reported separately. Do not count auxiliary lemma totals as completion of the original problem. The host obtains fixed-candidate review after the complete proof is checked; mark any advisory final-candidate task with reviewScope:"final-candidate" so it waits for freshly checked original goals. Use a distinct task with reviewScope:"feasibility" for independent mathematical route checks before a complete candidate exists. Inspect validated lemmaRequests in deliveries and adopt useful exact proposals as separate lemma tasks; proposals and their local checks are advisory. Advisory research may start before its planned dependencies are proved; use typed proof tasks when a consumer must wait for checked premises.\n' :
      action.kind === 'task' && ['lemma', 'goal'].includes(action.task.kind) ? 'Inspect relevant checked inputs and their exact declarations before reconstructing an argument. Save the concrete consumer application and discharge every premise; report the remaining original-goal obstacle in RESEARCH.md.\n' : '') +
    (action.kind === 'task' && ['research', 'sketch'].includes(action.task.kind)
      ? 'Before restoring a temporary Lean probe, retain its complete reusable code, namespace/context, exact declaration names and proposed consumer in a lean fence in worktree-root RESEARCH.md. A prose claim that Lean passed is not a recoverable proof. To report a successful local check explicitly, use leanChecks:[{status:"passed",path:"RESEARCH.md",declarations:["Qualified.name"]}] in the single JSON response and keep the complete code outside that JSON in a lean fence. The host binds retained artifacts to this problem, assignment and commit; every local check remains advisory until a separate typed host check passes.\n' : '') +
    routeRules + handoffRules + leadRouteRules +
    'A delivery summarySource names its full finding section in the context manifest. If that section was omitted for budget, retrieve the complete notes through the available savedSource commit and notesPath. Omission from the prompt does not mean that no mathematical result was saved.\n' +
    'Original declarations retain the frozen source order shown below. A goal cannot depend on a later original goal in the same file. Extract their shared argument into a newly named lemma before both goals; preserve every other original proof and declaration placement.\n' +
    'COOPERATION.json contains scoped live peer work, findings, gaps and checked results; leave it and CONTEXT-MANIFEST.json unchanged. The context compilation manifest identifies included and omitted material and why it was omitted. Exact mathematical interfaces and original assumptions are mandatory; retrieve full proof sources and context using their immutable commit/path references. Structured responses use one JSON object, plain or in a math/json fence, replacing old responses. The host manages versions, receipts and budgets, and independently checks all original targets. Unproved dependencies and reviews remain advisory.\n' +
    sharing + roleText;
  const optional: ContextSection[] = [
    ...(compilation.optional ?? []),
    { id: 'plan-feedback', kind: 'feedback', text: `Review: ${JSON.stringify(cooperation.review ?? null)}` },
    { id: 'proof-continuation', kind: 'continuation', text: '\nProof continuation (stored evidence, not replayed; planned use and actual proof use are separate):\n' + JSON.stringify(continuation) },
    { id: 'statement-reviews', kind: 'statement-review', text: 'Statement reviews: ' + JSON.stringify(cooperation.statementReviews?.filter(review => review.status !== 'superseded')
      .map(statementReviewSummary) ?? []) },
  ];
  return { ...context, assignment: action, workContract, instructions,
    ...compileTaskContext({ ...compilation, instructions, optional,
      mandatory: [...(compilation.mandatory ?? []),
        { id: 'work-contract', kind: 'assignment', text: 'Host work contract (one product; completion is not proof acceptance):\n' + JSON.stringify(workContract) },
        { id: 'assignment-policy', kind: 'assignment', text: roleText +
          (sharing ? 'Delivery protocol: see session instructions.\n' : '') },
        ...((action.kind === 'lead' || action.kind === 'task' && !isFeasibilityReview(action.task)) &&
          parallelQuestions.length ? [{
            id: 'parallel-questions', kind: 'assignment' as const,
            text: 'Current in-flight questions (scope-visible assignments; advisory, retrieve exact interfaces from COOPERATION.json):\n' +
              JSON.stringify(parallelQuestions),
          }] : []),
        ...(focusRules ? [{ id: 'frontier-focus', kind: 'continuation' as const,
          text: 'Original-goal focus (advisory, not proof acceptance):\n' + JSON.stringify(focusPacket) }] : []),
        ...(action.kind === 'lead' && action.recovery ? [{ id: 'frontier-recovery', kind: 'assignment' as const,
          text: 'Targeted recovery request (advisory; no proof acceptance):\n' + JSON.stringify({ ...action.recovery,
            failures: cooperation.tasks.filter(node => action.recovery!.taskIds.includes(node.task.id)).map(node => ({
              taskId: node.task.id, status: node.status, attempts: node.attempts, feedback: node.feedback,
              dependsOn: node.task.dependsOn, assignment: node.assignment && { workerId: node.assignment.workerId,
                seedCommit: node.assignment.seedCommit } })),
            unattemptedSupportingTasks: cooperation.tasks.filter(node => ['blocked', 'pending'].includes(node.status) && !node.attempts &&
              (node.task.status ?? 'active') === 'active').map(node => ({ taskId: node.task.id, status: node.status, dependsOn: node.task.dependsOn })),
          }) }] : [])] }) };
}
