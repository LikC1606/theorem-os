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
import { assignmentDeliveryFile, leadPlanDeliveryFile, isFeasibilityReview, taskGroup, taskVersion, type CooperativeAction } from '../tasks';
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
import { defaultResearchRouteConcurrency, researchTaskRole, type ResearchWorker } from './organization';

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
  /** Same-thread responsibility continuation; full compilation remains the context manifest. */
  continuationMessage?: string;
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
    : access.assignment?.kind === 'task' && access.assignment.task.kind === 'goal'
    ? `This assignment proves only ${access.assignment.task.theoremName}. Preserve every other original goal proof exactly as it appears in assignment.seedCommit, including existing sorry placeholders. Other workers and the host handle those goals.\n`
    : '';
  const instructions = `You prove the original mathematical problem in Lean. Work only in this isolated worktree.
Edit only ${task.ownedFiles.map(file => path.join(access.worktree, task.projectRelative, file)).join(', ')}, ${path.join(access.worktree, 'RESEARCH.md')}${access.assignment?.kind === 'task' ? `, ${path.join(access.worktree, assignmentDeliveryFile(access.assignment.assignment))}` : ''}.
Save RESEARCH.md and delivery logs at these exact worktree-root paths, including when a diagnostic command runs inside the Lean project subdirectory.
Temporary probes, backups and diagnostic output may be written under ${path.join(access.worktree, '.scratch', 'tmp')} or the Lean project's .scratch/tmp directory. The shell's TMPDIR points to the worktree-local directory; run mkdir -p "$TMPDIR" before creating temporary files. /tmp is read-only. Untracked regular scratch files stay advisory and remain outside formal proof checkpoints. Do not git add scratch files or use symlinks there. Retain reusable proof code and findings in RESEARCH.md or owned Lean files before returning.
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
    compilation, state.workers) : { ...bundle, ...compileTaskContext({ ...compilation, instructions }) };
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
  action: CooperativeAction, compilation: Omit<TaskContextInput, 'instructions'>,
  workers: readonly Pick<ResearchWorker, 'id' | 'role'>[] = []): ContextBundle {
  const workContract = cooperativeWorkContract(action, cooperation.tasks, cooperation);
  const capacityExploration = action.kind === 'task'
    ? cooperation.tasks.find(node => node.task.id === action.task.id)?.capacityExploration : undefined;
  const organizationRules = action.kind === 'lead' && workers.some(worker => worker.role === 'prover')
    ? 'Available worker responsibilities: ' + JSON.stringify(workers.map(({ id, role }) => ({ id, role }))) + '. ' +
      'Provers claim only typed lemma tasks in your plan. Give each useful independent proof obligation a full closed Lean type, owned proofPath, stable theoremName and exact dependencies; use ownerId only when a reservation is needed. ' +
      'Researchers prioritize mathematical investigation and precise lemma interfaces; the Engineer prioritizes original goals and consumes checked helpers. Researchers and the Engineer can also take eligible research or lemma tasks. ' +
      'Keep proof work executable as findings arrive, and let Provers wait when no useful independent typed obligation is known. ' +
      'The host may use spare slots for distinct advisory capacity explorations. These execution overlays appear in COOPERATION.json; omit them from your math-plan because the host preserves their ownership and drafts separately. Never depend on an exploration ID as a proof premise; adopt its exact interface under a new typed task ID using the actual typed inputs. Consume useful findings through the usual plan and handoff decisions. ' +
      `An unspecified route maxConcurrent uses ${defaultResearchRouteConcurrency(workers)} task slots; an explicit limit is respected.\n`
    : '';
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
  const leadDeliveryRules = action.kind === 'lead'
    ? 'Once a complete plan has useful executable work, save the full current graph and return promptly so peers can start it. Delegate unresolved library or mathematical searches as research tasks to eligible Researchers or the Engineer. For new, unstarted helpers that need no worker-specific context, omit ownerId so eligible peers can claim them. Keep explicit reservations when needed; removing ownerId never releases a saved assignment. Before adding work, inspect ready tasks reserved by ownerId to a busy worker while an eligible generalist is idle. Explicitly reassign an unstarted, unassigned task through the complete plan when useful, preserving its mathematical contract. Preserve route gates, group scope, independent reviewer eligibility and running assignments; an idle Engineer can do research while its original goal waits on a genuine route prerequisite. Apply this on every decision, including later replanning. Include every original target and preserve checked task contracts and active independent task definitions in the single math-plan JSON fence in RESEARCH.md. Add only mathematically useful executable tasks.\n'
    : '';
  const rules = action.kind === 'review'
    ? 'You are the Independent Reviewer. Leave Lean sources unchanged. Check this fixed proof against the original question, assumptions and Lean evidence. Write one JSON object in RESEARCH.md: {"verdict":"accepted|changes_requested"}. Optional summary and evidenceRefs explain the decision.\n'
    : action.kind !== 'task'
    ? `You are the Lead. Develop a mathematically plausible route from the exact original statement, definitions and relevant saved findings before choosing a task graph. Identify the central construction or estimate and how it would close each target. Save a concise mathematical route justification as Markdown before a single math-plan JSON fence in RESEARCH.md; include each new task's intended inference and consumer in its objective. Keep direct original-goal proof work when decomposition adds no mathematical benefit. Delegate a specific uncertain inference as research instead of inventing a helper proposition. Return the plan without running Lean diagnostics; leave Lean sources unchanged during planning. Write one JSON object in RESEARCH.md: {"tasks":[{"id":"helper","kind":"lemma","objective":"...","proofPath":${JSON.stringify(problem.ownedFiles.find(file => file.endsWith('.lean')))},"theoremName":"Namespace.helper","type":"∀ (P : Prop), P → P"},{"id":"goal","kind":"goal","objective":"...","theoremName":"Original.target","dependsOn":["helper"]}]}. Include every original target once. This example shows the schema only: replace its names, objectives and sample type with actual tasks and full closed Lean types, including all parameters and hypotheses. Never copy placeholder types. If no exact helper proposition is known, use an untyped research/sketch task. Choose proofPath from ${JSON.stringify(problem.ownedFiles.filter(file => file.endsWith('.lean')))}; goals infer it from theoremName, and lemmas may omit it only when one Lean file is owned. Use lemma tasks whenever workers should save proofs; research/sketch tasks without an exact typed target only return advisory findings and restore temporary probes. Typed research tasks are normalized to lemma tasks. dependsOn defaults to []; revision to 0. Keep accepted task definitions stable; record progress in notes rather than rewriting objectives, which invalidates their checked deliveries. Revise a mathematical contract to change a route; changing only prose or revision does not resolve a recorded blocker. conditional:true allows fixed typed lemma premises. statementReview:true with informalStatement requests meaning review. Optional groups set ownership, sharing and budgets.\n`
    : ['research', 'sketch'].includes(action.task.kind)
    ? 'You are a Mathematical Researcher. Explore the assigned mathematical question and leave Lean sources unchanged. Deliver a concise mathematical argument or counterexample with its exact assumptions, unresolved inference and intended original-goal application, so another solver can continue the work. Use library searches to resolve specific uncertainties in that argument. Save a scoped negative library result or a classification gap in worktree-root RESEARCH.md as soon as it is established, rather than waiting for a proof or the end of the turn. Record the pinned library/environment version, searched paths, queries or method, exact result and the missing mathematical inference. A scoped search failure is not proof of global absence. Replace inherited RESEARCH.md with findings for this assignment before returning; ordinary Markdown is supported. Timed checkpoints preserve progress and resume the same assignment without completing it. When a negative result or classification gap needs a route decision, promptly publish the existing research finding with needsDecision:true, conclusion:"inconclusive", a summary stating the precise gap, evidenceRefs and remainingObligations; use conclusion:"refuted" only for an actual refutation of the scoped claim. Otherwise ordinary findings may use JSON {"summary":"findings and evidence","needsDecision":true} to request a route change. Optional conclusion is supporting, refuted or inconclusive; findings remain advisory. To turn a useful bridge into proof work, add lemmaRequests:[{id,kind:"lemma",objective,theoremName,type,proofPath,dependsOn:[]}]. Supply new ids and full closed Lean types in your own route group. The host validates these proposals and presents them to Lead; adoption creates a separate typed assignment whose proof requires independent checking. A proposal does not authorize edits to Lean sources.\n'
    : (action.task.kind === 'lemma' ? 'You are a Lean Prover. Write and deliver the assigned auxiliary proof for its declared consumers. '
      : 'You are the main-goal Engineer. Close the original target using checked helpers. ') +
      'Prove the assigned Lean declaration with its exact requested type. Develop a complete mathematical argument and validate it with Lean. Distinguish missing mathematics from a library-name, type or tactic issue; save the useful argument and exact remaining goal in RESEARCH.md. An original goal may be a def: fill only its body. Helper proof targets must be theorems or lemmas. You may repair solver-created lemma proof bodies while preserving their statements and placement. Conditional tasks may reference fixed dependency lemmas; do not add stubs or extra assumptions. Run diagnostics on the saved target file and its local imports; a Helpers-only check does not check Submission. Preserve unrelated original goals\' exact seed bodies, including sorry or pre-existing diagnostics; do not prove or rewrite them to make the whole file pass. The host checks the assigned declaration in a disposable projection and checks the full candidate after integration. Save notes and return for host checking and integration.\n';
  const assessmentRules = action.kind === 'lead' && !action.recovery && (action.capacityRefill || action.stagnationRecovery)
    ? 'After assessing the shown requests, if no independent executable obligation is known and no handoff/challenge decision remains, ' +
      'append one complete event to ' + leadPlanDeliveryFile(action) + ': ' + JSON.stringify({ kind: 'assessment',
        baseVersion: action.planVersion, dispatchNonce: action.planNonce, assessments: [
          ...(action.capacityRefill ? [{ kind: 'capacity', requestId: action.capacityRefill.requestId,
            inputDigest: action.capacityRefill.inputDigest, outcome: 'no-independent-work', reason: 'EXACT_MISSING_MATHEMATICAL_INPUT' }] : []),
          ...(action.stagnationRecovery ? [{ kind: 'stagnation', requestId: action.stagnationRecovery.requestId,
            inputDigest: action.stagnationRecovery.inputDigest, outcome: 'no-independent-work', reason: 'EXACT_MISSING_MATHEMATICAL_INPUT' }] : []),
        ] }) + '. Replace each reason with the precise unresolved input. A checkpoint or unchanged plan does not acknowledge these requests. ' +
      'New evidence can reopen assessment. When deciding handoffs/challenges without new executable work, include this same assessments array in the short kind:"handoff" event or full plan so its explicit decisions and no-work reasons are accepted together. Unseen pending inbox items must remain queued and prevent a no-work acknowledgement until considered.\n' : '';
  const coordinationRules = action.kind === 'lead' && !action.initialPlanNonce
    ? 'Resolve the shown coordination requests before extended mathematical investigation. Use the saved findings to publish current handoff/challenge decisions, executable work, or the supported no-independent-work assessment. A coordination decision does not require solving the missing theorem. Delegate a specific new mathematical investigation when useful. Save the exact remaining gap and return after publishing the decision; the host preserves the unlimited solving budget and revisits new evidence. Lead scheduling checkpoints yield every two minutes even when notes are unchanged.\n' : '';
  const researchSourcesRules = action.kind === 'task' && ['lemma', 'goal'].includes(action.task.kind)
    ? 'When supporting Lean code is saved but the assigned declaration is still unproved, bind the research finding to those exact sources: add a top-level sources object to the kind:"research" event. Its keys must be exactly ' +
      JSON.stringify(problem.ownedFiles.filter(file => file.endsWith('.lean'))) +
      ', with each value the complete saved UTF-8 file content (total at most 1,000,000 bytes). Read all files and append the complete JSON line in one local script; do not copy large source text by hand. Omit commit when using sources. The host freezes these supplied bytes in an isolated snapshot and retains the supporting declarations for separate typed checks. Without sources or an existing commit, the finding is bound to the assignment seed. If blocked, include needsDecision:true, conclusion:"inconclusive", the exact mathematicalGap and remainingObligations for this snapshot. Source changes after that report require a fresh source-bound finding. Auxiliary code and a reported gap never accept the assigned proof.\n' : '';
  const sharing = action.kind === 'task'
    ? `To share before returning, append JSON to ${assignmentDeliveryFile(action.assignment)}: {"summary":"progress or gap"}. Publish a finding during proof work with {"kind":"research","finding":{"summary":"complete argument, exact assumptions and gap","conclusion":"inconclusive","needsDecision":true,"evidenceRefs":[],"remainingObligations":["precise unresolved mathematical inference"],"lemmaRequests":[]}}. Inline the full finding; the host snapshots notes. Supporting commits must descend from the assignment seed; publishing does not finish or park your proof task. For typed proofs, save files, append {"kind":"ready","summary":"saved proof"}, stop editing and return. Omit commit/targets. The host freezes the saved sources and independently checks and integrates them after turn settlement and confirmed shutdown. Receipts: COOPERATION.json proofReadyRecords. Retry failures with a new id; unconfirmed shutdown quarantines this workspace. Returning naturally also submits. Do not run git add or git commit. Do not truncate the delivery log.\n`
      : leadPlanDeliveryFile(action) ? `Once a useful executable plan is ready, publish it promptly: append one complete JSON line to ${leadPlanDeliveryFile(action)}. ` +
        `Use {"kind":"plan","baseVersion":${JSON.stringify(action.kind === 'lead' ? action.planVersion : '')},` +
        (action.kind === 'lead' && action.planNonce ? `"dispatchNonce":${JSON.stringify(action.planNonce)},` : '') +
        '"summary":"mathematical route and intended consumers","tasks":[...],"groups":[...],"proofRoutes":[...]}. ' +
        'Inline the complete valid graph covering every original target exactly once; optional groups and proofRoutes may be omitted. The host freezes the line and can start peers before you return. ' +
        'Only the first valid publication in this dispatch is accepted. A partial line, ordinary RESEARCH.md save, or an external file reference does not publish a plan. Do not truncate the log. ' +
        'Use the exact dispatch nonce and base version; a human edit or another accepted revision supersedes stale work. Preserve checked contracts and unrelated active assignments. ' +
        'Read the accepted graph in COOPERATION.json, retain it in your final response, and return promptly. The next Lead dispatch may publish its own revision; further changes in this dispatch use the normal final response.\n' : '';
  const handoffPublicationRules = action.kind === 'lead' && !action.initialPlanNonce && !action.recovery &&
    action.planNonce && (action.handoffIds?.length || action.challengeIds?.length) && leadPlanDeliveryFile(action)
    ? 'Decide the shown research handoffs and challenges before continuing long route investigation. Publish those decisions immediately without rewriting the task graph: append one complete JSON line to ' +
      leadPlanDeliveryFile(action) + '. Envelope: ' + JSON.stringify({ kind: 'handoff', dispatchNonce: action.planNonce,
        baseVersion: action.planVersion,
        ...(action.handoffIds?.length ? { handoffDecisions: [{ id: action.handoffIds[0], status: 'adopted' }] } : {}),
        ...(action.challengeIds?.length ? { challengeDecisions: action.challengeIds.map(id => ({ id, status: 'deferred',
          reason: 'EXACT_MISSING_MATHEMATICAL_INPUT', reopenOn: 'SPECIFIC_NEW_INPUT' })) } : {}),
      }) + '. ' +
      'The example shows the envelope, not a mathematical recommendation. Include exactly one explicit handoff decision for every shown handoff id: ' +
      JSON.stringify(action.handoffIds ?? []) + '. Choose {id,status:"adopted",ownerId?:"AVAILABLE_PROVER_ID"}, ' +
      '{id,status:"rejected",reason:"specific mathematical reason"}, or {id,status:"deferred",reason:"missing input",waitsOn?:["ACTUAL_PROOF_TASK_ID"]}. ' +
      'The host copies adopted exact typed proposals and dependencies from this immutable inbox into the current graph, retaining all existing tasks, groups, routes and assignments. ' +
      'Only newly added obligations may specify an owner. Include challengeDecisions for every shown challenge id ' + JSON.stringify(action.challengeIds ?? []) +
      ' using the challenge decision rules below; a pure challenge event needs no handoffDecisions. Do not include tasks, groups, proofRoutes or altered proposal fields in this event. ' +
      'This creates pending proof work and never accepts a proof. Later unseen handoffs and challenges remain queued. A defer decision alone does not fill capacity or decompose the frontier: include explicit assessments with exact no-independent-work reasons when appropriate. ' +
      'This event and kind:"plan" share the first-valid-publication limit. Use the exact nonce and base version; retrieve COOPERATION.json after publication and return promptly. ' +
      'Inherited plan notes may remain as a draft; do not reintroduce the previous graph as a new full-plan response.\n'
    : '';
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
    'Prioritize a ready typed step proving a substantive missing construction or quantitative estimate on the original-goal frontier. Choose genuinely weaker, independently Lean-checkable sublemmas with closed types. Record the actual consumer with explicit dependsOn or proofRoutes and show the concrete application, discharged inference and remaining premises. Renaming the whole theorem, assuming the core result or proving a conditional wrapper is not a reduction. Advisory dependencies identify questions, not proved premises. Preserve checked contracts and independent investigations. Let consumers do short glue; add helpers only for useful reusable results. Split independent core proof, strength/counterexample audit and library adaptation questions.\n' : '';
  const gapRules = ['lead', 'task'].includes(action.kind) ?
    'Report gaps in research/progress JSON: mathematicalGap:{consumer:{taskId:"ORIGINAL_GOAL_ID",taskDigest:"EXACT_GOAL_DIGEST"},previousGap:"prior inference",reduced:"established result",remaining:"exact quantifiers, strength, nondegeneracy and uniformity needed",evidenceScope:"checked assumptions and scope",reconsiderWhen:["new inputs or evidence"]}. Use a visible kind:"goal" original consumer and its exact digest, not the assigned lemma or research task. Submit the complete object on every correction. Optional previousDeliveryId must be a mathematicalGaps[].deliveryId in COOPERATION.json for this goal; ordinary research delivery IDs are not prior gap references. If none exists, omit only previousDeliveryId and keep the required previousGap description. Read full reports in COOPERATION.json mathematicalGaps. Historical reports are advisory; review changed inputs. A weaker bound or renamed route does not establish the stronger gap; conditional checks establish sufficiency only.\n' : '';
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
  const roleText = `Your role: ${action.kind === 'review' ? 'reviewer' : action.kind === 'task' ? researchTaskRole(action.task) : 'lead'}` + '\n';
  const routeRules = 'Report local obstructions in research/sketch responses or progress: blockers:[{mechanism:"stable mechanism",scope:"exact inference",evidenceRefs:[],reopenOn:[{kind:"contract-changed"},{kind:"environment-changed"},{kind:"dependency-checked",taskId:"DECLARED_DEPENDENCY_ID"}]}]. For the same obstruction, optionally reuse blockerId:"EXISTING_BLOCKER_ID" from this task/route to retain history; give distinct obstructions new entries. Use declared dependency ids; omit reopenOn for host defaults. Blockers are scoped and advisory. Repeating unchanged local premises, evidence and environment twice parks the task, without refuting the original theorem or imposing a deadline. Preserve useful proofs and explicit reopening conditions.\n';
  const handoffRules = action.kind === 'lead' ?
    'Research challenges are required advisory inputs even when optional research excerpts are omitted. For every shown challenge id, include ' +
    'challengeDecisions:[{id:"SHOWN_CHALLENGE_ID",status:"revised|disputed|deferred",reason:"specific mathematical response"}] in the same full plan or short kind:"handoff" response. ' +
    'For revised, change the affected mathematical route or explain the concrete repair. For disputed, provide nonempty evidenceRefs for the counterargument. ' +
    'For deferred, specify waitsOn:["PROOF_TASK_ID"] with exact current proof contracts or a concrete reopenOn condition. ' +
    'A checked waiting input reopens the challenge; a model refutation never proves the original theorem false or authorizes acceptance. ' +
    'Preserve queued challenge sources and inputs until their dispatch; also preserve the source, versioned inputs and waiting targets of deferred waitsOn decisions. ' +
    'Read researchChallenges in COOPERATION.json to explicitly replace a still-deferred decision by its id when revising the route or waiting contract.\n' +
    'Pending research-handoffs are required inputs, independent of the optional delivery excerpts. For each shown id, adopt its exact typed target in ' +
    'the complete task graph, or include handoffDecisions:[{id:"SHOWN_HANDOFF_ID",status:"rejected|deferred",reason:"specific mathematical reason or missing input"}]. A complete plan may explicitly acknowledge adoption with {id:"SHOWN_HANDOFF_ID",status:"adopted"}, but must also contain the exact proposed typed task. Copy proposal.type verbatim, including Lean notation; rewriting ᵀ as .transpose changes its frozen contract. If the proposed type needs repair, explain the rejection and obtain a corrected proposal rather than marking a different interface adopted. When this dispatch offers the short kind:"handoff" publication protocol, prefer it for these exact decisions before longer planning; the host materializes the immutable proposal. Adoption only schedules a new proof obligation. Do not mark an unproved proposal as checked. ' +
    'For a deferred proposal waiting on concrete proof tasks, add waitsOn:["ACTUAL_PROOF_TASK_ID"] to its decision. Use nonempty unique ids from the current proposed plan. The host pins their exact contracts and reopens the proposal only after all have fresh unconditional acceptance. Preserve waiting proposals, their sources and required inputs. All already checked inputs cannot justify another wait. You may explicitly replace or reject a still-waiting decision by its id when changing that route. A deferred decision without waitsOn has no automatic wakeup. Reopened proposals carry a previous decision and checked-prerequisites reason; decide their current activation instead of repeating a stale response. ' +
    'The host dispatches bounded dependency-first batches. Preserve a proposal id when other queued proposals depend on it. ' +
    'Queued proposals and late arrivals are handled by subsequent decisions; retain their source tasks, exact prerequisites and group mathematics until then. ' +
    'Inspect continuation.adoptedResearch in COOPERATION.json for adopted targets, their planned original-goal paths and recorded Lean consumers. Investigate useful adopted results without a connection or recorded use; incomplete reference coverage remains unknown. Adoption does not prove a target or require every exploratory proposal to have a consumer immediately. ' +
    '\n' : '';
  const leadRouteRules = action.kind === 'lead' ?
    'When the original-goal frontier is stalled, use new findings to split the substantive missing argument into genuinely weaker, independently Lean-checkable exact lemma tasks and a closing consumer. State what each sublemma removes from the original obstruction and verify that its hypotheses do not assume the unresolved core result. Changing notation or assuming the original bound in a wrapper does not reduce that gap. A paper theorem is a route reference; assign every unproved analytic premise explicitly. Preserve existing checked task contracts. If the available inputs give no further concrete step, retain the blockers and explain the specific new input needed to resume. The host will reconsider unchanged mathematical input only once, including across restarts.\n' +
    'For a parked task, assign a targeted feasibility check or a discriminating experiment, or change a relevant mathematical input. A revision number, reworded objective or unrelated helper does not resolve the recorded obstruction. You may declare alternative proofRoutes:[{id:"route_id",targetTaskId:"original_goal_task_id",prerequisiteTaskIds:["typed_lemma_task_id"],closingTaskId:"typed_closing_lemma_task_id"}]. Replace schema ids with actual task ids. Every route input must be a typed lemma with its full exact closed type; the closing lemma dependsOn must cover all route prerequisites. All prerequisites within one route are required together; routes for one target are alternatives. The target\'s ordinary dependsOn remain additional requirements. A checked closing lemma enables an original-goal attempt. A route is closed only after the original goal passes its strict host check and its Lean proof actually references that closing lemma; advisory findings and a conditional bridge never supply formal acceptance.\n' +
    'A Saved Lead draft pending integration delivery preserves interrupted source work that could not be safely merged. Inspect its fixed commit with git show COMMIT:PROJECT_RELATIVE_PATH and recover useful declarations through typed tasks against current canonical sources. Preserve other workers\' integrated proofs. A saved draft is advisory and must pass the normal host checks before use.\n' : '';
  const attemptRules = action.kind === 'task' ?
    'Before continuing, read task feedback and saved results; identify the unresolved inference, consumer and cheapest new discriminating check. Reuse checked declarations and exact signatures. Do not rescan the same negatively searched library scope under unchanged inputs. Reopen only for a new relevant version, assumption, theorem candidate or mathematical method; record the trigger. A renamed query alone is not a new mathematical direction. Without new evidence or a useful check, report the missing input instead of identical work. Before any checkpoint, recovery decision or context rotation, save in RESEARCH.md: attempted methods, exact results and evidence locations, scoped negative searches, reusable code, precise unresolved next inference and retry trigger. Distinguish checked unconditional facts from conditional sufficiency and unverified drafts. Preserve useful prior evidence.\n' : '';
  const recoveryRules = action.kind === 'lead' && action.recovery ?
    'This is a targeted recovery decision after actual failed work, not another ordinary plan recap. Inspect the failed frontier, its feedback and saved deliveries, and the declared pending tasks whose upstream helpers remain blocked. Adopt retained code through separately typed, host-checked tasks. Connect useful supporting tasks explicitly to the missing argument; an objective mentioning a consumer is not a dependency edge. Preserve checked contracts and scoped blockers. Return the complete math-plan JSON with recovery:{status:"planned",taskIds:["ACTUAL_READY_TASK_ID"]}. The named tasks must be executable now and either connect to an unfinished original goal or be an independent research/sketch investigation depending on the failed frontier. Split a missing construction, repair an unattempted prerequisite, or choose a different concrete inference; merely retrying the same failed target or changing its revision, name or prose is insufficient. Advisory research may investigate blocked inputs but grants no proof acceptance. If there is no concrete discriminating step, use recovery:{status:"awaiting-input",reason:"the specific mathematical input still needed"}. An unchanged recovery decision is durable and will not be repeated just because the process restarts.\n' : '';
  const stagnationRecoveryRules = action.kind === 'lead' && action.stagnationRecovery ?
    'This dispatch requests recovery from advisory stagnation, not proof failure. Read the saved negative searches and classification gaps for the named frontier before extending the plan. Propose genuinely weaker, independently Lean-checkable exact sub-obligations with an explicit derivation for their actual consumer, or retain the precise missing mathematical input. Do not restart an unchanged library scan, rename the central theorem, assume its core result, or count a conditional wrapper as substantive reduction. Publish any useful complete graph promptly through the existing plan protocol; no new recovery response schema is required. Preserve checked contracts, frozen sources and independent host acceptance.\n' : '';
  const checkpointRules = action.kind === 'lead' ?
    'Before any checkpoint, recovery decision or context rotation, update worktree-root RESEARCH.md with attempted methods, exact results and evidence locations, scoped negative searches, reusable steps, the precise unresolved next inference and retry trigger. Distinguish checked unconditional facts from conditional sufficiency and unverified drafts; preserve useful prior evidence rather than status-only recaps.\n' : '';
  const instructions = context.instructions + '\n' + rules + organizationRules + leadDeliveryRules + initialPlanningRules + coordinationRules + feasibilityRules + earlyRouteRules + connectionRules + attemptRules + recoveryRules + stagnationRecoveryRules + focusRules + gapRules + checkpointRules + researchSourcesRules +
    (action.kind === 'lead' || action.kind === 'task' && !isFeasibilityReview(action.task)
      ? 'For parallel work, assign distinct proof, feasibility/counterexample, library-connection or consumer questions. Inspect in-flight work and reuse saved results; do not duplicate an unchanged question. Keep backup routes testing different inferences. Leave a slot waiting for input when no independent useful work exists. Do not manufacture helpers. Route priority reflects recorded inputs and obstructions, not predicted ease.\n' : '') +
    (action.kind === 'lead' ? 'Use the proof-continuation snapshot to identify the original goal\'s current mathematical frontier. Prefer consuming relevant checked lemmas before creating more auxiliary work; give each new helper an intended consumer and explicitly assign every substantive missing premise. Keep useful alternative routes visible. A lemma without a recorded consumer may still be useful; investigate its connection rather than deleting it. Planned dependencies, actual Lean proof references and conditional references are reported separately. Do not count auxiliary lemma totals as completion of the original problem. The host obtains fixed-candidate review after the complete proof is checked; mark any advisory final-candidate task with reviewScope:"final-candidate" so it waits for freshly checked original goals. Use a distinct task with reviewScope:"feasibility" for independent mathematical route checks before a complete candidate exists. Inspect validated lemmaRequests in deliveries and adopt useful exact proposals as separate lemma tasks; proposals and their local checks are advisory. Advisory research may start before its planned dependencies are proved; use typed proof tasks when a consumer must wait for checked premises.\n' :
      action.kind === 'task' && ['lemma', 'goal'].includes(action.task.kind) ? 'Inspect relevant checked inputs and their exact declarations before reconstructing an argument. Save the concrete consumer application and discharge every premise; report the remaining original-goal obstacle in RESEARCH.md.\n' : '') +
    (action.kind === 'task' && ['research', 'sketch'].includes(action.task.kind)
      ? 'Before restoring a temporary Lean probe, retain its complete reusable code, namespace/context, exact declaration names and proposed consumer in a lean fence in worktree-root RESEARCH.md. A prose claim that Lean passed is not a recoverable proof. To report a successful local check explicitly, use leanChecks:[{status:"passed",path:"RESEARCH.md",declarations:["Qualified.name"]}] in the single JSON response and keep the complete code outside that JSON in a lean fence. The host binds retained artifacts to this problem, assignment and commit; every local check remains advisory until a separate typed host check passes.\n' : '') +
    routeRules + handoffRules + handoffPublicationRules + leadRouteRules +
    'A delivery summarySource identifies its full finding in the manifest. If omitted for budget, retrieve complete notes via savedSource commit and notesPath; omission does not mean no result was saved.\n' +
    'Original declarations retain the frozen source order shown below. A goal cannot depend on a later original goal in the same file. Extract their shared argument into a newly named lemma before both goals; preserve every other original proof and declaration placement.\n' +
    'COOPERATION.json contains scoped live peer work, findings, gaps and checked results; leave it and CONTEXT-MANIFEST.json unchanged. The manifest records included/omitted material and reasons. Exact mathematical interfaces and original assumptions are mandatory; retrieve full proof sources/context by immutable commit/path. Replace old responses with one JSON object, plain or in a math/json fence. The host manages versions, receipts and budgets and independently checks all original targets. Unproved dependencies and reviews remain advisory.\n' +
    sharing + assessmentRules + roleText;
  const optional: ContextSection[] = [
    ...(compilation.optional ?? []),
    { id: 'plan-feedback', kind: 'feedback', text: `Review: ${JSON.stringify(cooperation.review ?? null)}` },
    { id: 'proof-continuation', kind: 'continuation', text: '\nProof continuation (stored evidence, not replayed; planned use and actual proof use are separate):\n' + JSON.stringify(continuation) },
    { id: 'statement-reviews', kind: 'statement-review', text: 'Statement reviews: ' + JSON.stringify(cooperation.statementReviews?.filter(review => review.status !== 'superseded')
      .map(statementReviewSummary) ?? []) },
  ];
  const taskContinuation = action.kind === 'task' && !isFeasibilityReview(action.task);
  const assignedNode = action.kind === 'task' ? cooperation.tasks.find(node => node.task.id === action.task.id) : undefined;
  const taskReceipts = action.kind === 'task' ? cooperation.deliveryReceipts?.filter(receipt =>
    receipt.status === 'needs-correction' && receipt.workerId === action.assignment.workerId && receipt.taskId === action.task.id &&
    receipt.taskDigest === action.assignment.taskDigest && receipt.seedCommit === action.assignment.seedCommit &&
    receipt.assignmentKey === assignmentDeliveryFile(action.assignment) && receipt.environmentDigest === compilation.environmentDigest) ?? [] : [];
  const taskInbox = taskContinuation ? {
    file: 'COOPERATION.json',
    deliveries: (cooperation.deliveries ?? []).slice(-16).map(record => ({ id: record.id, taskId: record.taskId,
      taskDigest: record.taskDigest, kind: record.kind, status: record.status, findingDigest: record.findingDigest,
      commit: record.commit, sourceDigest: record.sourceDigest })),
    gaps: (cooperation.mathematicalGaps ?? []).map(gap => ({ deliveryId: gap.deliveryId,
      consumer: gap.consumer, scopeStatus: gap.scopeStatus })),
    handoffDecisions: cooperation.researchDecisions ?? [],
    challengeDecisions: cooperation.challengeDecisions ?? [],
    parallelQuestions: (cooperation.parallelQuestions ?? []).map(question => ({ taskId: question.taskId, taskDigest: question.taskDigest })),
  } : undefined;
  const continuationMessage = action.kind === 'lead' ? [
    'Continue the current Lead responsibility in this saved thread. The original problem and unchanged task graph are already in its history.',
    'Before further investigation, update worktree-root RESEARCH.md with the current argument and precise unresolved inference. Read the latest COOPERATION.json for new findings, handoffs, blockers and active peers; read their referenced saved evidence as needed. Preserve the complete current math-plan in RESEARCH.md.',
    'Current cooperative assignment (replaces every previous dispatch nonce and receipt):\n' + JSON.stringify(action),
    'Current host work contract:\n' + JSON.stringify(workContract),
    compilation.feedback ? 'Current host feedback:\n' + compilation.feedback : '',
    coordinationRules, checkpointRules, leadDeliveryRules, sharing, handoffPublicationRules, assessmentRules,
    'Act on the current capacity/stagnation requests and shown handoff/challenge activations. Publish a useful complete plan or explicit supported decisions promptly; retain the exact mathematical gap if it is unresolved. A checkpoint, unchanged control plan, or activity report does not establish decision progress or proof acceptance.',
  ].filter(Boolean).join('\n\n') : taskContinuation ? [
    'Continue the current task responsibility in this saved thread. Its frozen problem, exact interfaces, and unchanged source rules are already in the thread history.',
    'Current cooperative assignment:\n' + JSON.stringify(action),
    'Current host work contract:\n' + JSON.stringify(workContract),
    compilation.feedback ? 'Current host feedback:\n' + compilation.feedback : '',
    assignedNode?.feedback ? 'Current task feedback:\n' + assignedNode.feedback : '',
    ...(compilation.optional ?? []).filter(section => section.kind === 'feedback').map(section => section.text),
    'Current assignment delivery receipts (intake feedback, not proof acceptance):\n' + JSON.stringify(taskReceipts),
    'Current scoped inbox references (retrieve full records before using them):\n' + JSON.stringify(taskInbox),
    'Read the latest worktree-root COOPERATION.json before continuing. Inspect referenced deliveries, mathematicalGaps, researchHandoffs, researchChallenges, blockers, peers and their saved source references for new scoped input. A matching task digest does not mean its feedback or inbox is unchanged. Missing or unavailable referenced evidence supplies no premise.',
    'Correct every needs-correction receipt by appending a new complete event to ' +
      (action.kind === 'task' ? assignmentDeliveryFile(action.assignment) : '') +
      '; include replacesReceipt with the receipt id inside the corrected finding, and preserve the log and earlier valid work. If a correction is rejected again, replace its new receipt; acceptance resolves its verified chain of attempts, while independent rejected submissions still require their own corrections. Read RESEARCH.md and resume the saved argument, exact unresolved inference and retry trigger. Do not repeat an unchanged negative search without new input or a different mathematical method.',
    'Save useful progress and use the current assignment delivery protocol. A progress report, retained draft or intake receipt is advisory; only independent host checking can establish proof acceptance.',
    researchSourcesRules, sharing,
  ].filter(Boolean).join('\n\n') : undefined;
  return { ...context, assignment: action, workContract, instructions, continuationMessage,
    ...compileTaskContext({ ...compilation, instructions, optional,
      mandatory: [...(compilation.mandatory ?? []),
        { id: 'work-contract', kind: 'assignment', text: 'Host work contract (one product; completion is not proof acceptance):\n' + JSON.stringify(workContract) },
        ...(handoffPublicationRules ? [{ id: 'handoff-publication', kind: 'assignment' as const, text: handoffPublicationRules }] : []),
        ...(capacityExploration ? [{ id: 'capacity-exploration', kind: 'assignment' as const,
          text: 'Host capacity exploration (one distinct mathematical question; advisory only):\n' + JSON.stringify({
            ...capacityExploration, target: cooperation.tasks.find(node => node.task.id === capacityExploration.targetTaskId)?.task,
          }) + '\nWork on the assigned focus and frozen target interface. Inspect current in-flight questions and saved findings to avoid repeating another worker\'s search. ' +
            'Produce a specific construction, discriminating check, or exact closed Lean interface with its intended consumer. Save complete useful Lean probes and their check results in RESEARCH.md before restoring owned Lean sources. ' +
            'A local probe is advisory; proposed lemmas still require a separate typed assignment and independent host verification. Report the precise remaining gap and return when this question is answered. ' +
            'Use the actual typed inputs in lemmaRequests.dependsOn; this exploration ID is advisory provenance and cannot be a proof dependency. ' +
            'Typed proof work has priority; scheduling checkpoints preserve this draft for continuation. Use /usr/bin/python3 for Python on this host.\n' }] : []),
        ...(action.kind === 'lead' && action.capacityRefill ? [{ id: 'capacity-refill', kind: 'assignment' as const,
          text: 'Host capacity refill request (advisory; frozen at this Lead dispatch):\n' + JSON.stringify(action.capacityRefill) + '\n' +
            'At dispatch, listed Provers had no assignable typed lemma work; listed generalists had ready work reserved to busy owners. Review ownershipCandidates before creating new obligations: these are possible explicit plan reassignments, not authorization to bypass ownerId. Reassign a useful unstarted, unassigned task to one of its eligibleWorkerIds through the complete plan, preserving its mathematical contract, route gates, group scope and independent reviewer eligibility. Preserve running assignments. Review the original-goal frontier, retained findings and current in-flight questions before further investigation. ' +
            'When a mathematically useful independent proof obligation is available, give it a full closed Lean type, stable theoremName, owned proofPath and exact dependencies in the complete current task graph. ' +
            'Save and publish that graph promptly using this dispatch\'s delivery protocol so peers can start while other work continues. Preserve checked contracts and active independent task definitions. ' +
            'If no independent executable typed obligation is known, retain the graph and state the specific missing mathematical input in RESEARCH.md; waiting is valid. ' +
            'Do not manufacture helpers or duplicate in-flight questions to fill slots. Current agents and the latest receipt are in COOPERATION.json; capacity at dispatch is not a new assignment or proof acceptance.\n' }] : []),
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
