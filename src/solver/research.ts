import path from 'node:path';
import { setTimeout as delay } from 'node:timers/promises';
import type { MathAgentSession } from '../runtime/codexSession';
import { readMathBuildManifest } from '../math/mathBuildManifest';
import { writeMathJsonDurable } from '../math/mathRuntimeIo';
import type { SolverRunState, SolverWorkerState } from './archive';
import { commitSolverSources, git } from './problem';
import { CooperativeResearch } from './cooperation';
import { taskGroup, type CooperativeAction } from './tasks';
import { isStatementAction } from './statementReview';
import { rememberSolverFailure, solverSourceFeedback } from './feedback';
import type { SolverModules } from './modules';
import { solverProofIsCurrent, type ProofCheck } from './modules/evidence';
import type { ContextBundle } from './modules/context';
import type { ResearchWorker } from './modules/organization';
import type { ResearchOperation } from './modules/value';
import { runResearchTurn, type ResearchCandidate } from './modules/execution';
import { recoverableResearchFailure, researchFailureDetail, researchFailureReason } from './modules/search';
import { aggregateUsage, buildTokenBudget, initializeUsageAccounting, modelDispatchAllowed, recordThreadUsage } from './usageBudget';

export type WorkerAccess = { environment: NodeJS.ProcessEnv; corpusFile?: string; retrievalRoot: string;
  knowledgeFile?: string; knowledgeDigest?: string };

/** Lead and isolated task workers share one budget; only a full canonical check grants acceptance. */
export async function runResearchWorkers(input: {
  state: SolverRunState; workers: readonly ResearchWorker[]; access: ReadonlyMap<string, WorkerAccess>;
  modules: SolverModules; root: string; buildFile: string; taskText: string; executable: string; profile: string;
  signal: AbortSignal; deadline: number; maxTurns: number; maxTurnMs: number; maxTotalTokens: number; proofTimeoutMs?: number;
  save: () => void; emit: (event: string, details?: Record<string, unknown>) => void;
}): Promise<{ worktree: string; check: ProofCheck } | undefined> {
  const { state, modules, save } = input;
  const parallel = Boolean(state.workers);
  const records = input.workers.map(worker => ({ worker,
    research: parallel ? state.workers!.find(item => item.id === worker.id)! : state }));
  for (const { research } of records) initializeUsageAccounting(research);
  state.tokenBudget = buildTokenBudget(input.maxTotalTokens, records.map(record => record.research));
  const dispatchAllowed = () => modelDispatchAllowed(state.tokenBudget!);
  const accepted = records.find(({ worker }) => worker.id === (state.winningWorker ?? 'solver'));
  if (accepted && state.check?.passed && ['checking', 'evaluating', 'finished'].includes(state.phase) &&
      !solverSourceFeedback(state.problem, accepted.worker.worktree) &&
      solverProofIsCurrent(state.problem, accepted.worker.worktree, state.check)) {
    return { worktree: accepted.worker.worktree, check: state.check };
  }
  if (state.check?.passed) {
    state.check = undefined; state.winningWorker = undefined;
    if (accepted) accepted.research.check = undefined;
    save();
  }
  const controller = new AbortController();
  const signal = controller.signal;
  const abort = () => controller.abort();
  input.signal.addEventListener('abort', abort, { once: true });
  if (input.signal.aborted) abort();
  const budget = () => ({ maxTurns: input.maxTurns, remainingMs: Math.max(0, input.deadline - Date.now()), aborted: signal.aborted });
  let winner: { worktree: string; check: ProofCheck } | undefined;
  let verificationQueue = Promise.resolve();
  const exclusiveCheck = async <T>(check: () => Promise<T>): Promise<T> => {
    const previous = verificationQueue;
    let release!: () => void;
    verificationQueue = new Promise<void>(resolve => { release = resolve; });
    await previous;
    try { signal.throwIfAborted(); return await check(); } finally { release(); }
  };
  const cooperation = parallel && state.coordination !== 'independent'
    ? new CooperativeResearch({ ...input, signal, exclusiveCheck, timeoutMs: input.proofTimeoutMs,
      continuousResearch: input.maxTurns === Infinity && input.deadline === Infinity,
      modelDispatchAllowed: dispatchAllowed }) : undefined;
  const updateUsage = () => {
    if (parallel) state.usage = aggregateUsage(state.workers!);
    const previous = state.tokenBudget!.status;
    state.tokenBudget = buildTokenBudget(input.maxTotalTokens, records.map(record => record.research));
    if (state.tokenBudget.status !== previous && !dispatchAllowed()) input.emit('model_budget_stopped', { ...state.tokenBudget });
    cooperation?.modelBudgetChanged();
  };
  const errors: unknown[] = [];
  const cleanupErrors: unknown[] = [];
  state.error = undefined;
  try {
    await cooperation?.restore();
    cooperation?.start();
    await Promise.all(records.map(async ({ worker, research }) => {
      let session: MathAgentSession | undefined;
      let sessionInstructions: string | undefined;
      let closing: Promise<void> | undefined;
      let retries = 0;
      let lastCheck: ProofCheck | undefined;
      research.error = undefined;
      const access = input.access.get(worker.id)!;
      const view = (): SolverRunState => ({ ...state, ...research, turns: state.turns });
      const emit = (event: string, details = {}) => input.emit(event, { workerId: worker.id, ...details });
      const context = (feedback?: string, previousCheck?: ProofCheck, previousFailures = research.failures,
        operation?: ResearchOperation, assignment?: CooperativeAction) => modules.M4.build(state.problem,
          { ...view(), ...(cooperation ? { cooperation: cooperation.contextState(assignment, worker) } : {}) }, {
          root: input.root, worktree: worker.worktree, taskText: input.taskText, ...access,
          sourceFeedback: feedback, previousCheck, previousFailures, operation, assignment,
        });
      let feedbackCheck: ProofCheck | undefined;
      let feedbackFailures = research.failures;
      let unstarted: CooperativeAction | undefined;
      let reservedTurn = false;
      let pendingTurn: Promise<void> | undefined;
      let usageTurnActive = false;
      let usageTurnReported = false;
      const modelTurn = async <T>(run: () => Promise<T>, assignment?: CooperativeAction): Promise<T | undefined> => {
        // No await separates this final admission check from invoking the model request.
        if (!dispatchAllowed() || budget().remainingMs <= 0 || signal.aborted ||
            (assignment && !cooperation!.started(worker, assignment))) return undefined;
        const kind = assignment?.kind === 'lead' ? 'planning' : assignment && (assignment.kind === 'review' || isStatementAction(assignment))
          ? 'review' : assignment?.kind === 'task' && ['research', 'sketch'].includes(assignment.task.kind) ? 'research' : 'proof';
        for (const record of parallel ? [state, research] : [state]) {
          record.dispatchCounts ??= {};
          record.dispatchCounts[kind] = (record.dispatchCounts[kind] ?? 0) + 1;
        }
        reservedTurn = false; unstarted = undefined;
        cooperation?.settleTurn(worker);
        if (assignment) cooperation!.activate(worker, assignment,
          async () => { await session?.interrupt(); },
          async message => { if (!isStatementAction(assignment)) await session?.notify?.(message); });
        const accounting = research.usageAccounting!;
        accounting.startedTurns++;
        accounting.pending = true;
        usageTurnActive = true; usageTurnReported = false;
        updateUsage(); save();
        let completed = false;
        try {
          const result = await run();
          completed = typeof result === 'string' ? result === 'completed' :
            Boolean(result && typeof result === 'object' && 'status' in result && result.status === 'completed');
          return result;
        }
        finally {
          accounting.pending = false;
          // A notification during a failed or interrupted request may be only partial consumption.
          if (usageTurnReported && completed) accounting.reportedTurns++;
          else accounting.incomplete = true;
          usageTurnActive = false;
          updateUsage(); save();
        }
      };
      const waitForTurn = () => budget().remainingMs > 0 ? cooperation?.waitForTurn(input.maxTurns) : undefined;
      const reserveTurn = () => {
        if (!dispatchAllowed() || state.turns >= input.maxTurns || budget().remainingMs <= 0 || signal.aborted) return false;
        // Reserve synchronously before opening a session so peers cannot overspend the shared budget.
        reservedTurn = true;
        state.turns++;
        if (parallel) research.turns++;
        cooperation?.reserveTurn(worker);
        state.phase = research.phase = 'running'; save();
        return true;
      };
      const close = async () => {
        if (!session) { await closing; return; }
        const current = session; session = undefined;
        try { closing = current.close(); await closing; } catch (error) { cleanupErrors.push(error); throw error; }
      };
      const cancel = () => { void close().catch(() => {}); };
      signal.addEventListener('abort', cancel, { once: true });
      const beginTurn = async (currentContext: ContextBundle, assignment?: CooperativeAction) => {
        while ((pendingTurn = waitForTurn())) await pendingTurn;
        if (currentContext.manifest) {
          research.lastContextManifest = currentContext.manifest;
          writeMathJsonDurable(path.join(worker.worktree, 'CONTEXT-MANIFEST.json'), currentContext.manifest);
          emit('context_compiled', { taskId: assignment?.kind === 'task' ? assignment.task.id : undefined,
            contentDigest: currentContext.manifest.contentDigest, requiredTaskIds: currentContext.manifest.requiredTaskIds,
            included: currentContext.manifest.included.length, omitted: currentContext.manifest.omitted.length,
            usedBytes: currentContext.manifest.usedBytes, mandatoryBytes: currentContext.manifest.mandatoryBytes,
            optionalBytes: currentContext.manifest.optionalBytes, maxOptionalBytes: currentContext.manifest.maxOptionalBytes,
            maxBytes: currentContext.manifest.maxBytes });
        }
        if (!reserveTurn()) return false;
        if (!session) {
          const statement = assignment && isStatementAction(assignment) ? assignment : undefined;
          const workspace = statement?.workspace ?? worker.worktree;
          const environment = statement ? { ...Object.fromEntries(Object.entries(access.environment).filter(([key]) =>
            !key.startsWith('DEEPSCIENTIST_MATH_') && key !== 'PWD' && key !== 'OLDPWD')), PWD: workspace } : access.environment;
          while (!session) try {
            session = await modules.M1.open({ executable: input.executable, profile: input.profile,
            ...(!statement ? { proofProjectRoot: path.join(worker.worktree, state.problem.projectRelative) } : {}),
            workspace, environment: { ...environment,
              DEEPSCIENTIST_MATH_WORKER_ID: worker.id, DEEPSCIENTIST_MATH_WORKER_WORKTREE: workspace },
            model: state.model, effort: state.effort, threadId: research.threadId,
            turnTimeoutMs: Number.isFinite(input.maxTurnMs) ? input.maxTurnMs : undefined,
            instructions: currentContext.instructions, onActivity: activity => {
              research.lastActivity = { ...activity, at: Date.now() };
              emit('worker_activity', { activity: activity.event, itemType: activity.itemType }); save();
            }, onUsage: usage => {
              research.lastInputTokens = session?.lastInputTokens ?? research.lastInputTokens;
              const reported = recordThreadUsage(research, usage);
              if (usageTurnActive && reported) usageTurnReported = true;
              updateUsage(); save();
            } });
          } catch (error) {
            signal.throwIfAborted();
            const detail = researchFailureDetail(error);
            if (!recoverableResearchFailure(detail)) throw error;
            await retryFailedTurn(detail);
            if (!dispatchAllowed()) return false;
          }
          if (signal.aborted) { await close(); signal.throwIfAborted(); }
          sessionInstructions = currentContext.instructions;
          research.threadId = session.threadId; save();
        }
        // Opening a session can await while another worker exhausts the shared allowance.
        return dispatchAllowed();
      };
      const retryFailedTurn = async (error?: string): Promise<void> => {
        research.lastFailure = { at: Date.now(), reason: researchFailureReason(error),
          taskId: parallel ? (research as SolverWorkerState).sessionTaskId : undefined };
        save();
        if (!dispatchAllowed()) return;
        const retry = modules.M3.retry(error, retries, { ...view(), turns: state.turns - Number(reservedTurn) }, budget());
        if (!retry) throw new Error(researchFailureReason(error));
        retries = retry.attempt;
        if (research.threadId && (retry.reason === 'math_model_tool_failed' || retries === 1 &&
            ['math_model_request_failed', 'math_model_request_timeout', 'math_codex_transport_closed'].includes(retry.reason)))
          await rotateSession('request');
        emit('worker_recovering', { reason: retry.reason, attempt: retries, delayMs: retry.delayMs });
        emit('turn_retry', { reason: retry.reason, attempt: retries, delayMs: retry.delayMs,
          ...(error?.startsWith('math_codex_transport_closed:') ? { detail: error } : {}) });
        await delay(retry.delayMs, undefined, { signal });
      };
      const rotateSession = async (reason: 'context' | 'responsibility' | 'route' | 'request') => {
        const previous = research.threadId;
        await close();
        if (previous) research.previousThreadIds = [...(research.previousThreadIds ?? []), previous];
        research.threadId = undefined; research.lastInputTokens = undefined;
        research.usageBeforeThread = research.usage; save();
        emit('context_restarted', { previousThreadId: previous, turns: research.turns, reason });
      };
      const checkWhole = async (candidate = research.candidate, operation: ResearchOperation = 'direct') => {
        const previousFailures = research.failures;
        const checkStarted = Date.now();
        emit('proof_check_started', { turn: research.turns });
        research.check = lastCheck?.passed && commitSolverSources(state.problem, worker.worktree) === lastCheck.commit ? lastCheck :
          await modules.M2.check(state.problem, worker.worktree, access.environment, signal, lastCheck, input.proofTimeoutMs);
        research.failures = rememberSolverFailure(research.check, previousFailures);
        emit('proof_checked', { passed: research.check.passed, commit: research.check.commit,
          reused: research.check === lastCheck, durationMs: Date.now() - checkStarted });
        lastCheck = research.check; save();
        if (research.check.passed) {
          if (cooperation && !cooperation.reviewed(research.check)) { cooperation.requireReview(research.check); return; }
          state.check = research.check; state.candidate = candidate;
          if (parallel) state.winningWorker = worker.id;
          winner = { worktree: worker.worktree, check: research.check };
          save(); emit('candidate_selected', { commit: research.check.commit }); abort();
          return;
        }
        if (['unavailable', 'blocked'].includes(research.check.verification.status)) throw new Error('math_verifier_unavailable');
        if (!cooperation && modules.M2.checkLemma && operation !== 'direct') {
          research.lemmaResearch = candidate?.lemmaPlan
            ? await modules.M2.checkLemma(state.problem, worker.worktree, access.environment, signal,
              research.check, candidate.lemmaPlan, research.lemmaResearch)
            : { error: candidate?.lemmaPlanError || 'math_lemma_plan_missing' };
          save();
          emit('lemma_checked', { bridge: research.lemmaResearch.bridge?.passed ?? false,
            lemma: research.lemmaResearch.lemma?.passed ?? false, error: research.lemmaResearch.error,
            bridgeReused: research.lemmaResearch.bridge?.reused ?? false, lemmaReused: research.lemmaResearch.lemma?.reused ?? false });
          if ([research.lemmaResearch.bridge, research.lemmaResearch.lemma].some(receipt => receipt &&
              ['unavailable', 'blocked'].includes(receipt.verification.status))) throw new Error('math_verifier_unavailable');
        }
      };
      try {
        while (!signal.aborted) {
          const assignment = await cooperation?.next(worker, budget());
          unstarted = assignment?.kind === 'assemble' ? undefined : assignment;
          if (cooperation && !assignment) break;
          if (assignment?.kind === 'assemble') {
            state.phase = research.phase = 'checking'; save();
            emit('assembly_started', { commit: assignment.seedCommit });
            await exclusiveCheck(async () => { await checkWhole(); });
            if (!winner && !research.check!.passed) cooperation!.assemblyFailed(research.check!);
            continue;
          }
          while ((pendingTurn = waitForTurn())) await pendingTurn;
          if (!dispatchAllowed() || state.turns >= input.maxTurns || budget().remainingMs <= 0) break;
          if (assignment) {
            const record = research as SolverWorkerState;
            const role = assignment.kind === 'review' || isStatementAction(assignment) ? 'reviewer' :
              assignment.kind === 'task' ? assignment.task.kind === 'goal' ? 'engineer' : 'researcher' : worker.role;
            const groupId = assignment.kind === 'task' ? taskGroup(assignment.task) : undefined;
            const roleChanged = record.sessionRole && record.sessionRole !== role;
            const groupChanged = record.sessionGroupId && record.sessionGroupId !== groupId;
            const versionChanged = assignment.kind === 'task' && record.sessionTaskId === assignment.task.id &&
              record.sessionTaskVersion && record.sessionTaskVersion !== assignment.assignment.taskDigest;
            if (isStatementAction(assignment) || record.sessionStatementReview || roleChanged) await rotateSession('responsibility');
            else if (groupChanged) await rotateSession('route');
            else if (versionChanged) await rotateSession('context');
            if (groupChanged) {
              research.check = undefined; feedbackCheck = undefined;
            }
            record.sessionRole = role;
            record.sessionGroupId = groupId;
            record.sessionTaskId = assignment.kind === 'task' ? assignment.task.id : undefined;
            record.sessionTaskVersion = assignment.kind === 'task' ? assignment.assignment.taskDigest : undefined;
            record.sessionStatementReview = isStatementAction(assignment);
          }
          if (research.threadId && Math.max(session?.lastInputTokens ?? 0, research.lastInputTokens ?? 0) >= 96_000) {
            await rotateSession('context');
          }
          const options: readonly ResearchOperation[] = assignment?.kind === 'lead' ? ['direct', 'decompose'] :
            assignment?.kind === 'task' ? assignment.task.kind === 'lemma' ? ['direct', 'prove-lemma'] :
              assignment.task.kind === 'goal' ? ['direct', 'bridge', 'integrate-lemma'] : ['direct'] :
            !cooperation && modules.M2.checkLemma ? ['direct', 'decompose', 'bridge', 'prove-lemma', 'integrate-lemma'] : ['direct'];
          while ((pendingTurn = waitForTurn())) await pendingTurn;
          const estimates = modules.M3.estimate?.(view(), options) ?? [];
          const action = modules.M3.select(view(), options, estimates, budget(), assignment);
          if (action.operation === 'stop') break;
          const operation = action.operation;
          if (!options.includes(action.operation)) throw new Error('math_research_operation_unavailable');
          emit('research_action', { operation: action.operation, reason: action.reason,
            ...(estimates.length ? { estimates } : {}) });
          if (modules.M5.organize) {
            const team = modules.M5.organize(action, input.workers, budget());
            if (team.workers.some(item => !input.workers.includes(item)))
              throw new Error('math_solver_worker_outside_ownership');
            if (!team.workers.includes(worker)) break;
          }
          readMathBuildManifest(input.buildFile, input.root, path.join(input.root, 'out', 'main'));
          const onStarted = (turnId: string) => {
            emit('turn_started', { turnId, turn: research.turns, totalTurns: state.turns });
            if (assignment && cooperation && !cooperation.current(assignment)) void session?.interrupt().catch(() => {});
          };
          if (assignment && isStatementAction(assignment)) {
            const currentContext = cooperation!.statementContext(assignment);
            try {
              if (!await beginTurn(currentContext, assignment)) break;
              let status: string | undefined;
              let executionError: string | undefined;
              try {
                status = await modelTurn(() => runResearchTurn(session!, currentContext.message, assignment.workspace, signal, onStarted), assignment);
              } catch (error) {
                signal.throwIfAborted();
                executionError = researchFailureDetail(error, session?.lastError, session?.lastFailureDiagnostic);
                if (!recoverableResearchFailure(executionError)) throw error;
                status = 'failed';
              }
              if (status === undefined) break;
              await cooperation!.pulse(worker.id);
              if (!cooperation!.current(assignment) || status === 'completed') {
                retries = 0;
                await close();
                await exclusiveCheck(() => cooperation!.deliverStatement(worker, assignment));
              } else if (['interrupted', 'checkpoint'].includes(status)) {
                retries = 0;
                cooperation!.interrupted(worker, assignment); emit('turn_checkpoint', { turn: research.turns });
              } else {
                const diagnostic = session?.lastFailureDiagnostic;
                const turnError = executionError ?? researchFailureDetail(session?.lastError, undefined, diagnostic);
                await close(); emit('turn_failed', { reason: researchFailureReason(turnError), ...(diagnostic ? { diagnostic } : {}) });
                cooperation!.interrupted(worker, assignment);
                await retryFailedTurn(turnError);
              }
            } finally {
              try { await rotateSession('context'); } finally { cooperation!.deactivate(worker); }
              (research as SolverWorkerState).sessionStatementReview = false; save();
            }
            continue;
          }
          const repair = solverSourceFeedback(state.problem, worker.worktree);
          if (repair) research.check = undefined;
          const currentContext = { ...context(repair, feedbackCheck, feedbackFailures, action.operation, assignment),
            ...(assignment ? { assignment } : {}) };
          // Resume the same thread with new instructions, preserving its history and cumulative usage.
          if (session && sessionInstructions !== currentContext.instructions) await close();
          if (!await beginTurn(currentContext, assignment)) break;
          let candidate: ResearchCandidate | undefined;
          let executionError: string | undefined;
          try {
            try {
              candidate = await modelTurn(() => modules.M1.execute(state.problem, currentContext, operation, worker, session!, signal, onStarted), assignment);
            } catch (error) {
              signal.throwIfAborted();
              executionError = researchFailureDetail(error, session?.lastError, session?.lastFailureDiagnostic);
              if (!recoverableResearchFailure(executionError)) throw error;
              // The writer must stop before the ordinary saved-source checks and delivery run.
              candidate = { status: 'failed', worktree: worker.worktree, problemReceiptDigest: state.problem.receiptDigest,
                operation, provenance: { workerId: worker.id, threadId: session!.threadId } };
            }
            if (!candidate) break;
            await cooperation?.pulse(worker.id);
          } finally { cooperation?.deactivate(worker); }
          if (assignment && cooperation && !cooperation.current(assignment)) {
            if (candidate.status === 'failed') await close();
            const commit = solverSourceFeedback(state.problem, worker.worktree) ? git(worker.worktree, ['rev-parse', 'HEAD']) : commitSolverSources(state.problem, worker.worktree);
            await exclusiveCheck(() => cooperation.deliver(worker, assignment, commit));
            emit('assignment_superseded', { commit });
            await rotateSession('context');
            continue;
          }
          if (candidate.worktree !== worker.worktree || candidate.problemReceiptDigest !== state.problem.receiptDigest ||
              candidate.operation !== action.operation || candidate.provenance.workerId !== worker.id)
            throw new Error('math_candidate_identity_changed');
          research.lastInputTokens = session?.lastInputTokens ?? research.lastInputTokens;
          research.candidate = candidate;
          const turn = cooperation && assignment && candidate.status === 'interrupted' ? 'checkpoint' : candidate.status;
          if (!['completed', 'failed', 'checkpoint'].includes(turn)) break;
          if (turn !== 'failed') retries = 0;
          if (turn === 'checkpoint') emit('turn_checkpoint', { turn: research.turns });
          const diagnostic = session?.lastFailureDiagnostic;
          const turnError = executionError ?? researchFailureDetail(session?.lastError, undefined, diagnostic);
          if (turn === 'failed') { await close(); emit('turn_failed', { reason: researchFailureReason(turnError), ...(diagnostic ? { diagnostic } : {}) }); }
          const sourceError = solverSourceFeedback(state.problem, worker.worktree);
          if (sourceError) {
            research.check = undefined; research.lemmaResearch = undefined;
            if (assignment) cooperation!.rejected(assignment, sourceError);
            save(); emit('source_rejected');
            if (turn === 'failed') throw new Error(sourceError);
            continue;
          }
          if (cooperation && assignment && turn === 'failed' &&
              (assignment.kind !== 'task' || ['research', 'sketch'].includes(assignment.task.kind))) {
            cooperation.interrupted(worker, assignment);
            await retryFailedTurn(turnError);
            continue;
          }
          state.phase = research.phase = 'checking'; save();
          const previousCheck = research.check;
          const previousFailures = research.failures;
          let checkWholeRequired = true;
          let savedTaskProof = false;
          if (cooperation && assignment) {
            const commit = commitSolverSources(state.problem, worker.worktree);
            const deliver = () => cooperation.deliver(worker, assignment, commit, turn !== 'completed',
              turn === 'failed' ? 'request-failure' : 'checkpoint');
            const delivery = assignment.kind === 'task' ? await deliver() : await exclusiveCheck(deliver);
            if (assignment.kind === 'lead' && turn === 'checkpoint') await cooperation.startInitialTasks();
            research.check = delivery.check;
            savedTaskProof = delivery.check?.passed === true;
            checkWholeRequired = delivery.checkWhole;
            if (!checkWholeRequired) save();
          }
          if (checkWholeRequired) await exclusiveCheck(() => checkWhole(candidate, operation));
          feedbackCheck = previousCheck; feedbackFailures = previousFailures;
          if (!winner && turn === 'failed') {
            if (!savedTaskProof) await retryFailedTurn(turnError);
            else if (recoverableResearchFailure(turnError)) {
              // A checked delivery is progress, not work to replay after repairing the session.
              retries = 0;
              await rotateSession('request');
              emit('worker_recovered', { reason: researchFailureReason(turnError), savedTaskProof: true });
            } else throw new Error(researchFailureReason(turnError));
          }
        }
      } catch (error) {
        if (!signal.aborted) {
          errors.push(error);
          research.error = error instanceof Error ? error.message : 'math_worker_failed';
          emit('worker_failed', { reason: research.error });
          if (!parallel || (cooperation && worker.id === input.workers[0].id) ||
              (error instanceof Error && error.message === 'math_verifier_unavailable')) abort();
        }
      } finally {
        signal.removeEventListener('abort', cancel);
        try { await close(); } catch { /* close records each failure once, including cancellation. */ }
        if (reservedTurn) { state.turns--; if (parallel) research.turns--; }
        if (unstarted) cooperation?.release(worker, unstarted);
        cooperation?.stopped(worker, (research as SolverWorkerState).error);
        if (reservedTurn) cooperation?.settleTurn(worker);
        if (parallel) research.phase = 'finished';
        updateUsage(); save();
      }
    }));
    input.signal.throwIfAborted();
    if (cleanupErrors.length) throw cleanupErrors[0];
    if (!winner && errors.length) throw errors[0];
    return winner;
  } finally {
    try { await cooperation?.stop(); } finally { input.signal.removeEventListener('abort', abort); }
  }
}
