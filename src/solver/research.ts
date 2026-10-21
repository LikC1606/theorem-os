import path from 'node:path';
import fs from 'node:fs';
import crypto from 'node:crypto';
import { setTimeout as delay } from 'node:timers/promises';
import type { MathAgentFailureDiagnostic, MathAgentSession } from '../runtime/codexSession';
import { readMathBuildManifest } from '../math/mathBuildManifest';
import { canonicalMathJson, mathDigest, writeMathJsonDurable } from '../math/mathRuntimeIo';
import type { SolverRunState, SolverWorkerState } from './archive';
import { commitSolverSources, git } from './problem';
import { CooperativeResearch } from './cooperation';
import { isFeasibilityReview, taskGroup, type CooperativeAction } from './tasks';
import { isStatementAction } from './statementReview';
import { rememberSolverFailure, solverSourceFeedback } from './feedback';
import type { SolverModules } from './modules';
import { solverProofIsCurrent, type ProofCheck } from './modules/evidence';
import type { ContextBundle } from './modules/context';
import type { KnowledgeContextSnapshot } from './knowledgeContext';
import type { ResearchWorker } from './modules/organization';
import type { ResearchOperation } from './modules/value';
import { runResearchTurn, type ResearchCandidate } from './modules/execution';
import { planResearchCooldown, recoverableResearchFailure, researchFailureDetail, researchFailureReason } from './modules/search';
import { aggregateUsage, buildTokenBudget, initializeUsageAccounting, modelDispatchAllowed } from './usageBudget';
import { ResearchUsage } from './researchUsage';
import { inspectKnowledgeUses } from './knowledgeUsage';
import { checkKnowledgeApplications } from './knowledgeApplications';
import { parseMathResponse } from './deliveries';
import { committedSource } from './problem';
import type { ContinuationSnapshot } from './continuationInput';

export type WorkerAccess = { environment: NodeJS.ProcessEnv; corpusFile?: string; retrievalRoot: string;
  continuation?: ContinuationSnapshot;
  knowledgeFile?: string; knowledgeDigest?: string; knowledgeSnapshot?: KnowledgeContextSnapshot };

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
  const enforcement = state.tokenBudget?.enforcement;
  state.tokenBudget = buildTokenBudget(input.maxTotalTokens, records.map(record => record.research), enforcement);
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
    state.tokenBudget = buildTokenBudget(input.maxTotalTokens, records.map(record => record.research), enforcement);
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
      const recovered = () => {
        const recovery = research.recovery;
        if (!recovery || recovery.phase === 'recovered') return;
        recovery.phase = 'recovered'; recovery.recoveredAt = Date.now();
        emit('worker_recovered', { reason: recovery.reason, cycles: recovery.cycles, waitedMs: recovery.waitedMs });
        save();
      };
      const waitForRecovery = async (resumed = false) => {
        const recovery = research.recovery;
        if (recovery?.phase !== 'cooling-down' || !dispatchAllowed() || budget().remainingMs <= 0 ||
            state.turns - Number(reservedTurn) >= input.maxTurns) return;
        signal.throwIfAborted();
        const started = Date.now(), delayMs = Math.max(0, recovery.nextRetryAt - started);
        if (resumed) emit('worker_recovery_resumed', { reason: recovery.reason, cycle: recovery.cycles,
          delayMs, nextRetryAt: recovery.nextRetryAt });
        try {
          if (delayMs > 0) await delay(delayMs, undefined, { signal });
          signal.throwIfAborted();
          recovery.phase = 'retrying';
        } finally {
          recovery.waitedMs += Math.max(0, Date.now() - started); save();
        }
      };
      const context = (feedback?: string, previousCheck?: ProofCheck, previousFailures = research.failures,
        assignment?: CooperativeAction) => modules.M4.build(state.problem,
          { ...view(), ...(cooperation ? { cooperation: cooperation.contextState(assignment, worker) } : {}) }, {
          root: input.root, worktree: worker.worktree, taskText: input.taskText, ...access,
          sourceFeedback: feedback, previousCheck, previousFailures, assignment,
          maxOptionalContextBytes: research.contextOverflow?.maxOptionalContextBytes,
        });
      let feedbackCheck: ProofCheck | undefined;
      let feedbackFailures = research.failures;
      let unstarted: CooperativeAction | undefined;
      let reservedTurn = false;
      let pendingTurn: Promise<void> | undefined;
      let planningCheckpoint = false;
      let turnContext: { digest: string; fresh: boolean } | undefined;
      let rebuildContext = false;
      const usage = new ResearchUsage({ state, research, maxTotalTokens: input.maxTotalTokens,
        signal, remainingMs: () => budget().remainingMs, changed: () => { updateUsage(); save(); }, emit });
      const failureDetail = (error: unknown, sessionError?: string, diagnostic?: MathAgentFailureDiagnostic) =>
        researchFailureDetail(error, sessionError, diagnostic, usage.stopReason);
      const locallyStopped = (detail?: string) => usage.stopReason !== undefined && detail === usage.stopReason;
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
        planningCheckpoint = false;
        usage.begin(assignment);
        let completed = false;
        try {
          const result = await run();
          const detail = failureDetail(undefined, session?.lastError, session?.lastFailureDiagnostic);
          if (usage.stopReason && detail !== usage.stopReason) throw new Error(detail);
          planningCheckpoint = usage.stopReason === 'math_initial_planning_limit';
          const resultStatus = typeof result === 'string' ? result : result && typeof result === 'object' && 'status' in result ? result.status : undefined;
          completed = resultStatus === 'completed';
          if (completed) recovered();
          return result;
        }
        catch (error) {
          planningCheckpoint = usage.stopReason === 'math_initial_planning_limit' &&
            failureDetail(error, session?.lastError, session?.lastFailureDiagnostic) === usage.stopReason;
          throw error;
        }
        finally {
          usage.finish(completed);
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
      /** Return a reserved but unstarted turn to the shared budget; false when none was reserved. */
      const unreserveTurn = () => {
        if (!reservedTurn) return false;
        state.turns--; if (parallel) research.turns--;
        reservedTurn = false; cooperation?.settleTurn(worker);
        return true;
      };
      const releaseUnstartedTurn = (assignment: CooperativeAction) => {
        const superseded = !cooperation!.current(assignment);
        unreserveTurn();
        cooperation!.release(worker, assignment);
        unstarted = undefined; retries = 0;
        if (superseded) emit('assignment_superseded', { beforeStart: true });
        else emit('assignment_deferred', { reason: 'turn-admission-declined' });
        save();
      };
      const close = async () => {
        if (!session) { await closing; return; }
        const current = session, closingSessionId = usage.sessionId; session = undefined;
        try { closing = current.close(); await closing; } catch (error) { cleanupErrors.push(error); throw error; }
        finally { usage.sessionClosed(closingSessionId); }
      };
      const cancel = () => { void close().catch(() => {}); };
      signal.addEventListener('abort', cancel, { once: true });
      const beginTurn = async (currentContext: ContextBundle, assignment?: CooperativeAction, operation: ResearchOperation = 'direct') => {
        usage.resetTurn(); planningCheckpoint = false;
        rebuildContext = false;
        while ((pendingTurn = waitForTurn())) await pendingTurn;
        if (assignment && !cooperation!.current(assignment)) return false;
        // Feedback counters and dispatch UUIDs must not defeat the fresh-input capacity guard.
        const target = assignment?.kind === 'task' ? { kind: assignment.kind, taskDigest: assignment.assignment.taskDigest,
          dependencies: assignment.assignment.dependencies } : assignment && isStatementAction(assignment)
          ? { kind: assignment.kind, snapshotDigest: assignment.snapshotDigest } : { kind: assignment?.kind ?? operation };
        turnContext = { digest: mathDigest(canonicalMathJson({ instructions: currentContext.instructions, target,
          problem: state.problem.receiptDigest, environment: state.environmentDigest, model: state.model,
          planVersion: cooperation?.contextState(assignment, worker).planVersion,
          optionalBytes: research.contextOverflow?.maxOptionalContextBytes ?? currentContext.manifest?.maxOptionalBytes,
          sources: state.problem.ownedFiles.map(file => [file, mathDigest(fs.readFileSync(path.join(worker.worktree,
            state.problem.projectRelative, file)))]),
        })), fresh: !research.threadId };
        if (turnContext.fresh && research.contextOverflow?.failedFreshContextDigests.includes(turnContext.digest))
          throw new Error('math_model_context_capacity_blocked');
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
        if (currentContext.knowledgeRetrievals?.length && currentContext.manifest) {
          const ledger = state.knowledgeRetrievals ??= { dropped: 0, observations: [] };
          for (const retrieval of currentContext.knowledgeRetrievals) {
            const observation = { ...retrieval, workerId: worker.id, workerTurn: research.turns, runTurn: state.turns,
              contextDigest: currentContext.manifest.contentDigest, at: Date.now() };
            ledger.observations.push(observation);
            emit('knowledge_retrieval_observed', { ...observation });
          }
          const excess = Math.max(0, ledger.observations.length - 128);
          ledger.observations.splice(0, excess); ledger.dropped += excess;
          save();
        }
        if (!session) {
          const statement = assignment && isStatementAction(assignment) ? assignment : undefined;
          const workspace = statement?.workspace ?? worker.worktree;
          const environment = statement ? { ...Object.fromEntries(Object.entries(access.environment).filter(([key]) =>
            !key.startsWith('DEEPSCIENTIST_MATH_') && key !== 'PWD' && key !== 'OLDPWD')), PWD: workspace } : access.environment;
          while (!session) {
            signal.throwIfAborted();
            if (!dispatchAllowed() || budget().remainingMs <= 0 ||
                (assignment && !cooperation!.current(assignment))) return false;
            try {
              const sessionId = crypto.randomUUID();
              const usageCallbacks = usage.bindSession(sessionId, () => session?.lastInputTokens);
              session = await modules.M1.open({ executable: input.executable, profile: input.profile,
                ...(!statement ? { proofProjectRoot: path.join(worker.worktree, state.problem.projectRelative) } : {}),
                workspace, environment: { ...environment,
                  DEEPSCIENTIST_MATH_WORKER_ID: worker.id, DEEPSCIENTIST_MATH_WORKER_WORKTREE: workspace },
                model: state.model, effort: state.effort, threadId: research.threadId,
                turnTimeoutMs: Number.isFinite(input.maxTurnMs) ? input.maxTurnMs : undefined,
                instructions: currentContext.instructions, onActivity: activity => {
                  research.lastActivity = { ...activity, at: Date.now() };
                  emit('worker_activity', { activity: activity.event, itemType: activity.itemType }); save();
                }, ...usageCallbacks });
              usage.sessionOpened(session);
            } catch (error) {
              signal.throwIfAborted();
              if (assignment && !cooperation!.current(assignment)) return false;
              const detail = failureDetail(error);
              if (!recoverableResearchFailure(detail)) throw error;
              await retryFailedTurn(detail);
              if (researchFailureReason(detail) === 'math_model_context_window_exceeded') {
                rebuildContext = true;
                if (unreserveTurn()) save();
                return false;
              }
            }
          }
          if (signal.aborted) { await close(); signal.throwIfAborted(); }
          if (assignment && !cooperation!.current(assignment)) return false;
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
        if (researchFailureReason(error) === 'math_model_context_window_exceeded') {
          const overflow = research.contextOverflow ??= { maxOptionalContextBytes: 0, failedFreshContextDigests: [] };
          overflow.maxOptionalContextBytes = 0;
          if (turnContext?.fresh && !overflow.failedFreshContextDigests.includes(turnContext.digest))
            overflow.failedFreshContextDigests.push(turnContext.digest);
          await rotateSession('context');
          retries = 0;
          emit('worker_context_recovering', { reason: research.lastFailure.reason,
            contextDigest: turnContext?.digest, maxOptionalContextBytes: 0 });
          save(); return;
        }
        const retry = modules.M3.retry(error, retries, { ...view(), turns: state.turns - Number(reservedTurn) }, budget());
        if (!retry) {
          const previous = research.recovery?.phase !== 'recovered' ? research.recovery : undefined;
          const cooldown = retries >= 3 ? planResearchCooldown(error, previous?.cycles ?? 0, budget()) : undefined;
          if (!cooldown) throw new Error(researchFailureReason(error));
          await rotateSession('request');
          const now = Date.now();
          research.recovery = { phase: 'cooling-down', reason: cooldown.reason, cycles: cooldown.cycle,
            startedAt: previous?.startedAt ?? now, nextRetryAt: now + cooldown.delayMs, waitedMs: previous?.waitedMs ?? 0 };
          emit('worker_cooling_down', { reason: cooldown.reason, cycle: cooldown.cycle,
            delayMs: cooldown.delayMs, nextRetryAt: research.recovery.nextRetryAt });
          save();
          await waitForRecovery();
          retries = 0;
          return;
        }
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
      const checkWhole = async (candidate = research.candidate) => {
        const previousFailures = research.failures;
        const checkStarted = Date.now();
        emit('proof_check_started', { turn: research.turns });
        research.check = lastCheck?.passed && commitSolverSources(state.problem, worker.worktree) === lastCheck.commit ? lastCheck :
          await modules.M2.check(state.problem, worker.worktree, access.environment, signal, lastCheck, input.proofTimeoutMs);
        research.failures = rememberSolverFailure(research.check, previousFailures);
        emit('proof_checked', { passed: research.check.passed, commit: research.check.commit,
          reused: research.check === lastCheck || research.check.verification === lastCheck?.verification,
          durationMs: Date.now() - checkStarted });
        if (access.knowledgeSnapshot) {
          let claims: unknown;
          try { claims = parseMathResponse(committedSource(worker.worktree, research.check.commit, 'RESEARCH.md'),
            'math-result', {}, 'summary').knowledgeUses; } catch { /* Ordinary notes need no usage response. */ }
          if (claims !== undefined) {
            const records = state.knowledgeUses ??= [];
            for (const [index, target] of state.problem.targets.entries()) {
              const task = state.cooperation?.tasks.find(node => node.task.kind === 'goal' && node.task.theoremName === target.theoremName &&
                node.task.proofPath === target.proofPath)?.task ?? { id: `original_goal_${index + 1}`, kind: 'goal' as const,
                objective: `Prove ${target.theoremName}`, revision: 0, dependsOn: [], ...target };
              const observed = inspectKnowledgeUses(claims, access.knowledgeSnapshot, task, research.check);
              const checked = await checkKnowledgeApplications(observed.uses, { task, projectRoot: path.join(worker.worktree, state.problem.projectRelative),
                env: access.environment, environmentDigest: state.environmentDigest, commit: research.check.commit,
                signal, timeoutMs: input.proofTimeoutMs, originalContexts: state.problem.targets, previous: records,
                sourceAtCommit: file => committedSource(worker.worktree, research.check!.commit, path.posix.join(state.problem.projectRelative, file)) });
              for (const use of checked) {
                const record = { ...use, workerId: worker.id, commit: research.check!.commit };
                const key = canonicalMathJson(record);
                if (!records.some(previous => canonicalMathJson(previous) === key)) {
                  records.push(record); emit('knowledge_use_observed', { ...record });
                }
              }
              if (observed.rejected) emit('knowledge_use_rejected', { commit: research.check!.commit, rejected: observed.rejected });
            }
            if (records.length > 256) records.splice(0, records.length - 256);
          }
        }
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
      };
      try {
        await waitForRecovery(true);
        while (!signal.aborted) {
          const assignment = await cooperation?.next(worker, budget());
          unstarted = assignment?.kind === 'assemble' ? undefined : assignment;
          if (cooperation && !assignment) break;
          if (assignment?.kind === 'assemble') {
            state.phase = research.phase = 'checking'; save();
            emit('assembly_started', { commit: assignment.seedCommit });
            await exclusiveCheck(async () => {
              if (!cooperation!.current(assignment)) return;
              await checkWhole();
              if (!winner && !research.check!.passed) cooperation!.assemblyFailed(research.check!);
            });
            continue;
          }
          while ((pendingTurn = waitForTurn())) await pendingTurn;
          if (!dispatchAllowed() || state.turns >= input.maxTurns || budget().remainingMs <= 0) break;
          if (assignment) {
            const record = research as SolverWorkerState;
            const feasibility = assignment.kind === 'task' && isFeasibilityReview(assignment.task);
            const role = assignment.kind === 'review' || isStatementAction(assignment) || feasibility ? 'reviewer' :
              assignment.kind === 'task' ? assignment.task.kind === 'goal' ? 'engineer' : 'researcher' : worker.role;
            const groupId = assignment.kind === 'task' ? taskGroup(assignment.task) : undefined;
            const roleChanged = record.sessionRole && record.sessionRole !== role;
            const groupChanged = record.sessionGroupId && record.sessionGroupId !== groupId;
            const versionChanged = assignment.kind === 'task' && record.sessionTaskId === assignment.task.id &&
              record.sessionTaskVersion && record.sessionTaskVersion !== assignment.assignment.taskDigest;
            const sessionAssignmentId = assignment.kind === 'task'
              ? assignment.assignment.assignmentId ?? `legacy-task:${assignment.assignment.seedCommit}` : undefined;
            const reviewAssignmentChanged = feasibility && record.sessionAssignmentId !== sessionAssignmentId;
            const reviewTargetChanged = (feasibility || record.sessionRole === 'reviewer') &&
              (record.sessionTaskId !== (assignment.kind === 'task' ? assignment.task.id : undefined) || versionChanged);
            if (isStatementAction(assignment) || record.sessionStatementReview || roleChanged || reviewTargetChanged || reviewAssignmentChanged)
              await rotateSession('responsibility');
            else if (groupChanged) await rotateSession('route');
            else if (versionChanged) await rotateSession('context');
            if (groupChanged) {
              research.check = undefined; feedbackCheck = undefined;
            }
            record.sessionRole = role;
            record.sessionGroupId = groupId;
            record.sessionTaskId = assignment.kind === 'task' ? assignment.task.id : undefined;
            record.sessionTaskVersion = assignment.kind === 'task' ? assignment.assignment.taskDigest : undefined;
            record.sessionAssignmentId = sessionAssignmentId;
            record.sessionStatementReview = isStatementAction(assignment);
          }
          if (research.threadId && Math.max(session?.lastInputTokens ?? 0, research.lastInputTokens ?? 0) >= 96_000) {
            await rotateSession('context');
          }
          const options: readonly ResearchOperation[] = ['direct'];
          while ((pendingTurn = waitForTurn())) await pendingTurn;
          const action = modules.M3.select(view(), options, budget(), assignment);
          if (action.operation === 'stop') break;
          const operation = action.operation;
          if (!options.includes(action.operation)) throw new Error('math_research_operation_unavailable');
          emit('research_action', { operation: action.operation, reason: action.reason });
          readMathBuildManifest(input.buildFile, input.root, path.join(input.root, 'out', 'main'));
          const onStarted = (turnId: string) => {
            emit('turn_started', { turnId, turn: research.turns, totalTurns: state.turns });
            if (assignment && cooperation && !cooperation.current(assignment)) void session?.interrupt().catch(() => {});
          };
          if (assignment && isStatementAction(assignment)) {
            const currentContext = cooperation!.statementContext(assignment);
            try {
              if (!await beginTurn(currentContext, assignment, operation)) {
                if (rebuildContext) { releaseUnstartedTurn(assignment); continue; }
                if (!cooperation!.current(assignment)) { releaseUnstartedTurn(assignment); continue; }
                break;
              }
              let status: string | undefined;
              let executionError: string | undefined;
              try {
                status = await modelTurn(() => runResearchTurn(session!, currentContext.message, assignment.workspace, signal, onStarted), assignment);
              } catch (error) {
                signal.throwIfAborted();
                executionError = failureDetail(error, session?.lastError, session?.lastFailureDiagnostic);
                if (!recoverableResearchFailure(executionError) && !locallyStopped(executionError)) throw error;
                status = 'failed';
              }
              if (status === undefined) {
                if (dispatchAllowed() && budget().remainingMs > 0 && !signal.aborted) {
                  releaseUnstartedTurn(assignment); continue;
                }
                break;
              }
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
                const turnError = executionError ?? failureDetail(session?.lastError, undefined, diagnostic);
                await close();
                if (!cooperation!.current(assignment)) {
                  retries = 0;
                  await exclusiveCheck(() => cooperation!.deliverStatement(worker, assignment));
                  emit('assignment_superseded'); continue;
                }
                emit('turn_failed', { reason: researchFailureReason(turnError), ...(diagnostic ? { diagnostic } : {}) });
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
          const currentContext = { ...context(repair, feedbackCheck, feedbackFailures, assignment),
            ...(assignment ? { assignment } : {}) };
          // Resume the same thread with new instructions, preserving its history and cumulative usage.
          if (session && sessionInstructions !== currentContext.instructions) await close();
          if (!await beginTurn(currentContext, assignment, operation)) {
            if (rebuildContext) { if (assignment) releaseUnstartedTurn(assignment); continue; }
            if (assignment && !cooperation!.current(assignment)) {
              releaseUnstartedTurn(assignment); await rotateSession('context'); continue;
            }
            break;
          }
          let candidate: ResearchCandidate | undefined;
          let executionError: string | undefined;
          try {
            try {
              candidate = await modelTurn(() => modules.M1.execute(state.problem, currentContext, operation, worker, session!, signal, onStarted), assignment);
            } catch (error) {
              signal.throwIfAborted();
              executionError = failureDetail(error, session?.lastError, session?.lastFailureDiagnostic);
              if (!recoverableResearchFailure(executionError) && !locallyStopped(executionError)) throw error;
              // The writer must stop before the ordinary saved-source checks and delivery run.
              candidate = { status: 'failed', worktree: worker.worktree, problemReceiptDigest: state.problem.receiptDigest,
                operation, provenance: { workerId: worker.id, threadId: session!.threadId } };
            }
            if (candidate && planningCheckpoint) candidate = { ...candidate, status: 'checkpoint' };
            if (!candidate) {
              if (assignment && dispatchAllowed() && budget().remainingMs > 0 && !signal.aborted) {
                releaseUnstartedTurn(assignment); await rotateSession('context'); continue;
              }
              break;
            }
            await cooperation?.pulse(worker.id);
          } finally { cooperation?.deactivate(worker); }
          const lastInputTokens = session?.lastInputTokens;
          const diagnostic = session?.lastFailureDiagnostic;
          const turnError = executionError ?? failureDetail(session?.lastError, undefined, diagnostic);
          // Closing can yield to a plan edit; check ownership after the writer has stopped.
          if (candidate.status === 'failed' || planningCheckpoint) await close();
          if (assignment && cooperation && !cooperation.current(assignment)) {
            const commit = solverSourceFeedback(state.problem, worker.worktree) ? git(worker.worktree, ['rev-parse', 'HEAD']) : commitSolverSources(state.problem, worker.worktree);
            if (assignment.kind === 'task' || assignment.kind === 'lead') await cooperation.deliver(worker, assignment, commit);
            else await exclusiveCheck(() => cooperation.deliver(worker, assignment, commit));
            emit('assignment_superseded', { commit });
            await rotateSession('context');
            continue;
          }
          if (candidate.worktree !== worker.worktree || candidate.problemReceiptDigest !== state.problem.receiptDigest ||
              candidate.operation !== action.operation || candidate.provenance.workerId !== worker.id)
            throw new Error('math_candidate_identity_changed');
          research.lastInputTokens = lastInputTokens ?? research.lastInputTokens;
          research.candidate = candidate;
          const turn = cooperation && assignment && candidate.status === 'interrupted' ? 'checkpoint' : candidate.status;
          if (!['completed', 'failed', 'checkpoint'].includes(turn)) break;
          if (turn !== 'failed') retries = 0;
          if (turn === 'checkpoint') emit('turn_checkpoint', { turn: research.turns,
            ...(planningCheckpoint ? { reason: 'math_initial_planning_limit' } : {}) });
          if (turn === 'failed') emit('turn_failed', { reason: researchFailureReason(turnError), ...(diagnostic ? { diagnostic } : {}) });
          const sourceError = solverSourceFeedback(state.problem, worker.worktree);
          if (sourceError) {
            research.check = undefined;
            if (assignment) cooperation!.rejected(assignment, sourceError);
            save(); emit('source_rejected');
            if (turn === 'failed' || planningCheckpoint) throw new Error(sourceError);
            continue;
          }
          if (cooperation && assignment && turn === 'failed' &&
              ((assignment.kind !== 'task' && assignment.kind !== 'lead') ||
                (assignment.kind === 'task' && ['research', 'sketch'].includes(assignment.task.kind)))) {
            if (assignment.kind === 'task') {
              const commit = commitSolverSources(state.problem, worker.worktree);
              await cooperation.deliver(worker, assignment, commit, true, 'request-failure');
            } else cooperation.interrupted(worker, assignment);
            await retryFailedTurn(turnError);
            continue;
          }
          state.phase = research.phase = 'checking'; save();
          const previousCheck = research.check;
          const previousFailures = research.failures;
          let checkWholeRequired = true;
          let savedTaskProof = false;
          let savedPlan = false;
          if (cooperation && assignment) {
            const commit = commitSolverSources(state.problem, worker.worktree);
            const deliver = () => cooperation.deliver(worker, assignment, commit, turn !== 'completed',
              turn === 'failed' ? 'request-failure' : 'checkpoint');
            const delivery = assignment.kind === 'task' || assignment.kind === 'lead' ? await deliver() : await exclusiveCheck(deliver);
            if (assignment.kind === 'lead' && turn === 'checkpoint') await cooperation.startInitialTasks();
            research.check = delivery.check;
            savedTaskProof = delivery.check?.passed === true;
            savedPlan = delivery.savedPlan === true;
            checkWholeRequired = delivery.checkWhole;
            if (!checkWholeRequired) save();
          }
          if (checkWholeRequired) await exclusiveCheck(() => checkWhole(candidate));
          feedbackCheck = previousCheck; feedbackFailures = previousFailures;
          if (!winner && turn === 'failed') {
            if ((!savedTaskProof && !savedPlan) || researchFailureReason(turnError) === 'math_model_context_window_exceeded')
              await retryFailedTurn(turnError);
            else if (recoverableResearchFailure(turnError)) {
              // Accepted saved work can continue after repairing the session.
              retries = 0;
              await rotateSession('request');
              emit('worker_recovered', { reason: researchFailureReason(turnError),
                ...(savedTaskProof ? { savedTaskProof: true } : {}), ...(savedPlan ? { savedPlan: true } : {}) });
            } else throw new Error(researchFailureReason(turnError));
          }
        }
      } catch (error) {
        if (!signal.aborted) {
          errors.push(error);
          research.error = error instanceof Error ? error.message : 'math_worker_failed';
          emit('worker_failed', { reason: research.error });
          if (!parallel || (cooperation && worker.id === input.workers[0].id && research.error !== 'math_model_context_capacity_blocked') ||
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
