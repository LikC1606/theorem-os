import path from 'node:path';
import { setTimeout as delay } from 'node:timers/promises';
import type { MathAgentSession } from '../runtime/codexSession';
import { readMathBuildManifest } from '../math/mathBuildManifest';
import type { SolverRunState, SolverWorkerState } from './archive';
import { commitSolverSources, git } from './problem';
import { CooperativeResearch, taskGroup } from './cooperation';
import { rememberSolverFailure, solverSourceFeedback } from './feedback';
import type { SolverModules } from './modules';
import type { ProofCheck } from './modules/evidence';
import type { ContextBundle } from './modules/context';
import type { ResearchWorker } from './modules/organization';
import type { ResearchOperation } from './modules/value';

export type WorkerAccess = { environment: NodeJS.ProcessEnv; corpusFile?: string; retrievalRoot: string };

/** Lead and isolated task workers share one budget; only a full canonical check grants acceptance. */
export async function runResearchWorkers(input: {
  state: SolverRunState; workers: readonly ResearchWorker[]; access: ReadonlyMap<string, WorkerAccess>;
  modules: SolverModules; root: string; buildFile: string; taskText: string; executable: string; profile: string;
  signal: AbortSignal; deadline: number; maxTurns: number; maxTurnMs: number; proofTimeoutMs?: number;
  save: () => void; emit: (event: string, details?: Record<string, unknown>) => void;
}): Promise<{ worktree: string; check: ProofCheck } | undefined> {
  const { state, modules, save } = input;
  const parallel = Boolean(state.workers);
  const records = input.workers.map(worker => ({ worker,
    research: parallel ? state.workers!.find(item => item.id === worker.id)! : state }));
  const accepted = records.find(({ worker }) => worker.id === (state.winningWorker ?? 'solver'));
  if (accepted && state.check?.passed && ['checking', 'evaluating', 'finished'].includes(state.phase) &&
      !solverSourceFeedback(state.problem, accepted.worker.worktree) &&
      git(accepted.worker.worktree, ['rev-parse', 'HEAD']) === state.check.commit &&
      !git(accepted.worker.worktree, ['status', '--porcelain', '--', ...state.problem.ownedFiles
        .map(file => path.join(state.problem.projectRelative, file))])) {
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
  const cooperation = parallel ? new CooperativeResearch({ ...input, signal, exclusiveCheck, timeoutMs: input.proofTimeoutMs }) : undefined;
  const updateUsage = () => {
    if (!parallel) return;
    const usage: Record<string, unknown> = {};
    for (const record of state.workers!) for (const [key, value] of Object.entries(record.usage ?? {})) {
      if (typeof value === 'number') usage[key] = Number(usage[key] ?? 0) + value;
    }
    state.usage = usage;
  };
  const errors: unknown[] = [];
  const cleanupErrors: unknown[] = [];
  try {
    await cooperation?.restore();
    await Promise.all(records.map(async ({ worker, research }) => {
      let session: MathAgentSession | undefined;
      let closing: Promise<void> | undefined;
      let closeError: unknown;
      let retries = 0;
      let lastCheck: ProofCheck | undefined;
      if (parallel) (research as SolverWorkerState).error = undefined;
      const access = input.access.get(worker.id)!;
      const view = (): SolverRunState => ({ ...state, ...research, turns: state.turns });
      const emit = (event: string, details = {}) => input.emit(event, { workerId: worker.id, ...details });
      const context = (feedback?: string, previousCheck?: ProofCheck, previousFailures = research.failures,
        operation?: ResearchOperation) => modules.M4.build(state.problem, view(), {
          root: input.root, worktree: worker.worktree, taskText: input.taskText, ...access,
          sourceFeedback: feedback, previousCheck, previousFailures, operation,
        });
      let currentContext: ContextBundle;
      let feedbackCheck: ProofCheck | undefined;
      let feedbackFailures = research.failures;
      const close = async () => {
        if (!session) { await closing; return; }
        const current = session; session = undefined;
        closing = current.close();
        try { await closing; } catch (error) { closeError = error; throw error; }
      };
      const cancel = () => { void close().catch(error => { closeError = error; }); };
      signal.addEventListener('abort', cancel, { once: true });
      const open = async () => {
        signal.throwIfAborted();
        session = await modules.M1.open({ executable: input.executable, profile: input.profile,
          workspace: worker.worktree, environment: { ...access.environment,
            DEEPSCIENTIST_MATH_WORKER_ID: worker.id, DEEPSCIENTIST_MATH_WORKER_WORKTREE: worker.worktree },
          model: state.model, effort: state.effort, threadId: research.threadId,
          turnTimeoutMs: Number.isFinite(input.maxTurnMs) ? input.maxTurnMs : undefined,
          instructions: currentContext.instructions, onUsage: usage => {
            research.lastInputTokens = session?.lastInputTokens ?? research.lastInputTokens;
            research.usage = { ...research.usageBeforeThread, ...usage };
            for (const [key, value] of Object.entries(usage)) {
              const previous = research.usageBeforeThread?.[key];
              if (typeof value === 'number' && typeof previous === 'number') research.usage[key] = previous + value;
            }
            updateUsage(); save();
          } });
        if (signal.aborted) { await close(); signal.throwIfAborted(); }
        research.threadId = session.threadId; save();
      };
      const retryFailedTurn = async (error?: string): Promise<boolean> => {
        const retry = modules.M3.retry(error, retries, view(), budget());
        if (!retry) return false;
        retries = retry.attempt;
        emit('turn_retry', { reason: 'model_concurrency_limit', attempt: retries, delayMs: retry.delayMs });
        await delay(retry.delayMs, undefined, { signal });
        await open();
        return true;
      };
      const rotateSession = async (reason: 'context' | 'responsibility' | 'route') => {
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
          if (cooperation && !cooperation.reviewed()) { cooperation.requireReview(research.check); return; }
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
        currentContext = context(solverSourceFeedback(state.problem, worker.worktree));
        while (!signal.aborted) {
          const assignment = await cooperation?.next(worker, budget());
          if (cooperation && !assignment) break;
          if (assignment?.kind === 'assemble') {
            state.phase = research.phase = 'checking'; save();
            emit('assembly_started', { commit: assignment.seedCommit });
            await exclusiveCheck(async () => { await checkWhole(); });
            if (!winner && !research.check!.passed) cooperation!.assemblyFailed(research.check!);
            continue;
          }
          if (state.turns >= input.maxTurns || budget().remainingMs <= 0) break;
          if (assignment) {
            const record = research as SolverWorkerState;
            const role = assignment.kind === 'review' ? 'reviewer' : worker.role;
            const groupId = assignment.kind === 'task' ? taskGroup(assignment.task) : undefined;
            const roleChanged = record.sessionRole && record.sessionRole !== role;
            const groupChanged = record.sessionGroupId && record.sessionGroupId !== groupId;
            if (roleChanged) await rotateSession('responsibility');
            else if (groupChanged) await rotateSession('route');
            if (groupChanged) {
              research.check = undefined; feedbackCheck = undefined;
            }
            record.sessionRole = role;
            record.sessionGroupId = groupId;
          }
          if (research.threadId && Math.max(session?.lastInputTokens ?? 0, research.lastInputTokens ?? 0) >= 96_000) {
            await rotateSession('context');
          }
          const options: readonly ResearchOperation[] = !cooperation && modules.M2.checkLemma
            ? ['direct', 'decompose', 'bridge', 'prove-lemma', 'integrate-lemma'] : ['direct'];
          const estimates = modules.M3.estimate(view(), options);
          const action = modules.M3.select(view(), options, estimates, budget());
          if (action.operation === 'stop') break;
          const operation = action.operation;
          if (!options.includes(action.operation)) throw new Error('math_research_operation_unavailable');
          emit('research_action', { operation: action.operation, reason: action.reason, estimates });
          const team = modules.M5.organize(action, [worker], budget());
          if (!team.workers.includes(worker) || team.workers.some(item => item !== worker))
            throw new Error('math_solver_worker_outside_ownership');
          readMathBuildManifest(input.buildFile, input.root, path.join(input.root, 'out', 'main'));
          const repair = solverSourceFeedback(state.problem, worker.worktree);
          if (repair) research.check = undefined;
          currentContext = context(repair, feedbackCheck, feedbackFailures, action.operation);
          if (assignment) currentContext = cooperation!.decorate(currentContext, assignment);
          // Reserve synchronously before opening a session so peers cannot overspend the shared turn budget.
          state.turns++;
          if (parallel) research.turns++;
          state.phase = research.phase = 'running'; save();
          if (!session) await open();
          const candidate = await modules.M1.execute(state.problem, currentContext, action.operation, worker, session!, signal,
            turnId => emit('turn_started', { turnId, turn: research.turns, totalTurns: state.turns }));
          if (candidate.worktree !== worker.worktree || candidate.problemReceiptDigest !== state.problem.receiptDigest ||
              candidate.operation !== action.operation || candidate.provenance.workerId !== worker.id)
            throw new Error('math_candidate_identity_changed');
          research.lastInputTokens = session?.lastInputTokens ?? research.lastInputTokens;
          research.candidate = candidate;
          const turn = candidate.status;
          if (!['completed', 'failed', 'checkpoint'].includes(turn)) break;
          if (turn === 'checkpoint') emit('turn_checkpoint', { turn: research.turns });
          const turnError = session?.lastError;
          if (turn === 'failed') { await close(); emit('turn_failed'); }
          if (cooperation && assignment && turn === 'failed' && /\bConcurrency limit exceeded\b/iu.test(turnError ?? '')) {
            cooperation.interrupted(worker, assignment);
            if (!await retryFailedTurn(turnError)) break;
            continue;
          }
          const sourceError = solverSourceFeedback(state.problem, worker.worktree);
          if (sourceError) {
            research.check = undefined; research.lemmaResearch = undefined;
            if (assignment) cooperation!.rejected(assignment, sourceError);
            save(); emit('source_rejected');
            if (turn === 'failed' && !await retryFailedTurn(turnError)) break;
            continue;
          }
          state.phase = research.phase = 'checking'; save();
          const previousCheck = research.check;
          const previousFailures = research.failures;
          await exclusiveCheck(async () => {
            if (cooperation && assignment) {
              const commit = commitSolverSources(state.problem, worker.worktree);
              const delivery = await cooperation.deliver(worker, assignment, commit);
              research.check = delivery.check;
              if (!delivery.checkWhole) { save(); return; }
            }
            await checkWhole(candidate, operation);
          });
          feedbackCheck = previousCheck; feedbackFailures = previousFailures;
          currentContext = context(undefined, previousCheck, previousFailures);
          if (!winner && turn === 'failed' && !await retryFailedTurn(turnError)) break;
        }
      } catch (error) {
        if (!signal.aborted) {
          errors.push(error);
          if (parallel) { (research as SolverWorkerState).error = error instanceof Error ? error.message : 'math_worker_failed';
            emit('worker_failed', { reason: (research as SolverWorkerState).error }); }
          if (!parallel || worker.id === input.workers[0].id || (error instanceof Error && error.message === 'math_verifier_unavailable')) abort();
        }
      } finally {
        signal.removeEventListener('abort', cancel);
        try { await close(); } catch (error) { cleanupErrors.push(error); }
        if (closeError && !cleanupErrors.includes(closeError)) cleanupErrors.push(closeError);
        cooperation?.stopped(worker, (research as SolverWorkerState).error);
        if (parallel) research.phase = 'finished';
        updateUsage(); save();
      }
    }));
    input.signal.throwIfAborted();
    if (cleanupErrors.length) throw cleanupErrors[0];
    if (!winner && errors.length) throw errors[0];
    return winner;
  } finally { input.signal.removeEventListener('abort', abort); }
}
