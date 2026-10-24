import fs from 'node:fs';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { mathDigest } from '../src/math/mathRuntimeIo';
import type { MathAgentOptions, MathAgentSession } from '../src/runtime/codexSession';
import { CooperativeResearch } from '../src/solver/cooperation';
import type { ContextManifest } from '../src/solver/contextCompiler';
import { directSolverModules, type SolverModules } from '../src/solver/modules';
import { committedSource, commitSolverSources } from '../src/solver/problem';
import { researchSourceDigest, restoreResearch } from '../src/solver/researchRecords';
import { runResearchWorkers } from '../src/solver/research';
import { parseCooperationPlan, taskVersion, type CooperativeAction } from '../src/solver/tasks';
import { deferred } from './helpers/async';
import { workerAccess } from './helpers/cooperation';
import { leadWorker, localExample, peerWorker, solverState } from './helpers/solver';

vi.mock('../src/math/mathBuildManifest', () => ({ readMathBuildManifest: vi.fn() }));

describe('research basis at actual model dispatch', () => {
  let directory: string, controllers: AbortController[], running: Promise<unknown>[], releases: (() => void)[];

  beforeEach(() => {
    vi.useFakeTimers(); controllers = []; running = []; releases = [];
    // Drive the ordinary dispatch/checkpoint loop without an unrelated delivery poller.
    vi.spyOn(CooperativeResearch.prototype, 'start').mockImplementation(() => {});
  });
  afterEach(async () => {
    controllers.forEach(controller => controller.abort());
    releases.forEach(release => release());
    await Promise.allSettled(running);
    vi.useRealTimers(); vi.restoreAllMocks();
    if (directory) fs.rmSync(directory, { recursive: true, force: true });
  });

  function fixture() {
    const example = localExample('solver-research-basis-dispatch-', 'lead');
    directory = example.directory;
    const { workspace, problem } = example;
    const workers = [leadWorker(problem, workspace), peerWorker(example, 'researcher')];
    const plan = parseCooperationPlan(problem, { tasks: [
      ...problem.targets.map((target, index) => ({ id: `goal_${index + 1}`, kind: 'goal',
        objective: `Prove ${target.theoremName}`, ...target, status: 'paused' })),
      { id: 'prior', kind: 'research', objective: 'Identify the exact input.', status: 'paused' },
      { id: 'investigate', kind: 'research', ownerId: 'researcher', dependsOn: ['prior'],
        objective: 'Resolve the precise remaining construction.' },
    ] });
    const state = solverState(problem, workspace, { runId: 'research-basis-dispatch-fixture', phase: 'prepared',
      workers: workers.map(worker => ({ ...worker, phase: 'prepared', turns: 0 })),
      cooperation: { canonicalCommit: problem.baseCommit,
        tasks: plan.tasks.map(task => ({ task, status: task.id === 'prior' ? 'completed' : 'pending', attempts: 0,
          ...(task.id === 'prior' ? { finding: 'Exact dependency finding A.' } : {}) })),
        groups: plan.groups.map(group => ({ group, turns: 0 })) } });
    const investigate = () => state.cooperation!.tasks.find(node => node.task.id === 'investigate')!;
    const prior = () => state.cooperation!.tasks.find(node => node.task.id === 'prior')!;
    const sourcesAt = (commit: string) => researchSourceDigest(Object.fromEntries(problem.ownedFiles.map(file => [file,
      committedSource(workers[1].worktree, commit, `${problem.projectRelative}/${file}`)])));
    const advanceCanonical = () => {
      const file = path.join(workers[0].worktree, problem.projectRelative, 'Submission.lean');
      fs.writeFileSync(file, fs.readFileSync(file, 'utf8').replace('theorem add_zero',
        'lemma canonical_helper : True := by trivial\ntheorem add_zero'));
      const commit = commitSolverSources(problem, workers[0].worktree);
      state.cooperation!.canonicalCommit = commit;
      return commit;
    };
    const check = vi.fn(async () => { throw new Error('fixture_unexpected_proof_acceptance'); });
    const contexts: { assignment: CooperativeAction; dependencyFinding?: string }[] = [];
    const settings = { omitFinding: false, realContext: false, maxOptionalContextBytes: 0 };
    const manifests: ContextManifest[] = [];
    const events: { event: string; details?: Record<string, unknown> }[] = [];
    const controller = new AbortController(); controllers.push(controller);
    const run = (open: (options: MathAgentOptions) => Promise<MathAgentSession>, maxTurns = 1) => {
      const modules: SolverModules = { ...directSolverModules, M1: { ...directSolverModules.M1, open },
        M2: { ...directSolverModules.M2, check, checkTask: check },
        M4: { ...directSolverModules.M4, build: (_problem, view, access) => {
          const inputs = { assignment: access.assignment!,
            dependencyFinding: settings.omitFinding ? undefined : view.cooperation!.tasks.find(node => node.task.id === 'prior')?.finding };
          contexts.push(structuredClone(inputs));
          if (settings.realContext) {
            const compiled = directSolverModules.M4.build(_problem, view,
              { ...access, maxOptionalContextBytes: settings.maxOptionalContextBytes });
            manifests.push(compiled.manifest!);
            return compiled;
          }
          const manifest: ContextManifest | undefined = settings.omitFinding ? {
            schema: 'theorem-os.task-context.v1', evidence: 'recorded-not-replayed', contentDigest: 'omitted-finding-fixture',
            maxBytes: 4096, usedBytes: 100, mandatoryBytes: 100, maxOptionalBytes: 0, optionalBytes: 0,
            requiredTaskIds: ['investigate', 'prior'], included: [],
            omitted: [{ id: 'finding:prior', kind: 'finding', reason: 'optional-budget' }],
          } : undefined;
          return { instructions: 'Offline research dispatch fixture.',
            message: JSON.stringify({ ...inputs, inbox: view.cooperation!.deliveries?.map(record => record.summary), mode: 'full' }),
            continuationMessage: JSON.stringify({ ...inputs, inbox: view.cooperation!.deliveries?.map(record => record.summary), mode: 'short' }),
            scope: 'original-problem-and-allowed-library', sources: { problemReceiptDigest: problem.receiptDigest },
            ...(manifest ? { manifest } : {}) };
        } } };
      const completion = runResearchWorkers({ state, workers, modules, access: workerAccess(workers, directory),
        root: directory, buildFile: path.join(directory, 'build.json'), taskText: 'Prove the original targets.',
        executable: 'offline-fixture', profile: 'offline-fixture', signal: controller.signal,
        deadline: Infinity, maxTurnMs: Infinity, maxTurns, maxTotalTokens: 0,
        save: () => {}, emit: (event, details) => events.push({ event, details }) });
      running.push(completion); void completion.catch(() => {});
      return completion;
    };
    return { state, workers, contexts, manifests, events, settings, controller, run, check, investigate, prior, sourcesAt, advanceCanonical };
  }

  function heldResearchTurns(count: number) {
    const started = Array.from({ length: count }, () => deferred());
    const done = Array.from({ length: count }, () => deferred<string>());
    releases.push(() => done.forEach(turn => turn.resolve('interrupted')));
    const messages: string[] = [], threads: string[] = [];
    let nextThread = 0, active: ReturnType<typeof deferred<string>> | undefined;
    const open = vi.fn(async (options: MathAgentOptions): Promise<MathAgentSession> => {
      const threadId = options.threadId ?? `real-context-thread-${++nextThread}`;
      return { threadId, close: async () => { active?.resolve('interrupted'); },
        interrupt: async () => { active?.resolve('interrupted'); }, notify: async () => {},
        run: async (message, _id, worktree, onStarted) => {
          const index = messages.length;
          if (index >= count) throw new Error('fixture_unexpected_real_context_turn');
          messages.push(message); threads.push(threadId); active = done[index];
          onStarted(`real-context-turn-${index}`);
          fs.writeFileSync(path.join(worktree, 'RESEARCH.md'), `An unfinished derivation retains its exact remaining inference at step ${index}.\n`);
          started[index].resolve(); return done[index].promise;
        } };
    });
    const wait = (turn: number, completion: Promise<unknown>) => Promise.race([started[turn].promise,
      completion.then(() => { throw new Error('fixture_finished_before_real_context_turn:' + turn); })]);
    return { open, messages, threads, done, wait };
  }

  it('continues omitted real-context input briefly and dispatches newly visible evidence in full before consuming it', async () => {
    const { state, settings, manifests, events, run, check, investigate, prior, sourcesAt } = fixture();
    settings.realContext = true;
    const held = heldResearchTurns(4), completion = run(held.open, 4);
    await held.wait(0, completion);
    const finding = prior().finding!;
    expect(manifests.at(-1)!.omitted).toContainEqual({ id: 'finding:prior', kind: 'finding', reason: 'optional-budget' });
    expect(held.messages[0]).not.toContain(finding);
    expect(investigate().assignment!.researchBasis).toBeUndefined();

    await vi.advanceTimersByTimeAsync(120_000); await held.wait(1, completion);
    expect(held.messages[1]).toContain('Continue the current task responsibility');
    expect(held.messages[1]).not.toContain(finding);
    expect(investigate().assignment!.researchBasis).toBeUndefined();

    settings.maxOptionalContextBytes = 64 * 1024;
    await vi.advanceTimersByTimeAsync(120_000); await held.wait(2, completion);
    expect(manifests.at(-1)!.included).toContainEqual(expect.objectContaining({ id: 'finding:prior' }));
    expect(held.messages[2]).toContain(finding);
    const visibleBasis = investigate().assignment!.researchBasis!;
    expect(visibleBasis.dependencies).toContainEqual(expect.objectContaining({ taskId: 'prior', findingDigest: mathDigest(finding) }));

    await vi.advanceTimersByTimeAsync(120_000); await held.wait(3, completion);
    expect(held.messages[3]).toContain('Continue the current task responsibility');
    expect(investigate().assignment!.researchBasis).toBe(visibleBasis);
    expect(events.filter(item => item.event === 'context_dispatched').map(item => item.details?.mode))
      .toEqual(['full', 'continuation', 'full', 'continuation']);
    expect(held.open).toHaveBeenCalledOnce();
    held.done[3].resolve('completed'); await expect(completion).resolves.toBeUndefined();
    expect(restoreResearch(investigate().researchCompletion, investigate().task, {
      sourceDigest: sourcesAt(investigate().assignment!.seedCommit), problemReceiptDigest: state.problem.receiptDigest,
      environmentDigest: state.environmentDigest, tasks: state.cooperation!.tasks,
      deliveries: state.cooperation!.deliveries }, investigate().finding).status).toBe('completed');
    expect(check).not.toHaveBeenCalled(); expect(state.check).toBeUndefined();
  });

  it('notifies a changed hidden dependency once without claiming it was consumed', async () => {
    const { state, settings, events, run, check, investigate, prior, sourcesAt } = fixture();
    settings.realContext = true;
    const held = heldResearchTurns(4), completion = run(held.open, 4);
    await held.wait(0, completion);
    await vi.advanceTimersByTimeAsync(120_000); await held.wait(1, completion);
    prior().finding = 'A new hidden dependency construction requires its complete saved argument.';
    await vi.advanceTimersByTimeAsync(120_000); await held.wait(2, completion);
    expect(held.messages[2]).not.toContain(prior().finding!);
    expect(investigate().assignment!.researchBasis).toBeUndefined();
    await vi.advanceTimersByTimeAsync(120_000); await held.wait(3, completion);
    expect(events.filter(item => item.event === 'context_dispatched').map(item => item.details?.mode))
      .toEqual(['full', 'continuation', 'full', 'continuation']);
    expect(investigate().assignment!.researchBasis).toBeUndefined();
    held.done[3].resolve('completed'); await expect(completion).resolves.toBeUndefined();
    expect(restoreResearch(investigate().researchCompletion, investigate().task, {
      sourceDigest: sourcesAt(investigate().assignment!.seedCommit), problemReceiptDigest: state.problem.receiptDigest,
      environmentDigest: state.environmentDigest, tasks: state.cooperation!.tasks,
      deliveries: state.cooperation!.deliveries }, investigate().finding).status).toBe('pending');
    expect(check).not.toHaveBeenCalled(); expect(state.check).toBeUndefined();
  });

  it('sends full real context after rotating an omitted-input thread', async () => {
    const { settings, events, run, check, investigate } = fixture();
    settings.realContext = true;
    const held = heldResearchTurns(3), completion = run(held.open, 3);
    await held.wait(0, completion);
    await vi.advanceTimersByTimeAsync(120_000); await held.wait(1, completion);
    held.open.mock.calls[0][0].onActivity!({ event: 'item_started', itemType: 'contextCompaction' });
    await vi.advanceTimersByTimeAsync(10 * 60_000); await held.wait(2, completion);
    expect(held.threads).toEqual(['real-context-thread-1', 'real-context-thread-1', 'real-context-thread-2']);
    expect(events.filter(item => item.event === 'context_dispatched').map(item => item.details?.mode))
      .toEqual(['full', 'continuation', 'full']);
    expect(investigate().assignment!.researchBasis).toBeUndefined();
    held.done[2].resolve('completed'); await expect(completion).resolves.toBeUndefined();
    expect(check).not.toHaveBeenCalled();
  });

  it('settles the exact context prepared before a session opens and freezes its basis only when the request starts', async () => {
    const { state, workers, contexts, run, check, investigate, prior, sourcesAt, advanceCanonical } = fixture();
    const opening = deferred(), opened = deferred<MathAgentSession>(), started = deferred(), done = deferred<string>();
    const session: MathAgentSession = { threadId: 'basis-open-thread', close: async () => { done.resolve('interrupted'); },
      interrupt: async () => { done.resolve('interrupted'); }, notify: async () => {},
      run: async (message, _id, _workspace, onStarted) => {
        expect(investigate().assignment!.researchBasis).toBeUndefined();
        expect(JSON.parse(message)).toMatchObject({ dependencyFinding: 'Exact dependency finding A.' });
        expect(message).not.toContain('researchBasis');
        onStarted('basis-open-turn'); started.resolve(); return done.promise;
      } };
    releases.push(() => { opened.resolve(session); done.resolve('interrupted'); });
    const completion = run(async () => { opening.resolve(); return opened.promise; });
    await opening.promise;
    const seed = investigate().assignment!.seedCommit;
    expect(investigate().assignment!.researchBasis).toBeUndefined();
    expect(contexts[0].dependencyFinding).toBe('Exact dependency finding A.');
    prior().finding = 'Exact dependency finding B.';
    const canonical = advanceCanonical();
    opened.resolve(session); await started.promise;
    const basis = investigate().assignment!.researchBasis!;
    expect(basis.dependencies).toContainEqual(expect.objectContaining({ taskId: 'prior', findingDigest: mathDigest(contexts[0].dependencyFinding!) }));
    expect(basis.sourceDigest).toBe(sourcesAt(seed)); expect(basis.sourceDigest).not.toBe(sourcesAt(canonical));
    fs.writeFileSync(path.join(workers[1].worktree, 'RESEARCH.md'), 'The exact derivation and its precise remaining scope are saved.\n');
    done.resolve('completed'); await expect(completion).resolves.toBeUndefined();
    expect(investigate().researchCompletion).toMatchObject({ complete: true, basis, seedCommit: seed });
    expect(state.cooperation!.deliveries!.find(record => record.taskId === 'investigate' && record.kind === 'research')!.researchRecord)
      .toBe(investigate().researchCompletion);
    expect(check).not.toHaveBeenCalled(); expect(state.check).toBeUndefined();
  });

  it('refreshes changed input in full context, keeps the same seed and resumes unchanged input with a short prompt', async () => {
    const { state, workers, contexts, events, run, check, investigate, prior, sourcesAt, advanceCanonical } = fixture();
    const entered = [deferred(), deferred(), deferred()], started = [deferred(), deferred(), deferred()];
    const done = [deferred<string>(), deferred<string>(), deferred<string>()], startSecond = deferred();
    releases.push(() => { startSecond.resolve(); done.forEach(turn => turn.resolve('interrupted')); });
    const messages: { mode: string; assignment: CooperativeAction; dependencyFinding?: string }[] = [];
    let turn = 0, active = done[0];
    const open = vi.fn(async (options: MathAgentOptions): Promise<MathAgentSession> => ({
      threadId: options.threadId ?? 'same-research-thread', close: async () => { active.resolve('interrupted'); },
      interrupt: async () => { active.resolve('interrupted'); }, notify: async () => {},
      run: async (message, _id, _workspace, onStarted) => {
        const index = turn++;
        if (index > 2) throw new Error('fixture_unexpected_fourth_turn');
        messages.push(JSON.parse(message)); active = done[index]; entered[index].resolve();
        if (index === 1) await startSecond.promise;
        onStarted(`basis-continuation-${index}`); started[index].resolve();
        fs.writeFileSync(path.join(options.workspace, 'RESEARCH.md'), index === 0
          ? 'The unfinished derivation and exact remaining inference are retained.\n'
          : 'The completed advisory derivation retains all quantified hypotheses.\n');
        return done[index].promise;
      } }));
    const completion = run(open, 3);
    await started[0].promise;
    const firstBasis = investigate().assignment!.researchBasis!, seed = investigate().assignment!.seedCommit;
    prior().finding = 'A new exact dependency finding for the next prompt.';
    await vi.advanceTimersByTimeAsync(120_000); await entered[1].promise;
    expect(investigate().researchCompletion).toBeUndefined(); expect(investigate().finding).toBeUndefined();
    expect(state.cooperation!.researchDrafts?.investigate).toBeDefined();
    expect(investigate().assignment!.researchBasis).toBe(firstBasis);
    const canonical = advanceCanonical();
    startSecond.resolve(); await started[1].promise;
    const nextBasis = investigate().assignment!.researchBasis!;
    expect(nextBasis).not.toBe(firstBasis);
    expect(nextBasis.dependencies).toContainEqual(expect.objectContaining({ taskId: 'prior', findingDigest: mathDigest(contexts[1].dependencyFinding!) }));
    expect(contexts[1].dependencyFinding).toBe('A new exact dependency finding for the next prompt.');
    expect(nextBasis.sourceDigest).toBe(sourcesAt(seed)); expect(nextBasis.sourceDigest).not.toBe(sourcesAt(canonical));
    expect(messages.map(message => message.mode)).toEqual(['full', 'full']);
    const unrelated = state.cooperation!.tasks.find(node => node.task.kind === 'goal')!.task;
    (state.cooperation!.deliveries ??= []).push({ id: 'unrelated-peer-progress', taskId: unrelated.id,
      taskDigest: taskVersion(unrelated), kind: 'progress', status: 'advisory', producer: workers[0].id,
      summary: 'Unrelated original-goal activity.', statement: unrelated.objective, premises: [], dependencies: [],
      remainingObligations: [], evidenceRefs: [], createdAt: Date.now() });
    await vi.advanceTimersByTimeAsync(120_000); await started[2].promise;
    expect(investigate().researchCompletion).toBeUndefined();
    expect(investigate().assignment!.researchBasis).toEqual(nextBasis);
    expect(messages.map(message => message.mode)).toEqual(['full', 'full', 'short']);
    expect(JSON.stringify(messages)).not.toContain('researchBasis');
    expect(JSON.stringify(messages[2])).toContain('Unrelated original-goal activity.');
    expect(events.filter(event => event.event === 'context_dispatched').map(event => event.details?.mode)).toEqual(['full', 'full', 'continuation']);
    expect(open).toHaveBeenCalledOnce(); expect(state.workers![1].threadId).toBe('same-research-thread');
    done[2].resolve('completed'); await expect(completion).resolves.toBeUndefined();
    expect(investigate().researchCompletion).toMatchObject({ basis: nextBasis, complete: true });
    expect(check).not.toHaveBeenCalled(); expect(state.check).toBeUndefined();
  });

  it('does not manufacture an input basis when opening a session is cancelled before dispatch', async () => {
    const { state, run, controller, investigate, check } = fixture();
    const opening = deferred(), opened = deferred<MathAgentSession>();
    const request = vi.fn(async () => { throw new Error('fixture_unstarted_request_must_not_run'); });
    const close = vi.fn(async () => {});
    const session: MathAgentSession = { threadId: 'unstarted-thread', run: request, close, interrupt: async () => {}, notify: async () => {} };
    releases.push(() => opened.resolve(session));
    const completion = run(async () => { opening.resolve(); return opened.promise; });
    await opening.promise;
    expect(investigate().assignment!.researchBasis).toBeUndefined();
    controller.abort(new Error('fixture_cancel_before_start'));
    opened.resolve(session);
    await expect(completion).rejects.toThrow('fixture_cancel_before_start');
    expect(investigate().assignment?.researchBasis).toBeUndefined(); expect(investigate().researchCompletion).toBeUndefined();
    expect(state.cooperation!.deliveries ?? []).toEqual([]); expect(request).not.toHaveBeenCalled();
    expect(close).toHaveBeenCalledOnce(); expect(state.turns).toBe(0); expect(check).not.toHaveBeenCalled();
  });

  it.each([false, true])('does not claim consumption of an omitted dependency finding (previous basis: %s)', async previous => {
    const { state, settings, run, check, investigate, prior, sourcesAt } = fixture();
    const started = [deferred(), deferred()], done = [deferred<string>(), deferred<string>()];
    releases.push(() => done.forEach(turn => turn.resolve('interrupted')));
    let turn = 0, active = done[0];
    if (!previous) settings.omitFinding = true;
    const completion = run(async (): Promise<MathAgentSession> => ({ threadId: 'omitted-finding-thread',
      close: async () => { active.resolve('interrupted'); }, interrupt: async () => { active.resolve('interrupted'); }, notify: async () => {},
      run: async (message, _id, worktree, onStarted) => {
        const index = turn++; active = done[index];
        if (settings.omitFinding) expect(JSON.parse(message).dependencyFinding).toBeUndefined();
        onStarted(`omitted-finding-turn-${index}`); started[index].resolve();
        fs.writeFileSync(path.join(worktree, 'RESEARCH.md'), index === 0 && previous
          ? 'An unfinished derivation using the supplied first dependency finding.\n'
          : 'An advisory derivation based on the dependency findings actually supplied.\n');
        return done[index].promise;
      } }), previous ? 2 : 1);
    await started[0].promise;
    const oldBasis = investigate().assignment!.researchBasis;
    if (previous) {
      expect(oldBasis).toBeDefined();
      prior().finding = 'New dependency finding omitted from the model context.';
      settings.omitFinding = true;
      await vi.advanceTimersByTimeAsync(120_000); await started[1].promise;
    }
    expect(investigate().assignment!.researchBasis).toBe(oldBasis);
    if (!previous) expect(oldBasis).toBeUndefined();
    done[previous ? 1 : 0].resolve('completed'); await expect(completion).resolves.toBeUndefined();
    const node = investigate();
    expect(node.researchCompletion?.basis).toEqual(oldBasis);
    expect(restoreResearch(node.researchCompletion, node.task, { sourceDigest: sourcesAt(node.assignment!.seedCommit),
      problemReceiptDigest: state.problem.receiptDigest, environmentDigest: state.environmentDigest,
      tasks: state.cooperation!.tasks, deliveries: state.cooperation!.deliveries }, node.finding).status).toBe('pending');
    expect(check).not.toHaveBeenCalled(); expect(state.check).toBeUndefined();
  });
});
