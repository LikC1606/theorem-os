import fs from 'node:fs';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import type { MathAgentSession } from '../src/runtime/codexSession';
import type { SolverRunState } from '../src/solver/archive';
import { CooperativeResearch } from '../src/solver/cooperation';
import { directSolverModules, type SolverModules } from '../src/solver/modules';
import type { ResearchWorker } from '../src/solver/modules/organization';
import type { SolverProblem } from '../src/solver/problem';
import { runResearchWorkers } from '../src/solver/research';
import { parseCooperationPlan, type CooperativeAction } from '../src/solver/tasks';
import { workerAccess } from './helpers/cooperation';
import { leadWorker, localExample, peerWorker, solverState } from './helpers/solver';

const backoff = vi.hoisted(() => ({ run: vi.fn<() => Promise<void>>() }));
vi.mock('../src/math/mathBuildManifest', () => ({ readMathBuildManifest: vi.fn() }));
vi.mock('node:timers/promises', () => ({ setTimeout: async () => { await backoff.run(); } }));

describe('cooperative session admission', () => {
  let directory: string, problem: SolverProblem, state: SolverRunState, workers: ResearchWorker[];

  beforeEach(() => {
    backoff.run.mockReset();
    const example = localExample('solver-session-admission-', 'lead'), workspace = example.workspace;
    ({ directory, problem } = example);
    workers = [leadWorker(problem, workspace), peerWorker(example, 'peer')];
    const plan = parseCooperationPlan(problem, { tasks: [
      ...problem.targets.map((target, index) => ({ id: `goal_${index}`, kind: 'goal',
        objective: `Prove ${target.theoremName}`, proofPath: target.proofPath,
        theoremName: target.theoremName, status: 'paused' })),
      { id: 'first_investigation', kind: 'research', objective: 'Investigate the first route.', ownerId: 'peer' },
      { id: 'next_investigation', kind: 'research', objective: 'Investigate the next route.', ownerId: 'peer' },
    ] });
    state = solverState(problem, workspace, { runId: 'session-admission-fixture', phase: 'prepared',
      evaluatorDigest: 'evaluation', model: 'fixture', effort: 'fixture', workers: workers.map(worker => ({ ...worker, phase: 'prepared', turns: 0 })),
      cooperation: { tasks: plan.tasks.map(task => ({ task, status: 'pending', attempts: 0 })),
        groups: plan.groups.map(group => ({ group, turns: 0 })) } });
  });
  afterEach(() => { vi.restoreAllMocks(); fs.rmSync(directory, { recursive: true, force: true }); });

  it.each([...(['opened', 'failed', 'retrying'] as const).flatMap(opening =>
    (['pause', 'revise', 'remove'] as const).map(change => ({ opening, change }))),
    { opening: 'opened' as const, change: 'exhaust-route' as const }])
  ('continues current work after $change supersedes a session that $opening during startup', async ({ opening, change }) => {
    if (change === 'exhaust-route') {
      state.cooperation!.groups![0].group = { ...state.cooperation!.groups![0].group, maxTurns: 1 };
      state.cooperation!.groups!.push({ group: { id: 'secondary', objective: 'Investigate an independent route.',
        status: 'active', revision: 0 }, turns: 0 });
      const node = state.cooperation!.tasks.find(node => node.task.id === 'next_investigation')!;
      node.task = { ...node.task, groupId: 'secondary' };
    }
    let cooperation: CooperativeResearch | undefined;
    const next = CooperativeResearch.prototype.next;
    vi.spyOn(CooperativeResearch.prototype, 'next').mockImplementation(async function(worker, budget) {
      cooperation = this;
      return next.call(this, worker, budget);
    });
    const events: { event: string; details?: Record<string, unknown> }[] = [];
    const runs: CooperativeAction[] = [];
    const close = vi.fn(async () => {});
    const edit = async () => {
      const tasks = state.cooperation!.tasks.flatMap(({ task }) => {
        if (task.id !== 'first_investigation') return [task];
        if (change === 'remove') return [];
        return [{ ...task, ...(change === 'pause' ? { status: 'paused' as const } : { revision: task.revision + 1 }) }];
      });
      fs.appendFileSync(path.join(directory, 'edits.jsonl'), JSON.stringify({
        id: 'during-startup', baseVersion: state.cooperation!.planVersion, tasks,
      }) + '\n');
      await cooperation!.pulse();
      expect(state.cooperation!.edits?.find(edit => edit.id === 'during-startup')?.status).toBe('applied');
    };
    const retry = vi.fn().mockReturnValue(opening === 'retrying'
      ? { attempt: 1, reason: 'math_model_request_failed', delayMs: 0 } : undefined);
    if (opening === 'retrying') backoff.run.mockImplementationOnce(edit);
    const open = vi.fn(async (options: Parameters<SolverModules['M1']['open']>[0]): Promise<MathAgentSession> => {
      if (open.mock.calls.length === 1) {
        if (opening === 'retrying') throw new Error('fetch failed');
        if (change === 'exhaust-route') state.cooperation!.groups![0].turns = 1;
        else await edit();
        if (opening === 'failed') throw new Error('fetch failed');
      }
      return { threadId: `fixture-thread-${open.mock.calls.length}`, close, interrupt: vi.fn(async () => {}),
        run: async message => {
          const action = JSON.parse(message) as CooperativeAction;
          runs.push(action);
          fs.writeFileSync(path.join(options.workspace, 'RESEARCH.md'), 'A concrete advisory finding for the current route.\n');
          return 'completed';
        } };
    });
    const modules: SolverModules = { ...directSolverModules,
      M1: { ...directSolverModules.M1, open },
      M2: { ...directSolverModules.M2,
        check: async () => { throw new Error('fixture_unexpected_proof_check'); },
        checkTask: async () => { throw new Error('fixture_unexpected_task_check'); } },
      M3: { ...directSolverModules.M3, retry },
      M4: { ...directSolverModules.M4, build: (_problem, _state, access) => ({
        instructions: 'Local fixture.', message: JSON.stringify(access.assignment),
        scope: 'original-problem-and-allowed-library', sources: { problemReceiptDigest: problem.receiptDigest },
      }) },
    };

    await expect(runResearchWorkers({ state, workers, modules, access: workerAccess(workers, directory),
      root: directory, buildFile: path.join(directory, 'build.json'), taskText: 'Prove the original targets.',
      executable: 'fixture-no-model', profile: 'fixture', signal: new AbortController().signal,
      deadline: Infinity, maxTurns: 1, maxTurnMs: Infinity, maxTotalTokens: 0,
      save: () => {}, emit: (event, details) => events.push({ event, details }),
    })).resolves.toBeUndefined();

    expect(runs).toHaveLength(1);
    expect(runs[0]).toMatchObject({ kind: 'task', task: change === 'revise'
      ? { id: 'first_investigation', revision: 1 } : { id: 'next_investigation' } });
    expect(open).toHaveBeenCalledTimes(2);
    expect(retry).toHaveBeenCalledTimes(opening === 'retrying' ? 1 : 0);
    expect(state.turns).toBe(1);
    expect(state.workers![1].turns).toBe(1);
    expect(state.cooperation!.groups![0].turns).toBe(1);
    if (change === 'exhaust-route') {
      expect(state.cooperation!.groups![1].turns).toBe(1);
      expect(events).toContainEqual({ event: 'assignment_deferred', details: {
        workerId: 'peer', reason: 'turn-admission-declined',
      } });
    }
    expect(state.cooperation!.tasks.find(node => node.task.id === (change === 'revise'
      ? 'first_investigation' : 'next_investigation'))).toMatchObject({ status: 'completed', attempts: 1 });
    expect(state.cooperation!.deliveries?.filter(delivery => delivery.kind === 'failure') ?? []).toEqual([]);
    expect(events.some(event => event.event === 'worker_failed')).toBe(false);
    expect(close).toHaveBeenCalledTimes(opening === 'opened' ? 2 : 1);
  });
});
