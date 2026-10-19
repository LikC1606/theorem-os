import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { bootstrapLocalExample } from '../src/math/localExample';
import type { SolverRunState } from '../src/solver/archive';
import { CooperativeResearch } from '../src/solver/cooperation';
import { directSolverModules } from '../src/solver/modules';
import type { ResearchWorker } from '../src/solver/modules/organization';
import { git, readSolverProblem } from '../src/solver/problem';
import { parseCooperationPlan } from '../src/solver/tasks';

describe.each(['lead', 'primary', 'peer'] as const)('%s dispatch wakeups', role => {
  let directory: string, state: SolverRunState, lead: ResearchWorker, peer: ResearchWorker;
  let cooperative: CooperativeResearch, controller: AbortController;
  const budget = { maxTurns: 1, remainingMs: Infinity };
  const worker = () => role === 'peer' ? peer : lead;

  beforeEach(() => {
    directory = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'solver-dispatch-')));
    const workspace = path.join(directory, 'lead');
    const receipt = bootstrapLocalExample(workspace);
    const problem = readSolverProblem(workspace, receipt.activeProblemPath);
    const peerWorkspace = path.join(directory, 'peer');
    git(workspace, ['worktree', 'add', '--quiet', '--detach', peerWorkspace, problem.baseCommit]);
    lead = { id: 'solver', role: 'lead', worktree: workspace, ownedFiles: problem.ownedFiles };
    peer = { ...lead, id: 'peer', role: 'researcher', worktree: peerWorkspace };
    const plan = parseCooperationPlan(problem, { tasks: [
      ...problem.targets.map((target, index) => ({ id: `goal_${index}`, kind: 'goal',
        objective: `Prove ${target.theoremName}`, proofPath: target.proofPath,
        theoremName: target.theoremName, status: 'paused' })),
      { id: 'investigation', kind: 'research', objective: 'Investigate a concrete route.', ownerId: peer.id },
    ] });
    state = { schema: 'deepscientist.math.solver.v1', runId: 'dispatch-fixture', problem,
      taskDigest: 'task', buildDigest: 'build', environmentDigest: 'environment', evaluatorDigest: 'evaluation',
      model: 'fixture', effort: 'fixture', worktree: workspace, phase: 'running', turns: 1,
      cooperation: { canonicalCommit: problem.baseCommit, error: 'Reassess the saved mathematical input.',
        tasks: plan.tasks.map(task => ({ task, status: 'pending', attempts: 0 })),
        groups: plan.groups.map(group => ({ group, turns: 0 })) } };
    controller = new AbortController();
    const unexpectedModel = () => { throw new Error('fixture_models_forbidden'); };
    cooperative = new CooperativeResearch({ state, workers: [lead, peer],
      access: new Map([lead, peer].map(worker => [worker.id, { environment: {}, retrievalRoot: directory }])),
      signal: controller.signal, save: () => {}, emit: () => {},
      modules: { ...directSolverModules, M1: { ...directSolverModules.M1, open: unexpectedModel },
        M5: { ...directSolverModules.M5, primaryLed: role === 'primary' } },
      exclusiveCheck: async check => check() });
  });
  afterEach(async () => {
    await cooperative.stop();
    vi.restoreAllMocks();
    fs.rmSync(directory, { recursive: true, force: true });
  });

  it('rechecks a same-microtask turn refund without charging the assignment', async () => {
    cooperative.reserveTurn(peer);
    const next = cooperative.next(worker(), budget);
    queueMicrotask(() => {
      state.turns--;
      cooperative.settleTurn(peer);
    });
    const action = await next;
    expect(action?.kind).toBe(role === 'primary' ? 'solve' : role === 'peer' ? 'task' : 'lead');
    expect(state.turns).toBe(0);
    expect(state.cooperation!.groups!.every(group => group.turns === 0)).toBe(true);
    expect(state.cooperation!.tasks.every(node => node.attempts === 0)).toBe(true);
    expect(cooperative.started(worker(), action!)).toBe(true);
    expect(state.cooperation!.groups![0].turns).toBe(role === 'peer' ? 1 : 0);
  });

  it('stops waiting when an outstanding reservation becomes charged', async () => {
    cooperative.reserveTurn(peer);
    const next = cooperative.next(worker(), budget);
    queueMicrotask(() => cooperative.settleTurn(peer));
    await expect(next).resolves.toBeUndefined();
    expect(state.turns).toBe(1);
    expect(state.cooperation!.tasks.every(node => node.status === 'pending')).toBe(true);
  });

  it('propagates cancellation while awaiting a possible refund', async () => {
    cooperative.reserveTurn(peer);
    const next = cooperative.next(worker(), budget);
    queueMicrotask(() => controller.abort(new Error('fixture_dispatch_aborted')));
    await expect(next).rejects.toThrow('fixture_dispatch_aborted');
    expect(state.cooperation!.tasks.every(node => node.status === 'pending')).toBe(true);
  });

  it.each(['stopping', 'worker-stopped', 'lead-stopped'] as const)(
    'declines a selected action after %s before model admission', async change => {
      state.turns = 0;
      const next = cooperative.next(worker(), budget);
      const changed = Promise.resolve().then(async () => {
        if (change === 'stopping') await cooperative.stop();
        else cooperative.stopped(change === 'worker-stopped' ? worker() : lead);
      });
      const action = await next;
      await changed;
      expect(action).toBeDefined();
      expect(cooperative.started(worker(), action!)).toBe(false);
      expect(state.cooperation!.groups!.every(group => group.turns === 0)).toBe(true);
      expect(state.cooperation!.tasks.every(node => node.attempts === 0)).toBe(true);
    });

  if (role !== 'peer') it.each(['canonical-changed', 'not-ready', 'synchronizing', 'lead-stopped', 'stopping'] as const)(
    'invalidates a queued assembly after %s', async change => {
      const archive = state.cooperation!;
      for (const node of archive.tasks) if (node.task.kind === 'goal') node.status = 'integrated';
      archive.review = { commit: archive.canonicalCommit!, sourceDigest: 'fixture-source', status: 'accepted' };
      const action = await cooperative.next(lead, budget);
      expect(action?.kind).toBe('assemble');
      expect(cooperative.current(action!)).toBe(true);
      const canonical = archive.canonicalCommit;
      const goal = archive.tasks.find(node => node.task.kind === 'goal')!;
      if (change === 'canonical-changed') archive.canonicalCommit = 'a'.repeat(40);
      else if (change === 'not-ready') {
        archive.review = undefined;
        goal.status = 'pending';
      } else if (change === 'synchronizing') goal.pendingValidation = {
        id: 'fixture-validation', taskDigest: 'fixture-task', canonicalCommit: canonical!,
        environmentDigest: state.environmentDigest, problemReceiptDigest: state.problem.receiptDigest,
      };
      else if (change === 'lead-stopped') cooperative.stopped(lead);
      else await cooperative.stop();
      try { expect(cooperative.current(action!)).toBe(false); }
      finally { archive.canonicalCommit = canonical; }
    });
});
