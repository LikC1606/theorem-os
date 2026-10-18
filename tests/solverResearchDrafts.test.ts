import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { bootstrapLocalExample } from '../src/math/localExample';
import { readSolverRunState, type SolverRunState } from '../src/solver/archive';
import { CooperativeResearch } from '../src/solver/cooperation';
import { directSolverModules } from '../src/solver/modules';
import type { ResearchWorker } from '../src/solver/modules/organization';
import { commitSolverSources, git, readSolverProblem, type SolverProblem } from '../src/solver/problem';
import * as problemSource from '../src/solver/problem';
import { pendingResearchHandoffs } from '../src/solver/researchHandoffs';
import { taskVersion, type CooperativeTask } from '../src/solver/tasks';

describe('isolated advisory research drafts', () => {
  let directory: string, problem: SolverProblem, state: SolverRunState, cooperative: CooperativeResearch;
  let lead: ResearchWorker, peer: ResearchWorker, sequence: number;
  const instances: CooperativeResearch[] = [];
  const budget = { maxTurns: Infinity, remainingMs: Infinity };
  const notes = () => path.join(peer.worktree, 'RESEARCH.md');
  const source = (worker = peer) => path.join(worker.worktree, problem.projectRelative, 'Submission.lean');
  const node = (id: string) => state.cooperation!.tasks.find(node => node.task.id === id)!;
  const write = (worker: ResearchWorker, value: unknown, code = '') => fs.writeFileSync(path.join(worker.worktree, 'RESEARCH.md'),
    '```math\n' + JSON.stringify(value) + '\n```\n' + code);
  const finding = () => ({ conclusion: 'supporting', summary: 'FIRST_ROUTE_FINDING',
    leanChecks: [{ status: 'passed', path: 'RESEARCH.md', declarations: ['Candidate.probe'] }],
    lemmaRequests: [{ id: 'bridge', kind: 'lemma', objective: 'Prove the proposed bridge',
      theoremName: 'Candidate.bridge', type: 'True', proofPath: 'Submission.lean' }] });
  const saveFinding = () => write(peer, finding(), '```lean\nnamespace Candidate\nlemma probe : True := by trivial\nend Candidate\n```\n');
  const create = (current = state) => {
    const instance = new CooperativeResearch({ state: current, workers: [lead, peer],
      access: new Map([lead, peer].map(worker => [worker.id, { environment: {}, retrievalRoot: directory }])),
      modules: { ...directSolverModules, M2: { ...directSolverModules.M2,
        check: async () => { throw new Error('fixture_unexpected_verifier'); },
        checkTask: async () => { throw new Error('fixture_unexpected_verifier'); } } },
      signal: new AbortController().signal, save: () => {}, emit: () => {}, exclusiveCheck: async check => check() });
    instances.push(instance); return instance;
  };
  const task = async () => {
    const action = await cooperative.next(peer, budget);
    if (action?.kind !== 'task') throw new Error('fixture_expected_task');
    expect(cooperative.started(peer, action)).toBe(true);
    Object.assign(state.workers![1], { sessionRole: 'researcher', sessionTaskId: action.task.id,
      sessionTaskVersion: taskVersion(action.task), sessionGroupId: action.task.groupId ?? 'main' });
    return action;
  };
  const edit = async (statuses: Record<string, CooperativeTask['status']>) => {
    fs.appendFileSync(path.join(directory, 'edits.jsonl'), JSON.stringify({ id: `edit_${++sequence}`,
      baseVersion: state.cooperation!.planVersion,
      tasks: state.cooperation!.tasks.map(node => ({ ...node.task, status: statuses[node.task.id] ?? node.task.status })),
      groups: state.cooperation!.groups!.map(route => route.group) }) + '\n');
    await cooperative.pulse();
    expect(state.cooperation!.edits!.at(-1)!.status).toBe('applied');
  };
  const switchTask = async () => {
    await edit({ first_route: 'paused', second_route: 'active' });
    const other = await task(); expect(other.task.id).toBe('second_route');
    expect(fs.readFileSync(notes(), 'utf8')).not.toContain('FIRST_ROUTE_FINDING');
    write(peer, { summary: 'SECOND_ROUTE_FINDING', conclusion: 'inconclusive' });
    await cooperative.deliver(peer, other, commitSolverSources(problem, peer.worktree));
    await edit({ first_route: 'active', second_route: 'paused' });
  };
  const restart = async () => {
    const file = path.join(directory, 'saved-state.json'); fs.writeFileSync(file, JSON.stringify(state));
    state = readSolverRunState(file); cooperative = create(); await cooperative.restore();
  };
  const advanceCanonical = async () => {
    const previous = state.cooperation!.canonicalCommit!;
    fs.writeFileSync(source(lead), fs.readFileSync(source(lead), 'utf8').replace('by sorry', 'by rfl'));
    write(lead, { tasks: state.cooperation!.tasks.map(node => node.task), groups: state.cooperation!.groups!.map(route => route.group) });
    await cooperative.deliver(lead, { kind: 'lead', seedCommit: previous, planVersion: state.cooperation!.planVersion },
      commitSolverSources(problem, lead.worktree));
  };
  const duringRestore = (commit: string, hook: () => Promise<void>) => {
    const original = problemSource.withSolverWorktree;
    let armed = true;
    vi.spyOn(problemSource, 'withSolverWorktree').mockImplementation(async <T>(worktree: string, version: string,
      run: (checkout: string) => Promise<T>): Promise<T> => {
      const selected = armed && version === commit;
      if (selected) armed = false;
      try { return await original(worktree, version, run); }
      finally { if (selected) await hook(); }
    });
  };
  beforeEach(async () => {
    sequence = 0;
    directory = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'solver-research-drafts-')));
    const workspace = path.join(directory, 'lead'), receipt = bootstrapLocalExample(workspace);
    problem = readSolverProblem(workspace, receipt.activeProblemPath);
    const peerRoot = path.join(directory, 'researcher');
    git(workspace, ['worktree', 'add', '--quiet', '--detach', peerRoot, problem.baseCommit]);
    lead = { id: 'solver', role: 'lead', worktree: workspace, ownedFiles: problem.ownedFiles };
    peer = { ...lead, id: 'researcher', role: 'researcher', worktree: peerRoot };
    state = { schema: 'deepscientist.math.solver.v1', runId: 'research-drafts-fixture', problem,
      taskDigest: 'task', buildDigest: 'build', environmentDigest: 'environment', evaluatorDigest: 'evaluation',
      model: 'fixture', effort: 'fixture', worktree: workspace, phase: 'running', turns: 0,
      workers: [lead, peer].map(worker => ({ ...worker, phase: 'running', turns: 0 })) };
    write(lead, { tasks: [
      { id: 'first_route', kind: 'research', objective: 'Investigate the first route', groupId: 'a', sharing: 'problem' },
      { id: 'second_route', kind: 'research', objective: 'Investigate the second route', groupId: 'b', status: 'paused' },
      ...problem.targets.map((target, index) => ({ id: `goal_${index + 1}`, kind: 'goal',
        objective: target.theoremName, proofPath: target.proofPath, theoremName: target.theoremName, dependsOn: ['first_route'] })),
    ], groups: ['main', 'a', 'b'].map(id => ({ id, objective: id })) });
    cooperative = create(); await cooperative.restore();
  });
  afterEach(async () => {
    for (const instance of instances.splice(0)) await instance.stop();
    vi.restoreAllMocks(); fs.rmSync(directory, { recursive: true, force: true });
  });

  it.each(['research', 'sketch'] as const)('restores a %s draft after another task and process restart', async kind => {
    node('first_route').task = { ...node('first_route').task, kind };
    const action = await task(); saveFinding();
    const commit = commitSolverSources(problem, peer.worktree);
    await cooperative.deliver(peer, action, commit, true);
    expect(node('first_route').status).toBe('pending');
    expect(state.cooperation!.researchDrafts!.first_route).toMatchObject({ commit, workerId: peer.id,
      seedCommit: action.assignment.seedCommit, taskDigest: taskVersion(action.task),
      artifacts: { scope: 'advisory-unverified', artifacts: [{ kind: 'notes-lean' }] } });
    expect(git(lead.worktree, ['rev-parse', `refs/math/${state.runId}/evidence/${commit}`])).toBe(commit);
    expect(pendingResearchHandoffs(state.cooperation!)).toEqual([]);
    expect(directSolverModules.M3.ready(state.cooperation!.tasks, state.cooperation!.groups).some(node => node.task.kind === 'goal')).toBe(false);
    await switchTask(); await restart();
    const resumed = await task(); expect(resumed.task.id).toBe('first_route');
    expect(resumed.task.kind).toBe(kind);
    expect(fs.readFileSync(notes(), 'utf8')).toContain('FIRST_ROUTE_FINDING');
    expect(fs.readFileSync(notes(), 'utf8')).not.toContain('SECOND_ROUTE_FINDING');
    expect(node('first_route').status).toBe('running');
    expect(pendingResearchHandoffs(state.cooperation!)).toEqual([]);
    await cooperative.deliver(peer, resumed, commitSolverSources(problem, peer.worktree));
    expect(node('first_route').status).toBe('completed');
    expect(state.cooperation!.deliveries!.filter(delivery => delivery.kind === 'research' && delivery.taskId === 'first_route'))
      .toMatchObject([{ summary: 'FIRST_ROUTE_FINDING', artifacts: { reportedChecks: [{ status: 'passed' }] }, lemmaRequests: [{ id: 'bridge' }] }]);
    expect(pendingResearchHandoffs(state.cooperation!)).toHaveLength(1);
    expect(state.cooperation!.tasks.filter(node => node.task.kind === 'goal').every(node => node.status === 'pending')).toBe(true);
  });

  it('keeps request failures as saved drafts without increasing mathematical stagnation', async () => {
    for (let index = 0; index < 4; index++) {
      const action = await task(); saveFinding();
      await cooperative.deliver(peer, action, commitSolverSources(problem, peer.worktree), true, 'request-failure');
      expect(node('first_route').status).toBe('pending');
      expect(state.cooperation!.researchDrafts!.first_route.artifacts.artifacts).toHaveLength(1);
      expect(state.cooperation!.researchCheckpoints?.first_route).toBeUndefined();
    }
    expect(state.cooperation!.deliveries ?? []).toEqual([]);
    expect(pendingResearchHandoffs(state.cooperation!)).toEqual([]);
    expect(node('goal_1').attempts).toBe(0);
  });

  it('scopes saved drafts to visible task versions across groups', async () => {
    const first = await task(); saveFinding();
    await cooperative.deliver(peer, first, commitSolverSources(problem, peer.worktree), true);
    await edit({ first_route: 'paused', second_route: 'active' });
    const second = await task();
    write(peer, { summary: 'SECOND_ROUTE_FINDING', conclusion: 'inconclusive' });
    await cooperative.deliver(peer, second, commitSolverSources(problem, peer.worktree), true);
    const scoped = cooperative.contextState(second, peer);
    expect(node('first_route').status).toBe('pending');
    expect(node('first_route').task.sharing).toBe('problem');
    expect(scoped.tasks.some(node => node.task.id === 'first_route')).toBe(false);
    expect(Object.keys(scoped.researchDrafts ?? {})).toEqual(['second_route']);
    expect(cooperative.contextState(first, peer).researchDrafts?.first_route).toBeDefined();
    state.cooperation!.researchDrafts!.second_route.taskDigest = 'stale-task-version';
    expect(cooperative.contextState(second, peer).researchDrafts).toEqual({});
  });

  it('preserves a newer uncommitted checkpoint in the same task workspace', async () => {
    const action = await task(); saveFinding();
    await cooperative.deliver(peer, action, commitSolverSources(problem, peer.worktree), true);
    fs.writeFileSync(notes(), 'NEWER_UNCOMMITTED_FINDING');
    await restart();
    expect((await task()).task.id).toBe('first_route');
    expect(fs.readFileSync(notes(), 'utf8')).toBe('NEWER_UNCOMMITTED_FINDING');
  });

  it.each(['legacy', 'task-version', 'assignment', 'dispatch-id', 'output-digest'] as const)('rejects %s snapshots after another responsibility', async mismatch => {
    const action = await task(); saveFinding();
    await cooperative.deliver(peer, action, commitSolverSources(problem, peer.worktree), true);
    await switchTask();
    const draft = state.cooperation!.researchDrafts!.first_route;
    if (mismatch === 'legacy') delete state.cooperation!.researchDrafts;
    else if (mismatch === 'task-version') draft.taskDigest = 'obsolete-version';
    else if (mismatch === 'assignment') draft.seedCommit = git(peer.worktree, ['rev-parse', 'HEAD']);
    else if (mismatch === 'dispatch-id') draft.assignmentId = 'obsolete-assignment';
    else draft.outputDigest = 'different-output';
    await restart();
    const resumed = await task();
    expect(resumed.assignment).not.toEqual(action.assignment);
    expect(fs.readFileSync(notes(), 'utf8')).toBe('');
    expect(node('first_route').feedback).toContain('math_research_draft_unavailable');
    await cooperative.deliver(peer, resumed, commitSolverSources(problem, peer.worktree));
    expect(node('first_route').status).not.toBe('completed');
    expect(pendingResearchHandoffs(state.cooperation!)).toEqual([]);
    expect(state.cooperation!.deliveries!.some(delivery => delivery.kind === 'research' && delivery.taskId === 'first_route')).toBe(false);
  });

  it('keeps current canonical proofs while preserving a conflicting source draft as advisory evidence', async () => {
    const action = await task(); saveFinding();
    fs.writeFileSync(source(), fs.readFileSync(source(), 'utf8').replace('by sorry', 'by exact unfinished_draft'));
    const draftCommit = commitSolverSources(problem, peer.worktree);
    await cooperative.deliver(peer, action, draftCommit, true);
    await switchTask();
    await advanceCanonical();
    const canonical = state.cooperation!.canonicalCommit!;
    const resumed = await task();
    expect(fs.readFileSync(source(), 'utf8')).toContain('by rfl');
    expect(fs.readFileSync(source(), 'utf8')).not.toContain('unfinished_draft');
    expect(fs.readFileSync(notes(), 'utf8')).toContain('FIRST_ROUTE_FINDING');
    expect(state.cooperation!.canonicalCommit).toBe(canonical);
    expect(state.cooperation!.deliveries).toContainEqual(expect.objectContaining({ kind: 'progress', status: 'advisory',
      taskId: 'first_route', commit: draftCommit, artifacts: expect.objectContaining({ scope: 'advisory-unverified' }) }));
    expect(resumed.assignment.seedCommit).not.toBe(action.assignment.seedCommit);
    expect(resumed.assignment.assignmentId).not.toBe(action.assignment.assignmentId);
    expect(node('first_route').status).toBe('running');
    expect(pendingResearchHandoffs(state.cooperation!)).toEqual([]);
  });

  it('does not restore a task paused while its snapshot is being read', async () => {
    const action = await task(); saveFinding();
    const commit = commitSolverSources(problem, peer.worktree);
    await cooperative.deliver(peer, action, commit, true);
    await switchTask();
    duringRestore(commit, async () => { await edit({ first_route: 'paused' }); state.turns = 1; });
    await expect(cooperative.next(peer, { maxTurns: 1, remainingMs: Infinity })).resolves.toBeUndefined();
    expect(node('first_route').task.status).toBe('paused');
    expect(fs.readFileSync(notes(), 'utf8')).not.toContain('FIRST_ROUTE_FINDING');
    expect(state.cooperation!.researchDrafts!.first_route.suspended).toBe(true);
    expect(pendingResearchHandoffs(state.cooperation!)).toEqual([]);
  });

  it('rejects a feasibility draft when its reviewer becomes an input owner during the snapshot read', async () => {
    node('first_route').task = { ...node('first_route').task, reviewScope: 'feasibility', dependsOn: ['goal_1'] };
    node('goal_1').task = { ...node('goal_1').task, sharing: 'problem', dependsOn: [] };
    const action = await task();
    expect(action.task.id).toBe('first_route');
    saveFinding();
    fs.writeFileSync(source(), fs.readFileSync(source(), 'utf8').replace('by sorry', 'by exact first_route_source_draft'));
    const commit = commitSolverSources(problem, peer.worktree);
    await cooperative.deliver(peer, action, commit, true);
    await switchTask();
    fs.writeFileSync(notes(), 'CURRENT_UNCOMMITTED_NOTES');
    fs.writeFileSync(source(), fs.readFileSync(source(), 'utf8').replace('by sorry', 'by exact current_uncommitted_source'));
    const currentSource = fs.readFileSync(source(), 'utf8'), head = git(peer.worktree, ['rev-parse', 'HEAD']);
    const canonical = state.cooperation!.canonicalCommit;
    const restore = vi.spyOn(cooperative as any, 'restoreResearchDraft');
    duringRestore(commit, async () => {
      node('goal_1').task = { ...node('goal_1').task, ownerId: peer.id };
      state.turns = 1;
    });

    await expect(cooperative.next(peer, { maxTurns: 1, remainingMs: Infinity })).resolves.toBeUndefined();

    expect(restore).toHaveBeenCalledTimes(1);
    await expect(restore.mock.results[0].value).resolves.toBe(false);
    expect(fs.readFileSync(notes(), 'utf8')).toBe('CURRENT_UNCOMMITTED_NOTES');
    expect(fs.readFileSync(source(), 'utf8')).toBe(currentSource);
    expect(git(peer.worktree, ['rev-parse', 'HEAD'])).toBe(head);
    expect(node('first_route').status).toBe('pending');
    expect(node('first_route').assignment).toBeUndefined();
    expect(cooperative.current(action)).toBe(false);
    expect(state.cooperation!.researchDrafts!.first_route).toMatchObject({ commit, suspended: true });
    expect(state.cooperation!.canonicalCommit).toBe(canonical);
    expect(node('goal_1').status).toBe('pending');
    expect(node('goal_1').proof).toBeUndefined();
    expect(node('goal_1').integratedCheck).toBeUndefined();
    expect(pendingResearchHandoffs(state.cooperation!)).toEqual([]);
  });

  it('uses canonical source changes that arrive while a snapshot is being read', async () => {
    const action = await task(); saveFinding();
    const commit = commitSolverSources(problem, peer.worktree);
    await cooperative.deliver(peer, action, commit, true);
    await switchTask();
    duringRestore(commit, advanceCanonical);
    const resumed = await task();
    expect(fs.readFileSync(source(), 'utf8')).toContain('by rfl');
    expect(fs.readFileSync(notes(), 'utf8')).toContain('FIRST_ROUTE_FINDING');
    expect(resumed.assignment.assignmentId).not.toBe(action.assignment.assignmentId);
    expect(node('first_route').status).toBe('running');
  });

  it('uses the current canonical proof when a snapshot read fails during canonical advancement', async () => {
    const action = await task(); saveFinding();
    const commit = commitSolverSources(problem, peer.worktree);
    await cooperative.deliver(peer, action, commit, true);
    await switchTask();
    state.cooperation!.researchDrafts!.first_route.outputDigest = 'different-output';
    duringRestore(commit, advanceCanonical);
    const resumed = await task();
    expect(state.cooperation!.canonicalCommit).not.toBe(action.assignment.canonicalCommit);
    expect(resumed.assignment.canonicalCommit).toBe(state.cooperation!.canonicalCommit);
    expect(resumed.assignment.assignmentId).not.toBe(action.assignment.assignmentId);
    expect(fs.readFileSync(source(), 'utf8')).toContain('by rfl');
    expect(fs.readFileSync(notes(), 'utf8')).toBe('');
    expect(node('first_route').status).toBe('running');
    expect(pendingResearchHandoffs(state.cooperation!)).toEqual([]);
  });

  it('restores notes after a fixed candidate review uses the same worker', async () => {
    const action = await task(); saveFinding();
    await cooperative.deliver(peer, action, commitSolverSources(problem, peer.worktree), true);
    const commit = state.cooperation!.canonicalCommit!;
    cooperative.requireReview({ commit, sourceDigest: 'fixture-source', passed: true,
      verification: { status: 'kernel_verified', results: [], targetCommit: commit } } as any);
    const review = await cooperative.next(peer, budget);
    expect(review?.kind).toBe('review');
    Object.assign(state.workers![1], { sessionRole: 'reviewer', sessionTaskId: undefined, sessionTaskVersion: undefined });
    if (review?.kind !== 'review') throw new Error('fixture_expected_review');
    cooperative.interrupted(peer, review);
    state.cooperation!.review = undefined;
    expect((await task()).task.id).toBe('first_route');
    expect(fs.readFileSync(notes(), 'utf8')).toContain('FIRST_ROUTE_FINDING');
    expect(pendingResearchHandoffs(state.cooperation!)).toEqual([]);
  });
});
