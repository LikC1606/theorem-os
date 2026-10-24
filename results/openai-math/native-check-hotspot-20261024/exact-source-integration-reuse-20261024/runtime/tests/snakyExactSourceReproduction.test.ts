import fs from 'node:fs';
import path from 'node:path';
import { createHash } from 'node:crypto';
import { expect, it, vi } from 'vitest';
import { applyTaskChanges, checkTaskProofs, TaskProofCache, trustedTaskProjectionReuse, type TaskProof } from '../src/solver/cooperativeProof';
import { committedSource, commitSolverSources, git, withSolverWorktree, type SolverProblem } from '../src/solver/problem';
import { taskVersion, type CooperativeTask, type TaskAssignment } from '../src/solver/tasks';
import { receiptBatch } from './helpers/verifier';

const host = vi.hoisted(() => ({ verify: vi.fn(), models: vi.fn() }));
vi.mock('../src/math/verifier', async original => ({
  ...await original<typeof import('../src/math/verifier')>(), checkManyFormalVerifications: host.verify,
  formalVerificationToolIdentity: () => 'snaky-byte-reproduction-fixture-tools',
}));
vi.mock('../src/math/mathProofEnvironment', async original => ({
  ...await original<typeof import('../src/math/mathProofEnvironment')>(),
  resolveMathProofEnvironment: () => ({ identity: 'snaky-byte-reproduction-fixture-sealed-environment' }),
}));
vi.mock('../src/runtime/codexSession', () => ({ createCodexMathSession: host.models }));

const fixture = process.env.DEEPSCIENTIST_SNAKY_SOURCE_FIXTURE;
const stateFile = process.env.DEEPSCIENTIST_SNAKY_SOURCE_STATE;
const reportFile = process.env.DEEPSCIENTIST_SNAKY_SOURCE_REPORT;
const summary = (source: string) => ({ bytes: Buffer.byteLength(source), newlines: source.split('\n').length - 1,
  sha256: createHash('sha256').update(source).digest('hex') });

it.skipIf(!fixture || !stateFile || !reportFile)('reproduces the real Snaky normalization and exact complete TaskProofCache keys without invoking Lean', async () => {
  const state = JSON.parse(fs.readFileSync(stateFile!, 'utf8'));
  expect(path.resolve(fixture!)).not.toBe(path.resolve(state.worktree));
  const problem: SolverProblem = { ...state.problem, workspace: fixture!, activeProblemPath: path.join(fixture!, 'active-problem.json') };
  const node = state.cooperation.tasks.find((item: { task: CooperativeTask }) => item.task.id === 'v8_original_goal');
  const task: CooperativeTask = node.task, assignment: TaskAssignment = node.assignment, saved: TaskProof = node.proof;
  expect(taskVersion(task)).toBe(assignment.taskDigest);
  const relative = `${problem.projectRelative}/Submission.lean`;
  const seed = committedSource(fixture!, problem.baseCommit, relative);
  const assignedSeed = committedSource(fixture!, assignment.seedCommit, relative);
  const delivered = committedSource(fixture!, saved.commit, relative);
  const archivedMerge = committedSource(fixture!, '14d49c0f2bb94a8973471120f675554798126117', relative);
  expect(assignedSeed).toBe(seed);
  expect(summary(delivered).sha256).toBe('712ecd4ee1a6cf29e5dc08a07510910addc1870b4039327836646b7a0f16daab');
  expect(summary(archivedMerge).sha256).toBe('dc40df160330f9058ff0af4e85adac6ed1be8be0b2d54c7fba5f10f71450eaae');
  expect(saved.conditions ?? []).toEqual([]);

  const merge = async (exact: boolean) => withSolverWorktree(fixture!, problem.baseCommit, async checkout => {
    const started = performance.now();
    applyTaskChanges(problem, checkout, saved.changes, saved.imports, [], exact ? saved : undefined);
    const source = fs.readFileSync(path.join(checkout, relative), 'utf8');
    const commit = commitSolverSources(problem, checkout);
    return { source, commit, durationMs: performance.now() - started };
  });
  const old = await merge(false);
  expect(old.source).toBe(archivedMerge);
  const fixed = await merge(true);
  expect(fixed.source).toBe(delivered);
  expect(summary(fixed.source).newlines - summary(old.source).newlines).toBe(1101);

  host.models.mockImplementation(() => { throw new Error('fixture_real_models_forbidden'); });
  host.verify.mockImplementation(async request => receiptBatch(request, {
    sessionId: 'MOCK_ONLY_snaky_source_reproduction', receiptId: index => `MOCK_ONLY_${request.targetCommit}_${index}`,
  }));
  const cache = new TaskProofCache(), cacheChecks = vi.spyOn(cache, 'check');
  const signal = new AbortController().signal;
  const env = { PATH: '/usr/bin:/bin', DEEPSCIENTIST_MATH_ENV_FILE: path.join(fixture!, 'missing-fixture.env') };
  const lake = path.join(fixture!, problem.projectRelative, '.lake');
  fs.mkdirSync(lake, { recursive: true });
  fs.writeFileSync(path.join(lake, 'package-overrides.json'), '{"path":"/fixture/engineer/packages"}\n');
  const check = async (sourceCommit: string, delivery: boolean) => {
    const currentAssignment: TaskAssignment = delivery ? assignment : {
      taskId: task.id, taskDigest: taskVersion(task), workerId: 'solver', seedCommit: sourceCommit,
    };
    const run = async (checkout: string) => (await checkTaskProofs(problem, checkout, sourceCommit,
      [{ task, assignment: currentAssignment, retainedGoals: [], conditions: [] }], env, signal, Infinity,
      state.environmentDigest, cache))[0]!;
    return delivery ? run(fixture!) : withSolverWorktree(fixture!, sourceCommit, run);
  };
  const checkedDelivery = await check(saved.commit, true);
  expect(host.verify).toHaveBeenCalledTimes(1);
  const checkedOld = await check(old.commit, false);
  expect(host.verify).toHaveBeenCalledTimes(2);
  const checkedFixed = await check(fixed.commit, false);
  expect(host.verify).toHaveBeenCalledTimes(2);
  expect(cacheChecks).toHaveBeenCalledTimes(3);
  const keys = cacheChecks.mock.calls.map(call => call[0]);
  expect(keys[1]).not.toBe(keys[0]);
  expect(keys[2]).toBe(keys[0]);
  expect(checkedFixed.verification).toEqual(checkedDelivery.verification);
  const reuse = trustedTaskProjectionReuse(checkedFixed)!;
  expect(reuse).toBeDefined();
  expect(reuse.checkedProjectionCommit).toBe(checkedDelivery.verification.targetCommit);
  const projections = [checkedDelivery.verification.targetCommit, checkedOld.verification.targetCommit, reuse.projectionCommit]
    .map(commit => ({ commit, tree: git(fixture!, ['rev-parse', `${commit}^{tree}`]),
      ...summary(committedSource(fixture!, commit, relative)) }));
  expect(projections[0]!.tree).not.toBe(projections[1]!.tree);
  expect(projections[2]!.tree).toBe(projections[0]!.tree);
  expect(host.models).not.toHaveBeenCalled();
  fs.writeFileSync(reportFile!, JSON.stringify({ schema: 'theorem-os.snaky-exact-source-reproduction.v1',
    fixtureOnly: true, verifier: 'mock-only; actual checker/projector/cache code; no Lean or model runs',
    originalState: stateFile, isolatedRepository: fixture,
    target: task.theoremName, taskDigest: taskVersion(task), changes: saved.changes.length,
    unchangedSeed: { canonicalCommit: problem.baseCommit, assignmentSeedCommit: assignment.seedCommit, ...summary(seed) },
    delivery: { commit: saved.commit, ...summary(delivered) },
    archivedMerge: { commit: '14d49c0f2bb94a8973471120f675554798126117', ...summary(archivedMerge) },
    reproducedOldMerge: { commit: old.commit, durationMs: old.durationMs, ...summary(old.source) },
    fixedMerge: { commit: fixed.commit, durationMs: fixed.durationMs, ...summary(fixed.source) },
    projections: { delivery: projections[0], oldMerge: projections[1], fixedMerge: projections[2] },
    actualTaskProofCacheKeys: { delivery: keys[0], oldMerge: keys[1], fixedMerge: keys[2] },
    verifierInvocations: 2, callsAfterDelivery: 1, callsAfterOldMerge: 2, callsAfterFixedMerge: 2,
    fixedReceiptEqualsDelivery: true, generatedOverrideOnlyOnDelivery: true, leanInvocations: 0, modelInvocations: 0,
  }, null, 2) + '\n');
}, 240_000);
