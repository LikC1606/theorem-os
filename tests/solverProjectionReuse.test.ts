import fs from 'node:fs';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { LOCAL_EXAMPLE_PROOF } from '../src/math/localExample';
import type { MathematicsVerifierBatchRequest, MathematicsVerifierBatchResult } from '../src/math/verifier';
import type { CooperativeResearch } from '../src/solver/cooperation';
import { checkTaskProof, TaskProofCache, trustedTaskProjectionReuse, type TaskProof } from '../src/solver/cooperativeProof';
import { commitSolverSources, git, type SolverProblem } from '../src/solver/problem';
import { taskVersion, type CooperativeTask, type TaskAssignment } from '../src/solver/tasks';
import { cooperativeResearch } from './helpers/cooperation';
import { leadWorker, localExample, solverState } from './helpers/solver';

const host = vi.hoisted(() => ({ verify: vi.fn() }));
vi.mock('../src/math/verifier', async importOriginal => ({
  ...await importOriginal<typeof import('../src/math/verifier')>(),
  checkManyFormalVerifications: host.verify, formalVerificationToolIdentity: () => 'projection-reuse-fixture-tools',
}));
vi.mock('../src/math/mathProofEnvironment', async importOriginal => ({
  ...await importOriginal<typeof import('../src/math/mathProofEnvironment')>(), resolveMathProofEnvironment: () => undefined,
}));

describe('host validation of content-equivalent task projections', () => {
  let directory: string, workspace: string, problem: SolverProblem, task: CooperativeTask, assignment: TaskAssignment;
  let cooperative: CooperativeResearch, controller: AbortController, raw: TaskProof, sourceCommit: string;
  let environment: NodeJS.ProcessEnv;
  const check = (proof: TaskProof) => (cooperative as any).check(task, assignment, workspace, sourceCommit, [], proof) as Promise<TaskProof>;

  beforeEach(async () => {
    host.verify.mockReset().mockImplementation(async (request: MathematicsVerifierBatchRequest): Promise<MathematicsVerifierBatchResult> => {
      const sessionId = 'original-projection-check';
      return { schema: 'deepscientist.mathematics.verification-batch/v1', status: 'kernel_verified',
        targetCommit: request.targetCommit!, sessionId, events: [], startedAt: 1, checkedAt: 2, durationMs: 1,
        results: request.items.map((item, index) => ({ ...item, sourceDeclarationHash: item.expectedSourceDeclarationHash,
          status: 'kernel_verified', targetCommit: request.targetCommit!, claim: 'statement',
          checkId: `check-${index + 1}`, receiptId: `original-receipt-${index}`, sessionId, checkedAt: 2,
          declarationReferences: { statement: [], proof: [] } })) as MathematicsVerifierBatchResult['results'] };
    });
    const example = localExample('host-projection-reuse-'), receipt = example.receipt;
    ({ directory, workspace, problem } = example);
    const file = path.join(receipt.projectRoot, 'Submission.lean');
    fs.writeFileSync(file, LOCAL_EXAMPLE_PROOF);
    const seedCommit = commitSolverSources(problem, workspace);
    fs.writeFileSync(file, LOCAL_EXAMPLE_PROOF.replace('theorem add_zero', 'lemma helper : True := by trivial\ntheorem add_zero'));
    const first = commitSolverSources(problem, workspace);
    task = { id: 'helper', kind: 'lemma', objective: 'Prove the current helper.', proofPath: 'Submission.lean',
      theoremName: 'Tutorial.helper', type: 'True', dependsOn: [], revision: 0 };
    assignment = { taskId: task.id, taskDigest: taskVersion(task), seedCommit, workerId: 'solver' };
    controller = new AbortController(); environment = { PATH: '/usr/bin:/bin' };
    const cache = new TaskProofCache();
    await checkTaskProof(problem, workspace, first, task, assignment, [], environment, controller.signal, Infinity, [], 'environment', cache);
    git(workspace, ['-c', 'user.name=Fixture', '-c', 'user.email=fixture@localhost', 'commit', '--allow-empty', '--no-gpg-sign', '--quiet', '-m', 'Same content, new source commit']);
    sourceCommit = git(workspace, ['rev-parse', 'HEAD']);
    raw = await checkTaskProof(problem, workspace, sourceCommit, task, assignment, [], environment, controller.signal, Infinity, [], 'environment', cache);
    expect(host.verify).toHaveBeenCalledOnce();
    expect(trustedTaskProjectionReuse(raw)).toBeDefined();
    const state = solverState(problem, workspace, { runId: 'projection-reuse-fixture', phase: 'running',
      cooperation: { canonicalCommit: seedCommit, tasks: [{ task, assignment, status: 'delivered', proof: raw, attempts: 1 }] } });
    const worker = leadWorker(problem, workspace);
    cooperative = cooperativeResearch({ state, workers: [worker], retrievalRoot: workspace,
      access: new Map([[worker.id, { environment, retrievalRoot: workspace }]]), signal: controller.signal, exclusiveCheck: operation => operation() });
  });
  afterEach(() => { controller?.abort(); vi.restoreAllMocks(); fs.rmSync(directory, { recursive: true, force: true }); });

  it('validates and pins both projections while keeping the checked receipt unchanged', async () => {
    const receipt = structuredClone(raw.verification), reuse = trustedTaskProjectionReuse(raw)!;
    const checked = await check(raw);
    expect(checked.passed).toBe(true);
    expect(checked.commit).toBe(sourceCommit);
    expect(checked.verification).toEqual(receipt);
    expect(checked.verification.targetCommit).toBe(reuse.checkedProjectionCommit);
    expect(reuse.projectionCommit).not.toBe(reuse.checkedProjectionCommit);
    expect(git(workspace, ['rev-parse', `${reuse.projectionCommit}^{tree}`])).toBe(reuse.projectionTree);
    expect(git(workspace, ['rev-parse', `${reuse.checkedProjectionCommit}^{tree}`])).toBe(reuse.projectionTree);
    expect((cooperative as any).pinned.has(reuse.projectionCommit)).toBe(true);
    expect((cooperative as any).pinned.has(reuse.checkedProjectionCommit)).toBe(true);
    expect(host.verify).toHaveBeenCalledOnce();
  });

  it.each(['clone', 'json', 'changed-map', 'removed-map', 'changed-reference'] as const)
  ('rejects %s evidence before adding host annotations', async kind => {
    if (kind === 'clone') raw = structuredClone(raw);
    else if (kind === 'json') raw = JSON.parse(JSON.stringify(raw));
    else if (kind === 'changed-map') raw.projectionReuse = { ...raw.projectionReuse!, inputDigest: 'f'.repeat(64) };
    else if (kind === 'removed-map') delete raw.projectionReuse;
    else raw.references!.sourceCommit = 'e'.repeat(40);
    expect(trustedTaskProjectionReuse(raw)).toBeUndefined();
    await expect(check(raw)).rejects.toThrow('math_task_check_identity_changed');
    expect((cooperative as any).checkedDeliveries.has(raw)).toBe(false);
    expect(host.verify).toHaveBeenCalledOnce();
  });
});
