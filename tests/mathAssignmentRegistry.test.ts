import {
  publishMathLiteBlockerBoundary,
  publishMathLiteBlockerContext,
  readMathLiteBlockerContext,
  readMathLiteBlockerHistory,
} from '../src/math/mathLiteBlockerContext';
import { readMathPlanningBlockerContext } from '../src/math/mathPlanningContext';
import { mathDigest } from '../src/math/mathRuntimeIo';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import type { MathRunBinding, RuntimeMathAssignment } from '../src/common/types/team/mathRuntimeContracts';
import { MathAssignmentRegistry } from '../src/math/mathAssignmentRegistry';
import { projectMathWorkerDeliveryToEnvelope } from '../src/math/mathWorkerDeliveryAdapter';
import {
  listProjectGitResearchTeamAssignments,
  recordProjectGitResearchTeamAssignment,
  recordProjectGitResearchTeamDelivery,
  completeProjectGitResearchTeamAssignment,
  supersedeProjectGitResearchTeamAssignment,
} from '../src/project-git';

const request = (overrides: Record<string, unknown> = {}) => ({
  idempotencyKey: 'first',
  targetSlotId: 'worker',
  kind: 'research',
  objective: 'Establish an invariant',
  acceptance: ['State and justify the invariant'],
  ...overrides,
});

describe('durable mathematics assignment ownership', () => {
  let sandbox: string;
  let workspace: string;
  let binding: MathRunBinding;
  let predecessorEnded: boolean;
  let currentCommit: string;
  const record = vi.fn(recordProjectGitResearchTeamAssignment);
  const readPath = vi.fn();
  const writePath = vi.fn();
  const grants = vi.fn(async () => ['index', 'notes']);
  const assertion = vi.fn();
  const supersede = vi.fn(({ receipt, winnerAssignmentId, reason }) => {
    return supersedeProjectGitResearchTeamAssignment({
      workspace,
      teamId: receipt.teamId,
      slotId: receipt.slotId,
      assignmentId: receipt.assignmentId,
      supersession: { winnerAssignmentId, reason },
    });
  });
  const list = () => listProjectGitResearchTeamAssignments({ workspace, teamId: 'team', strict: true });
  const create = (readAssignments = list) =>
    new MathAssignmentRegistry({
      binding,
      teamId: 'team',
      workerIds: new Set(['worker', 'worker2']),
      flockExecutable: '/usr/bin/flock',
      assertBinding: assertion,
      ports: {
        readAssignments,
        recordAssignment: record,
        currentCommit: () => currentCommit,
        assertReadPath: readPath,
        assertWritePath: writePath,
        grantArtifacts: grants,
        predecessorEnded: async () => predecessorEnded,
        supersedeAssignment: supersede,
      },
    });
  beforeEach(() => {
    sandbox = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'math-registry-')));
    workspace = path.join(sandbox, 'solver');
    fs.mkdirSync(workspace);
    fs.mkdirSync(path.join(sandbox, 'runs/run'), { recursive: true, mode: 0o700 });
    const git = spawnSync('git', ['init', workspace], { encoding: 'utf8' });
    if (git.status !== 0) throw new Error('fixture_git_init_failed');
    fs.writeFileSync(path.join(workspace, 'Shared.lean'), '-- public source');
    binding = {
      schema: 'deepscientist.math.run-binding.v2',
      runId: 'run',
      taskFile: path.join(sandbox, 'task'),
      taskHash: 'b'.repeat(64),
      workspace,
      projectRoot: workspace,
      baseCommit: 'a'.repeat(40),
      allowedWriteRoots: [workspace],
      environmentFile: path.join(sandbox, 'env'),
      environmentDigest: 'c'.repeat(64),
      leanToolchain: 'leanprover/lean4:v4.19.0',
      lakeExecutableDigest: 'd'.repeat(64),
      toolManifestDigest: 'e'.repeat(64),
      leanSourceRoots: [workspace],
      generatedSourceRoot: workspace,
      artifactStoreRoot: path.join(sandbox, 'runs/run/artifacts'),
      artifactStorePolicyDigest: 'f'.repeat(64),
      buildManifestRef: path.join(sandbox, 'build/manifest.json'),
      buildManifestDigest: 'a'.repeat(64),
      evaluatorConfigured: false,
    };
    predecessorEnded = true;
    currentCommit = 'a'.repeat(40);
    vi.clearAllMocks();
  });
  afterEach(() => fs.rmSync(sandbox, { recursive: true, force: true }));

  it('replays the same durable identity after process-local registry recreation', async () => {
    const first = await create().prepare(request());
    const replay = await create().prepare(request());
    expect(replay).toEqual(first);
    expect(record).toHaveBeenCalledTimes(1);
    expect(first.assignment).toMatchObject({
      schema: 'deepscientist.math.assignment.v2',
      request: request(),
      baseCommit: 'a'.repeat(40),
    });
  });

  it('binds research to a proof owner and replays after that owner completes', async () => {
    const owner = await create().prepare(request({ kind: 'formalize' }));
    const research = request({
      targetSlotId: 'worker2',
      objective: 'Investigate the missing bridge',
      consumerAssignmentIds: [owner.assignmentId],
    });
    const assigned = await create().prepare(research);
    const completed = () =>
      list().map((entry) =>
        entry.assignmentId === owner.assignmentId ? { ...entry, state: 'integrated' as const } : entry
      );
    expect((assigned.assignment as RuntimeMathAssignment).request.consumerAssignmentIds).toEqual([owner.assignmentId]);
    expect((await create(completed).prepare(research)).assignmentId).toBe(assigned.assignmentId);
    await expect(
      create(completed).prepare({ ...research, consumerAssignmentIds: ['changed-proof'] })
    ).rejects.toMatchObject({ issues: [{ path: 'idempotencyKey', code: 'conflict' }] });
  });

  it('accepts a blocked proof owner as the consumer of a new investigation', async () => {
    const owner = await create().prepare(request({ kind: 'formalize' }));
    recordProjectGitResearchTeamAssignment({ ...owner, workspace, state: 'accepted' });
    const deliveryId = `${owner.teamId}:${owner.slotId}:${owner.assignmentId}`;
    const envelope = projectMathWorkerDeliveryToEnvelope(
      { status: 'blocked', summary: 'Missing bridge', blockers: ['Need an invariant'], evidence: [] },
      { deliveryId, assignmentId: owner.assignmentId, targetSlotId: owner.slotId }
    );
    recordProjectGitResearchTeamDelivery({
      workspace,
      teamId: owner.teamId,
      slotId: owner.slotId,
      assignmentId: owner.assignmentId,
      result: envelope,
      leadPayloadBytes: 0,
    });
    expect(
      await create().prepare(
        request({
          targetSlotId: 'worker2',
          objective: 'Investigate the invariant',
          consumerAssignmentIds: [owner.assignmentId],
        })
      )
    ).toMatchObject({ state: 'prepared' });
  });

  it.each(['missing', 'research', 'same-slot', 'integrated', 'superseded', 'supersession', 'cancelled', 'foreign-run'])(
    'rejects a %s consumer before reserving research',
    async (invalid) => {
      const owner = await create().prepare(request({ kind: invalid === 'research' ? 'research' : 'formalize' }));
      const altered = () =>
        list().map((entry) => {
          if (entry.assignmentId !== owner.assignmentId) return entry;
          if (invalid === 'integrated' || invalid === 'superseded') return { ...entry, state: invalid } as typeof entry;
          if (invalid === 'supersession')
            return { ...entry, supersessionPending: { winnerAssignmentId: 'winner', reason: 'Replaced' } };
          if (invalid === 'cancelled')
            return {
              ...entry,
              budgetCancellation: {
                status: 'succeeded' as const,
                teamRunId: 'turn',
                requestedAt: new Date().toISOString(),
                attemptCount: 1,
              },
            };
          if (invalid === 'foreign-run')
            return { ...entry, assignment: { ...(entry.assignment as RuntimeMathAssignment), runId: 'other-run' } };
          return entry;
        });
      await expect(
        create(altered).prepare(
          request({
            targetSlotId: invalid === 'same-slot' ? 'worker' : 'worker2',
            objective: 'Investigate the missing bridge',
            consumerAssignmentIds: [invalid === 'missing' ? 'unknown' : owner.assignmentId],
          })
        )
      ).rejects.toThrow();
      expect(record).toHaveBeenCalledTimes(1);
    }
  );

  it('rejects changed canonical payload under the same idempotency key', async () => {
    await create().prepare(request());
    await expect(create().prepare(request({ acceptance: ['Changed acceptance'] }))).rejects.toMatchObject({
      issues: [{ path: 'idempotencyKey', code: 'conflict' }],
    });
    expect(record).toHaveBeenCalledTimes(1);
  });

  it('rejects an exactly normalized duplicate objective but does not impose a mathematical method', async () => {
    await create().prepare(request());
    await expect(
      create().prepare(request({ targetSlotId: 'worker2', objective: '  Establish  an\n invariant ' }))
    ).rejects.toMatchObject({ issues: [{ path: 'objective', code: 'conflict' }] });
    expect(
      await create().prepare(request({ targetSlotId: 'worker2', objective: 'Disprove a candidate invariant' }))
    ).toMatchObject({ state: 'prepared' });
  });

  it('allows the same research question on distinct frozen evidence while retaining slot ownership', async () => {
    await create().prepare(
      request({ inputs: [{ artifactRef: `math-artifact://${binding.runId}/first-evidence`, purpose: 'Current goal' }] })
    );
    const next = request({
      idempotencyKey: 'second-evidence',
      targetSlotId: 'worker2',
      inputs: [{ artifactRef: `math-artifact://${binding.runId}/second-evidence`, purpose: 'Changed hypothesis' }],
    });
    expect(await create().prepare(next)).toMatchObject({ state: 'prepared' });
    await expect(create().prepare(request({ idempotencyKey: 'third', inputs: next.inputs }))).rejects.toMatchObject({
      issues: [{ path: 'targetSlotId', code: 'conflict' }],
    });
  });

  it('rejects duplicate structured questions with different task wording without reserving another slot', async () => {
    const researchQuestion = {
      statement: 'The constraint state is finite.',
      assumptions: ['a is valid'],
      targetConnection: 'Supplies the missing recurrence bridge.',
    };
    const first = await create().prepare(request({ researchQuestion }));
    const before = list();
    await expect(
      create().prepare(
        request({
          targetSlotId: 'worker2',
          objective: 'Use alternate wording to investigate finiteness',
          researchQuestion,
        })
      )
    ).rejects.toMatchObject({ issues: [{ path: 'researchQuestion', code: 'conflict' }] });
    expect(list()).toEqual(before);
    expect((await create().prepare(request({ researchQuestion }))).assignmentId).toBe(first.assignmentId);
  });

  it.each(['evidence', 'assumptions', 'commit'])(
    'allows a structured research question with changed %s despite identical task wording',
    async (change) => {
      const researchQuestion = {
        statement: 'The constraint state is finite.',
        assumptions: ['a is valid'],
        targetConnection: 'Supplies the missing recurrence bridge.',
      };
      await create().prepare(request({ researchQuestion }));
      if (change === 'commit') currentCommit = 'b'.repeat(40);
      const next = await create().prepare(
        request({
          targetSlotId: 'worker2',
          researchQuestion:
            change === 'assumptions'
              ? { ...researchQuestion, assumptions: ['a has bounded support'] }
              : researchQuestion,
          ...(change === 'evidence'
            ? { inputs: [{ artifactRef: 'math-artifact://run/new-evidence', purpose: 'Changed evidence' }] }
            : {}),
        })
      );
      expect(next.state).toBe('prepared');
      expect(list()).toHaveLength(2);
    }
  );

  it('retains a completed provisional report for deduplication after advisory integration', async () => {
    const researchQuestion = {
      statement: 'The constraint state is finite.',
      assumptions: ['a is valid'],
      targetConnection: 'Supplies the missing recurrence bridge.',
    };
    const first = await create().prepare(request({ researchQuestion }));
    recordProjectGitResearchTeamAssignment({ ...first, workspace, state: 'accepted' });
    const deliveryId = `${first.teamId}:${first.slotId}:${first.assignmentId}`;
    const envelope = projectMathWorkerDeliveryToEnvelope(
      { status: 'completed', summary: 'The bounded investigation is complete, not a proof.', evidence: [] },
      { deliveryId, assignmentId: first.assignmentId, targetSlotId: first.slotId }
    );
    recordProjectGitResearchTeamDelivery({
      workspace,
      teamId: first.teamId,
      slotId: first.slotId,
      assignmentId: first.assignmentId,
      result: envelope,
      leadPayloadBytes: 0,
    });
    completeProjectGitResearchTeamAssignment({
      workspace,
      teamId: first.teamId,
      slotId: first.slotId,
      assignmentId: first.assignmentId,
      integration: { executionMode: 'advisory' },
    });
    await expect(
      create().prepare(
        request({ targetSlotId: 'worker2', objective: 'Repeat the already reported question', researchQuestion })
      )
    ).rejects.toMatchObject({ issues: [{ path: 'researchQuestion', code: 'conflict' }] });
    expect(list()).toHaveLength(1);
  });

  it('allows the same question and evidence through a legal blocked predecessor continuation', async () => {
    const researchQuestion = {
      statement: 'The constraint state is finite.',
      assumptions: ['a is valid'],
      targetConnection: 'Supplies the missing recurrence bridge.',
    };
    const first = await create().prepare(request({ researchQuestion }));
    recordProjectGitResearchTeamAssignment({ ...first, workspace, state: 'accepted' });
    const deliveryId = `${first.teamId}:${first.slotId}:${first.assignmentId}`;
    const envelope = projectMathWorkerDeliveryToEnvelope(
      { status: 'blocked', summary: 'The bridge remains open.', blockers: ['Missing bound'], evidence: [] },
      { deliveryId, assignmentId: first.assignmentId, targetSlotId: first.slotId }
    );
    recordProjectGitResearchTeamDelivery({
      workspace,
      teamId: first.teamId,
      slotId: first.slotId,
      assignmentId: first.assignmentId,
      result: envelope,
      leadPayloadBytes: 0,
    });
    const successor = await create().prepare(
      request({ idempotencyKey: 'resume-question', predecessorAssignmentId: first.assignmentId, researchQuestion })
    );
    expect(successor.state).toBe('prepared');
    expect((successor.assignment as RuntimeMathAssignment).scopeId).toBe(
      (first.assignment as RuntimeMathAssignment).scopeId
    );
  });

  it('freezes exact diagnostic source and refuses to associate stale errors with edited bytes', async () => {
    const source = 'theorem demo : True := by\n  fail_if_success trivial\n';
    const target = {
      targetId: 'demo',
      pathRelative: 'Main.lean',
      theoremName: 'demo',
      statementHash: 'a'.repeat(64),
      expectedSourceDeclarationHash: 'b'.repeat(64),
    };
    const receipt = await create().prepare(request({ kind: 'formalize', verificationTargets: [target] }));
    const assignment = receipt.assignment as RuntimeMathAssignment;
    const privateWorktree = path.join(sandbox, 'private-worker');
    const executionReceipt = {
      ...receipt,
      preparedGit: { branch: 'worker', baseCommit: binding.baseCommit, worktreePath: privateWorktree },
    };
    const directory = path.resolve(privateWorktree, assignment.sourceRootRelative);
    fs.mkdirSync(directory, { recursive: true });
    fs.writeFileSync(path.join(directory, 'Main.lean'), source);
    const result = {
      sourceHash: mathDigest(source),
      diagnostics: 'Main.lean:2:2: error: unsolved goals\nn : Nat\n⊢ True',
      remainingGoals: ['n : Nat\n⊢ True'],
      attempts: [{ action: 'omega', diagnostics: 'omega could not prove goal' }],
    };
    await publishMathLiteBlockerContext(binding, executionReceipt, { result }, new AbortController().signal);
    const refs = readMathLiteBlockerContext(binding, receipt);
    expect(refs).toHaveLength(1);
    const manifest = JSON.parse(fs.readFileSync(path.join(binding.artifactStoreRoot, 'manifest.v1.json'), 'utf8'));
    const entry = manifest.entries[refs[0]!.split('/').at(-1)!];
    expect(entry).toMatchObject({
      kind: 'diagnostic',
      assignmentId: receipt.assignmentId,
      sensitivity: 'solver-visible',
    });
    const evidence = JSON.parse(fs.readFileSync(path.join(binding.artifactStoreRoot, 'objects', entry.sha256), 'utf8'));
    expect(evidence).toMatchObject({
      sources: [{ path: 'Main.lean', source }],
      diagnostics: result.diagnostics,
      goals: result.remainingGoals,
      attempts: result.attempts,
    });
    fs.writeFileSync(path.join(directory, 'Main.lean'), 'theorem demo : True := by trivial');
    await publishMathLiteBlockerContext(
      binding,
      executionReceipt,
      { result: { ...result, diagnostics: 'new but stale diagnostics' } },
      new AbortController().signal
    );
    expect(readMathLiteBlockerContext(binding, receipt)).toEqual(refs);
  });

  it.each([false, true])('retains a readable proof owner boundary (large source: %s)', async (largeSource) => {
    // Run 23 attempt 14: the second proof owner delivered `blocked` and the slot then sat
    // idle for 26 minutes, because only the Lean-probe path ever published a boundary.
    const source = 'theorem demo : True := by\n  sorry\n' + (largeSource ? '-- retained helper\n'.repeat(4096) : '');
    const target = {
      targetId: 'demo',
      pathRelative: 'Main.lean',
      theoremName: 'demo',
      statementHash: 'a'.repeat(64),
      expectedSourceDeclarationHash: 'b'.repeat(64),
    };
    const receipt = await create().prepare(request({ kind: 'formalize', verificationTargets: [target] }));
    const assignment = receipt.assignment as RuntimeMathAssignment;
    const privateWorktree = path.join(sandbox, 'private-worker');
    const executionReceipt = {
      ...receipt,
      preparedGit: { branch: 'worker', baseCommit: binding.baseCommit, worktreePath: privateWorktree },
    };
    const directory = path.resolve(privateWorktree, assignment.sourceRootRelative);
    fs.mkdirSync(directory, { recursive: true });
    fs.writeFileSync(path.join(directory, 'Main.lean'), source);
    const summary = 'The gcd recurrence closes but the antichain bound does not follow at n = 3.';
    const blockers = ['Need: finite relevance set is upward closed under divisibility.', 'Excluded: induction on n.'];

    const artifactId = await publishMathLiteBlockerBoundary(
      binding,
      executionReceipt,
      { summary, blockers },
      new AbortController().signal
    );
    expect(artifactId).toMatch(/^blocker-[a-f0-9]{64}$/u);
    const refs = readMathLiteBlockerContext(binding, receipt);
    expect(refs).toEqual([`math-artifact://${binding.runId}/${artifactId}`]);
    const manifest = JSON.parse(fs.readFileSync(path.join(binding.artifactStoreRoot, 'manifest.v1.json'), 'utf8'));
    const entry = manifest.entries[artifactId];
    expect(entry).toMatchObject({ kind: 'diagnostic', assignmentId: receipt.assignmentId });
    const content = JSON.parse(fs.readFileSync(path.join(binding.artifactStoreRoot, 'objects', entry.sha256), 'utf8'));
    expect(content).toMatchObject({
      provenance: 'owner_boundary_report',
      summary,
      goals: blockers,
      sources: largeSource
        ? [{ path: 'Main.lean', sha256: mathDigest(source), bytes: Buffer.byteLength(source) }]
        : [{ path: 'Main.lean', source }],
    });
    expect(entry.bytes).toBeLessThanOrEqual(64 * 1024);
    const planning = await readMathPlanningBlockerContext({
      binding,
      target: receipt,
      receipts: list(),
      signal: new AbortController().signal,
    });
    expect(planning.text).toContain(summary);

    // A boundary with no content is never published, and never displaces the record above.
    expect(
      await publishMathLiteBlockerBoundary(
        binding,
        executionReceipt,
        { summary: '   ', blockers: [] },
        new AbortController().signal
      )
    ).toBeUndefined();
    expect(readMathLiteBlockerContext(binding, receipt)).toEqual(refs);
  });

  it('retains the mathematical handoff alongside an earlier infrastructure diagnostic', async () => {
    const source = 'theorem demo : True := by\n  fail_if_success trivial\n';
    const target = {
      targetId: 'demo',
      pathRelative: 'Main.lean',
      theoremName: 'demo',
      statementHash: 'a'.repeat(64),
      expectedSourceDeclarationHash: 'b'.repeat(64),
    };
    const receipt = await create().prepare(request({ kind: 'formalize', verificationTargets: [target] }));
    const assignment = receipt.assignment as RuntimeMathAssignment;
    const privateWorktree = path.join(sandbox, 'private-worker');
    const executionReceipt = {
      ...receipt,
      preparedGit: { branch: 'worker', baseCommit: binding.baseCommit, worktreePath: privateWorktree },
    };
    const directory = path.resolve(privateWorktree, assignment.sourceRootRelative);
    fs.mkdirSync(directory, { recursive: true });
    fs.writeFileSync(path.join(directory, 'Main.lean'), source);
    const result = {
      sourceHash: mathDigest(source),
      diagnostics: 'math_search_provider_unavailable: math_search_frozen_corpus_unavailable',
      remainingGoals: [],
    };
    await publishMathLiteBlockerContext(binding, executionReceipt, { result }, new AbortController().signal);
    const measured = readMathLiteBlockerContext(binding, receipt);
    expect(measured).toHaveLength(1);
    const report = await publishMathLiteBlockerBoundary(
      binding,
      executionReceipt,
      { summary: 'Need the finite antichain bridge under the original assumptions.' },
      new AbortController().signal
    );
    expect(report).toMatch(/^blocker-[a-f0-9]{64}$/u);
    expect(readMathLiteBlockerHistory(binding, receipt).map((entry) => entry.artifactId)).toEqual([
      report,
      measured[0]!.split('/').at(-1),
    ]);
    const planning = await readMathPlanningBlockerContext({
      binding,
      target: receipt,
      receipts: list(),
      signal: new AbortController().signal,
    });
    expect(planning.text).toContain('Need the finite antichain bridge under the original assumptions.');
    expect(planning.text).toContain('Owner-reported boundary (unverified)');
    expect(planning.text).toContain(result.diagnostics);
  });

  it('refreshes owner notes without evicting the eight measured observations', async () => {
    const target = {
      targetId: 'demo',
      pathRelative: 'Main.lean',
      theoremName: 'demo',
      statementHash: 'a'.repeat(64),
      expectedSourceDeclarationHash: 'b'.repeat(64),
    };
    const receipt = await create().prepare(request({ kind: 'formalize', verificationTargets: [target] }));
    const assignment = receipt.assignment as RuntimeMathAssignment;
    const directory = path.resolve(workspace, assignment.sourceRootRelative);
    fs.mkdirSync(directory, { recursive: true });
    const source = 'theorem demo : True := by\n  sorry\n';
    fs.writeFileSync(path.join(directory, 'Main.lean'), source);
    const signal = new AbortController().signal;
    for (let index = 0; index < 8; index++) {
      // eslint-disable-next-line no-await-in-loop -- preserve chronological diagnostic history.
      await publishMathLiteBlockerContext(
        binding,
        receipt,
        { result: { sourceHash: mathDigest(source), diagnostics: `unsolved goal ${index}` } },
        signal
      );
    }
    const probes = readMathLiteBlockerHistory(binding, receipt);
    for (let index = 0; index < 10; index++) {
      // eslint-disable-next-line no-await-in-loop -- each revision supersedes the previous owner note.
      await publishMathLiteBlockerBoundary(binding, receipt, { summary: `Revised owner gap ${index}` }, signal);
    }
    const history = readMathLiteBlockerHistory(binding, receipt);
    expect(history.filter((entry) => entry.provenance !== 'owner_boundary')).toEqual(probes);
    expect(history.filter((entry) => entry.provenance === 'owner_boundary')).toMatchObject([
      { diagnosticsExcerpt: 'Revised owner gap 9' },
    ]);
    const planning = await readMathPlanningBlockerContext({ binding, target: receipt, receipts: list(), signal });
    expect(planning.text).toContain('Revised owner gap 9');
    // Retry is idempotent, and malformed advisory history can be rebuilt from a new report.
    const artifactId = history[0]!.artifactId;
    expect(await publishMathLiteBlockerBoundary(binding, receipt, { summary: 'Revised owner gap 9' }, signal)).toBe(
      artifactId
    );
    fs.writeFileSync(
      path.join(path.dirname(binding.artifactStoreRoot), 'lite-blockers', `${mathDigest(receipt.assignmentId)}.json`),
      '{'
    );
    const repaired = await publishMathLiteBlockerBoundary(binding, receipt, { summary: 'Recovered owner gap' }, signal);
    expect(readMathLiteBlockerHistory(binding, receipt)).toMatchObject([{ artifactId: repaired }]);
  });

  it.each(['research', 'formalize'] as const)(
    'rejects a kind change when continuing a blocked %s assignment',
    async (kind) => {
      const first = await create().prepare(request({ kind }));
      recordProjectGitResearchTeamAssignment({ ...first, workspace, state: 'accepted' });
      const deliveryId = `${first.teamId}:${first.slotId}:${first.assignmentId}`;
      const envelope = projectMathWorkerDeliveryToEnvelope(
        { status: 'blocked', summary: 'Missing bridge', blockers: ['Need an invariant'], evidence: [] },
        { deliveryId, assignmentId: first.assignmentId, targetSlotId: first.slotId }
      );
      recordProjectGitResearchTeamDelivery({
        workspace,
        teamId: first.teamId,
        slotId: first.slotId,
        assignmentId: first.assignmentId,
        result: envelope,
        leadPayloadBytes: 0,
      });
      await expect(
        create().prepare(
          request({
            kind: kind === 'research' ? 'formalize' : 'research',
            idempotencyKey: 'wrong-kind',
            predecessorAssignmentId: first.assignmentId,
          })
        )
      ).rejects.toMatchObject({ issues: [{ path: 'predecessorAssignmentId', code: 'conflict' }] });
      expect(list()).toHaveLength(1);
      expect(supersede).not.toHaveBeenCalled();
      expect(
        await create().prepare(
          request({ kind, idempotencyKey: 'same-kind', predecessorAssignmentId: first.assignmentId })
        )
      ).toMatchObject({ state: 'prepared' });
    }
  );

  it('reserves shared file ownership across distinct worker requests', async () => {
    await create().prepare(request({ sharedWritePaths: ['Shared.lean'] }));
    await expect(
      create().prepare(
        request({ targetSlotId: 'worker2', objective: 'Independent goal', sharedWritePaths: ['Shared.lean'] })
      )
    ).rejects.toMatchObject({ issues: [{ path: 'sharedWritePaths', code: 'conflict' }] });
    expect(list()).toHaveLength(1);
  });

  it('allows only one concurrent reservation for a worker slot', async () => {
    const results = await Promise.allSettled([
      create().prepare(request()),
      create().prepare(request({ idempotencyKey: 'second', objective: 'Other goal' })),
    ]);
    expect(results.filter((result) => result.status === 'fulfilled')).toHaveLength(1);
    expect(list()).toHaveLength(1);
  });

  it('inherits scope through an ended predecessor without inheriting its write roots', async () => {
    const first = await create().prepare(request());
    recordProjectGitResearchTeamAssignment({ ...first, workspace, state: 'accepted' });
    completeProjectGitResearchTeamAssignment({
      workspace,
      teamId: 'team',
      slotId: 'worker',
      assignmentId: first.assignmentId,
      integration: { executionMode: 'advisory' },
    });
    const next = await create().prepare(
      request({
        idempotencyKey: 'next',
        predecessorAssignmentId: first.assignmentId,
        objective: 'Extend the invariant',
      })
    );
    const original = first.assignment as RuntimeMathAssignment;
    const successor = next.assignment as RuntimeMathAssignment;
    expect(successor.scopeId).toBe(original.scopeId);
    expect(successor.sourceRootRelative).not.toBe(original.sourceRootRelative);
    expect(successor.draftRoot).not.toBe(original.draftRoot);
  });

  it('checks an integrated predecessor before first reservation but replays its already transferred ownership', async () => {
    const first = await create().prepare(request());
    recordProjectGitResearchTeamAssignment({ ...first, workspace, state: 'accepted' });
    completeProjectGitResearchTeamAssignment({
      workspace,
      teamId: 'team',
      slotId: 'worker',
      assignmentId: first.assignmentId,
      integration: { executionMode: 'advisory' },
    });
    const successorRequest = request({
      idempotencyKey: 'integrated-successor',
      predecessorAssignmentId: first.assignmentId,
      objective: 'Extend the completed invariant',
    });
    predecessorEnded = false;
    await expect(create().prepare(successorRequest)).rejects.toMatchObject({
      issues: [{ path: 'predecessorAssignmentId', code: 'conflict' }],
    });
    expect(list()).toHaveLength(1);
    predecessorEnded = true;
    const successor = await create().prepare(successorRequest);
    recordProjectGitResearchTeamAssignment({ ...successor, workspace, state: 'accepted' });
    const accepted = list();
    // The same Core slot now executes the successor, not the retired predecessor.
    predecessorEnded = false;
    expect((await create().prepare(successorRequest)).assignmentId).toBe(successor.assignmentId);
    expect(list()).toEqual(accepted);
    await expect(create().prepare({ ...successorRequest, objective: 'Changed replay' })).rejects.toMatchObject({
      issues: [{ path: 'idempotencyKey', code: 'conflict' }],
    });
  });

  it('supersedes an accepted predecessor with a durable candidate rejection', async () => {
    const first = await create().prepare(request());
    recordProjectGitResearchTeamAssignment({ ...first, workspace, state: 'accepted' });
    recordProjectGitResearchTeamAssignment({
      ...first,
      workspace,
      state: 'accepted',
      integration: {
        executionMode: 'artifact',
        branch: 'repair-source',
        headCommit: 'a'.repeat(40),
        mergedCommit: 'b'.repeat(40),
        reverificationRequired: true,
        verification: {
          schema: 'deepscientist.math.source-verification-evidence.v1',
          disposition: 'candidate_rejected',
          targetCommit: 'b'.repeat(40),
          checkedAt: 1,
          itemIds: ['assignment:target'],
          sourceHashes: ['c'.repeat(64)],
          diagnostics: 'Lean rejected the candidate.',
        },
      },
    });
    const successor = await create().prepare(
      request({ predecessorAssignmentId: first.assignmentId, idempotencyKey: 'repair' })
    );
    expect(successor.state).toBe('prepared');
    expect(supersede).toHaveBeenCalledWith(
      expect.objectContaining({
        receipt: expect.objectContaining({ assignmentId: first.assignmentId, state: 'accepted' }),
        winnerAssignmentId: successor.assignmentId,
      })
    );
    expect(list().find((receipt) => receipt.assignmentId === first.assignmentId)).toMatchObject({
      state: 'superseded',
      integration: { reverificationRequired: true },
    });
  });

  it('does not treat a bare reverification marker as a candidate rejection', async () => {
    const first = await create().prepare(request());
    recordProjectGitResearchTeamAssignment({ ...first, workspace, state: 'accepted' });
    recordProjectGitResearchTeamAssignment({
      ...first,
      workspace,
      state: 'accepted',
      integration: {
        executionMode: 'artifact',
        branch: 'repair-source',
        headCommit: 'a'.repeat(40),
        mergedCommit: 'b'.repeat(40),
        reverificationRequired: true,
      },
    });
    await expect(
      create().prepare(request({ predecessorAssignmentId: first.assignmentId, idempotencyKey: 'pending-retry' }))
    ).rejects.toMatchObject({ issues: [{ path: 'predecessorAssignmentId', code: 'conflict' }] });
  });

  it('LITE-RELIABILITY T19: reserves one successor for a private rejected candidate without merge markers', async () => {
    const first = await create().prepare(request({ kind: 'formalize', idempotencyKey: 'rejected-a' }));
    recordProjectGitResearchTeamAssignment({ ...first, workspace, state: 'accepted' });
    recordProjectGitResearchTeamAssignment({
      ...first,
      workspace,
      state: 'accepted',
      integration: {
        executionMode: 'artifact',
        branch: 'private-a',
        headCommit: 'b'.repeat(40),
        retainedWithoutMerge: true,
        verification: {
          schema: 'deepscientist.math.source-verification-evidence.v1',
          disposition: 'candidate_rejected',
          targetCommit: 'b'.repeat(40),
          checkedAt: 1,
          itemIds: ['assignment:target'],
          sourceHashes: ['c'.repeat(64)],
          diagnostics: 'Lean rejected candidate A.',
        },
      },
    });

    const successorRequest = request({
      kind: 'formalize',
      idempotencyKey: 'repair-a',
      predecessorAssignmentId: first.assignmentId,
    });
    const successor = await create().prepare(successorRequest);
    const replay = await create().prepare(successorRequest);

    expect(replay.assignmentId).toBe(successor.assignmentId);
    expect(successor).toMatchObject({ state: 'prepared' });
    expect(supersede).toHaveBeenCalledTimes(1);
    expect(list().find((receipt) => receipt.assignmentId === first.assignmentId)).toMatchObject({
      state: 'superseded',
      supersession: { winnerAssignmentId: successor.assignmentId },
    });
    expect(list().filter((receipt) => receipt.assignment.assignmentId === successor.assignmentId)).toHaveLength(1);
  });

  it('LITE-RELIABILITY T22: reserves a successor only after the predecessor execution ends', async () => {
    const first = await create().prepare(request({ kind: 'formalize', idempotencyKey: 'interrupted-a' }));
    recordProjectGitResearchTeamAssignment({ ...first, workspace, state: 'accepted' });
    recordProjectGitResearchTeamAssignment({
      ...first,
      workspace,
      state: 'accepted',
      integration: {
        executionMode: 'artifact',
        branch: 'private-interrupted-a',
        headCommit: 'b'.repeat(40),
        retainedWithoutMerge: true,
        verification: {
          schema: 'deepscientist.math.source-verification-evidence.v1',
          disposition: 'candidate_rejected',
          targetCommit: 'b'.repeat(40),
          checkedAt: 1,
          itemIds: ['assignment:target'],
          sourceHashes: ['c'.repeat(64)],
        },
      },
    });
    predecessorEnded = false;
    const successorRequest = request({
      kind: 'formalize',
      idempotencyKey: 'resume-interrupted-a',
      predecessorAssignmentId: first.assignmentId,
    });

    await expect(create().prepare(successorRequest)).rejects.toMatchObject({
      issues: [{ path: 'predecessorAssignmentId', code: 'conflict' }],
    });
    const reserved = list().find(
      (receipt) =>
        receipt.assignment.request.predecessorAssignmentId === first.assignmentId && receipt.state === 'prepared'
    );
    expect(reserved).toBeUndefined();
    expect(supersede).not.toHaveBeenCalled();

    predecessorEnded = true;
    const resumed = await create().prepare(successorRequest);
    expect(resumed.state).toBe('prepared');
    expect(supersede).toHaveBeenCalledTimes(1);
    expect(list().filter((receipt) => receipt.assignmentId === resumed.assignmentId)).toHaveLength(1);
  });

  it('does not accept a successor while retirement failed, and replays its reservation after recovery', async () => {
    const first = await create().prepare(request({ kind: 'formalize' }));
    recordProjectGitResearchTeamAssignment({
      ...first,
      workspace,
      state: 'accepted',
      integration: {
        executionMode: 'artifact',
        branch: 'private-rejected',
        headCommit: 'b'.repeat(40),
        retainedWithoutMerge: true,
        verification: {
          schema: 'deepscientist.math.source-verification-evidence.v1',
          disposition: 'candidate_rejected',
          targetCommit: 'b'.repeat(40),
          checkedAt: 1,
          itemIds: ['assignment:target'],
          sourceHashes: ['c'.repeat(64)],
        },
      },
    });
    const successorRequest = request({
      kind: 'formalize',
      idempotencyKey: 'repair',
      predecessorAssignmentId: first.assignmentId,
    });
    supersede.mockImplementationOnce(() => {
      throw new Error('injected retirement write failure');
    });
    await expect(create().prepare(successorRequest)).rejects.toThrow('injected retirement write failure');
    const reserved = list().find((receipt) => receipt.assignmentId !== first.assignmentId)!;
    expect(() => recordProjectGitResearchTeamAssignment({ ...reserved, workspace, state: 'accepted' })).toThrow(
      'math_assignment_predecessor_not_retired'
    );
    expect(() =>
      recordProjectGitResearchTeamDelivery({
        workspace,
        teamId: reserved.teamId,
        slotId: reserved.slotId,
        assignmentId: reserved.assignmentId,
        result: { status: 'blocked' },
        leadPayloadBytes: 0,
      })
    ).toThrow('math_assignment_predecessor_not_retired');
    supersede.mockImplementationOnce(() => undefined as never);
    await expect(create().prepare(successorRequest)).rejects.toMatchObject({
      issues: [{ path: 'predecessorAssignmentId', code: 'integrity' }],
    });
    const recovered = await create().prepare(successorRequest);
    recordProjectGitResearchTeamAssignment({ ...recovered, workspace, state: 'accepted' });
    expect(list().map((receipt) => [receipt.assignmentId, receipt.state])).toEqual([
      [first.assignmentId, 'superseded'],
      [reserved.assignmentId, 'accepted'],
    ]);
  });

  it('LITE-RELIABILITY T01: round-trips a private pending verification without inventing merge state', async () => {
    const first = await create().prepare(request({ kind: 'formalize', idempotencyKey: 'private-pending' }));
    const pendingCommit = 'b'.repeat(40);
    const evidence = {
      schema: 'deepscientist.math.source-verification-evidence.v1' as const,
      disposition: 'pending' as const,
      targetCommit: pendingCommit,
      checkedAt: 1,
      itemIds: ['assignment:target'],
      sourceHashes: ['c'.repeat(64)],
      diagnostics: 'Lean process was unavailable; retry the exact private commit.',
    };
    recordProjectGitResearchTeamAssignment({
      ...first,
      workspace,
      state: 'accepted',
      integration: {
        executionMode: 'artifact',
        branch: 'repair-source',
        headCommit: pendingCommit,
        retainedWithoutMerge: true,
        verification: evidence,
      },
    });
    const read = list().find((receipt) => receipt.assignmentId === first.assignmentId);
    expect(read).toMatchObject({
      state: 'accepted',
      integration: {
        retainedWithoutMerge: true,
        headCommit: pendingCommit,
        verification: evidence,
      },
    });
    expect(read?.integration?.mergedCommit).toBeUndefined();
    expect(read?.integration?.reverificationRequired).toBeUndefined();
  });

  it('does not fork a predecessor even after its first successor becomes terminal', async () => {
    const first = await create().prepare(request());
    recordProjectGitResearchTeamAssignment({ ...first, workspace, state: 'accepted' });
    completeProjectGitResearchTeamAssignment({
      workspace,
      teamId: 'team',
      slotId: 'worker',
      assignmentId: first.assignmentId,
      integration: { executionMode: 'advisory' },
    });
    const next = await create().prepare(
      request({ idempotencyKey: 'next', predecessorAssignmentId: first.assignmentId })
    );
    recordProjectGitResearchTeamAssignment({ ...next, workspace, state: 'accepted' });
    completeProjectGitResearchTeamAssignment({
      workspace,
      teamId: 'team',
      slotId: 'worker',
      assignmentId: next.assignmentId,
      integration: { executionMode: 'advisory' },
    });
    await expect(
      create().prepare(request({ idempotencyKey: 'fork', predecessorAssignmentId: first.assignmentId }))
    ).rejects.toMatchObject({ issues: [{ path: 'predecessorAssignmentId', code: 'conflict' }] });
  });

  it('rejects a terminal WAL predecessor while its runtime still has write authority', async () => {
    const first = await create().prepare(request());
    recordProjectGitResearchTeamAssignment({ ...first, workspace, state: 'accepted' });
    completeProjectGitResearchTeamAssignment({
      workspace,
      teamId: 'team',
      slotId: 'worker',
      assignmentId: first.assignmentId,
      integration: { executionMode: 'advisory' },
    });
    predecessorEnded = false;
    await expect(
      create().prepare(request({ idempotencyKey: 'next', predecessorAssignmentId: first.assignmentId }))
    ).rejects.toMatchObject({ issues: [{ path: 'predecessorAssignmentId', code: 'conflict' }] });
  });

  it('freezes explicit artifact grants and validates input paths at the chosen base', async () => {
    const prepared = await create().prepare(
      request({
        inputs: [
          { path: 'Shared.lean', purpose: 'Existing statement' },
          { artifactRef: 'math-artifact://run/index', purpose: 'Prior notes' },
        ],
      })
    );
    expect(prepared.assignment).toMatchObject({ artifactGrants: ['index', 'notes'] });
    expect(readPath).toHaveBeenCalledWith('Shared.lean', 'a'.repeat(40));
    expect(grants).toHaveBeenCalledWith('index');
  });

  it('LITE-RELIABILITY T31: validates inputs at the predecessor execution base rather than current HEAD', async () => {
    const first = await create().prepare(request({ idempotencyKey: 'base-a' }));
    recordProjectGitResearchTeamAssignment({ ...first, workspace, state: 'accepted' });
    completeProjectGitResearchTeamAssignment({
      workspace,
      teamId: 'team',
      slotId: 'worker',
      assignmentId: first.assignmentId,
      integration: {
        executionMode: 'artifact',
        branch: 'integrated-a',
        headCommit: 'b'.repeat(40),
        mergedCommit: 'b'.repeat(40),
      },
    });
    currentCommit = 'c'.repeat(40);

    const next = await create().prepare(
      request({
        idempotencyKey: 'base-b',
        predecessorAssignmentId: first.assignmentId,
        inputs: [{ path: 'Shared.lean', purpose: 'Read from the authorized execution base' }],
      })
    );

    expect(next.assignment).toMatchObject({ baseCommit: 'b'.repeat(40) });
    expect(readPath).toHaveBeenCalledWith('Shared.lean', 'b'.repeat(40));
    expect(readPath).not.toHaveBeenCalledWith('Shared.lean', 'c'.repeat(40));
  });

  it('does not grant cross-run references or accept a model-owned identity', async () => {
    await expect(
      create().prepare(request({ inputs: [{ artifactRef: 'math-artifact://other/index', purpose: 'Private' }] }))
    ).rejects.toMatchObject({ issues: [{ path: 'inputs', code: 'unauthorized' }] });
    await expect(create().prepare(request({ scopeId: 'forged' }))).rejects.toMatchObject({
      issues: [{ path: '$', code: 'runtime_owned_field' }],
    });
    expect(record).not.toHaveBeenCalled();
  });

  it('rejects a changed frozen binding before touching the WAL', async () => {
    assertion.mockImplementationOnce(() => {
      throw new Error('binding_changed');
    });
    await expect(create().prepare(request())).rejects.toThrow('binding_changed');
    expect(record).not.toHaveBeenCalled();
  });
});
