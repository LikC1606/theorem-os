import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import type { MathAgentFailureDiagnostic, MathAgentOptions, MathAgentSession } from '../src/runtime/codexSession';
import type { ModelRequestStopReason } from '../src/runtime/modelRequest';
import { canonicalMathProblemStatementPayloads } from '../src/math/contracts';
import { LEAN_EVAL_BENCHMARK_COMMIT } from '../src/math/leanEvalCatalogAdapter';
import { mathDigest } from '../src/math/mathRuntimeIo';
import { hashMathFormalSourceDeclaration } from '../src/math/leanSource';
import type { MathematicsVerifierBatchRequest, MathematicsVerifierBatchResult } from '../src/math/verifier';
import { directSolverModules } from '../src/solver/modules';
import { researchFailureDetail, researchFailureReason, recoverableResearchFailure, planResearchRetry,
  planResearchCooldown } from '../src/solver/modules/search';
import { git } from '../src/solver/problem';
import { runSolver } from '../src/solver/run';
import type { CooperativeAction } from '../src/solver/tasks';

const host = vi.hoisted(() => ({ open: vi.fn(), verify: vi.fn(), prepare: vi.fn(), delay: vi.fn(), official: vi.fn() }));
vi.mock('../src/math/mathBuildManifest', () => ({ readMathBuildManifest: vi.fn() }));
vi.mock('../src/math/leanDiagnostics', async original => ({
  ...await original<typeof import('../src/math/leanDiagnostics')>(), runLeanDiagnostics: host.prepare,
}));
vi.mock('../src/math/leanToolchainReadiness', () => ({ checkResolvedLeanToolchainReadiness: () => ({ status: 'ready' }) }));
vi.mock('../src/runtime/codexConnectivity', () => ({ checkCodexProviderConnectivity: async () => ({ status: 'reachable' }) }));
vi.mock('node:timers/promises', async original => ({
  ...await original<typeof import('node:timers/promises')>(), setTimeout: host.delay,
}));
vi.mock('../src/math/verifier', async original => ({
  ...await original<typeof import('../src/math/verifier')>(), checkManyFormalVerifications: host.verify,
  resolveMathematicsLakePackagesCache: () => undefined,
}));
vi.mock('../src/math/leanEvalBootstrap', async original => ({
  ...await original<typeof import('../src/math/leanEvalBootstrap')>(), runPersistedLeanEvalOfficialGate: host.official,
}));
vi.mock('../src/runtime/codexSession', () => ({ createCodexMathSession: host.open }));

function evidence(request: MathematicsVerifierBatchRequest): MathematicsVerifierBatchResult {
  const passed = !fs.readFileSync(path.join(request.projectRoot, 'Submission.lean'), 'utf8').includes('sorry');
  return { schema: 'deepscientist.mathematics.verification-batch/v1', status: passed ? 'kernel_verified' : 'failed',
    targetCommit: request.targetCommit!, sessionId: 'offline', events: [], startedAt: 1, checkedAt: 2, durationMs: 1,
    results: request.items.map(item => ({ ...item, status: passed ? 'kernel_verified' : 'failed', claim: 'statement',
      sourceDeclarationHash: item.expectedSourceDeclarationHash, targetCommit: request.targetCommit,
      receiptId: `offline-${request.targetCommit}-${item.theoremName}`,
      ...(!passed ? { stdoutPreview: 'Submission.lean:3:1: error: unsolved goals\n⊢ True' } : {}),
    })) as MathematicsVerifierBatchResult['results'] };
}

describe('bounded role session recovery', () => {
  let directory: string;
  let workspace: string;
  let output: string;
  let args: string[];
  const original = 'namespace Submission\ndef fixed : Nat := 2\ntheorem claim : True := by sorry\nend Submission\n';
  const partial = original.replace('theorem claim', 'lemma checkpoint : True := by trivial\ntheorem claim');
  const completed = partial.replace('by sorry', 'by exact checkpoint');
  const proof = (options: MathAgentOptions) => path.join(options.workspace, 'generated/p/Submission.lean');
  const state = () => JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
  const result = () => JSON.parse(fs.readFileSync(output, 'utf8'));
  const events = () => vi.mocked(console.log).mock.calls.map(([message]) => JSON.parse(String(message)));
  const session = (options: MathAgentOptions, run: MathAgentSession['run'], lastError?: string): MathAgentSession => ({
    threadId: options.threadId || `thread-${host.open.mock.calls.length}`, lastError,
    run, close: vi.fn().mockResolvedValue(undefined), interrupt: vi.fn().mockResolvedValue(undefined),
  });
  const recoveryClock = () => {
    let now = Date.now();
    vi.spyOn(Date, 'now').mockImplementation(() => now);
    host.delay.mockImplementation(async (milliseconds: number) => { now += milliseconds; });
    return { advance: (milliseconds: number) => { now += milliseconds; }, current: () => now };
  };
  const claim = { id: 'claim', kind: 'goal', objective: 'Prove the original claim', theoremName: 'Submission.claim' };
  const research = (options: MathAgentOptions, value: object) =>
    fs.writeFileSync(path.join(options.workspace, 'RESEARCH.md'), JSON.stringify(value));
  /** Runs two cooperative workers, recording the assignment each worktree receives. */
  const cooperate = (assignments: Map<string, CooperativeAction>) => runSolver([...args, '--workers', '2'], directory,
    { ...directSolverModules, M1: { ...directSolverModules.M1, execute: async (...input) => {
      assignments.set(input[3].worktree, input[1].assignment!);
      return directSolverModules.M1.execute(...input);
    } } });

  beforeEach(() => {
    vi.clearAllMocks();
    host.open.mockReset(); host.delay.mockReset().mockResolvedValue(undefined);
    host.verify.mockReset().mockImplementation(async request => evidence(request));
    host.prepare.mockReset().mockResolvedValue({ exitCode: 0, timedOut: false, phases: [] });
    host.official.mockReset().mockResolvedValue({ comparison: { status: 'official_verified' } });
    vi.spyOn(console, 'log').mockImplementation(() => {});
    directory = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'theoremos-role-recovery-')));
    workspace = path.join(directory, 'public'); output = path.join(directory, 'result.json');
    const project = path.join(workspace, 'generated/p');
    fs.mkdirSync(project, { recursive: true }); fs.mkdirSync(`${workspace}.source`);
    for (const file of ['Submission.lean', 'Challenge.lean']) fs.writeFileSync(path.join(project, file), original);
    fs.writeFileSync(path.join(project, 'lean-toolchain'), 'leanprover/lean4:v4.31.0');
    fs.writeFileSync(path.join(project, 'lakefile.toml'), 'name = "offline"\n');
    const payload = canonicalMathProblemStatementPayloads({ informalStatement: 'Prove the claim', formalStatement: original, assumptions: [] });
    fs.writeFileSync(path.join(workspace, 'active-problem.json'), JSON.stringify({
      schema: 'deepscientist.mathematics.lean-eval-bootstrap-receipt.v1', receiptId: 'offline', problemId: 'p',
      benchmarkCommit: LEAN_EVAL_BENCHMARK_COMMIT, catalogHash: 'a'.repeat(64), leaderboardSource: 'disabled',
      contract: { problemId: 'p', informalStatement: 'Prove the claim', formalStatement: original, assumptions: [],
        knownTraps: [], acceptanceCriteria: ['Original claim'], officialVerificationCommand: 'lake test',
        statementHash: mathDigest(payload.informal), leanStatementHash: mathDigest(payload.lean) },
      workspaceRoot: workspace, projectRoot: project, sourceProjectRoot: `${workspace}.source`,
      activeProblemPath: path.join(workspace, 'active-problem.json'), createdAt: 1,
      trustedFiles: ['Challenge.lean', 'lean-toolchain', 'lakefile.toml'], solverOwnedFiles: ['Submission.lean'],
      publicObligations: [{ name: 'Submission.claim', declarationHash: hashMathFormalSourceDeclaration(original, 'Submission.claim') }],
    }));
    git(workspace, ['init', '--quiet']); git(workspace, ['add', 'generated']);
    git(workspace, ['-c', 'user.name=Offline', '-c', 'user.email=offline@localhost', 'commit', '--no-gpg-sign', '--quiet', '-m', 'Frozen fixture']);
    fs.appendFileSync(path.join(workspace, '.git/info/exclude'), '\n/active-problem.json\n**/.lake/\n');
    const task = path.join(directory, 'task.md'), build = path.join(directory, 'build.json');
    fs.writeFileSync(task, 'Prove the original claim'); fs.writeFileSync(build, '{}');
    args = ['--workspace', workspace, '--task-file', task, '--build-manifest', build, '--output', output,
      '--workers', '1', '--max-turns', '0', '--max-run-seconds', '0', '--max-turn-seconds', '0', '--evaluator-timeout-seconds', '0'];
  });
  afterEach(() => { vi.restoreAllMocks(); fs.rmSync(directory, { recursive: true, force: true }); });

  it('logs only structured authentication metadata and stops without retrying the provider', async () => {
    host.open.mockImplementationOnce(async (options: MathAgentOptions) => ({
      ...session(options, async () => 'failed', 'private provider response'),
      lastFailureDiagnostic: { code: 'unauthorized' },
    }));
    expect(await runSolver(args, directory)).toBe(1);
    expect(host.open).toHaveBeenCalledOnce();
    expect(host.delay).not.toHaveBeenCalled();
    expect(events().filter(event => event.event === 'turn_failed')).toEqual([
      expect.objectContaining({ reason: 'math_model_authentication_failed', diagnostic: { code: 'unauthorized' } }),
    ]);
    expect(JSON.stringify(events())).not.toContain('private provider response');
    expect(result().reason).toBe('math_model_authentication_failed');
  });

  it('recovers a structured network failure even when the provider message mentions authentication', async () => {
    host.open.mockImplementationOnce(async (options: MathAgentOptions) => ({
      ...session(options, async () => 'failed', 'Invalid authentication; private provider response'),
      lastFailureDiagnostic: { code: 'responseStreamDisconnected', httpStatusCode: 503 },
    }));
    host.open.mockImplementationOnce(async (options: MathAgentOptions) => session(options, async () => {
      fs.writeFileSync(proof(options), completed);
      return 'completed';
    }));
    expect(await runSolver(args, directory)).toBe(0);
    expect(host.open).toHaveBeenCalledTimes(2);
    expect(host.delay).toHaveBeenCalledOnce();
    expect(events().filter(event => event.event === 'turn_failed')).toEqual([
      expect.objectContaining({ reason: 'math_model_request_failed',
        diagnostic: { code: 'responseStreamDisconnected', httpStatusCode: 503 } }),
    ]);
    expect(JSON.stringify(events())).not.toContain('private provider response');
    expect(host.official).toHaveBeenCalledOnce();
  });

  it('recovers first-turn context overflow below the rotation threshold with saved work and a leaner fresh prompt', async () => {
    host.open.mockImplementationOnce(async (options: MathAgentOptions) => ({
      ...session(options, async () => {
        fs.writeFileSync(proof(options), partial);
        fs.writeFileSync(path.join(options.workspace, 'RESEARCH.md'), 'The checkpoint is saved; inspect RESEARCH.md.');
        options.onUsage({ totalTokens: 12 });
        return 'failed';
      }), lastInputTokens: 1000, lastFailureDiagnostic: { code: 'contextWindowExceeded' },
    }));
    host.open.mockImplementationOnce(async (options: MathAgentOptions) => session(options, async message => {
      expect(options.threadId).toBeUndefined();
      expect(fs.readFileSync(proof(options), 'utf8')).toBe(partial);
      expect(fs.readFileSync(path.join(options.workspace, 'RESEARCH.md'), 'utf8')).toContain('checkpoint');
      expect(message).toContain('Submission.claim');
      expect(message).toContain('unsolved goals');
      fs.writeFileSync(proof(options), completed); return 'completed';
    }));
    expect(await runSolver(args, directory)).toBe(0);
    expect(host.open).toHaveBeenCalledTimes(2);
    expect(host.delay).not.toHaveBeenCalled();
    expect(state().contextOverflow).toMatchObject({ maxOptionalContextBytes: 0,
      failedFreshContextDigests: [expect.stringMatching(/^[a-f0-9]{64}$/u)] });
    expect(events().filter(event => event.event === 'worker_context_recovering')).toHaveLength(1);
    expect(host.official).toHaveBeenCalledOnce();
  });

  it('blocks repeated identical fresh overflow and preserves that guard on resume', async () => {
    host.open.mockImplementation(async (options: MathAgentOptions) => ({
      ...session(options, async () => 'failed'), lastFailureDiagnostic: { code: 'contextWindowExceeded' },
    }));
    expect(await runSolver(args, directory)).toBe(1);
    expect(result().reason).toBe('math_model_context_capacity_blocked');
    const requests = host.open.mock.calls.length;
    expect(requests).toBeGreaterThan(0); expect(requests).toBeLessThanOrEqual(3);
    expect(state().contextOverflow.failedFreshContextDigests.length).toBe(requests);
    expect(await runSolver([...args, '--resume'], directory)).toBe(1);
    expect(host.open).toHaveBeenCalledTimes(requests);
    expect(result().reason).toBe('math_model_context_capacity_blocked');
    expect(host.official).not.toHaveBeenCalled();
  });

  it('keeps peers running after a Lead context overflow with a saved valid plan', async () => {
    const assignments = new Map<string, CooperativeAction>();
    let leadOverflow = false;
    host.open.mockImplementation(async (options: MathAgentOptions) => session(options, async () => {
      const action = assignments.get(options.workspace)!;
      if (action.kind === 'lead') {
        research(options, { tasks: [claim] });
        if (!leadOverflow) { leadOverflow = true; throw new Error('contextWindowExceeded'); }
      } else if (action.kind === 'task') fs.writeFileSync(proof(options), completed);
      else if (action.kind === 'review') research(options, { commit: action.seedCommit, verdict: 'accepted' });
      else throw new Error(`unexpected action: ${action.kind}`);
      return 'completed';
    }));
    expect(await cooperate(assignments)).toBe(0);
    expect(leadOverflow).toBe(true);
    expect(events().filter(event => event.event === 'worker_failed')).toHaveLength(0);
    expect(events().filter(event => event.event === 'worker_context_recovering')).toHaveLength(1);
    expect(state().cooperation.tasks[0].status).toBe('integrated');
    expect(host.official).toHaveBeenCalledOnce();
  });

  it.each(['tool', 'network'] as const)('recovers a thrown %s failure in the same role with saved notes, proof and exact usage', async kind => {
    const detail = kind === 'tool' ? 'Error parsing function call: invalid JSON arguments' : 'stream disconnected before completion: error sending request';
    host.open.mockImplementationOnce(async (options: MathAgentOptions) => session(options, async () => {
      fs.writeFileSync(proof(options), partial);
      fs.writeFileSync(path.join(options.workspace, 'RESEARCH.md'), 'Keep the checked checkpoint lemma and finish claim.');
      options.onUsage({ totalTokens: 12 }); options.onUsage({ totalTokens: 12 });
      throw new Error('math_model_turn_failed', { cause: new Error(detail) });
    }, 'math_model_turn_failed'));
    host.open.mockImplementationOnce(async (options: MathAgentOptions) => session(options, async message => {
      expect(options.threadId).toBeUndefined(); expect(options.turnTimeoutMs).toBeUndefined();
      expect(fs.readFileSync(proof(options), 'utf8')).toBe(partial);
      expect(fs.readFileSync(path.join(options.workspace, 'RESEARCH.md'), 'utf8')).toContain('checked checkpoint');
      expect(message).toContain('unsolved goals');
      options.onUsage({ totalTokens: 7 }); options.onUsage({ totalTokens: 7 });
      fs.writeFileSync(proof(options), completed); return 'completed';
    }));
    expect(await runSolver(args, directory)).toBe(0);
    expect(host.open).toHaveBeenCalledTimes(2);
    expect(host.open.mock.calls.map(([options]) => options.workspace)).toEqual([state().worktree, state().worktree]);
    expect(state()).toMatchObject({ turns: 2, usage: { totalTokens: 19 }, usageBeforeThread: { totalTokens: 12 },
      previousThreadIds: ['thread-1'], usageAccounting: { startedTurns: 2, reportedTurns: 1, incomplete: true, pending: false } });
    expect(events().filter(event => event.event === 'worker_recovering')).toHaveLength(1);
    expect(events().filter(event => event.event === 'worker_failed')).toHaveLength(0);
    expect(host.delay).toHaveBeenCalledWith(10_000, undefined, { signal: expect.any(AbortSignal) });
    expect(host.verify).toHaveBeenCalledTimes(3); expect(host.official).toHaveBeenCalledOnce();
  });

  it('recovers a transient session startup without charging an unstarted request twice', async () => {
    host.open.mockImplementationOnce(async (options: MathAgentOptions) => {
      fs.writeFileSync(proof(options), partial);
      throw new Error('math_model_turn_failed', { cause: new Error('tool call interrupted by transport close') });
    });
    host.open.mockImplementationOnce(async (options: MathAgentOptions) => session(options, async () => {
      expect(fs.readFileSync(proof(options), 'utf8')).toBe(partial);
      options.onUsage({ totalTokens: 6 }); fs.writeFileSync(proof(options), completed); return 'completed';
    }));
    expect(await runSolver(args, directory)).toBe(0);
    expect(state()).toMatchObject({ turns: 1, dispatchCounts: { proof: 1 }, usage: { totalTokens: 6 },
      usageAccounting: { startedTurns: 1, reportedTurns: 1, incomplete: false } });
    expect(host.open).toHaveBeenCalledTimes(2); expect(host.official).toHaveBeenCalledOnce();
  });

  it('keeps reconnecting a sustained startup outage while charging only the request that starts', async () => {
    const clock = recoveryClock();
    let openings = 0;
    host.open.mockImplementation(async (options: MathAgentOptions) => {
      if (++openings <= 5) {
        fs.writeFileSync(proof(options), partial);
        throw new Error('math_codex_transport_closed:process_exit:code=9:signal=none');
      }
      return session(options, async () => {
        expect(fs.readFileSync(proof(options), 'utf8')).toBe(partial);
        options.onUsage({ totalTokens: 6 }); fs.writeFileSync(proof(options), completed); return 'completed';
      });
    });
    expect(await runSolver(args, directory)).toBe(0);
    expect(host.open).toHaveBeenCalledTimes(6);
    expect(host.delay.mock.calls.map(([ms]) => ms)).toEqual([10_000, 20_000, 40_000, 60_000, 10_000]);
    expect(state()).toMatchObject({ turns: 1, dispatchCounts: { proof: 1 }, usage: { totalTokens: 6 },
      usageAccounting: { startedTurns: 1, reportedTurns: 1, incomplete: false },
      recovery: { phase: 'recovered', reason: 'math_codex_transport_closed', cycles: 1,
        waitedMs: 60_000, recoveredAt: clock.current() } });
    expect(events().filter(event => event.event === 'worker_cooling_down')).toEqual([
      expect.objectContaining({ reason: 'math_codex_transport_closed', cycle: 1, delayMs: 60_000,
        nextRetryAt: state().recovery.nextRetryAt }),
    ]);
    expect(events().filter(event => event.event === 'worker_recovered')).toEqual([
      expect.objectContaining({ reason: 'math_codex_transport_closed', cycles: 1, waitedMs: 60_000 }),
    ]);
    expect(events().filter(event => event.event === 'worker_failed')).toHaveLength(0);
    expect(host.official).toHaveBeenCalledOnce();
  });

  it('retains the same worker and draft across two cooldown cycles of failed requests', async () => {
    const clock = recoveryClock();
    let requests = 0;
    host.open.mockImplementation(async (options: MathAgentOptions) => session(options, async message => {
      if (++requests <= 8) {
        fs.writeFileSync(proof(options), partial);
        fs.writeFileSync(path.join(options.workspace, 'RESEARCH.md'), 'Preserve the checkpoint lemma across reconnections.');
        return 'failed';
      }
      expect(fs.readFileSync(proof(options), 'utf8')).toBe(partial);
      expect(fs.readFileSync(path.join(options.workspace, 'RESEARCH.md'), 'utf8')).toContain('checkpoint lemma');
      expect(message).toContain('unsolved goals');
      fs.writeFileSync(proof(options), completed); return 'completed';
    }, 'stream disconnected before completion: error sending request'));
    expect(await runSolver(args, directory)).toBe(0);
    expect(requests).toBe(9);
    expect(new Set(host.open.mock.calls.map(([options]) => options.workspace))).toEqual(new Set([state().worktree]));
    expect(host.delay.mock.calls.map(([ms]) => ms)).toEqual([
      10_000, 20_000, 40_000, 60_000, 10_000, 20_000, 40_000, 120_000,
    ]);
    expect(state()).toMatchObject({ turns: 9, recovery: { phase: 'recovered', reason: 'math_model_request_failed',
      cycles: 2, waitedMs: 180_000, recoveredAt: clock.current() } });
    expect(events().filter(event => event.event === 'worker_cooling_down').map(event => [event.cycle, event.delayMs]))
      .toEqual([[1, 60_000], [2, 120_000]]);
    expect(events().filter(event => event.event === 'worker_recovered')).toEqual([
      expect.objectContaining({ reason: 'math_model_request_failed', cycles: 2, waitedMs: 180_000 }),
    ]);
    expect(events().filter(event => event.event === 'worker_failed')).toHaveLength(0);
    expect(host.official).toHaveBeenCalledOnce();
  });

  it('persists interrupted cooling and waits its remaining interval before opening a resumed session', async () => {
    const clock = recoveryClock();
    host.open.mockImplementation(async (options: MathAgentOptions) => {
      fs.writeFileSync(proof(options), partial);
      throw new Error('math_codex_transport_closed');
    });
    host.delay.mockImplementation(async (milliseconds: number) => {
      if (milliseconds === 60_000) {
        expect(state().recovery.phase).toBe('cooling-down');
        clock.advance(20_000); process.emit('SIGTERM');
      } else clock.advance(milliseconds);
    });
    expect(await runSolver(args, directory)).toBe(4);
    expect(host.open).toHaveBeenCalledTimes(4);
    const interrupted = state().recovery;
    expect(interrupted).toMatchObject({ phase: 'cooling-down', reason: 'math_codex_transport_closed', cycles: 1, waitedMs: 20_000 });
    expect(interrupted.recoveredAt).toBeUndefined();
    expect(state().turns).toBe(0);
    expect(host.official).not.toHaveBeenCalled();
    clock.advance(5_000);
    const delayedBeforeResume = host.delay.mock.calls.length;
    host.delay.mockImplementation(async (milliseconds: number) => {
      expect(host.open).toHaveBeenCalledTimes(4);
      clock.advance(milliseconds);
    });
    host.open.mockImplementation(async (options: MathAgentOptions) => {
      expect(clock.current()).toBe(interrupted.nextRetryAt);
      expect(host.delay.mock.calls.slice(delayedBeforeResume).map(([ms]) => ms)).toEqual([35_000]);
      return session(options, async () => {
        expect(fs.readFileSync(proof(options), 'utf8')).toBe(partial);
        fs.writeFileSync(proof(options), completed); return 'completed';
      });
    });
    expect(await runSolver([...args, '--resume'], directory)).toBe(0);
    expect(host.open).toHaveBeenCalledTimes(5);
    expect(state()).toMatchObject({ turns: 1, recovery: { phase: 'recovered', cycles: 1,
      startedAt: interrupted.startedAt, nextRetryAt: interrupted.nextRetryAt, waitedMs: 55_000, recoveredAt: interrupted.nextRetryAt } });
    expect(events().filter(event => event.event === 'worker_recovery_resumed')).toEqual([
      expect.objectContaining({ reason: 'math_codex_transport_closed', cycle: 1, delayMs: 35_000, nextRetryAt: interrupted.nextRetryAt }),
    ]);
    expect(events().filter(event => event.event === 'worker_failed')).toHaveLength(0);
    expect(host.official).toHaveBeenCalledOnce();
  });

  it.each(['turns', 'deadline'] as const)('preserves bounded startup retry behavior for a finite %s budget', kind => {
    host.open.mockRejectedValue(new Error('math_codex_transport_closed'));
    const finite = kind === 'turns' ? ['--max-turns', '10'] : ['--max-run-seconds', '3600'];
    return runSolver([...args, ...finite], directory).then(code => {
      expect(code).toBe(1);
      expect(host.open).toHaveBeenCalledTimes(4);
      expect(host.delay.mock.calls.map(([ms]) => ms)).toEqual([10_000, 20_000, 40_000]);
      expect(state().turns).toBe(0);
      expect(state().recovery).toBeUndefined();
      expect(events().filter(event => event.event === 'worker_cooling_down')).toHaveLength(0);
      expect(host.official).not.toHaveBeenCalled();
    });
  });

  it('honors incomplete token accounting before retrying a sustained network failure', async () => {
    host.open.mockImplementation(async (options: MathAgentOptions) => session(options, async () => {
      options.onUsage({ totalTokens: 5 }); fs.writeFileSync(proof(options), partial); return 'failed';
    }, 'stream disconnected before completion: error sending request'));
    expect(await runSolver([...args, '--max-total-tokens', '100'], directory)).toBe(4);
    expect(host.open).toHaveBeenCalledOnce();
    expect(host.delay).not.toHaveBeenCalled();
    expect(state().recovery).toBeUndefined();
    expect(state().tokenBudget).toMatchObject({ status: 'usage-unavailable', reportedTotalTokens: 5, usageComplete: false });
    expect(events().filter(event => event.event === 'worker_cooling_down')).toHaveLength(0);
    expect(host.official).not.toHaveBeenCalled();
  });

  it.each(['solver', 'engineer'] as const)('keeps cooperative worker %s available after a sustained startup outage', async workerId => {
    recoveryClock();
    const assignments = new Map<string, CooperativeAction>();
    let failedOpenings = 0;
    host.open.mockImplementation(async (options: MathAgentOptions) => {
      if (options.environment.DEEPSCIENTIST_MATH_WORKER_ID === workerId && ++failedOpenings <= 5)
        throw new Error('math_codex_transport_closed');
      return session(options, async () => {
        const action = assignments.get(options.workspace)!;
        if (action.kind === 'lead') research(options, { tasks: [{ ...claim, ownerId: 'engineer' }] });
        else if (action.kind === 'task') fs.writeFileSync(proof(options), completed);
        else if (action.kind === 'review') research(options, { commit: action.seedCommit, verdict: 'accepted' });
        else throw new Error(`unexpected recovery action: ${action.kind}`);
        return 'completed';
      });
    });
    expect(await cooperate(assignments)).toBe(0);
    expect(state().workers.find((worker: { id: string }) => worker.id === workerId)).toMatchObject({
      recovery: { phase: 'recovered', reason: 'math_codex_transport_closed', cycles: 1, waitedMs: 60_000 },
    });
    expect(state().workers.every((worker: { error?: string }) => !worker.error)).toBe(true);
    expect(state().cooperation.tasks[0].status).toBe('integrated');
    expect(state().cooperation.review.status).toBe('accepted');
    expect(events().filter(event => event.event === 'worker_failed')).toHaveLength(0);
    expect(events().filter(event => event.event === 'worker_cooling_down')).toEqual([
      expect.objectContaining({ workerId, cycle: 1, delayMs: 60_000 }),
    ]);
    expect(host.official).toHaveBeenCalledOnce();
  });

  it('bounds repeated tool schema failures without setting any solving deadline or discarding the draft', async () => {
    host.open.mockImplementation(async (options: MathAgentOptions) => session(options, async () => {
      fs.writeFileSync(proof(options), partial); options.onUsage({ totalTokens: 3 }); return 'failed';
    }, 'Error parsing function call: invalid JSON arguments'));
    expect(await runSolver(args, directory)).toBe(1);
    expect(host.open).toHaveBeenCalledTimes(4);
    expect(host.open.mock.calls.every(([options]) => options.threadId === undefined && options.turnTimeoutMs === undefined)).toBe(true);
    expect(host.delay.mock.calls.map(([ms]) => ms)).toEqual([10_000, 20_000, 40_000]);
    expect(state()).toMatchObject({ turns: 4, usage: { totalTokens: 12 }, error: 'math_model_tool_failed',
      usageAccounting: { startedTurns: 4, reportedTurns: 0, incomplete: true } });
    expect(fs.readFileSync(path.join(state().worktree, 'generated/p/Submission.lean'), 'utf8')).toBe(partial);
    expect(host.official).not.toHaveBeenCalled();
  });

  it.each(['Invalid authentication', 'unclassified provider failure', 'math_candidate_identity_changed'])('does not recover a hard failure: %s', async error => {
    host.open.mockImplementation(async (options: MathAgentOptions) => session(options, async () => {
      fs.writeFileSync(proof(options), partial);
      throw new Error(error, { cause: new Error(error === 'math_candidate_identity_changed' ? 'stream disconnected' : error) });
    }));
    expect(await runSolver(args, directory)).toBe(1);
    expect(host.open).toHaveBeenCalledOnce(); expect(host.delay).not.toHaveBeenCalled();
    expect(fs.readFileSync(path.join(state().worktree, 'generated/p/Submission.lean'), 'utf8')).toBe(partial);
    expect(host.official).not.toHaveBeenCalled();
  });

  it('preserves source guards even when the same failed turn reports a recoverable network error', async () => {
    host.open.mockImplementation(async (options: MathAgentOptions) => session(options, async () => {
      fs.writeFileSync(proof(options), original.replace('def fixed : Nat := 2', 'def fixed : Nat := 3'));
      return 'failed';
    }, 'stream disconnected before completion: error sending request'));
    expect(await runSolver(args, directory)).toBe(1);
    expect(host.open).toHaveBeenCalledOnce(); expect(host.delay).not.toHaveBeenCalled();
    expect(host.verify).not.toHaveBeenCalled(); expect(host.official).not.toHaveBeenCalled();
    expect(result().reason).toContain('math_original_declaration_changed');
  });

  it('keeps incomplete token accounting authoritative when a failed tool turn would otherwise retry', async () => {
    host.open.mockImplementation(async (options: MathAgentOptions) => session(options, async () => {
      options.onUsage({ totalTokens: 5 }); fs.writeFileSync(proof(options), partial); return 'failed';
    }, 'Error parsing function call: invalid JSON arguments'));
    expect(await runSolver([...args, '--max-total-tokens', '100'], directory)).toBe(4);
    expect(host.open).toHaveBeenCalledOnce(); expect(host.delay).not.toHaveBeenCalled();
    expect(state().tokenBudget).toMatchObject({ status: 'usage-unavailable', reportedTotalTokens: 5, usageComplete: false });
    expect(host.official).not.toHaveBeenCalled();
  });

  it.each(['Invalid authentication', 'unclassified provider failure'])('retains a checked task proof but stops its worker after a hard failure: %s', async error => {
    const assignments = new Map<string, CooperativeAction>();
    let proofTurns = 0;
    host.open.mockImplementation(async (options: MathAgentOptions) => session(options, async () => {
      const action = assignments.get(options.workspace)!;
      if (action.kind === 'lead') research(options, { tasks: [claim] });
      else if (action.kind === 'task') {
        proofTurns++; fs.writeFileSync(proof(options), completed); options.onUsage({ totalTokens: 11 });
        return 'failed';
      } else throw new Error('hard-failed worker must not be dispatched for review');
      options.onUsage({ totalTokens: 8 }); return 'completed';
    }, error));
    expect(await cooperate(assignments)).toBe(1);
    expect(proofTurns).toBe(1);
    expect(events().filter(event => event.event === 'task_integrated' && event.taskId === 'claim')).toHaveLength(1);
    expect(events().filter(event => event.event === 'worker_recovered')).toHaveLength(0);
    expect(state().workers.some((worker: { error?: string }) => worker.error === researchFailureReason(error))).toBe(true);
    expect(host.delay).not.toHaveBeenCalled(); expect(host.official).not.toHaveBeenCalled();
  });

  it('continues distinct typed proof checkpoints beyond the first repair without a solving limit', async () => {
    const assignments = new Map<string, CooperativeAction>();
    let proofTurns = 0;
    host.open.mockImplementation(async (options: MathAgentOptions) => session(options, async () => {
      const action = assignments.get(options.workspace)!;
      if (action.kind === 'lead') research(options, { tasks: [claim] });
      else if (action.kind === 'task') {
        proofTurns++;
        const helpers = Array.from({ length: Math.min(proofTurns, 3) }, (_, index) =>
          `lemma checkpoint_${index + 1} : True := by trivial\n`).join('');
        const draft = original.replace('theorem claim', helpers + 'theorem claim');
        fs.writeFileSync(proof(options), proofTurns <= 3 ? draft : draft.replace('by sorry', 'by exact checkpoint_3'));
        options.onUsage({ totalTokens: 11 });
        return proofTurns <= 3 ? 'checkpoint' : 'completed';
      } else if (action.kind === 'review') research(options, { commit: action.seedCommit, verdict: 'accepted' });
      else throw new Error(`unexpected checkpoint action: ${action.kind}`);
      options.onUsage({ totalTokens: 8 }); return 'completed';
    }));
    expect(await cooperate(assignments)).toBe(0);
    expect(proofTurns).toBe(4);
    expect(events().filter(event => event.event === 'turn_checkpoint')).toHaveLength(3);
    expect(state().cooperation.tasks[0].status).toBe('integrated');
    expect(state().cooperation.review.status).toBe('accepted');
    expect(host.delay).not.toHaveBeenCalled(); expect(host.official).toHaveBeenCalledOnce();
  });

  it.each(['completed', 'failed', 'checkpoint'] as const)('keeps a late assignment and its saved bytes through repeated ownership rejections on %s turns', async status => {
    const assignments = new Map<string, CooperativeAction>();
    const relative = 'generated/p/generated/p/.scratch/tmp/Bridge.lean';
    const content = 'lemma advisory_bridge : True := by trivial\n';
    const draft = original.replace('theorem claim', 'lemma checkpoint_1 : True := by trivial\nlemma checkpoint_2 : True := by trivial\ntheorem claim')
      .replace('by sorry', 'by exact checkpoint_2');
    let proofTurns = 0, first: Extract<CooperativeAction, { kind: 'task' }> | undefined;
    let before: string | undefined, thread: string | undefined;
    let priorFailures: unknown[] = [];
    host.open.mockImplementation(async (options: MathAgentOptions) => {
      const current = session(options, async message => {
        const action = assignments.get(options.workspace)!;
        if (action.kind === 'lead') research(options, { tasks: [{ ...claim, ownerId: 'engineer' }] });
        else if (action.kind === 'task') {
          proofTurns++;
          first ??= action;
          expect(action.assignment).toEqual(first.assignment);
          expect(current.threadId).toBe(thread ??= current.threadId);
          options.onUsage({ totalTokens: 3 });
          if (proofTurns <= 2) {
            const helpers = Array.from({ length: proofTurns }, (_, index) => `lemma checkpoint_${index + 1} : True := by trivial\n`).join('');
            fs.writeFileSync(proof(options), original.replace('theorem claim', helpers + 'theorem claim'));
            return 'checkpoint';
          }
          const misplaced = path.join(options.workspace, relative);
          if (proofTurns === 3) {
            priorFailures = state().cooperation.failedTaskInputs ?? [];
            fs.mkdirSync(path.dirname(misplaced), { recursive: true }); fs.writeFileSync(misplaced, content);
            fs.writeFileSync(proof(options), draft); before = git(options.workspace, ['rev-parse', 'HEAD']);
          } else {
            expect(message).toContain(`File: ${relative}\nError: math_source_outside_ownership`);
            expect(fs.readFileSync(misplaced, 'utf8')).toBe(content);
            expect(fs.readFileSync(proof(options), 'utf8')).toBe(draft);
            expect(git(options.workspace, ['rev-parse', 'HEAD'])).toBe(before);
            expect(git(options.workspace, ['diff', '--cached', '--name-only'])).toBe('');
            expect(state().cooperation.failedTaskInputs ?? []).toEqual(priorFailures);
          }
          if (proofTurns < 6) return status;
          const corrected = path.join(options.workspace, 'generated/p/.scratch/tmp/Bridge.lean');
          fs.mkdirSync(path.dirname(corrected), { recursive: true }); fs.renameSync(misplaced, corrected);
          return 'completed';
        } else if (action.kind === 'review') research(options, { commit: action.seedCommit, verdict: 'accepted' });
        else throw new Error(`unexpected ownership recovery action: ${action.kind}`);
        options.onUsage({ totalTokens: 3 }); return 'completed';
      });
      return current;
    });
    const exit = await cooperate(assignments);
    expect(exit, JSON.stringify(events().filter(event => event.event === 'worker_failed'))).toBe(0);
    expect(proofTurns).toBe(6);
    expect(events().filter(event => event.event === 'source_repair_requested')).toHaveLength(3);
    expect(events().filter(event => event.event === 'worker_failed')).toHaveLength(0);
    expect(state().cooperation.tasks[0]).toMatchObject({ status: 'integrated', attempts: 6 });
    expect(state().cooperation.tasks[0].assignment).toEqual(JSON.parse(JSON.stringify(first!.assignment)));
    expect(state().cooperation.failedTaskInputs ?? []).toEqual(priorFailures);
    expect(state().cooperation.deliveries.filter((delivery: { kind: string; summary?: string }) =>
      delivery.kind === 'failure' && delivery.summary?.includes('math_source_outside_ownership'))).toEqual([]);
    expect(host.delay).not.toHaveBeenCalled(); expect(host.official).toHaveBeenCalledOnce();
  });

  it('checks and integrates a saved proof once after a tool failure, then keeps the peer available for independent review', async () => {
    const assignments = new Map<string, CooperativeAction>();
    let proofTurns = 0;
    host.open.mockImplementation(async (options: MathAgentOptions) => session(options, async () => {
      const action = assignments.get(options.workspace)!;
      if (action.kind === 'lead') research(options, { tasks: [claim] });
      else if (action.kind === 'task') {
        proofTurns++; fs.writeFileSync(proof(options), completed);
        options.onUsage({ totalTokens: 11 });
        throw new Error('math_model_turn_failed', { cause: new Error('Error parsing function call: invalid JSON arguments') });
      } else if (action.kind === 'review') research(options, { commit: action.seedCommit, verdict: 'accepted' });
      else throw new Error(`unexpected offline action: ${action.kind}`);
      options.onUsage({ totalTokens: 8 }); return 'completed';
    }));
    expect(await cooperate(assignments)).toBe(0);
    expect(proofTurns).toBe(1);
    expect(events().filter(event => event.event === 'task_integrated' && event.taskId === 'claim')).toHaveLength(1);
    expect(events().filter(event => event.event === 'worker_recovered')).toEqual([
      expect.objectContaining({ reason: 'math_model_tool_failed', savedTaskProof: true }),
    ]);
    expect(state().cooperation.review.status).toBe('accepted');
    expect(state().cooperation.tasks[0].status).toBe('integrated');
    expect(state().workers.every((worker: { error?: string }) => !worker.error)).toBe(true);
    expect(host.official).toHaveBeenCalledOnce();
  });
});

describe('recoverable failure classification', () => {
  const localStops = ['math_total_token_limit', 'math_model_usage_unavailable', 'math_model_request_stopped',
    'math_initial_planning_limit'] as const satisfies readonly ModelRequestStopReason[];

  it.each(localStops)('keeps trusted local %s stops ahead of misleading authentication diagnostics', reason => {
    const diagnostics: MathAgentFailureDiagnostic[] = [{ code: 'unauthorized' },
      { code: 'httpConnectionFailed', httpStatusCode: 401 }, { code: 'httpConnectionFailed', httpStatusCode: 403 }];
    for (const diagnostic of diagnostics) {
      expect(researchFailureDetail(new Error('HTTP 403 Forbidden'), 'Unauthorized', diagnostic, reason)).toBe(reason);
      expect(researchFailureDetail(new Error('HTTP 403 Forbidden'), 'Unauthorized', diagnostic))
        .toBe('math_model_authentication_failed');
    }
    expect(researchFailureReason(reason)).toBe(reason);
    expect(recoverableResearchFailure(reason)).toBe(false);
    const budget = { maxTurns: Infinity, remainingMs: Infinity, aborted: false };
    expect(planResearchRetry(reason, 0, { turns: 1 } as Parameters<typeof planResearchRetry>[2], budget)).toBeUndefined();
    expect(planResearchCooldown(reason, 0, budget)).toBeUndefined();
  });

  it.each(localStops)('preserves host integrity failures over trusted local %s stops', reason => {
    expect(researchFailureDetail(new Error('math_source_outside_ownership'), 'HTTP 403 Forbidden',
      { code: 'unauthorized' }, reason)).toBe('math_source_outside_ownership');
    expect(researchFailureDetail(new Error('math_model_turn_failed', { cause: new Error('math_candidate_identity_changed') }),
      'HTTP 401 Unauthorized', { code: 'httpConnectionFailed', httpStatusCode: 401 }, reason))
      .toBe('math_candidate_identity_changed');
  });

  it.each(localStops)('does not infer a local stop from %s embedded in provider text', reason => {
    const message = `HTTP 403 Forbidden; provider response mentions ${reason}`;
    expect(researchFailureReason(message)).toBe('math_model_authentication_failed');
    expect(researchFailureDetail(new Error(message), undefined, { code: 'unauthorized' }))
      .toBe('math_model_authentication_failed');
    expect(researchFailureReason(`Provider response mentions ${reason}`)).toBe('math_model_turn_failed');
  });

  it.each(['Request failed after 401 retries', 'Request failed after 403 retries', 'Forbidden tool call',
    'Authentication notes were included in the prompt'])('does not infer an authentication failure from unrelated text: %s', message => {
    expect(researchFailureReason(message)).toBe('math_model_turn_failed');
  });

  it.each(['Invalid authentication', 'Authentication failed', 'Authentication required', 'Unauthenticated',
    'Unauthorized', 'Invalid API key', 'Expired access token', 'HTTP 401', 'HTTP status: 403',
    'unexpected status 401', 'status code: 403', '401 Unauthorized', '403 Forbidden'])('retains explicit authentication failures: %s', message => {
    expect(researchFailureReason(message)).toBe('math_model_authentication_failed');
    expect(recoverableResearchFailure(message)).toBe(false);
  });

  it.each([
    [{ code: 'unauthorized' }, 'math_model_authentication_failed'],
    [{ code: 'httpConnectionFailed', httpStatusCode: 401 }, 'math_model_authentication_failed'],
    [{ code: 'httpConnectionFailed', httpStatusCode: 403 }, 'math_model_authentication_failed'],
    [{ code: 'httpConnectionFailed', httpStatusCode: 429 }, 'math_model_concurrency_limit'],
    [{ code: 'rateLimitExceeded' }, 'math_model_concurrency_limit'],
    [{ code: 'usageLimitExceeded' }, 'math_model_concurrency_limit'],
    [{ code: 'responseTooManyFailedAttempts', httpStatusCode: 408 }, 'math_model_request_timeout'],
    [{ code: 'responseStreamDisconnected', httpStatusCode: 503 }, 'math_model_request_failed'],
    [{ code: 'serverOverloaded' }, 'math_model_request_failed'],
    [{ code: 'httpConnectionFailed', httpStatusCode: 400 }, 'math_model_turn_failed'],
    [{ code: 'contextWindowExceeded' }, 'math_model_context_window_exceeded'],
    [{ code: 'sandboxError' }, 'math_model_turn_failed'],
  ] as const)('uses structured provider metadata before arbitrary message text: %j', (diagnostic, expected) => {
    const error = 'Invalid authentication; stream disconnected; rate limit';
    expect(researchFailureReason(error, diagnostic as MathAgentFailureDiagnostic)).toBe(expected);
    expect(researchFailureDetail(new Error('math_model_turn_failed'), error, diagnostic as MathAgentFailureDiagnostic)).toBe(expected);
  });

  it('uses a concrete cause or same-turn session error without guessing from a generic failure', () => {
    const tool = 'Error parsing function call: invalid JSON arguments';
    expect(researchFailureDetail(new Error('math_model_turn_failed', { cause: new Error(tool) }))).toBe(tool);
    expect(researchFailureDetail(new Error('math_model_turn_failed'), 'stream disconnected')).toBe('stream disconnected');
    expect(researchFailureReason(tool)).toBe('math_model_tool_failed');
    expect(recoverableResearchFailure('math_model_turn_failed')).toBe(false);
    expect(recoverableResearchFailure('SyntaxError in a Lean source transformation')).toBe(false);
    expect(recoverableResearchFailure('Cannot find trusted tool for COMPARATOR_BIN')).toBe(false);
    expect(researchFailureDetail(new Error('math_source_outside_ownership', { cause: new Error('stream disconnected') })))
      .toBe('math_source_outside_ownership');
    expect(researchFailureReason('math_source_outside_ownership', { code: 'unauthorized' })).toBe('math_source_outside_ownership');
    expect(researchFailureDetail(new Error('math_source_outside_ownership'), 'Invalid authentication',
      { code: 'responseStreamDisconnected' })).toBe('math_source_outside_ownership');
    expect(researchFailureDetail(new Error('math_model_turn_failed', { cause: new Error('math_source_outside_ownership') }),
      'Invalid authentication', { code: 'unauthorized' })).toBe('math_source_outside_ownership');
    expect(researchFailureReason('Invalid authentication', { code: 'other' })).toBe('math_model_authentication_failed');
    const wrappedAuthentication = researchFailureDetail(new Error('stream disconnected', { cause: new Error('HTTP 401 Unauthorized') }));
    expect(researchFailureReason(wrappedAuthentication)).toBe('math_model_authentication_failed');
    expect(recoverableResearchFailure(wrappedAuthentication)).toBe(false);
  });

  it('enforces the recovery count and existing budgets while permitting unlimited total solving time', () => {
    const run = { turns: 5 } as Parameters<typeof planResearchRetry>[2];
    const unlimited = { maxTurns: Infinity, remainingMs: Infinity, aborted: false };
    expect(planResearchRetry('math_model_tool_failed', 2, run, unlimited)).toEqual({ attempt: 3, delayMs: 40_000, reason: 'math_model_tool_failed' });
    expect(planResearchRetry('math_model_tool_failed', 3, run, unlimited)).toBeUndefined();
    expect(planResearchRetry('math_model_tool_failed', 0, run, { ...unlimited, maxTurns: 5 })).toBeUndefined();
    expect(planResearchRetry('math_model_tool_failed', 0, run, { ...unlimited, aborted: true })).toBeUndefined();
    expect(planResearchRetry('math_source_outside_ownership', 0, run, unlimited)).toBeUndefined();
  });

  it.each(['math_model_concurrency_limit', 'math_model_request_failed', 'math_model_request_timeout',
    'math_codex_transport_closed'])('cools a sustained %s outage with capped exponential intervals', reason => {
    const unlimited = { maxTurns: Infinity, remainingMs: Infinity, aborted: false };
    expect([0, 1, 2, 3, 4, 100].map(cycles => planResearchCooldown(reason, cycles, unlimited))).toEqual(
      [60_000, 120_000, 240_000, 300_000, 300_000, 300_000].map((delayMs, index) => ({
        cycle: [1, 2, 3, 4, 5, 101][index], delayMs, reason,
      })));
  });

  it('keeps finite budgets, cancellation, tool errors and hard failures outside continuous cooling', () => {
    const unlimited = { maxTurns: Infinity, remainingMs: Infinity, aborted: false };
    for (const budget of [{ ...unlimited, maxTurns: 10 }, { ...unlimited, remainingMs: 600_000 },
      { ...unlimited, remainingMs: 0 }, { ...unlimited, aborted: true }])
      expect(planResearchCooldown('math_codex_transport_closed', 0, budget)).toBeUndefined();
    for (const reason of ['math_model_tool_failed', 'math_model_authentication_failed', 'math_candidate_identity_changed',
      'math_source_outside_ownership', 'math_model_turn_failed'])
      expect(planResearchCooldown(reason, 0, unlimited)).toBeUndefined();
  });
});
