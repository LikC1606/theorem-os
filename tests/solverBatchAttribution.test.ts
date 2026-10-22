import fs from 'node:fs';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import type { MathematicsVerifierBatchRequest, MathematicsVerifierBatchResult } from '../src/math/verifier';
import { checkTaskProofs, isAttributedTaskProof } from '../src/solver/cooperativeProof';
import { attributeProofEvidence, proofReceiptsMatch } from '../src/solver/modules/evidence';
import { commitSolverSources, type SolverProblem } from '../src/solver/problem';
import { hasDeterministicLeanFailure } from '../src/solver/proofReuse';
import { taskVersion, type CooperativeTask } from '../src/solver/tasks';
import { localExample } from './helpers/solver';
import { failedBatch, receiptBatch } from './helpers/verifier';

const host = vi.hoisted(() => ({ verify: vi.fn() }));
vi.mock('../src/math/verifier', async importOriginal => ({
  ...await importOriginal<typeof import('../src/math/verifier')>(), checkManyFormalVerifications: host.verify,
}));

const request: MathematicsVerifierBatchRequest & { targetCommit: string } = {
  projectRoot: '/unused', targetCommit: 'fixture-commit',
  items: ['first', 'second'].map(name => ({ proofPath: 'Submission.lean', theoremName: `Tutorial.${name}`,
    statementHash: `task-${name}`, leanStatementHash: `task-${name}`, expectedSourceDeclarationHash: `source-${name}`, claim: 'statement' })),
};

const verified = (input: MathematicsVerifierBatchRequest) =>
  receiptBatch(input, { sessionId: 'batch-fixture', receiptId: index => `receipt-${input.targetCommit}-${index}` });
const rejected = (input: MathematicsVerifierBatchRequest, indices = [0, 1]) => failedBatch(verified(input),
  { stdoutPreview: () => 'Submission.lean:4:1: error: unsolved goals', goalsRemaining: 1, selected: (_, index) => indices.includes(index) });

const attribute = (batch: MathematicsVerifierBatchResult) => attributeProofEvidence(batch, request.targetCommit, request.items);

describe('per-target batch receipt attribution', () => {
  it.each(['sorry', 'admit', 'explicit-axiom', 'unsupported-axiom'] as const)
  ('retains a precisely bound %s source rejection without requiring a Lean process error', kind => {
    const batch = verified(request);
    batch.status = 'failed';
    for (const result of batch.results) {
      result.status = 'failed';
      if (kind === 'sorry' || kind === 'admit') {
        result.error = 'Proof source contains sorry or admit.';
        if (kind === 'sorry') result.sorryCount = 1; else result.admitCount = 1;
      } else {
        result.axioms = ['Unproved.assumption'];
        result.error = kind === 'explicit-axiom' ? 'Proof source declares explicit axioms: Unproved.assumption.' :
          'Theorem depends on non-foundational Lean axioms: Unproved.assumption.';
      }
    }
    expect(attribute(batch).map(check => [check.passed, check.attributable])).toEqual([[false, true], [false, true]]);
    batch.results[0]!.targetCommit = 'wrong-commit';
    expect(() => attribute(batch)).toThrow('math_task_check_identity_changed');
  });

  it.each(['missing-count', 'unrelated-error', 'foundational-axiom'] as const)
  ('does not turn %s metadata into an attributable source rejection', kind => {
    const batch = verified(request);
    batch.status = 'failed';
    for (const result of batch.results) {
      result.status = 'failed';
      result.error = kind === 'unrelated-error' ? 'Verifier transport unavailable.' :
        kind === 'foundational-axiom' ? 'Theorem depends on non-foundational Lean axioms: propext.' :
          'Proof source contains sorry or admit.';
      if (kind === 'unrelated-error') result.sorryCount = 1;
      if (kind === 'foundational-axiom') result.axioms = ['propext'];
    }
    expect(attribute(batch).map(check => check.attributable)).toEqual([false, false]);
  });

  it('does not interpret a successfully checked declaration name as an interrupted invocation', () => {
    const batch = verified(request);
    batch.results[0]!.stdoutPreview = 'Checked theorem timeout; all goals closed.';
    expect(attribute(batch).map(check => check.passed)).toEqual([true, true]);
  });

  it('retains a successful target and a deterministic failure without rewriting their receipts', () => {
    const batch = rejected(request, [1]), before = JSON.stringify(batch);
    const checks = attribute(batch);
    expect(checks.map(check => ({ passed: check.passed, attributable: check.attributable, status: check.verification.status })))
      .toEqual([{ passed: true, attributable: true, status: 'kernel_verified' }, { passed: false, attributable: true, status: 'failed' }]);
    expect(proofReceiptsMatch(checks[0]!.verification, request.targetCommit, [request.items[0]!])).toBe(true);
    expect(hasDeterministicLeanFailure(checks[1]!.verification)).toBe(true);
    for (const [index, check] of checks.entries()) {
      expect(check.verification.results).toEqual([batch.results[index]]);
      expect(check.verification.results[0]).toBe(batch.results[index]);
      expect(check.verification).toMatchObject({ sessionId: batch.sessionId, startedAt: 1, checkedAt: 2, durationMs: 1 });
    }
    expect(JSON.stringify(batch)).toBe(before);
  });

  it('attributes a shared-source compile failure to both targets', () => {
    const checks = attribute(rejected(request));
    expect(checks.map(check => check.attributable)).toEqual([true, true]);
    expect(checks.map(check => check.passed)).toEqual([false, false]);
    expect(checks.every(check => hasDeterministicLeanFailure(check.verification))).toBe(true);
  });

  it.each(['timeout', 'deadline', 'abort', 'interrupted'])
  ('keeps Lean errors mentioning %s attributable in raw and JSON diagnostics', word => {
    for (const stdoutPreview of [
      `Submission.lean:4:1: error(lean.unknownIdentifier): Unknown identifier ${word}`,
      JSON.stringify({ severity: 'error', fileName: 'Submission.lean', pos: { line: 4, column: 0 },
        data: `Unknown identifier ${word}` }),
    ]) {
      const batch = rejected(request, [1]);
      batch.results[0]!.stdoutPreview = `Checked theorem ${word}; all goals closed.`;
      batch.results[1]!.stdoutPreview = stdoutPreview;
      expect(hasDeterministicLeanFailure(batch)).toBe(true);
      expect(attribute(batch).map(check => [check.passed, check.attributable]))
        .toEqual([[true, true], [false, true]]);
    }
  });

  it.each(['stdoutPreview', 'stderrPreview'] as const)
  ('attributes coded Lean diagnostics in %s without changing rejection receipts', channel => {
    const batch = rejected(request);
    for (const result of batch.results) {
      delete result.stdoutPreview;
      result[channel] = 'Projection.lean:380:8: error(lean.unknownIdentifier): Unknown identifier terminal_unique_of_prod_gt_one';
    }
    const before = JSON.stringify(batch), checks = attribute(batch);
    expect(checks.map(check => [check.passed, check.attributable])).toEqual([[false, true], [false, true]]);
    expect(checks.every(check => hasDeterministicLeanFailure(check.verification))).toBe(true);
    expect(JSON.stringify(batch)).toBe(before);
  });

  it.each(['crashed', 'cleanup', 'timeout', 'unrelated-error', 'warning-only', 'no-location'] as const)
  ('does not turn %s into a deterministic source failure when coded output is present', kind => {
    const batch = rejected(request);
    for (const result of batch.results) {
      result.stdoutPreview = 'Projection.lean:380:8: error(lean.unknownIdentifier): Unknown identifier missing';
      if (kind === 'crashed') result.error = 'Lean exited with status 137.';
      else if (kind === 'cleanup') result.cleanupError = 'Checkout cleanup failed.';
      else if (kind === 'timeout') result.error = 'Lean verification timed out.';
      else if (kind === 'unrelated-error') result.error = 'Verifier transport unavailable.';
      else if (kind === 'warning-only') result.stdoutPreview = 'Projection.lean:380:8: warning(lean.unusedVariables): unused variable';
      else result.stdoutPreview = 'error(lean.unknownIdentifier): Unknown identifier missing';
    }
    expect(hasDeterministicLeanFailure(batch)).toBe(false);
    const checks = attribute(batch);
    expect(checks.every(check => !check.passed && !hasDeterministicLeanFailure(check.verification))).toBe(true);
    if (kind !== 'cleanup' && kind !== 'timeout') expect(checks.every(check => !check.attributable)).toBe(true);
  });

  it('keeps generic failures eligible for an individual fallback', () => {
    const batch = rejected(request);
    for (const result of batch.results) { delete result.stdoutPreview; delete result.error; }
    expect(attribute(batch).map(check => check.attributable)).toEqual([false, false]);
  });

  it.each([
    ['missing receipt', (batch: MathematicsVerifierBatchResult) => { batch.results.pop(); }],
    ['extra receipt', (batch: MathematicsVerifierBatchResult) => { batch.results.push(batch.results[0]!); }],
    ['reordered receipt', (batch: MathematicsVerifierBatchResult) => { batch.results.reverse(); }],
    ['duplicate target', (batch: MathematicsVerifierBatchResult) => { batch.results[1] = batch.results[0]!; }],
    ['duplicate receipt ID', (batch: MathematicsVerifierBatchResult) => { batch.results[1]!.receiptId = batch.results[0]!.receiptId; }],
    ['duplicate check ID', (batch: MathematicsVerifierBatchResult) => { batch.results[1]!.checkId = batch.results[0]!.checkId; }],
    ['missing receipt ID', (batch: MathematicsVerifierBatchResult) => { batch.results[0]!.receiptId = ''; }],
    ['wrong batch commit', (batch: MathematicsVerifierBatchResult) => { batch.targetCommit = 'wrong-commit'; }],
    ['wrong target commit', (batch: MathematicsVerifierBatchResult) => { batch.results[0]!.targetCommit = 'wrong-commit'; }],
    ['wrong file', (batch: MathematicsVerifierBatchResult) => { batch.results[0]!.proofPath = 'Other.lean'; }],
    ['wrong theorem', (batch: MathematicsVerifierBatchResult) => { batch.results[0]!.theoremName = 'Tutorial.other'; }],
    ['wrong statement', (batch: MathematicsVerifierBatchResult) => { batch.results[0]!.statementHash = 'wrong-statement'; }],
    ['wrong Lean statement', (batch: MathematicsVerifierBatchResult) => { batch.results[0]!.leanStatementHash = 'wrong-statement'; }],
    ['wrong source header', (batch: MathematicsVerifierBatchResult) => { batch.results[0]!.sourceDeclarationHash = 'wrong-source'; }],
    ['wrong claim', (batch: MathematicsVerifierBatchResult) => { batch.results[0]!.claim = 'negation'; }],
    ['wrong session', (batch: MathematicsVerifierBatchResult) => { batch.results[0]!.sessionId = 'other-session'; }],
    ['missing session', (batch: MathematicsVerifierBatchResult) => { batch.sessionId = ''; }],
    ['inconsistent summary', (batch: MathematicsVerifierBatchResult) => { batch.status = 'failed'; }],
  ] as const)('rejects %s before a slice can authorize acceptance', (_name, corrupt) => {
    const batch = verified(request);
    corrupt(batch);
    expect(() => attribute(batch)).toThrow('math_task_check_identity_changed');
  });

  it('rejects duplicated requested targets rather than granting two acceptances', () => {
    expect(() => attributeProofEvidence(verified(request), request.targetCommit, [request.items[0]!, request.items[0]!]))
      .toThrow('math_task_check_identity_changed');
  });

  it.each(['blocked', 'unavailable'] as const)('retains %s semantics in a batch also containing a deterministic failure', status => {
    const batch = rejected(request, [0]);
    batch.results[1]!.status = status;
    const before = JSON.stringify(batch), checks = attribute(batch);
    expect(checks.map(check => ({ passed: check.passed, attributable: check.attributable, status: check.verification.status })))
      .toEqual([0, 1].map(() => ({ passed: false, attributable: true, status })));
    expect(checks.some(check => hasDeterministicLeanFailure(check.verification))).toBe(false);
    expect(JSON.stringify(batch)).toBe(before);
  });

  it.each(['blocked', 'unavailable', 'cleanup', 'aborted', 'timeout'] as const)
  ('does not promote a sibling success when the invocation contains %s', failure => {
    const batch = verified(request), result = batch.results[1]!;
    if (failure === 'blocked' || failure === 'unavailable') { result.status = failure; batch.status = failure; }
    else if (failure === 'cleanup') result.cleanupError = 'Checkout cleanup failed.';
    else {
      batch.status = result.status = 'failed';
      result.error = failure === 'aborted' ? 'Formal verification was aborted.' : 'Lean verification timed out.';
    }
    const before = JSON.stringify(batch), checks = attribute(batch);
    expect(checks.map(check => check.passed)).toEqual([false, false]);
    expect(checks.map(check => check.verification.status)).toEqual([failure === 'unavailable' ? 'unavailable' : 'blocked',
      failure === 'unavailable' ? 'unavailable' : 'blocked']);
    expect(checks.map(check => check.attributable)).toEqual([true, true]);
    expect(checks.some(check => hasDeterministicLeanFailure(check.verification))).toBe(false);
    expect(JSON.stringify(batch)).toBe(before);
  });

  it('preserves the existing single-target receipt boundary', () => {
    const single = { ...request, items: request.items.slice(0, 1) }, batch = verified(single);
    delete (batch.results[0] as Partial<typeof batch.results[number]>)!.sessionId;
    delete (batch.results[0] as Partial<typeof batch.results[number]>)!.checkId;
    expect(attributeProofEvidence(batch, single.targetCommit, single.items)[0]!.passed).toBe(true);
  });
});

describe('task proof batch views', () => {
  let directory: string, workspace: string, problem: SolverProblem, commit: string, tasks: CooperativeTask[];
  const check = (signal = new AbortController().signal) => checkTaskProofs(problem, workspace, commit,
    tasks.map(task => ({ task, retainedGoals: [], assignment: { taskId: task.id, taskDigest: taskVersion(task),
      workerId: 'solver', seedCommit: problem.baseCommit } })), {}, signal);

  beforeEach(() => {
    host.verify.mockReset().mockImplementation(async input => verified(input));
    const example = localExample('solver-batch-attribution-');
    ({ directory, workspace, problem } = example);
    const file = path.join(example.receipt.projectRoot, 'Submission.lean');
    fs.writeFileSync(file, fs.readFileSync(file, 'utf8').replace('theorem add_zero',
      'lemma first : True := by trivial\nlemma second : True := by trivial\n\ntheorem add_zero'));
    commit = commitSolverSources(problem, workspace);
    tasks = ['first', 'second'].map(name => ({ id: name, kind: 'lemma', objective: `Prove ${name}.`,
      proofPath: 'Submission.lean', theoremName: `Tutorial.${name}`, type: 'True', dependsOn: [], revision: 0 }));
  });
  afterEach(() => { vi.restoreAllMocks(); fs.rmSync(directory, { recursive: true, force: true }); });

  it('uses one invocation, captures references only for success, and preserves receipt objects', async () => {
    let batch!: MathematicsVerifierBatchResult;
    host.verify.mockImplementation(async input => batch = rejected(input, [1]));
    const proofs = await check();
    expect(host.verify).toHaveBeenCalledOnce();
    expect(proofs.map(proof => proof.passed)).toEqual([true, false]);
    expect(proofs.map(isAttributedTaskProof)).toEqual([true, true]);
    expect(proofs[0]!.references).toMatchObject({ root: { name: 'Tutorial.first', file: 'Submission.lean' } });
    expect(proofs[1]!.references).toBeUndefined();
    expect(proofs.map(proof => proof.verification.status)).toEqual(['kernel_verified', 'failed']);
    for (const [index, proof] of proofs.entries()) expect(proof.verification.results[0]).toBe(batch.results[index]);
    expect(batch.status).toBe('failed');
  });

  it('keeps deterministic shared-source failures reusable without individual retries', async () => {
    host.verify.mockImplementation(async input => rejected(input));
    const proofs = await check();
    expect(proofs.map(proof => proof.passed)).toEqual([false, false]);
    expect(proofs.map(isAttributedTaskProof)).toEqual([true, true]);
    expect(host.verify).toHaveBeenCalledOnce();
  });

  it('returns attributable failed task views for coded diagnostics instead of verifier unavailability', async () => {
    host.verify.mockImplementation(async input => failedBatch(verified(input), {
      stdoutPreview: () => 'Projection.lean:380:8: error(lean.unknownIdentifier): Unknown identifier terminal_unique_of_prod_gt_one',
    }));
    const proofs = await check();
    expect(proofs.map(proof => proof.passed)).toEqual([false, false]);
    expect(proofs.map(isAttributedTaskProof)).toEqual([true, true]);
    expect(proofs.every(proof => hasDeterministicLeanFailure(proof.verification))).toBe(true);
    expect(host.verify).toHaveBeenCalledOnce();
  });

  it('does not mark generic batch failures as attributable for retry suppression', async () => {
    host.verify.mockImplementation(async input => {
      const batch = rejected(input);
      for (const result of batch.results) delete result.stdoutPreview;
      return batch;
    });
    expect((await check()).map(isAttributedTaskProof)).toEqual([false, false]);
  });

  it('does not trust copied, restored or mutated attribution markers', async () => {
    const [proof] = await check();
    expect(isAttributedTaskProof(proof!)).toBe(true);
    expect(isAttributedTaskProof({ ...proof! })).toBe(false);
    expect(isAttributedTaskProof(JSON.parse(JSON.stringify(proof)))).toBe(false);
    proof!.verification.results[0]!.receiptId = 'mutated';
    expect(isAttributedTaskProof(proof!)).toBe(false);
  });

  it('does not return acceptance after its signal is aborted during verification', async () => {
    const controller = new AbortController();
    host.verify.mockImplementation(async input => { controller.abort(); return verified(input); });
    await expect(check(controller.signal)).rejects.toMatchObject({ name: 'AbortError' });
    expect(host.verify).toHaveBeenCalledOnce();
  });

  it('rejects malformed batch identities before task proof objects are published', async () => {
    host.verify.mockImplementation(async input => {
      const batch = verified(input);
      batch.results[1]!.sourceDeclarationHash = 'wrong-source';
      return batch;
    });
    await expect(check()).rejects.toThrow('math_task_check_identity_changed');
  });
});
