import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it } from 'vitest';
import { bootstrapLocalExample } from '../src/math/localExample';
import { mathDigest } from '../src/math/mathRuntimeIo';
import type { SolverRunState } from '../src/solver/archive';
import { frozenSourceContext } from '../src/solver/contextCompiler';
import { freezeContinuationInput, readContinuationInput, type ContinuationSnapshot } from '../src/solver/continuationInput';
import { buildResearchContext, buildStatementReviewContext, type ContextBundle } from '../src/solver/modules/context';
import { readSolverProblem, type SolverProblem } from '../src/solver/problem';
import type { StatementAction, StatementReview } from '../src/solver/statementReview';
import { taskVersion, type CooperativeAction, type CooperativeTask } from '../src/solver/tasks';

describe('explicit continuation context', () => {
  let directory: string, workspace: string, problem: SolverProblem, state: SolverRunState, snapshot: ContinuationSnapshot;
  const taskText = 'Keep the full controls.\n# Historical heading\nThis text remains mandatory and verbatim.\n';
  const body = 'HISTORICAL_PROOF_BODY_MUST_BE_READ_ON_DEMAND\n'.repeat(1000);
  const helper: CooperativeTask = { id: 'helper', kind: 'lemma', objective: 'Prove helper', dependsOn: [], revision: 0,
    proofPath: 'Submission.lean', theoremName: 'Tutorial.helper', type: 'True' };
  const research: CooperativeTask = { id: 'research', kind: 'research', objective: 'Investigate one missing inference', dependsOn: [], revision: 0 };
  const actionFor = (task: CooperativeTask): CooperativeAction => ({ kind: 'task', task,
    assignment: { taskId: task.id, taskDigest: taskVersion(task), workerId: task.id, seedCommit: problem.baseCommit } });
  const build = (action: CooperativeAction, continuation: ContinuationSnapshot | undefined, attached = true) =>
    buildResearchContext(problem, { ...state, continuationDigest: attached ? snapshot.digest : undefined }, {
      root: '/runtime', worktree: workspace, environment: {}, taskText, continuation,
      assignment: action, retrievalRoot: workspace, maxOptionalContextBytes: 0,
      frozenContexts: Object.fromEntries(problem.ownedFiles.map(file => [file,
        frozenSourceContext(problem, file, fs.readFileSync(path.join(workspace, problem.projectRelative, file), 'utf8'))])),
    });
  function section(bundle: ContextBundle, id: string): string {
    let offset = 0;
    for (const item of bundle.manifest!.included) {
      if (item.id === id) return Buffer.from(bundle.message).subarray(offset, offset + item.bytes).toString('utf8');
      offset += item.bytes + 2;
    }
    throw new Error(`missing section ${id}`);
  }
  beforeEach(() => {
    directory = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'continuation-context-')));
    workspace = path.join(directory, 'workspace');
    const receipt = bootstrapLocalExample(workspace);
    problem = readSolverProblem(workspace, receipt.activeProblemPath);
    const taskDigest = mathDigest(taskText), source = path.join(directory, 'old-proof.txt'), manifest = path.join(directory, 'input.json');
    fs.writeFileSync(source, body);
    fs.writeFileSync(manifest, JSON.stringify({ schema: 'theorem-os.continuation-input.v1', taskDigest,
      problemReceiptDigest: problem.receiptDigest,
      attachments: [{ id: 'old-proof', kind: 'proof-source', path: source, bytes: Buffer.byteLength(body), sha256: mathDigest(body) }] }));
    snapshot = freezeContinuationInput(readContinuationInput(manifest, { taskDigest, problemReceiptDigest: problem.receiptDigest }),
      path.join(directory, 'runtime'));
    state = { schema: 'deepscientist.math.solver.v1', runId: 'continuation-fixture', problem, taskDigest,
      buildDigest: 'build', environmentDigest: 'environment', evaluatorDigest: 'evaluator', model: 'unused', effort: 'unused',
      worktree: workspace, phase: 'running', turns: 0, continuationDigest: snapshot.digest,
      cooperation: { canonicalCommit: problem.baseCommit, tasks: [helper, research,
        ...problem.targets.map((target, index) => ({ id: `goal_${index}`, kind: 'goal' as const, objective: 'Original goal',
          theoremName: target.theoremName, proofPath: target.proofPath, dependsOn: [], revision: 0 }))]
        .map(task => ({ task, status: 'pending', attempts: 0 })) } };
  });
  afterEach(() => fs.rmSync(directory, { recursive: true, force: true }));

  it.each(['lead', 'engineer', 'researcher', 'reviewer'] as const)
  ('retains a mandatory attachment index for %s without injecting historical bodies or changing the original problem', role => {
    const action: CooperativeAction = role === 'lead' ? { kind: 'lead', seedCommit: problem.baseCommit } :
      role === 'reviewer' ? { kind: 'review', seedCommit: problem.baseCommit, sourceDigest: 'fixed-source' } :
        actionFor(role === 'engineer' ? helper : research);
    const attached = build(action, snapshot), plain = build(action, undefined, false);
    expect(attached.message).toContain('continuation read --snapshot');
    expect(attached.message).toContain(snapshot.digest);
    expect(attached.message).toContain('old-proof');
    expect(attached.message).not.toContain(body.slice(0, 100));
    expect(attached.manifest!.included.some(item => item.required && item.kind === 'continuation' &&
      section(attached, item.id).includes(snapshot.digest))).toBe(true);
    expect(section(attached, 'original-problem')).toBe(section(plain, 'original-problem'));
    expect(section(attached, 'original-problem')).toContain(taskText);
    expect(attached.instructions).toBe(plain.instructions);
  });

  it('rejects a missing or changed attachment identity instead of silently dropping the mandatory index', () => {
    const action: CooperativeAction = { kind: 'lead', seedCommit: problem.baseCommit };
    expect(() => build(action, undefined, true)).toThrow('math_continuation_identity_missing');
    expect(() => build(action, { ...snapshot, digest: mathDigest('another-snapshot') })).toThrow('math_continuation_identity_changed');
    expect(() => buildResearchContext(problem, { ...state, taskDigest: mathDigest('another-task') }, {
      root: '/runtime', worktree: workspace, environment: {}, taskText, continuation: snapshot,
      retrievalRoot: workspace,
    })).toThrow();
  });

  it('withholds the attachment index and content from blind statement review', () => {
    const action = { kind: 'backtranslate', reviewId: 'fixed-review' } as StatementAction;
    const context = buildStatementReviewContext({ intendedStatement: 'WITHHELD_INTENT', premises: [] } as unknown as StatementReview,
      action, problem.receiptDigest);
    expect(context.scope).toBe('fixed-statement');
    expect(context.message).not.toContain(snapshot.digest);
    expect(context.message).not.toContain('old-proof');
    expect(context.message).not.toContain('WITHHELD_INTENT');
    expect(context.message).not.toContain('HISTORICAL_PROOF_BODY');
  });
});
