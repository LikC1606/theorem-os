import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it } from 'vitest';
import { readSolverRunState, writeSolverRunState, type SolverRunState } from '../src/solver/archive';
import { mathDigest } from '../src/math/mathRuntimeIo';

describe('advisory type and residual checkpoint records', () => {
  let root: string, state: SolverRunState;
  beforeEach(() => {
    root = fs.mkdtempSync(path.join(os.tmpdir(), 'preflight-archive-'));
    state = { schema: 'deepscientist.math.solver.v1', runId: 'archive', worktree: root, phase: 'running', turns: 0,
      model: 'fixture', effort: 'fixture', taskDigest: 'task', buildDigest: 'build', environmentDigest: 'environment',
      evaluatorDigest: 'evaluator', problem: { workspace: root, receiptDigest: 'receipt' },
      cooperation: { tasks: [{ task: { id: 'helper', kind: 'lemma', objective: 'Prove helper', dependsOn: [], revision: 0 },
        status: 'blocked', attempts: 0, typePreflight: { status: 'invalid', inputDigest: mathDigest('input'), taskDigest: mathDigest('task'),
          reason: 'Type mismatch in fixed query', context: 'Fixture.original', evidence: 'advisory-type-elaboration', proofAcceptance: 'not-assessed',
          artifact: { path: '.lake/type-diagnostics/query/manifest.json', digest: mathDigest('query') } } }] },
      knowledgeRetrievals: { dropped: 0, observations: [{ sectionId: 'knowledge:helper', catalogDigest: mathDigest('catalog'),
        searchInputDigest: mathDigest('goal'), searchSource: 'residual-goal', consumer: { taskId: 'helper', taskDigest: mathDigest('task') },
        diagnostic: { authority: 'advisory-lean-process', sourceDigest: mathDigest('source'), environmentDigest: mathDigest('environment'),
          toolIdentity: mathDigest('tools'), artifact: { path: '.lake/diagnostic-artifacts/fixed.json', digest: mathDigest('diagnostic') },
          file: 'Submission.lean', line: 3, column: 0 }, candidateIds: [mathDigest('candidate')], routeFindingIds: [], included: true,
        workerId: 'proof', workerTurn: 1, runTurn: 1, contextDigest: mathDigest('context'), at: 100 }] },
    } as unknown as SolverRunState;
  });
  afterEach(() => fs.rmSync(root, { recursive: true, force: true }));
  const read = () => { const file = path.join(root, 'state.json'); writeSolverRunState(file, state); return readSolverRunState(file); };

  it('round-trips exact preflight and residual provenance without converting it to proof evidence', () => {
    const restored = read();
    expect(restored.cooperation!.tasks[0].typePreflight).toEqual(state.cooperation!.tasks[0].typePreflight);
    expect(restored.knowledgeRetrievals).toEqual(state.knowledgeRetrievals);
    expect(restored.cooperation!.tasks[0]).toMatchObject({ status: 'blocked', attempts: 0 });
    expect(restored.cooperation!.tasks[0].proof).toBeUndefined();
    expect(restored.cooperation!.tasks[0].integratedCheck).toBeUndefined();
  });

  it('keeps old checkpoints without preflight or diagnostic retrieval metadata readable', () => {
    delete state.cooperation!.tasks[0].typePreflight;
    delete state.knowledgeRetrievals!.observations[0].searchSource;
    delete state.knowledgeRetrievals!.observations[0].diagnostic;
    expect(read().cooperation!.tasks[0].typePreflight).toBeUndefined();
    expect(read().knowledgeRetrievals!.observations[0].diagnostic).toBeUndefined();
  });

  it('preserves case search coverage, reader omissions and application experiences across recovery', () => {
    const observation = state.knowledgeRetrievals!.observations[0];
    observation.searchCandidateIds = ['included', 'omitted-for-bytes'];
    observation.residualSearches = [{ inputDigest: mathDigest('case'), diagnostic: observation.diagnostic!,
      localContext: 'no-locals', searched: false, candidateIds: [] }];
    observation.residualOmissions = [{ count: 3, reason: 'diagnostic-reader-budget' }];
    state.knowledgeUses = [{ id: 'included', catalogDigest: mathDigest('catalog'), consumer: observation.consumer as { taskId: string; taskDigest: string },
      declaration: { name: 'Adapted.bridge', file: 'Submission.lean' }, status: 'reported-attempt', attribution: 'model-reported-origin',
      workerId: 'proof', commit: 'fixed', application: { expression: 'Adapted.bridge', expectedType: 'True',
        context: { file: 'Submission.lean', declaration: 'Fixture.original' }, adaptationSteps: ['Normalize then exact.'],
        check: { status: 'failed', authority: 'advisory-application-elaboration', reason: 'missing-premise',
          proofAcceptance: 'not-assessed', consumerCoverage: 'not-assessed', environmentDigest: 'environment', commit: 'fixed',
          reuseEnvironmentDigest: mathDigest('reuse'), diagnostic: 'Missing an explicit premise.' } } }];
    const restored = read();
    expect(restored.knowledgeRetrievals).toEqual(state.knowledgeRetrievals);
    expect(restored.knowledgeUses).toEqual(state.knowledgeUses);
  });

  it('preserves successful projection reuse and the distinct origin and current raw inputs', () => {
    const preflight = state.cooperation!.tasks[0].typePreflight!;
    Object.assign(preflight, { status: 'elaborated', projectionReuse: {
      originInputDigest: mathDigest('origin-input'), originSourceDigest: mathDigest('origin-source'),
      sourceDigest: mathDigest('current-source'), projectionDigest: mathDigest('projection'),
    } });
    expect(read().cooperation!.tasks[0].typePreflight).toEqual(preflight);
    expect(read().cooperation!.tasks[0].proof).toBeUndefined();
  });

  it('rejects projection reuse metadata attached to an invalid query', () => {
    Object.assign(state.cooperation!.tasks[0].typePreflight!, { projectionReuse: {
      originInputDigest: mathDigest('origin-input'), originSourceDigest: mathDigest('origin-source'),
      sourceDigest: mathDigest('current-source'), projectionDigest: mathDigest('projection'),
    } });
    expect(read).toThrow('math_resume_state_invalid:cooperation.tasks.0.typePreflight');
  });

  it('rejects preflight metadata claiming proof acceptance', () => {
    (state.cooperation!.tasks[0].typePreflight as any).proofAcceptance = 'kernel_verified';
    expect(read).toThrow('math_resume_state_invalid:cooperation.tasks.0.typePreflight.proofAcceptance');
  });
});
