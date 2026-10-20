import { describe, expect, it } from 'vitest';
import type { SolverRunState } from '../src/solver/archive';
import type { TaskProof } from '../src/solver/cooperativeProof';
import type { DeliveryRecord } from '../src/solver/deliveries';
import { summarizeKnowledgeFunnel } from '../src/solver/knowledgeFunnel';
import type { KnowledgeRetrievalObservation, KnowledgeUse } from '../src/solver/knowledgeUsage';
import { taskVersion, type TaskRecord } from '../src/solver/tasks';

const catalog = 'catalog', environmentDigest = 'environment';
const declaration = { name: 'Current.adapted', file: 'Submission.lean' };
function goal(id = 'original'): TaskRecord {
  return { task: { id, kind: 'goal', objective: 'Prove Current.original', revision: 0, dependsOn: [],
    proofPath: 'Submission.lean', theoremName: 'Current.original' }, status: 'pending', attempts: 0 };
}
function state(nodes: TaskRecord[] = [goal()]): SolverRunState {
  return { schema: 'deepscientist.math.solver.v1', knowledgeDigest: catalog, environmentDigest,
    cooperation: { tasks: nodes }, problem: { targets: [{ proofPath: 'Submission.lean', theoremName: 'Current.original',
      declarationHash: 'declaration' }], contract: { statementHash: 'statement', leanStatementHash: 'lean-statement' } } } as SolverRunState;
}
function use(node: TaskRecord, id = 'selected'): KnowledgeUse {
  return { id, catalogDigest: catalog, consumer: { taskId: node.task.id, taskDigest: taskVersion(node.task) },
    declaration, status: 'reported-attempt', attribution: 'model-reported-origin' };
}
function retrieval(node: TaskRecord, included = true): KnowledgeRetrievalObservation {
  return { sectionId: 'section', catalogDigest: catalog, searchInputDigest: 'query',
    consumer: { taskId: node.task.id, taskDigest: taskVersion(node.task) }, candidateIds: ['selected'], routeFindingIds: [],
    included, contextDigest: 'context', workerId: 'solver', workerTurn: 1, runTurn: 1, at: 1 };
}
function checked(node: TaskRecord): TaskProof {
  node.status = 'integrated';
  return node.integratedCheck = { taskDigest: taskVersion(node.task), passed: true, commit: 'checked',
    sourceDigest: 'checked-source', seedCommit: 'seed', changes: [],
    verification: { status: 'kernel_verified', targetCommit: 'projection', results: [
      { status: 'kernel_verified', targetCommit: 'projection', receiptId: 'receipt' },
    ] }, references: { environmentDigest, sourceCommit: 'projection', contextDigest: 'context',
      inputs: [], root: { file: node.task.proofPath!, name: node.task.theoremName! }, tasks: [], statement: [], proof: [declaration] } } as TaskProof;
}
function application(item: KnowledgeUse, status: 'elaborated' | 'failed' | 'unavailable', selectedDeclarationUsed?: boolean): KnowledgeUse {
  return { ...item, application: { expression: 'Current.adapted', expectedType: 'True',
    context: { file: 'Submission.lean', declaration: 'Current.original' }, check: { status, reason: status,
      authority: 'advisory-application-elaboration', proofAcceptance: 'not-assessed', consumerCoverage: 'not-assessed',
      commit: 'selected-check', environmentDigest, ...(selectedDeclarationUsed === undefined ? {} : { selectedDeclarationUsed }) } } };
}
function saveUse(input: SolverRunState, item: KnowledgeUse) {
  (input.knowledgeUses ??= []).push({ ...item, workerId: 'solver', commit: 'selected-check' });
}

describe('knowledge observations across retrieval, context, application and original closure', () => {
  it('separates bounded search hits, packet candidates and actual context inclusion', () => {
    const node = goal(), input = state([node]), observation = retrieval(node, false);
    observation.residualSearches = [
      { inputDigest: 'case-a', localContext: 'closed-for-retrieval', searched: true,
        candidateIds: ['selected', 'not-in-packet'], diagnostic: {} as never },
      { inputDigest: 'case-b', localContext: 'closed-for-retrieval', searched: false,
        candidateIds: [], diagnostic: {} as never },
    ];
    input.knowledgeRetrievals = { dropped: 7, observations: [observation] };
    saveUse(input, use(node));
    const result = summarizeKnowledgeFunnel(input, { mode: 'recovery' });
    expect(result).toMatchObject({ mode: 'recovery', attribution: 'observed-not-causal', acceptance: 'not-assessed',
      coverage: { droppedRetrievalObservations: 7, missingEvidence: 'absence-from-retained-records-does-not-establish-non-use' },
      retrieval: { observations: 1, residualRequests: 2, searchedResidualRequests: 1, omittedResidualRequests: 1,
        returnedResidualHitOccurrences: 2, packetCandidateOccurrences: 1 },
      context: { includedSections: 0, omittedSections: 1, includedCandidateExposures: 0 },
      selection: { recordedUses: 1, withoutRetainedIncludedContext: 1, withRetainedIncludedContext: 0 } });
  });

  it('links context only within the same candidate, catalog and consumer version', () => {
    const node = goal(), other = goal('other'), input = state([node]), observed = retrieval(node);
    input.knowledgeRetrievals = { dropped: 0, observations: [observed, { ...retrieval(other), at: 2 }] };
    saveUse(input, use(node)); saveUse(input, { ...use(node, 'not-shown') });
    saveUse(input, { ...use(node), consumer: { ...use(node).consumer, taskDigest: 'old-contract' } });
    let result = summarizeKnowledgeFunnel(input);
    expect(result.selection).toMatchObject({ recordedUses: 3, withRetainedIncludedContext: 1, withoutRetainedIncludedContext: 2,
      currentConsumerContracts: 2, historicalOrMissingConsumerContracts: 1 });
    input.knowledgeRetrievals.observations[0] = { ...observed, catalogDigest: 'another-catalog' };
    result = summarizeKnowledgeFunnel(input);
    expect(result.coverage.catalogMismatchRetrievals).toBe(1);
    expect(result.selection.withRetainedIncludedContext).toBe(0);
  });

  it('counts returned hit unions before packet limits and records diagnostics omitted by the reader', () => {
    const node = goal(), input = state([node]), observation = retrieval(node);
    observation.searchCandidateIds = ['selected', 'outside-packet', 'other-case'];
    observation.residualOmissions = [{ count: 5, reason: 'diagnostic-reader-budget' }];
    input.knowledgeRetrievals = { dropped: 0, observations: [observation] };
    expect(summarizeKnowledgeFunnel(input)).toMatchObject({
      coverage: { rawSearchHits: 'recorded' },
      retrieval: { observationsWithRawHitDetails: 1, observationsWithoutRawHitDetails: 0,
        returnedCandidateOccurrences: 3, distinctReturnedCandidates: 3, packetCandidateOccurrences: 1,
        recordedOmittedResidualDiagnosticsAtReader: 5 },
      context: { includedCandidateExposures: 1 },
    });
  });

  it('distinguishes measured zero hits from missing legacy hit telemetry', () => {
    const node = goal(), input = state([node]), observation = retrieval(node);
    input.knowledgeRetrievals = { dropped: 0, observations: [observation] };
    expect(summarizeKnowledgeFunnel(input)).toMatchObject({ coverage: { rawSearchHits: 'not-recorded' },
      retrieval: { returnedCandidateOccurrences: null, distinctReturnedCandidates: null, observationsWithoutRawHitDetails: 1 } });
    observation.searchCandidateIds = [];
    expect(summarizeKnowledgeFunnel(input)).toMatchObject({ coverage: { rawSearchHits: 'recorded' },
      retrieval: { returnedCandidateOccurrences: 0, distinctReturnedCandidates: 0, observationsWithoutRawHitDetails: 0 } });
    input.knowledgeRetrievals.observations.push({ ...retrieval(node), at: 2 });
    expect(summarizeKnowledgeFunnel(input)).toMatchObject({ coverage: { rawSearchHits: 'partially-recorded' },
      retrieval: { observationsWithRawHitDetails: 1, observationsWithoutRawHitDetails: 1 } });
  });

  it('does not count duplicate state/delivery copies as additional selections or checks', () => {
    const node = goal(), input = state([node]), item = application(use(node), 'failed');
    saveUse(input, item);
    input.cooperation!.deliveries = [{ knowledgeUses: [item] } as DeliveryRecord];
    input.knowledgeRetrievals = { dropped: 0, observations: [retrieval(node), retrieval(node)] };
    const result = summarizeKnowledgeFunnel(input);
    expect(result.selection).toMatchObject({ recordedUses: 1, duplicateRecords: 1 });
    expect(result.application).toMatchObject({ reports: 1, checks: 1, failed: 1 });
    expect(result.retrieval).toMatchObject({ observations: 1, duplicateObservations: 1 });
  });

  it('keeps reference evidence separate from application elaboration and selected declaration use', () => {
    const node = goal(), input = state([node]);
    saveUse(input, { ...use(node), status: 'checked-reference', checkedCommit: 'checked', checkedSourceDigest: 'checked-source' });
    saveUse(input, application(use(node, 'expression-without-the-selected-constant'), 'elaborated', false));
    saveUse(input, application(use(node, 'actual-selected-expression'), 'elaborated', true));
    saveUse(input, application(use(node, 'not-elaborated'), 'failed'));
    saveUse(input, application(use(node, 'no-environment'), 'unavailable'));
    const result = summarizeKnowledgeFunnel(input);
    expect(result.selection.checkedReferences).toBe(1);
    expect(result.application).toMatchObject({ reports: 4, checks: 4, elaborated: 2,
      elaboratedUsingSelectedDeclaration: 1, failed: 1, unavailable: 1 });
    expect(result.consumerClosure.recordedClosedOriginalGoals).toBe(0);
  });

  it('reports historical environments without relabelling them as current checked applications', () => {
    const node = goal(), input = state([node]), item = application(use(node), 'elaborated', true);
    item.application!.check!.environmentDigest = 'old-environment';
    saveUse(input, item);
    expect(summarizeKnowledgeFunnel(input).application).toMatchObject({ elaborated: 1, matchingRecordedEnvironment: 0,
      otherRecordedEnvironment: 1 });
  });

  it('records a closed original only from a current unconditional integrated receipt', () => {
    const node = goal(), input = state([node]), proof = checked(node);
    const item = { ...use(node), status: 'checked-reference' as const, checkedCommit: proof.commit, checkedSourceDigest: proof.sourceDigest };
    saveUse(input, item);
    let result = summarizeKnowledgeFunnel(input);
    expect(result.consumerClosure).toMatchObject({ originalGoals: 1, recordedClosedOriginalGoals: 1,
      usesWithClosedOriginalConsumer: 1, checkedReferencesAtClosedOriginalReceipt: 1 });
    proof.conditions = [{ taskId: 'unproved', taskDigest: 'unproved' }];
    node.status = 'conditional';
    result = summarizeKnowledgeFunnel(input);
    expect(result.consumerClosure).toMatchObject({ recordedClosedOriginalGoals: 0,
      usesWithClosedOriginalConsumer: 0, checkedReferencesAtClosedOriginalReceipt: 0 });
  });

  it('does not join an old reference receipt to a later closed original just by declaration name', () => {
    const node = goal(), input = state([node]), proof = checked(node);
    saveUse(input, { ...use(node), status: 'checked-reference', checkedCommit: 'old-check', checkedSourceDigest: proof.sourceDigest });
    expect(summarizeKnowledgeFunnel(input).consumerClosure).toMatchObject({ recordedClosedOriginalGoals: 1,
      usesWithClosedOriginalConsumer: 1, checkedReferencesAtClosedOriginalReceipt: 0 });
    node.task = { ...node.task, revision: 1 };
    expect(summarizeKnowledgeFunnel(input).consumerClosure.recordedClosedOriginalGoals).toBe(0);
  });

  it('does not count a checked helper, plan dependency or advisory link as original closure', () => {
    const original = goal(), helper: TaskRecord = { ...goal('helper'), task: { ...goal('helper').task, kind: 'lemma',
      theoremName: 'Current.helper', type: 'True' } };
    checked(helper);
    original.task = { ...original.task, dependsOn: ['helper'] };
    helper.application = { helperDigest: taskVersion(helper.task), consumerTaskId: original.task.id,
      consumerDigest: taskVersion(original.task) };
    const input = state([helper, original]); saveUse(input, use(helper));
    expect(summarizeKnowledgeFunnel(input).consumerClosure).toMatchObject({ originalGoals: 1,
      recordedClosedOriginalGoals: 0, usesWithClosedOriginalConsumer: 0 });
  });

  it('supports direct-run original identities and frozen target receipts without cooperative tasks', () => {
    const input = state([]), target = input.problem.targets[0]!;
    const node: TaskRecord = { task: { id: 'original_goal_1', kind: 'goal', objective: `Prove ${target.theoremName}`,
      revision: 0, dependsOn: [], ...target }, attempts: 0, status: 'pending' };
    input.knowledgeRetrievals = { dropped: 0, observations: [{ ...retrieval(node),
      consumer: { theoremName: target.theoremName, proofPath: target.proofPath } }] };
    input.check = { passed: true, commit: 'whole', sourceDigest: 'whole-source', verification: { status: 'kernel_verified',
      targetCommit: 'whole', results: [{ status: 'kernel_verified', targetCommit: 'whole', proofPath: target.proofPath,
        theoremName: target.theoremName, sourceDeclarationHash: target.declarationHash, statementHash: 'statement',
        leanStatementHash: 'lean-statement', claim: 'statement', declarationReferences: { proof: [declaration], statement: [] } }] } } as SolverRunState['check'];
    saveUse(input, { ...use(node), status: 'checked-reference', checkedCommit: 'whole', checkedSourceDigest: 'whole-source' });
    expect(summarizeKnowledgeFunnel(input)).toMatchObject({ selection: { withRetainedIncludedContext: 1 },
      consumerClosure: { recordedClosedOriginalGoals: 1, checkedReferencesAtClosedOriginalReceipt: 1 } });
    input.check!.verification.results[0]!.sourceDeclarationHash = 'wrong-target';
    expect(summarizeKnowledgeFunnel(input).consumerClosure.recordedClosedOriginalGoals).toBe(0);
  });

  it('marks absent legacy telemetry and rejects mismatched catalog records without claiming non-use', () => {
    const node = goal(), input = state([node]);
    saveUse(input, { ...use(node), catalogDigest: 'other' });
    const result = summarizeKnowledgeFunnel(input);
    expect(result).toMatchObject({ coverage: { retrievalLedger: 'not-recorded', catalogMismatchUses: 1,
      rawSearchHits: 'not-recorded', useHistory: 'retained-records-only; earlier-drops-not-counted' },
      retrieval: { returnedCandidateOccurrences: null, distinctReturnedCandidates: null },
      selection: { recordedUses: 0 }, context: { includedSections: 0 } });
  });
});
