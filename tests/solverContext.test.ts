import { expect, it } from 'vitest';
import { buildResearchContext } from '../src/solver/modules/context';
import type { SolverProblem } from '../src/solver/problem';
import type { SolverRunState } from '../src/solver/archive';
import type { DeliveryReceipt } from '../src/solver/deliveryReceipts';
import { deliveryDetails, parseMathResponse, type DeliveryRecord } from '../src/solver/deliveries';
import { assignmentDeliveryFile, leadPlanDeliveryFile, taskVersion, type CooperativeAction, type CooperativeTask } from '../src/solver/tasks';

it('deduplicates repeated findings and progress while preserving exact Lean types and version references', () => {
  const exactType = '∀ (n : Nat), ' + 'True ∧ '.repeat(2100) + 'True';
  const task: CooperativeTask = { id: 'core', kind: 'lemma', objective: 'Prove the core lemma',
    dependsOn: ['library'], revision: 0, theoremName: 'core', proofPath: 'Submission.lean', type: exactType };
  const library: CooperativeTask = { id: 'library', kind: 'research', objective: 'Search library', dependsOn: [], revision: 0 };
  const problem = { projectRelative: '.', ownedFiles: ['Submission.lean'], declarations: {}, targets: [], receiptDigest: 'problem',
    baseCommit: 'fixed-commit', contract: { formalStatement: 'theorem target : True := by sorry', assumptions: [] } } as unknown as SolverProblem;
  const delivery = (kind: DeliveryRecord['kind'], summary: string, id: string): DeliveryRecord => ({
    id, kind, taskId: 'library', taskDigest: taskVersion(library), producer: 'researcher', status: 'advisory',
    statement: '', premises: [], dependencies: [], remainingObligations: ['core'], summary, evidenceRefs: [], createdAt: 1 });
  const finding = 'library-finding: ' + 'long advisory explanation '.repeat(500);
  const action: CooperativeAction = { kind: 'lead', seedCommit: 'fixed-commit', planVersion: 'current-plan',
    planNonce: 'latest-dispatch-nonce', planningInputDigest: 'latest-planning-input',
    capacityRefill: { inputDigest: 'latest-capacity-receipt', workerIds: ['prover'], requestedAt: 24 },
    stagnationRecovery: { inputDigest: 'latest-stagnation-receipt', taskIds: ['core'], workerIds: ['researcher'],
      requestedAt: 25, reason: 'frontier-not-decomposed' },
    handoffIds: ['latest-handoff'], handoffActivations: { 'latest-handoff': 'current-activation' },
    challengeIds: ['latest-challenge'], challengeActivations: { 'latest-challenge': 'current-challenge-activation' } };
  const state = { cooperation: { tasks: [{ task, status: 'pending', attempts: 0 },
    { task: library,
      status: 'completed', attempts: 1, finding }], deliveries: [delivery('progress', 'obsolete-progress', 'old'),
      delivery('research', finding, 'research'), delivery('progress', 'latest-progress', 'new')] } } as unknown as SolverRunState;
  const context = buildResearchContext(problem, state, { root: '/runtime', worktree: '/proof', environment: {},
    taskText: 'Prove the target', retrievalRoot: '/library', frozenContexts: { 'Submission.lean': 'theorem target : True := /- body omitted -/' },
    assignment: action });
  expect(context.message).toContain(JSON.stringify(exactType));
  expect(context.message).toContain(taskVersion(library));
  expect(context.message).toContain('latest-progress');
  expect(context.message).not.toContain('obsolete-progress');
  expect(context.message.match(/library-finding:/gu)).toHaveLength(1);
  expect(context.message).toContain(finding);
  expect(context.continuationMessage).toBeDefined();
  expect(context.continuationMessage!.length).toBeLessThan(context.message.length / 2);
  expect(context.continuationMessage).not.toContain(exactType);
  expect(context.continuationMessage).not.toContain(finding);
  expect(context.continuationMessage).toContain(JSON.stringify(action));
  expect(context.continuationMessage).toContain(leadPlanDeliveryFile(action));
  expect(context.continuationMessage).toContain(JSON.stringify(context.workContract));
  expect(context.continuationMessage).toContain('replaces every previous dispatch nonce and receipt');
  expect(context.continuationMessage).toContain('RESEARCH.md');
  expect(context.continuationMessage).toContain('COOPERATION.json');
  expect(context.continuationMessage).toContain('complete current math-plan');
  expect(context.continuationMessage).toContain('proof acceptance');
  expect(context.manifest!.usedBytes).toBeLessThanOrEqual(context.manifest!.maxBytes);
  const graph = context.message.split('Lead task graph and host feedback:\n')[1].split('\n\nRoute groups')[0];
  expect(JSON.parse(graph)[0].type).toBe(exactType);
});

it.each([false, true])('asks the Lead to return executable work promptly on every decision (existing graph: %s)', existing => {
  const problem = { projectRelative: '.', ownedFiles: ['Submission.lean'], declarations: {}, targets: [], receiptDigest: 'problem',
    baseCommit: 'fixed-commit', contract: { formalStatement: 'theorem target : True := by sorry', assumptions: [] } } as unknown as SolverProblem;
  const task: CooperativeTask = { id: 'core', kind: 'lemma', objective: 'Prove the core lemma.',
    dependsOn: [], revision: 0, theoremName: 'core', proofPath: 'Submission.lean', type: 'True' };
  const state = { cooperation: { tasks: existing ? [{ task, status: 'pending', attempts: 0 }] : [] } } as unknown as SolverRunState;
  const context = buildResearchContext(problem, state, { root: '/runtime', worktree: '/proof', environment: {},
    taskText: 'Prove the target', retrievalRoot: '/library', frozenContexts: { 'Submission.lean': 'theorem target : True := /- body omitted -/' },
    assignment: { kind: 'lead', seedCommit: 'fixed-commit' } });
  expect(context.instructions).toContain('Once a complete plan has useful executable work, save the full current graph and return promptly so peers can start it.');
  expect(context.instructions).toContain('Delegate unresolved library or mathematical searches as research tasks to Researchers.');
  expect(context.instructions).toContain('Return the plan without running Lean diagnostics');
});

const gapContext = (kind: 'research' | 'lemma' | 'goal' | 'lead' | 'review',
  stagnationRecovery?: Extract<CooperativeAction, { kind: 'lead' | 'assemble' }>['stagnationRecovery']) => {
  const formal = 'theorem target : True := by sorry';
  const problem = { projectRelative: '.', ownedFiles: ['Submission.lean'],
    declarations: { 'Submission.lean': [{ name: 'target', header: 'target : True' }] }, targets: [],
    receiptDigest: 'problem', baseCommit: 'fixed-commit',
    contract: { formalStatement: formal, assumptions: [] } } as unknown as SolverProblem;
  const task: CooperativeTask = { id: 'frontier', kind: kind === 'lead' || kind === 'review' ? 'research' : kind,
    objective: 'Resolve the precise missing classification input.', dependsOn: [], revision: 0,
    ...(['lemma', 'goal'].includes(kind) ? { theoremName: 'target', proofPath: 'Submission.lean', type: 'True' } : {}) };
  const state = { cooperation: { tasks: [{ task, status: 'pending', attempts: 0 }] } } as unknown as SolverRunState;
  const action: CooperativeAction = kind === 'lead' ? { kind, seedCommit: 'fixed-commit', stagnationRecovery } :
    kind === 'review' ? { kind, seedCommit: 'fixed-commit', sourceDigest: 'fixed-source' } :
      { kind: 'task', task, assignment: { taskId: task.id, taskDigest: taskVersion(task), workerId: 'worker', seedCommit: 'fixed-commit' } };
  return buildResearchContext(problem, state, { root: '/runtime', worktree: '/proof', environment: {},
    taskText: 'Prove the target', retrievalRoot: '/library', maxOptionalContextBytes: 0,
    frozenContexts: { 'Submission.lean': formal }, assignment: action });
};

it('asks researchers to save scoped negative evidence and publish a schema-valid gap decision promptly', () => {
  const context = gapContext('research');
  expect(context.instructions).toContain('Save a scoped negative library result or a classification gap in worktree-root RESEARCH.md as soon as it is established');
  expect(context.instructions).toContain('pinned library/environment version, searched paths, queries or method, exact result');
  expect(context.instructions).toContain('A scoped search failure is not proof of global absence');
  expect(context.instructions).toContain('needsDecision:true, conclusion:"inconclusive"');
  const encoded = context.instructions.split('Publish a finding during proof work with ')[1].split('. Inline the full finding;')[0];
  const publication = JSON.parse(encoded);
  expect(publication.kind).toBe('research');
  const finding = parseMathResponse(JSON.stringify(publication.finding), 'math-result', { taskId: 'frontier' }, 'summary');
  expect(finding).toMatchObject({ taskId: 'frontier', needsDecision: true, conclusion: 'inconclusive' });
  expect(deliveryDetails(finding)).toMatchObject({ evidenceRefs: [],
    remainingObligations: ['precise unresolved mathematical inference'] });
  expect(context.instructions).toContain('publishing does not finish or park your proof task');
  expect(context.instructions).toContain('leave Lean sources unchanged');
});

it.each(['research', 'lemma', 'goal'] as const)('keeps scoped no-rescan and durable reasoning guidance for %s work', kind => {
  const context = gapContext(kind);
  expect(context.instructions).toContain('Do not rescan the same negatively searched library scope under unchanged inputs');
  expect(context.instructions).toContain('A renamed query alone is not a new mathematical direction');
  expect(context.instructions).toContain('Before any checkpoint, recovery decision or context rotation');
  expect(context.instructions).toContain('attempted methods, exact results and evidence locations, scoped negative searches');
  expect(context.instructions).toContain('precise unresolved next inference');
  expect(context.instructions).toContain('Distinguish checked unconditional facts from conditional sufficiency and unverified drafts');
  expect(context.instructions).toContain('actual consumer with explicit dependsOn or proofRoutes');
  expect(context.instructions).toContain('Renaming the whole theorem, assuming the core result or proving a conditional wrapper is not a reduction');
  expect(context.manifest!.optionalBytes).toBe(0);
});

it('asks the Lead for a real reduction and preserves the dispatch recovery packet with zero optional context', () => {
  const recovery = { inputDigest: 'd'.repeat(64), taskIds: ['frontier'], workerIds: ['worker'], requestedAt: 25,
    reason: 'frontier-not-decomposed' as const };
  const context = gapContext('lead', recovery);
  expect(context.instructions).toContain('genuinely weaker, independently Lean-checkable exact lemma tasks');
  expect(context.instructions).toContain('its hypotheses do not assume the unresolved core result');
  expect(context.instructions).toContain('This dispatch requests recovery from advisory stagnation, not proof failure');
  expect(context.instructions).toContain('no new recovery response schema is required');
  expect(context.manifest!.included).toContainEqual(expect.objectContaining({ id: 'stagnation-recovery', required: true }));
  const encoded = context.message.split('Host stagnation recovery request (advisory scheduling evidence; not proof failure or acceptance):\n')[1];
  expect(JSON.parse(encoded.split('\n\n')[0])).toEqual(recovery);
  expect(gapContext('lead').manifest!.included.some(item => item.id === 'stagnation-recovery')).toBe(false);
});

it('does not inject work recovery instructions into fixed-candidate independent review', () => {
  const context = gapContext('review');
  expect(context.instructions).toContain('You are the Independent Reviewer');
  expect(context.instructions).not.toContain('Before any checkpoint, recovery decision or context rotation');
  expect(context.instructions).not.toContain('This dispatch requests recovery from advisory stagnation');
  expect(context.manifest!.included.some(item => item.id === 'stagnation-recovery')).toBe(false);
});

it.each(['research', 'lemma', 'goal'] as const)(
  'offers a short same-responsibility continuation for %s while retaining full compilation', kind => {
    const context = gapContext(kind);
    expect(context.continuationMessage).toContain('Current cooperative assignment:');
    expect(context.continuationMessage).toContain(JSON.stringify(context.assignment));
    expect(context.continuationMessage).toContain(JSON.stringify(context.workContract));
    expect(context.continuationMessage).toContain('COOPERATION.json');
    expect(context.continuationMessage).toContain('proof acceptance');
    expect(context.message).toContain('Frozen source context and immutable retrieval references:');
    expect(context.manifest).toBeDefined();
  });

it('keeps fixed independent review on the full-message protocol', () => {
  expect(gapContext('review').continuationMessage).toBeUndefined();
});


it('keeps current task feedback and scoped intake receipts inline without repeating full finding bodies', () => {
  const task: CooperativeTask = { id: 'investigate', kind: 'research', objective: 'Resolve the exact classification gap.',
    dependsOn: [], revision: 0, groupId: 'route', sharing: 'group' };
  const action: Extract<CooperativeAction, { kind: 'task' }> = { kind: 'task', task,
    assignment: { taskId: task.id, taskDigest: taskVersion(task), workerId: 'researcher',
      seedCommit: 'fixed-commit', assignmentId: 'fixed-assignment' } };
  const fullFinding = 'Complete retained classification argument. ' + 'Precise intermediate evidence. '.repeat(500);
  const problem = { projectRelative: '.', ownedFiles: ['Submission.lean'], declarations: {}, targets: [], receiptDigest: 'problem',
    baseCommit: 'fixed-commit', contract: { formalStatement: 'theorem target : True := by sorry', assumptions: [] } } as unknown as SolverProblem;
  const receipt: DeliveryReceipt = { id: 'own-receipt', submissionDigest: 'submission', workerId: 'researcher',
    assignmentKey: assignmentDeliveryFile(action.assignment), taskId: task.id, taskDigest: taskVersion(task),
    seedCommit: action.assignment.seedCommit, environmentDigest: 'current-environment', createdAt: 1,
    status: 'needs-correction', code: 'math_delivery_invalid',
    issues: [{ path: 'mathematicalGap.previousDeliveryId', message: 'Use a visible scoped prior gap or omit the reference.' }] };
  const state = { environmentDigest: 'current-environment', cooperation: {
    tasks: [{ task, status: 'pending', attempts: 1, finding: fullFinding, feedback: 'Exact missing uniformity inference.' }],
    deliveries: [{ id: 'latest-finding', kind: 'research', status: 'advisory', producer: 'peer', taskId: task.id,
      taskDigest: taskVersion(task), summary: fullFinding, statement: '', premises: [], dependencies: [],
      remainingObligations: [], evidenceRefs: [], createdAt: 1, findingDigest: 'finding-reference', commit: 'saved-commit' }],
    deliveryReceipts: [receipt, { ...receipt, id: 'other-worker-secret', workerId: 'other' },
      { ...receipt, id: 'old-seed-secret', seedCommit: 'old-seed' },
      { ...receipt, id: 'old-env-secret', environmentDigest: 'old-environment' }],
  } } as unknown as SolverRunState;
  const access = { root: '/runtime', worktree: '/proof', environment: {}, taskText: 'Prove the target', retrievalRoot: '/library',
    frozenContexts: { 'Submission.lean': 'theorem target : True := /- body omitted -/' }, assignment: action,
    sourceFeedback: 'Current host correction: preserve the exact original source.' };
  const first = buildResearchContext(problem, state, access);
  expect(first.continuationMessage).toContain(JSON.stringify(receipt));
  expect(first.continuationMessage).toContain('Current host correction: preserve the exact original source.');
  expect(first.continuationMessage).toContain('Exact missing uniformity inference.');
  expect(first.continuationMessage).toContain('latest-finding');
  expect(first.continuationMessage).toContain('finding-reference');
  expect(first.continuationMessage).toContain('saved-commit');
  expect(first.continuationMessage).not.toContain('other-worker-secret');
  expect(first.continuationMessage).not.toContain('old-seed-secret');
  expect(first.continuationMessage).not.toContain('old-env-secret');
  expect(first.continuationMessage).not.toContain(fullFinding);
  expect(first.continuationMessage!.length).toBeLessThan(first.message.length / 2);
  expect(first.continuationMessage).toContain('matching task digest does not mean its feedback or inbox is unchanged');
  state.cooperation!.tasks[0].feedback = 'New diagnostic under the same exact task digest.';
  const updated = { ...receipt, id: 'new-receipt', issues: [{ path: 'summary', message: 'Include the new exact counterexample.' }] };
  state.cooperation!.deliveryReceipts!.push(updated);
  const next = buildResearchContext(problem, state, access);
  expect(next.continuationMessage).toContain('New diagnostic under the same exact task digest.');
  expect(next.continuationMessage).toContain(JSON.stringify(updated));
  expect(next.assignment).toEqual(first.assignment);
});
