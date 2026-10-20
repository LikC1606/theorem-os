import { canonicalMathJson } from '../math/mathRuntimeIo';
import type { SolverRunState } from './archive';
import type { KnowledgeUse } from './knowledgeUsage';
import { proofReceiptsMatch, type ProofCheck } from './modules/evidence';
import { captureObligationSnapshot } from './obligationProgress';
import { taskVersion } from './tasks';

type FunnelState = Pick<SolverRunState, 'knowledgeDigest' | 'knowledgeRetrievals' | 'knowledgeUses' |
  'cooperation' | 'environmentDigest' | 'problem' | 'check'>;
const unique = <T>(items: readonly T[], key: (item: T) => string) => [...new Map(items.map(item => [key(item), item])).values()];
const distinctIds = (items: readonly { id?: string }[]) => new Set(items.flatMap(item => item.id ? [item.id] : [])).size;
const declarationMatches = (left: { name?: string; file?: string }, right: { name?: string; file?: string }) =>
  Boolean(left.name && left.file && left.name === right.name && left.file === right.file);

/** Describe retained observations. No stage grants proof acceptance or establishes that retrieval caused a solve. */
export function summarizeKnowledgeFunnel(state: FunnelState, options: { mode?: 'transfer' | 'recovery' } = {}) {
  const catalog = state.knowledgeDigest;
  const allRetrievals = state.knowledgeRetrievals?.observations ?? [];
  const retrievals = unique(allRetrievals.filter(item => catalog !== undefined && item.catalogDigest === catalog), item => canonicalMathJson(item));
  const allUses: KnowledgeUse[] = [
    ...(state.knowledgeUses ?? []).map(({ workerId: _worker, commit: _commit, ...use }) => use),
    ...(state.cooperation?.deliveries ?? []).flatMap(item => item.knowledgeUses ?? []),
  ];
  const uses = unique(allUses.filter(item => catalog !== undefined && item.catalogDigest === catalog), item => canonicalMathJson(item));
  const included = retrievals.filter(item => item.included);
  const residualRequests = retrievals.flatMap(item => item.residualSearches ?? []);
  const nodes = state.cooperation?.tasks ?? [];
  const snapshot = captureObligationSnapshot(nodes, { environmentDigest: state.environmentDigest,
    proofRoutes: state.cooperation?.proofRoutes });

  const wholeCheck = state.check;
  const wholeClosed = Boolean(wholeCheck?.passed && state.problem.targets.length &&
    proofReceiptsMatch(wholeCheck.verification, wholeCheck.commit, state.problem.targets.map(target => ({
      proofPath: target.proofPath, theoremName: target.theoremName, expectedSourceDeclarationHash: target.declarationHash,
      statementHash: state.problem.contract.statementHash, leanStatementHash: state.problem.contract.leanStatementHash, claim: 'statement',
    }))));
  const originals = state.problem.targets.map((target, index) => {
    const node = nodes.find(item => item.task.kind === 'goal' && item.task.proofPath === target.proofPath &&
      item.task.theoremName === target.theoremName);
    // Match the host's direct-run original identity, including its frozen declaration hash.
    const task = node?.task ?? { id: `original_goal_${index + 1}`, kind: 'goal' as const,
      objective: `Prove ${target.theoremName}`, revision: 0, dependsOn: [], ...target };
    const integrated = snapshot.obligations.find(item => item.taskId === task.id)?.closed ?? false;
    const proof: ProofCheck | undefined = wholeClosed ? wholeCheck : integrated ? node?.integratedCheck ?? node?.proof : undefined;
    return { target, taskId: task.id, taskDigest: taskVersion(task), closed: Boolean(proof),
      source: wholeClosed ? 'whole-original-check' as const : integrated ? 'integrated-original-task' as const : 'not-recorded' as const,
      proof };
  });
  const originalForUse = (use: KnowledgeUse) => originals.find(item => item.taskId === use.consumer.taskId &&
    item.taskDigest === use.consumer.taskDigest);
  const includedForUse = (use: KnowledgeUse) => included.some(item => {
    if (!item.candidateIds.includes(use.id)) return false;
    if (item.consumer.taskId !== undefined || item.consumer.taskDigest !== undefined)
      return item.consumer.taskId === use.consumer.taskId && item.consumer.taskDigest === use.consumer.taskDigest;
    const original = originalForUse(use);
    return original !== undefined && original.target.theoremName === item.consumer.theoremName &&
      original.target.proofPath === item.consumer.proofPath;
  });
  const currentConsumer = (use: KnowledgeUse) => nodes.some(node => node.task.id === use.consumer.taskId &&
    taskVersion(node.task) === use.consumer.taskDigest) || Boolean(originalForUse(use));
  const checkedReferenceAtClosure = (use: KnowledgeUse) => {
    const original = originalForUse(use), proof = original?.proof;
    if (!proof || use.status !== 'checked-reference' || use.checkedCommit !== proof.commit ||
        use.checkedSourceDigest !== proof.sourceDigest) return false;
    const node = nodes.find(item => item.task.id === original.taskId);
    const references = original.source === 'integrated-original-task'
      ? (node?.integratedCheck ?? node?.proof)?.references?.proof
      : proof.verification.results.find(item => item.proofPath === original.target.proofPath &&
        item.theoremName === original.target.theoremName)?.declarationReferences?.proof;
    return references?.some(item => declarationMatches(item, use.declaration)) ?? false;
  };
  const applications = uses.flatMap(use => use.application ? [use.application] : []);
  const checks = applications.flatMap(application => application.check ? [application.check] : []);
  const includedSelectionCount = uses.filter(includedForUse).length;
  const residualHits = residualRequests.flatMap(item => item.candidateIds);
  const detailedSearches = retrievals.filter(item => item.searchCandidateIds !== undefined);
  const returnedIds = detailedSearches.flatMap(item => item.searchCandidateIds!);
  const packetIds = retrievals.flatMap(item => item.candidateIds);
  const includedIds = included.flatMap(item => item.candidateIds);
  const currentChecks = checks.filter(check => check.environmentDigest === state.environmentDigest);
  return {
    schema: 'theorem-os.knowledge-funnel.v1' as const,
    evidence: 'recorded-not-replayed' as const, attribution: 'observed-not-causal' as const,
    acceptance: 'not-assessed' as const, scope: 'retained-observations' as const,
    mode: options.mode ?? 'unspecified', catalogDigest: catalog ?? null,
    coverage: {
      retrievalLedger: state.knowledgeRetrievals === undefined ? 'not-recorded' as const : 'recorded' as const,
      droppedRetrievalObservations: state.knowledgeRetrievals?.dropped ?? 0,
      useHistory: 'retained-records-only; earlier-drops-not-counted' as const,
      contextSelectionLink: 'same-catalog-candidate-and-consumer; ordering-and-causality-not-assessed' as const,
      rawSearchHits: !detailedSearches.length ? 'not-recorded' as const : detailedSearches.length < retrievals.length
        ? 'partially-recorded' as const : 'recorded' as const,
      searchHitScope: 'returned-hit-unions-per-observation-before-packet-limits; search-api-limits-still-apply' as const,
      residualReaderOmissions: 'retained-omission-records-only; earlier-reader-drops-not-counted' as const,
      applicationScope: 'recorded-elaboration; current-source-bytes-not-rechecked' as const,
      missingEvidence: 'absence-from-retained-records-does-not-establish-non-use' as const,
      catalogMismatchRetrievals: allRetrievals.filter(item => item.catalogDigest !== catalog).length,
      catalogMismatchUses: allUses.filter(item => item.catalogDigest !== catalog).length,
    },
    retrieval: {
      observations: retrievals.length,
      duplicateObservations: allRetrievals.filter(item => item.catalogDigest === catalog).length - retrievals.length,
      residualRequests: residualRequests.length, searchedResidualRequests: residualRequests.filter(item => item.searched).length,
      omittedResidualRequests: residualRequests.filter(item => !item.searched).length,
      recordedOmittedResidualDiagnosticsAtReader: retrievals.flatMap(item => item.residualOmissions ?? [])
        .reduce((count, item) => count + item.count, 0),
      returnedResidualHitOccurrences: residualHits.length, distinctReturnedResidualCandidates: new Set(residualHits).size,
      observationsWithRawHitDetails: detailedSearches.length,
      observationsWithoutRawHitDetails: retrievals.length - detailedSearches.length,
      returnedCandidateOccurrences: detailedSearches.length ? returnedIds.length : null,
      distinctReturnedCandidates: detailedSearches.length ? new Set(returnedIds).size : null,
      packetCandidateOccurrences: packetIds.length, distinctPacketCandidates: new Set(packetIds).size,
    },
    context: {
      includedSections: included.length, omittedSections: retrievals.length - included.length,
      includedCandidateExposures: includedIds.length, distinctIncludedCandidates: new Set(includedIds).size,
    },
    selection: {
      recordedUses: uses.length, distinctCandidates: distinctIds(uses),
      duplicateRecords: allUses.filter(item => item.catalogDigest === catalog).length - uses.length,
      reportedAttempts: uses.filter(item => item.status === 'reported-attempt').length,
      checkedReferences: uses.filter(item => item.status === 'checked-reference').length,
      withRetainedIncludedContext: includedSelectionCount,
      withoutRetainedIncludedContext: uses.length - includedSelectionCount,
      currentConsumerContracts: uses.filter(currentConsumer).length,
      historicalOrMissingConsumerContracts: uses.filter(use => !currentConsumer(use)).length,
    },
    application: {
      reports: applications.length, checks: checks.length, reportsWithoutCheck: applications.length - checks.length,
      elaborated: checks.filter(check => check.status === 'elaborated').length,
      elaboratedUsingSelectedDeclaration: checks.filter(check => check.status === 'elaborated' && check.selectedDeclarationUsed === true).length,
      failed: checks.filter(check => check.status === 'failed').length,
      unavailable: checks.filter(check => check.status === 'unavailable').length,
      reused: checks.filter(check => check.reused).length,
      matchingRecordedEnvironment: currentChecks.length,
      otherRecordedEnvironment: checks.length - currentChecks.length,
    },
    consumerClosure: {
      originalGoals: originals.length, recordedClosedOriginalGoals: originals.filter(item => item.closed).length,
      usesWithClosedOriginalConsumer: uses.filter(use => originalForUse(use)?.closed).length,
      checkedReferencesAtClosedOriginalReceipt: uses.filter(checkedReferenceAtClosure).length,
      goals: originals.map(({ target, taskId, taskDigest, closed, source }) => ({ theoremName: target.theoremName,
        proofPath: target.proofPath, taskId, taskDigest, closed, source })),
    },
  };
}
