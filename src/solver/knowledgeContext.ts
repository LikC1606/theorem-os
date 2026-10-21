import { canonicalMathJson, mathDigest } from '../math/mathRuntimeIo';
import type { CooperationState } from './cooperation';
import type { ContextSection } from './contextCompiler';
import { originalGoalTaskFocus } from './modules/search';
import type { SolverProblem } from './problem';
import { isAdvisoryTask, isFinalCandidateReview, taskVersion, type CooperativeAction, type CooperativeTask } from './tasks';
import type { TheoremKnowledgeBase } from './theoremKnowledge';
import { knowledgeTypeExpression, searchTheoremKnowledgeRequests } from './theoremKnowledgeSearch';
import { searchKnowledgeRouteFindingRequests } from './theoremKnowledgeFindings';
import type { LeanResidualGoal, LeanResidualGoalConsumer, LeanResidualGoalOmission } from '../math/leanResidualGoals';
import { knowledgeResidualViews, type KnowledgeResidualView } from './theoremKnowledgeGoal';

/** Validated once when the run pins its catalog; no archived proof sources enter task hints. */
export type KnowledgeContextSnapshot = Readonly<{
  digest: string;
  base: Pick<TheoremKnowledgeBase, 'entries' | 'evidence' | 'routeFindings'>;
}>;
export type KnowledgeRetrieval = Readonly<{
  sectionId: string; catalogDigest: string; searchInputDigest: string; consumer: SearchTarget['consumer'];
  candidateIds: readonly string[]; routeFindingIds: readonly string[];
  searchCandidateIds?: readonly string[];
  searchSource?: SearchTarget['source']; diagnostic?: SearchTarget['diagnostic'];
  residualSearches?: readonly { inputDigest: string; diagnostic: NonNullable<SearchTarget['diagnostic']>;
    caseLabel?: string; localContext: KnowledgeResidualView['localContext']; fallbackReason?: string;
    searched: boolean; candidateIds: readonly string[] }[];
  residualOmissions?: readonly Pick<LeanResidualGoalOmission, 'count' | 'reason'>[];
}>;

type SearchTarget = {
  consumer: { taskId?: string; taskDigest?: string; theoremName?: string; proofPath?: string };
  source: 'closed-task-type' | 'frozen-source-header' | 'research-objective' | 'residual-goal';
  query: string; goal?: string;
  diagnostic?: Pick<LeanResidualGoal, 'authority' | 'sourceDigest' | 'environmentDigest' | 'toolIdentity' | 'artifact' | 'file' | 'line' | 'column'>;
};
const maxTargets = 3, candidateLimit = 3, maxSectionBytes = 4096;
const title = 'Saved theorem candidates (advisory; inspect full types and premises, then check the actual application):\n';

function originalTarget(problem: SolverProblem, target: { theoremName?: string; proofPath?: string }): SearchTarget | undefined {
  if (!target.theoremName || !target.proofPath) return undefined;
  const headers = problem.declarations[target.proofPath] ?? [];
  const exact = headers.filter(item => item.name === target.theoremName);
  const matches = exact.length ? exact : headers.filter(item => item.name.split('.').at(-1) === target.theoremName!.split('.').at(-1));
  if (matches.length !== 1) return undefined;
  return { consumer: { theoremName: target.theoremName, proofPath: target.proofPath },
    source: 'frozen-source-header', query: '',
    goal: knowledgeTypeExpression({ type: matches[0]!.header, typeKind: 'source-header' }) };
}

function taskTarget(problem: SolverProblem, task: CooperativeTask): SearchTarget | undefined {
  if (isFinalCandidateReview(task)) return undefined;
  const target: SearchTarget | undefined = isAdvisoryTask(task)
    ? { consumer: {}, source: 'research-objective', query: task.objective }
    : task.kind === 'goal' ? originalTarget(problem, task) : task.type
      ? { consumer: { theoremName: task.theoremName, proofPath: task.proofPath },
        source: 'closed-task-type', query: '', goal: task.type } : undefined;
  return target && { ...target, consumer: { ...target.consumer, taskId: task.id, taskDigest: taskVersion(task) } };
}

function searchTargets(problem: SolverProblem, cooperation?: CooperationState, action?: CooperativeAction,
  environmentDigest?: string): SearchTarget[] {
  if (action?.kind === 'task') {
    const target = taskTarget(problem, action.task);
    return target ? [target] : [];
  }
  if (action && action.kind !== 'lead') return [];
  if (action?.kind === 'lead' && cooperation?.tasks.length) {
    const focus = originalGoalTaskFocus(cooperation.tasks, cooperation.groups, environmentDigest);
    const targets = cooperation.tasks.filter(node => focus.frontier.has(node.task.id))
      .toSorted((a, b) => Number(focus.preferred.frontier.has(b.task.id)) - Number(focus.preferred.frontier.has(a.task.id)))
      .flatMap(node => { const target = taskTarget(problem, node.task); return target ? [target] : []; });
    if (targets.length) return targets.slice(0, maxTargets);
  }
  return problem.targets.flatMap(target => {
    const search = originalTarget(problem, target); return search ? [search] : [];
  }).slice(0, maxTargets);
}

export function knowledgeContextConsumers(problem: SolverProblem, cooperation?: CooperationState,
  action?: CooperativeAction, environmentDigest?: string): LeanResidualGoalConsumer[] {
  return searchTargets(problem, cooperation, action, environmentDigest).flatMap(({ consumer }) => consumer.theoremName && consumer.proofPath
    ? [{ ...consumer, theoremName: consumer.theoremName, proofPath: consumer.proofPath }] : []);
}

/** Search exact assigned inputs; hits never become task dependencies, checks or accepted proofs. */
export function knowledgeContextSections(input: {
  problem: SolverProblem; cooperation?: CooperationState; action?: CooperativeAction;
  knowledge: KnowledgeContextSnapshot; environmentDigest?: string;
  residualGoals?: readonly LeanResidualGoal[];
  residualOmissions?: readonly LeanResidualGoalOmission[];
}): (ContextSection & { knowledge: KnowledgeRetrieval })[] {
  const { problem, knowledge } = input;
  const targets = searchTargets(problem, input.cooperation, input.action, input.environmentDigest).map(original => {
    const residuals = input.residualGoals?.filter(goal => canonicalMathJson(goal.consumer) === canonicalMathJson(original.consumer) &&
      Buffer.byteLength(goal.goalText) <= 16000);
    const views = residuals?.flatMap(residual => knowledgeResidualViews(residual.goalText).map(view => ({ view,
      target: { ...original, source: 'residual-goal' as const, query: '', goal: view.display,
        diagnostic: { authority: residual.authority, sourceDigest: residual.sourceDigest, environmentDigest: residual.environmentDigest,
          toolIdentity: residual.toolIdentity, artifact: residual.artifact, file: residual.file, line: residual.line, column: residual.column } } })));
    const independent: { target: SearchTarget; view?: KnowledgeResidualView }[] = views?.length ? views : [{ target: original }];
    // Stable selection prevents case order or diagnostic message order deciding coverage.
    const unique = new Map(independent.map(item => [mathDigest(canonicalMathJson(item.target)), item] as const));
    const items = [...unique].sort(([a], [b]) => a.localeCompare(b)).map(([inputDigest, { target, view }]) => {
      const bounded = Buffer.byteLength(target.query) <= 4000 && Buffer.byteLength(target.goal ?? '') <= 16000;
      return { target, view, inputDigest, bounded, searchable: Boolean(bounded && (target.query.trim() || target.goal?.trim())),
        requestIndex: undefined as number | undefined };
    });
    const omissions = input.residualOmissions?.filter(item => canonicalMathJson(item.consumer) === canonicalMathJson(original.consumer))
      .map(({ count, reason }) => ({ count, reason })) ?? [];
    return { items, omissions, inputDigest: items.length === 1 ? items[0]!.inputDigest : mathDigest(canonicalMathJson(items.map(item => item.inputDigest))) };
  });
  const requests: { query: string; goal?: string }[] = [];
  // Round robin across consumers, within the existing eight-request batch budget.
  for (let index = 0; index < Math.max(0, ...targets.map(target => target.items.length)); index++) {
    for (const group of targets) {
      const item = group.items[index];
      if (!item?.searchable || requests.length >= 8) continue;
      item.requestIndex = requests.length;
      requests.push({ query: item.target.query, goal: item.target.goal });
    }
  }
  const searches = requests.length ? searchTheoremKnowledgeRequests(knowledge.base, requests, { limit: candidateLimit,
    displayGrouping: 'exact-interface', environmentDigest: input.environmentDigest,
    problemReceiptDigest: problem.receiptDigest }) : [];
  const findingSearches = requests.length ? searchKnowledgeRouteFindingRequests(knowledge.base, requests, { limit: 2,
    environmentDigest: input.environmentDigest, problemReceiptDigest: problem.receiptDigest }) : [];
  return targets.flatMap(({ items, omissions, inputDigest }) => {
    const { target, bounded } = items[0]!;
    const results = items.flatMap(item => item.requestIndex !== undefined ? [searches[item.requestIndex]!] : []);
    const hits = results.flatMap(result => result.hits);
    // Include a first candidate from each case before adding alternatives for a single case.
    const diverse = Array.from({ length: candidateLimit }, (_, rank) => results.flatMap(result => result.hits[rank] ? [result.hits[rank]!] : [])).flat();
    const candidates = [...new Map(diverse.map(hit => [hit.id, hit])).values()].slice(0, candidateLimit).map(hit => ({ id: hit.id, name: hit.name, kind: hit.kind,
      typeKind: hit.typeKind, typePreview: hit.typePreview, typeTruncated: hit.typeTruncated,
      dependencyCoverage: hit.dependencyCoverage, environmentMatch: hit.environmentMatch,
      consumers: hit.consumers,
      problemReceiptMatch: hit.problemReceiptMatch, versionCount: hit.versionCount,
      declarationVariantCount: hit.declarationVariantCount }));
    const routeFindings = [...new Map(items.flatMap(item => item.requestIndex !== undefined ? findingSearches[item.requestIndex]!.hits : [])
      .map(hit => [hit.id, hit])).values()].slice(0, 2);
    const residualSearches = items.flatMap(item => item.view && item.target.diagnostic ? [{ inputDigest: item.inputDigest,
      diagnostic: item.target.diagnostic, ...(item.view.caseLabel ? { caseLabel: item.view.caseLabel } : {}),
      localContext: item.view.localContext, ...(item.view.fallbackReason ? { fallbackReason: item.view.fallbackReason } : {}),
      searched: item.requestIndex !== undefined,
      candidateIds: item.requestIndex !== undefined ? searches[item.requestIndex]!.hits.map(hit => hit.id) : [] }] : []);
    const residualCoverage = residualSearches.length || omissions.length ? { total: residualSearches.length,
      searched: residualSearches.filter(item => item.searched).length,
      omittedForRequestBudget: residualSearches.filter(item => !item.searched).length, omittedDetailsForBytes: 0,
      omittedDiagnosticsAtReader: omissions.reduce((sum, item) => sum + item.count, 0) } : undefined;
    const residualDetails = residualSearches.map(({ diagnostic: _diagnostic, ...item }) => item);
    const packet = { schema: 'theorem-os.knowledge-context.v1', catalogDigest: knowledge.digest,
      evidence: 'recorded-not-replayed', requiresFreshCheck: true,
      preferenceEvidence: 'recorded-metadata-not-applicability', consumer: target.consumer,
      searchInputDigest: inputDigest, searchSource: target.source,
      ...(target.diagnostic ? { diagnostic: target.diagnostic } : {}),
      status: results.length ? 'searched' : 'input-not-searched',
      ...(!results.length ? { reason: bounded ? 'empty-input' : 'input-too-large' } : {}),
      candidateGrouping: 'exact-name-type-typeKind-display-only',
      variantCountEvidence: 'distinct-recorded-declarations-not-interchangeable',
      totalMatches: results.length === 1 ? results[0]!.total : new Set(hits.map(hit => hit.id)).size,
      totalInterfaces: results.length === 1 ? results[0]!.totalInterfaces : undefined, candidateLimit, omittedForBytes: 0, candidates,
      ...(residualCoverage ? { residualCoverage, residualSearches: residualDetails } : {}),
      routeFindings };
    let text = title + JSON.stringify(packet);
    while (Buffer.byteLength(text) > maxSectionBytes && residualDetails.length) {
      residualDetails.pop(); residualCoverage!.omittedDetailsForBytes++;
      text = title + JSON.stringify(packet);
    }
    while (Buffer.byteLength(text) > maxSectionBytes && candidates.length) {
      candidates.pop(); packet.omittedForBytes++;
      text = title + JSON.stringify(packet);
    }
    while (Buffer.byteLength(text) > maxSectionBytes && routeFindings.length) {
      routeFindings.pop(); text = title + JSON.stringify(packet);
    }
    const sectionId = `knowledge:${inputDigest}`;
    return Buffer.byteLength(text) <= maxSectionBytes
      ? [{ id: sectionId, kind: 'sources' as const, text, priority: 7, knowledge: { sectionId,
        catalogDigest: knowledge.digest, searchInputDigest: inputDigest, consumer: target.consumer,
        searchSource: target.source, ...(target.diagnostic ? { diagnostic: target.diagnostic } : {}),
        ...(residualSearches.length ? { residualSearches } : {}),
        ...(omissions.length ? { residualOmissions: omissions } : {}),
        searchCandidateIds: [...new Set(hits.map(hit => hit.id))],
        candidateIds: candidates.map(item => item.id), routeFindingIds: routeFindings.map(item => item.id) } }] : [];
  });
}
