import { canonicalMathJson, mathDigest } from '../math/mathRuntimeIo';
import type { CooperationState } from './cooperation';
import type { ContextSection } from './contextCompiler';
import { originalGoalTaskFocus } from './modules/search';
import type { SolverProblem } from './problem';
import { isAdvisoryTask, isFinalCandidateReview, taskVersion, type CooperativeAction, type CooperativeTask } from './tasks';
import type { TheoremKnowledgeBase } from './theoremKnowledge';
import { knowledgeTypeExpression, searchTheoremKnowledge } from './theoremKnowledgeSearch';

/** Validated once when the run pins its catalog; no archived proof sources enter task hints. */
export type KnowledgeContextSnapshot = Readonly<{
  digest: string;
  base: Pick<TheoremKnowledgeBase, 'entries' | 'evidence'>;
}>;

type SearchTarget = {
  consumer: { taskId?: string; taskDigest?: string; theoremName?: string; proofPath?: string };
  source: 'closed-task-type' | 'frozen-source-header' | 'research-objective';
  query: string; goal?: string;
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

function searchTargets(problem: SolverProblem, cooperation?: CooperationState, action?: CooperativeAction): SearchTarget[] {
  if (action?.kind === 'task') {
    const target = taskTarget(problem, action.task);
    return target ? [target] : [];
  }
  if (action && action.kind !== 'lead' && action.kind !== 'solve') return [];
  if (action?.kind === 'lead' && cooperation?.tasks.length) {
    const focus = originalGoalTaskFocus(cooperation.tasks, cooperation.groups);
    const targets = cooperation.tasks.filter(node => focus.frontier.has(node.task.id))
      .flatMap(node => { const target = taskTarget(problem, node.task); return target ? [target] : []; });
    if (targets.length) return targets.slice(0, maxTargets);
  }
  return problem.targets.flatMap(target => {
    const search = originalTarget(problem, target); return search ? [search] : [];
  }).slice(0, maxTargets);
}

/** Search exact assigned inputs; hits never become task dependencies, checks or accepted proofs. */
export function knowledgeContextSections(input: {
  problem: SolverProblem; cooperation?: CooperationState; action?: CooperativeAction;
  knowledge: KnowledgeContextSnapshot; environmentDigest?: string;
}): ContextSection[] {
  const { problem, knowledge } = input;
  return searchTargets(problem, input.cooperation, input.action).flatMap(target => {
    const inputDigest = mathDigest(canonicalMathJson(target));
    const bounded = Buffer.byteLength(target.query) <= 4000 && Buffer.byteLength(target.goal ?? '') <= 16000;
    const search = bounded && (target.query.trim() || target.goal?.trim())
      ? searchTheoremKnowledge(knowledge.base, target.query, { goal: target.goal, limit: candidateLimit,
        environmentDigest: input.environmentDigest, problemReceiptDigest: problem.receiptDigest }) : undefined;
    const candidates = search?.hits.map(hit => ({ id: hit.id, name: hit.name, kind: hit.kind,
      typeKind: hit.typeKind, typePreview: hit.typePreview, typeTruncated: hit.typeTruncated,
      dependencyCoverage: hit.dependencyCoverage, environmentMatch: hit.environmentMatch,
      problemReceiptMatch: hit.problemReceiptMatch, versionCount: hit.versionCount })) ?? [];
    const packet = { schema: 'theorem-os.knowledge-context.v1', catalogDigest: knowledge.digest,
      evidence: 'recorded-not-replayed', requiresFreshCheck: true,
      preferenceEvidence: 'recorded-metadata-not-applicability', consumer: target.consumer,
      searchInputDigest: inputDigest, searchSource: target.source,
      status: search ? 'searched' : 'input-not-searched',
      ...(!search ? { reason: bounded ? 'empty-input' : 'input-too-large' } : {}),
      totalMatches: search?.total, candidateLimit, omittedForBytes: 0, candidates };
    let text = title + JSON.stringify(packet);
    while (Buffer.byteLength(text) > maxSectionBytes && candidates.length) {
      candidates.pop(); packet.omittedForBytes++;
      text = title + JSON.stringify(packet);
    }
    return Buffer.byteLength(text) <= maxSectionBytes
      ? [{ id: `knowledge:${inputDigest}`, kind: 'sources' as const, text, priority: 7 }] : [];
  });
}
