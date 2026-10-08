import type {
  MathAssignmentRequest,
  MathRunBinding,
  RuntimeMathAssignment,
} from "../common/types/team/mathRuntimeContracts";
import type { ProjectGitResearchTeamAssignmentReceipt } from "../project-git/ProjectGitService";
import type { MathResearchWorkflowState } from "./mathResearchWorkflow";
import { decodeMathAssignmentJournal, normalizeRuntimeMathAssignment } from "./mathAssignmentJournal";
import { selectMathV2IntegrationDelivery } from "./mathIntegrationSelector";
import { buildMathResearchGraph, mathResearchNoteReference } from "./mathResearchGraph";
import { canonicalMathJson, mathDigest } from "./mathRuntimeIo";
import { parseMathArtifactReference } from "./mathPublicWire";

type ResearchQuestion = NonNullable<MathAssignmentRequest['researchQuestion']>;
type Receipt = ProjectGitResearchTeamAssignmentReceipt;
type Note = MathResearchWorkflowState['notebook'][number];
export type MathAssignmentResearchQuestion = Readonly<{
  questionId: string;
  evidenceVersion: string;
  statement: string;
  assumptions: readonly string[];
  targetConnection: string;
  producerAssignmentIds: readonly string[];
  consumerAssignmentIds: readonly string[];
  status: 'active' | 'reported' | 'blocked' | 'inactive';
  mathematicallyVerified: false;
  reports: readonly Readonly<{
    assignmentId: string;
    deliveryId: string;
    summary: string;
    evidenceRefs: readonly string[];
  }>[];
}>;
const normalizedText = (value: string) => value.normalize('NFC').replace(/\s+/gu, ' ').trim();
const normalizedQuestion = (question: ResearchQuestion) => ({
  statement: normalizedText(question.statement),
  assumptions: question.assumptions.map(normalizedText).toSorted(),
  targetConnection: normalizedText(question.targetConnection),
});

/** Exact normalized identity; this does not infer mathematical equivalence. */
export function mathAssignmentResearchQuestionId(binding: MathRunBinding, question: ResearchQuestion): string {
  return `question_${mathDigest(
    canonicalMathJson({
      runId: binding.runId,
      bindingDigest: mathDigest(canonicalMathJson(binding)),
      problemId: binding.problem?.problemId ?? null,
      statementHash: binding.problem?.statementHash ?? null,
      question: normalizedQuestion(question),
    })
  )}`;
}

/** Frozen inputs and their source commit define evidence; private edits are never read. */
export function mathAssignmentResearchEvidenceVersion(
  request: Pick<MathAssignmentRequest, 'inputs'>,
  baseCommit: string
): string {
  const inputs = (request.inputs ?? []).flatMap((input) => {
    if ('artifactRef' in input) {
      const reference = parseMathArtifactReference(input.artifactRef);
      if (reference?.scheme === 'math-artifact' && reference.artifactId.startsWith('math-worked-')) return [];
      return [canonicalMathJson({ artifactRef: input.artifactRef })];
    }
    return [canonicalMathJson({ path: input.path })];
  });
  return mathDigest(canonicalMathJson({ baseCommit, inputs: [...new Set(inputs)].toSorted() }));
}

const integrity = (): never => {
  throw new Error('math_research_graph_integrity');
};

/** Read-only projection of validated assignment WAL records, without another state store. */
export function buildMathAssignmentResearchGraph(binding: MathRunBinding, receipts: readonly Receipt[]) {
  const bindingDigest = mathDigest(canonicalMathJson(binding));
  const assignments = new Map<string, RuntimeMathAssignment>();
  const seen = new Set<string>();
  let teamId: string | undefined;
  for (const receipt of receipts) {
    const decoded = decodeMathAssignmentJournal(receipt);
    if (seen.has(decoded.assignmentId) || (teamId !== undefined && teamId !== decoded.teamId)) integrity();
    seen.add(decoded.assignmentId);
    teamId = decoded.teamId;
    if (decoded.version === 1) {
      if (decoded.state !== 'integrated' && decoded.state !== 'superseded') integrity();
      continue;
    }
    const assignment = normalizeRuntimeMathAssignment(decoded.assignment);
    if (assignment.runId !== binding.runId || assignment.bindingDigest !== bindingDigest) integrity();
    for (const input of assignment.request.inputs ?? []) {
      if ('artifactRef' in input) {
        const reference = parseMathArtifactReference(input.artifactRef);
        if (reference?.scheme !== 'math-artifact' || reference.runId !== binding.runId) integrity();
      }
    }
    assignments.set(decoded.assignmentId, assignment);
  }
  const groups = new Map<
    string,
    {
      questionId: string;
      evidenceVersion: string;
      question: ResearchQuestion;
      producers: Set<string>;
      consumers: Set<string>;
      statuses: Set<MathAssignmentResearchQuestion['status']>;
      evidenceRefs: Set<string>;
      reports: Array<MathAssignmentResearchQuestion['reports'][number]>;
    }
  >();
  for (const receipt of receipts) {
    const assignment = assignments.get(receipt.assignmentId);
    if (!assignment?.request.researchQuestion) continue;
    const questionId = mathAssignmentResearchQuestionId(binding, assignment.request.researchQuestion);
    const evidenceVersion = mathAssignmentResearchEvidenceVersion(assignment.request, assignment.baseCommit);
    const key = `${questionId}:${evidenceVersion}`;
    const group = groups.get(key) ?? {
      questionId,
      evidenceVersion,
      question: normalizedQuestion(assignment.request.researchQuestion),
      producers: new Set<string>(),
      consumers: new Set<string>(),
      statuses: new Set<MathAssignmentResearchQuestion['status']>(),
      evidenceRefs: new Set<string>(),
      reports: [],
    };
    groups.set(key, group);
    group.producers.add(receipt.assignmentId);
    for (const id of assignment.request.consumerAssignmentIds ?? []) {
      if (id === receipt.assignmentId || assignments.get(id)?.request.kind !== 'formalize') integrity();
      group.consumers.add(id);
    }
    for (const input of assignment.request.inputs ?? [])
      if ('artifactRef' in input) group.evidenceRefs.add(input.artifactRef);
    const delivery = receipt.delivery
      ? selectMathV2IntegrationDelivery(receipt, receipt.delivery.deliveryId, {
          expectedRunId: binding.runId,
          expectedBindingDigest: bindingDigest,
        }).delivery.delivery
      : undefined;
    if (delivery) {
      for (const evidence of delivery.evidence) group.evidenceRefs.add(evidence.ref);
      group.reports.push({
        assignmentId: receipt.assignmentId,
        deliveryId: receipt.delivery!.deliveryId,
        summary: delivery.summary,
        evidenceRefs: delivery.evidence.map((evidence) => evidence.ref),
      });
    }
    group.statuses.add(
      receipt.state === 'superseded' || receipt.supersessionPending || receipt.budgetCancellation
        ? 'inactive'
        : delivery?.status === 'blocked'
          ? 'blocked'
          : delivery?.status === 'completed'
            ? 'reported'
            : receipt.state === 'integrated' || receipt.integration
              ? 'inactive'
              : 'active'
    );
  }
  const questions: MathAssignmentResearchQuestion[] = [...groups.values()]
    .map((group) => ({
      questionId: group.questionId,
      evidenceVersion: group.evidenceVersion,
      statement: group.question.statement,
      assumptions: group.question.assumptions,
      targetConnection: group.question.targetConnection,
      producerAssignmentIds: [...group.producers].toSorted(),
      consumerAssignmentIds: [...group.consumers].toSorted(),
      status: (['active', 'reported', 'blocked', 'inactive'] as const).find((status) => group.statuses.has(status))!,
      mathematicallyVerified: false as const,
      reports: [...group.reports].toSorted((a, b) => a.assignmentId.localeCompare(b.assignmentId)),
    }))
    .toSorted((a, b) => a.questionId.localeCompare(b.questionId) || a.evidenceVersion.localeCompare(b.evidenceVersion));
  const notebooks = new Map<string, Note[]>();
  const consumerDependencies = new Map<string, string[]>();
  for (const question of questions) {
    const notebook = notebooks.get(question.questionId) ?? [];
    notebook.push({
      key: question.evidenceVersion,
      author: question.producerAssignmentIds[0]!,
      routeRevision: 0,
      kind: 'conjecture',
      summary: question.statement,
      statement: question.statement,
      targetConnection: question.targetConnection,
      assessment: 'unverified',
      evidenceRefs: [...groups.get(`${question.questionId}:${question.evidenceVersion}`)!.evidenceRefs].toSorted(),
    });
    notebooks.set(question.questionId, notebook);
    for (const consumer of question.consumerAssignmentIds) {
      const dependencies = consumerDependencies.get(consumer) ?? [];
      dependencies.push(mathResearchNoteReference(question.questionId, question.evidenceVersion));
      consumerDependencies.set(consumer, dependencies);
    }
  }
  for (const [consumer, dependencies] of consumerDependencies) {
    const assignment = assignments.get(consumer)!;
    notebooks.set(consumer, [
      {
        key: 'proof_obligation',
        author: assignment.request.targetSlotId,
        routeRevision: 0,
        kind: 'dependency',
        summary: assignment.request.objective,
        assessment: 'unverified',
        evidenceRefs: [],
        dependsOn: dependencies,
      },
    ]);
  }
  const graph = buildMathResearchGraph([...notebooks].map(([assignmentId, notebook]) => ({ assignmentId, notebook })));
  return { ...graph, authority: 'organization' as const, solverReady: false as const, questions };
}
