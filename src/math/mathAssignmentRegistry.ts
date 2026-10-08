import crypto from 'node:crypto';
import fs from 'node:fs';
import path from 'node:path';
import type { MathRunBinding, RuntimeMathAssignment } from "../common/types/team/mathRuntimeContracts";
import type { ProtocolIssue } from "../common/types/team/mathematicsTeam";
import type {
  ProjectGitResearchTeamAssignmentReceipt,
  ProjectGitResearchTeamAssignmentRequest,
} from "../project-git/ProjectGitService";
import { normalizeRuntimeMathAssignment } from "./mathAssignmentJournal";
import { hasMathV2BlockedDelivery } from "./mathIntegrationSelector";
import {
  assertMathCanonicalPath,
  isMathPathWithin,
  mathAssignmentSourceRoot,
  normalizeMathRunBinding,
} from "./mathRunBinding";
import {
  mathPathsOverlap,
  MathWireValidationError,
  normalizedMathObjective,
  normalizeMathAssignment,
  parseMathArtifactReference,
} from "./mathPublicWire";
import { canonicalMathJson, mathDigest, withMathRuntimeLease } from "./mathRuntimeIo";
import {
  buildMathAssignmentResearchGraph,
  mathAssignmentResearchEvidenceVersion,
  mathAssignmentResearchQuestionId,
} from "./mathAssignmentResearchGraph";

type Receipt = ProjectGitResearchTeamAssignmentReceipt;
type RegistryPorts = Readonly<{
  readAssignments: () => readonly Receipt[];
  recordAssignment: (request: ProjectGitResearchTeamAssignmentRequest) => Receipt;
  currentCommit: () => string;
  assertReadPath: (relativePath: string, commit: string) => void;
  assertWritePath: (relativePath: string) => void;
  grantArtifacts: (artifactId: string) => Promise<readonly string[]>;
  predecessorEnded: (receipt: Receipt) => Promise<boolean>;
  /** Optional canonical ancestry check used when a repair starts from C1. */
  isCommitAncestor?: (ancestor: string, descendant: string) => boolean;
  supersedeAssignment?: (input: Readonly<{ receipt: Receipt; winnerAssignmentId: string; reason: string }>) => void;
}>;
const terminal = (receipt: Receipt): boolean => receipt.state === 'integrated' || receipt.state === 'superseded';
const reject = (field: string, code: ProtocolIssue['code']): never => {
  throw new MathWireValidationError([
    { path: field, code, message: 'Assignment conflicts with its runtime binding or ownership.' },
  ]);
};

/** Cross-process ownership and lineage transaction over the existing ProjectGit assignment WAL. */
export class MathAssignmentRegistry {
  private readonly binding: MathRunBinding;
  private readonly bindingDigest: string;
  private readonly runRoot: string;

  constructor(
    private readonly options: Readonly<{
      binding: MathRunBinding;
      teamId: string;
      workerIds: ReadonlySet<string>;
      flockExecutable: string;
      ports: RegistryPorts;
      assertBinding: () => void;
    }>
  ) {
    this.binding = normalizeMathRunBinding(options.binding);
    this.bindingDigest = mathDigest(canonicalMathJson(this.binding));
    this.runRoot = path.dirname(this.binding.artifactStoreRoot);
    if (
      !/^[A-Za-z0-9_-]{1,128}$/u.test(options.teamId) ||
      path.basename(this.binding.artifactStoreRoot) !== 'artifacts' ||
      path.basename(this.runRoot) !== this.binding.runId ||
      path.basename(path.dirname(this.runRoot)) !== 'runs'
    )
      reject('$', 'integrity');
  }

  private assignment(receipt: Receipt): RuntimeMathAssignment {
    const assignment = normalizeRuntimeMathAssignment(receipt.assignment);
    if (
      receipt.teamId !== this.options.teamId ||
      assignment.runId !== this.binding.runId ||
      assignment.bindingDigest !== this.bindingDigest ||
      receipt.slotId !== assignment.request.targetSlotId ||
      receipt.assignmentId !== assignment.assignmentId ||
      assignment.sourceRootRelative !==
        path
          .relative(this.binding.projectRoot, mathAssignmentSourceRoot(this.binding, assignment.assignmentId))
          .split(path.sep)
          .join('/') ||
      assignment.draftRoot !== path.join(this.runRoot, 'drafts', `A_${mathDigest(assignment.assignmentId)}`)
    )
      reject('$', 'integrity');
    return assignment;
  }

  async prepare(value: unknown): Promise<Receipt> {
    const request = normalizeMathAssignment(value, this.options.workerIds);
    const payloadHash = mathDigest(canonicalMathJson(request));
    this.options.assertBinding();
    assertMathCanonicalPath(this.runRoot);
    return withMathRuntimeLease(
      {
        lockPath: path.join(this.runRoot, 'math-run.lock'),
        flockExecutable: this.options.flockExecutable,
      },
      async (lease) => {
        this.options.assertBinding();
        const receipts = this.options.ports.readAssignments();
        const assignments = new Map<string, RuntimeMathAssignment>();
        for (const receipt of receipts) {
          if (receipt.teamId !== this.options.teamId || assignments.has(receipt.assignmentId)) reject('$', 'integrity');
          if (receipt.schema === 'deepscientist.research_team_assignment.v1') {
            if (!terminal(receipt)) reject('$', 'conflict');
            continue;
          }
          assignments.set(receipt.assignmentId, this.assignment(receipt));
        }
        const replays = receipts.filter((receipt) => {
          const assignment = assignments.get(receipt.assignmentId);
          return (
            assignment?.request.targetSlotId === request.targetSlotId &&
            assignment.request.idempotencyKey === request.idempotencyKey
          );
        });
        if (replays.length > 1) reject('$', 'integrity');
        let replayReceipt: Receipt | undefined;
        if (replays.length) {
          if (assignments.get(replays[0].assignmentId)!.payloadHash !== payloadHash)
            reject('idempotencyKey', 'conflict');
          if (!request.predecessorAssignmentId) return replays[0];
          replayReceipt = replays[0];
        }
        let predecessor: RuntimeMathAssignment | undefined;
        let predecessorReceipt: Receipt | undefined;
        let predecessorEnded = true;
        let candidateRejected = false;
        let explicitlyBlocked = false;
        if (request.predecessorAssignmentId) {
          const receipt = receipts.find((candidate) => candidate.assignmentId === request.predecessorAssignmentId);
          predecessor = assignments.get(request.predecessorAssignmentId);
          predecessorReceipt = receipt;
          if (!receipt || !predecessor) reject('predecessorAssignmentId', 'not_found');
          if (predecessor.request.kind !== request.kind) reject('predecessorAssignmentId', 'conflict');
          candidateRejected = receipt.integration?.verification?.disposition === 'candidate_rejected';
          explicitlyBlocked = hasMathV2BlockedDelivery(receipt);
          // A validated exact replay with a terminal predecessor already owns
          // this slot. Its running successor must not be mistaken for the old
          // execution; unfinished retirement still requires the fresh check.
          predecessorEnded =
            Boolean(replayReceipt && terminal(receipt)) || (await this.options.ports.predecessorEnded(receipt));
          if (
            (!terminal(receipt) && !candidateRejected && !explicitlyBlocked) ||
            [...assignments.values()].some(
              (assignment) =>
                assignment.request.predecessorAssignmentId === request.predecessorAssignmentId &&
                assignment.request.idempotencyKey !== request.idempotencyKey
            )
          )
            reject('predecessorAssignmentId', 'conflict');
        }
        const successorReason = explicitlyBlocked
          ? 'The prior assignment delivered an explicit blocker; the host opened a continuation with its frozen progress.'
          : 'A completed source verification rejected the prior delivery; the host opened a repair successor.';
        // A rejected request must not reserve a second owner while the previous
        // Worker still has authority. A retry can reserve once that authority ends.
        if (predecessorReceipt && !predecessorEnded) reject('predecessorAssignmentId', 'conflict');
        const retirePredecessor = (winnerAssignmentId: string): void => {
          if (!predecessorReceipt || terminal(predecessorReceipt)) return;
          if (!this.options.ports.supersedeAssignment) reject('predecessorAssignmentId', 'conflict');
          this.options.ports.supersedeAssignment({
            receipt: predecessorReceipt,
            winnerAssignmentId,
            reason: successorReason,
          });
          const retired = this.options.ports
            .readAssignments()
            .find((receipt) => receipt.assignmentId === predecessorReceipt!.assignmentId);
          if (
            !retired ||
            retired.state !== 'superseded' ||
            retired.supersession?.winnerAssignmentId !== winnerAssignmentId
          )
            reject('predecessorAssignmentId', 'integrity');
        };
        if (replayReceipt) {
          retirePredecessor(replayReceipt.assignmentId);
          return replayReceipt;
        }
        // Validate only new reservations. Exact retries retain their original
        // authorization even if a consumer has subsequently completed or moved on.
        for (const consumerId of request.consumerAssignmentIds ?? []) {
          const consumer = receipts.find((receipt) => receipt.assignmentId === consumerId);
          const assignment = assignments.get(consumerId);
          if (!consumer || !assignment) reject('consumerAssignmentIds', 'not_found');
          const blocked = hasMathV2BlockedDelivery(consumer);
          if (
            assignment.request.kind !== 'formalize' ||
            consumer.slotId === request.targetSlotId ||
            consumer.state === 'superseded' ||
            consumer.supersessionPending ||
            consumer.budgetCancellation ||
            (!blocked && (consumer.state === 'integrated' || consumer.delivery || consumer.integration))
          )
            reject('consumerAssignmentIds', 'conflict');
        }
        const baseCommit = this.options.ports.currentCommit();
        if (!/^(?:[a-f0-9]{40}|[a-f0-9]{64})$/u.test(baseCommit)) reject('$', 'integrity');
        const executionBaseCommit = predecessorReceipt?.integration?.mergedCommit ?? baseCommit;
        if (!/^(?:[a-f0-9]{40}|[a-f0-9]{64})$/u.test(executionBaseCommit)) reject('$', 'integrity');
        if (
          executionBaseCommit !== this.binding.baseCommit &&
          this.options.ports.isCommitAncestor &&
          !this.options.ports.isCommitAncestor(this.binding.baseCommit, executionBaseCommit)
        ) {
          reject('predecessorAssignmentId', 'integrity');
        }
        if (
          this.options.ports.isCommitAncestor &&
          !this.options.ports.isCommitAncestor(executionBaseCommit, baseCommit)
        ) {
          reject('predecessorAssignmentId', 'integrity');
        }
        const sharedPaths = request.sharedWritePaths ?? [];
        if (request.researchQuestion) {
          const questionId = mathAssignmentResearchQuestionId(this.binding, request.researchQuestion);
          const evidenceVersion = mathAssignmentResearchEvidenceVersion(request, executionBaseCommit);
          const graph = buildMathAssignmentResearchGraph(this.binding, receipts);
          if (
            graph.questions.some(
              (question) =>
                question.questionId === questionId &&
                question.evidenceVersion === evidenceVersion &&
                (question.status === 'active' || question.status === 'reported')
            )
          )
            reject('researchQuestion', 'conflict');
        }
        for (const [index, relative] of sharedPaths.entries()) {
          const absolute = path.resolve(this.binding.projectRoot, relative);
          assertMathCanonicalPath(absolute);
          if (!this.binding.allowedWriteRoots.some((root) => isMathPathWithin(root, absolute)))
            reject('sharedWritePaths', 'unauthorized');
          this.options.ports.assertWritePath(relative);
          if (!fs.statSync(absolute).isFile()) reject('sharedWritePaths', 'invalid');
          if (sharedPaths.slice(index + 1).some((other) => mathPathsOverlap(relative, other)))
            reject('sharedWritePaths', 'conflict');
        }
        for (const receipt of receipts.filter((candidate) => !terminal(candidate))) {
          const active = assignments.get(receipt.assignmentId)!;
          const isDesignatedRepairPredecessor =
            request.predecessorAssignmentId === receipt.assignmentId && (candidateRejected || explicitlyBlocked);
          if (receipt.slotId === request.targetSlotId && !isDesignatedRepairPredecessor)
            reject('targetSlotId', 'conflict');
          if (
            !isDesignatedRepairPredecessor &&
            // Structured research uses exact question/evidence identity above;
            // task wording alone cannot collapse distinct hypotheses or versions.
            !(
              request.kind === 'research' &&
              active.request.kind === 'research' &&
              request.researchQuestion &&
              active.request.researchQuestion
            ) &&
            normalizedMathObjective(active.request.objective) === normalizedMathObjective(request.objective) &&
            (request.kind !== 'research' ||
              active.request.kind !== 'research' ||
              canonicalMathJson(
                (active.request.inputs ?? [])
                  .map((input) => ('artifactRef' in input ? input.artifactRef : input.path))
                  .sort()
              ) ===
                canonicalMathJson(
                  (request.inputs ?? [])
                    .map((input) => ('artifactRef' in input ? input.artifactRef : input.path))
                    .sort()
                ))
          )
            reject('objective', 'conflict');
          const owned = [...(active.request.sharedWritePaths ?? []), active.sourceRootRelative];
          if (sharedPaths.some((relative) => owned.some((other) => mathPathsOverlap(relative, other))))
            reject('sharedWritePaths', 'conflict');
        }
        const grants = new Set<string>();
        for (const input of request.inputs ?? []) {
          if ('path' in input) {
            assertMathCanonicalPath(path.resolve(this.binding.projectRoot, input.path));
            this.options.ports.assertReadPath(input.path, executionBaseCommit);
          } else {
            const ref = parseMathArtifactReference(input.artifactRef);
            if (ref?.scheme !== 'math-artifact' || ref.runId !== this.binding.runId)
              return reject('inputs', 'unauthorized');
            for (const grant of await this.options.ports.grantArtifacts(ref.artifactId)) grants.add(grant);
          }
        }
        const assignmentId = crypto.randomUUID();
        const sourceRoot = mathAssignmentSourceRoot(this.binding, assignmentId);
        assertMathCanonicalPath(sourceRoot);
        if (!isMathPathWithin(this.binding.projectRoot, sourceRoot)) reject('$', 'integrity');
        const assignment = normalizeRuntimeMathAssignment({
          schema: 'deepscientist.math.assignment.v2',
          runId: this.binding.runId,
          bindingDigest: this.bindingDigest,
          assignmentId,
          scopeId: predecessor?.scopeId ?? crypto.randomUUID(),
          baseCommit: executionBaseCommit,
          request,
          payloadHash,
          sourceRootRelative: path.relative(this.binding.projectRoot, sourceRoot).split(path.sep).join('/'),
          draftRoot: path.join(this.runRoot, 'drafts', `A_${mathDigest(assignmentId)}`),
          artifactGrants: [...grants].toSorted(),
        });
        this.options.assertBinding();
        lease.assertHeld();
        // The reservation becomes durable before a worktree, draft directory or Core turn is created.
        const recorded = this.options.ports.recordAssignment({
          schema: 'deepscientist.research_team_assignment.v2',
          workspace: this.binding.workspace,
          teamId: this.options.teamId,
          slotId: request.targetSlotId,
          assignmentId,
          assignment,
          state: 'prepared',
        });
        retirePredecessor(assignmentId);
        return recorded;
      }
    );
  }
}
