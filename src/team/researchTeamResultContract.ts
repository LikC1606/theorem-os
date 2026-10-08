/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

import { RESEARCH_TEAM_RESULT_SCHEMA } from "../common/types/team/researchTeamContracts";
import {
  MATH_EVIDENCE_DELTA_KINDS,
  MATH_FAILURE_CATEGORIES,
  MATH_INFRA_STATUSES,
  MATH_RESEARCH_PROBE_KINDS,
  MATH_ROUTE_DISPOSITIONS,
} from "../common/types/team/mathematicsTeam";
import type { ResearchTeamToolCapability } from "./toolCapability";
import type { ResearchTeamMcpAction } from "../common/types/team/researchTeamMcp";
import { isMathLiteRunEnvironment } from "../math/mathRunInputs";

type MathematicsLaneId = 'strategy-exploration' | 'lean-engineering' | 'independent-review';
type MathematicsWorkerResultVariant = 'complete' | 'research-finding' | 'direct-formalization';

const RETRY_NOTE =
  'Repair every validation error in the same Worker solver episode and call deliver again; do not start an outer assignment retry.';
const MATHEMATICS_RESULT_DISPOSITIONS = Object.freeze(['accepted', 'refuted', 'inconclusive', 'blocked']);
export const MATHEMATICS_WORKER_ACTIONS = Object.freeze([
  'compile_patch',
  'add_helper',
  'query_premise',
  'refute_route',
  'request_support',
  'declare_solver_ready',
] as const);
export type MathematicsWorkerAction = (typeof MATHEMATICS_WORKER_ACTIONS)[number];

export function normalizeMathematicsWorkerAction(value: unknown): MathematicsWorkerAction | undefined {
  if (value === undefined) return undefined;
  if (
    typeof value !== 'string' ||
    value.length > 64 ||
    !MATHEMATICS_WORKER_ACTIONS.includes(value as MathematicsWorkerAction)
  ) {
    throw new TypeError('Mathematics Worker action must be one bounded canonical action');
  }
  return value as MathematicsWorkerAction;
}
const MATHEMATICS_PROGRESS_ENUMS = Object.freeze({
  disposition: MATHEMATICS_RESULT_DISPOSITIONS,
  'math.routeDisposition': MATH_ROUTE_DISPOSITIONS,
  'math.infraStatus': MATH_INFRA_STATUSES,
  'math.evidenceDelta.kind': MATH_EVIDENCE_DELTA_KINDS,
});
const MATHEMATICS_RUNTIME_SHELL =
  'schema, workflowId, laneId, executionMode, producedAt, git.projectRoot, git.baseCommit';

/** Error-local help for the active v1 wire, not a second assignment contract. */
export function createMathematicsProtocolHelp(
  action: ResearchTeamMcpAction,
  capability: ResearchTeamToolCapability
): Readonly<Record<string, unknown>> | undefined {
  if (
    capability.profileId !== 'mathematics-research-team' ||
    !capability.allowedActions.includes(action) ||
    (capability.roleKind === 'worker'
      ? !['deliver', 'share', 'read_feedback', 'read_artifact'].includes(action)
      : action === 'deliver')
  ) {
    return undefined;
  }
  const base = { schema: 'deepscientist.math.protocol-help.v1', action };
  if (isMathLiteRunEnvironment(process.env)) {
    if (action === 'share')
      return Object.freeze({
        ...base,
        fields: ['result.summary', 'result.files?', 'result.wait_for_question_ids?', 'target_slot_id?'],
        instruction:
          'Send a self-contained finding immediately without files; attach frozen notes later. For a related active Researcher use target_slot_id. A proof owner may use wait_for_question_ids from read_feedback.research_questions only when all useful work at the current source awaits those producers; [] clears waiting. The host freezes source and an evidence baseline; a new report, ended producer or source change releases the wait.',
      });
    if (action === 'read_feedback')
      return Object.freeze({
        ...base,
        fields: [],
        instruction:
          'Read provisional findings addressed to your current mathematics assignment at a safe tool boundary. Do not poll unchanged feedback.',
      });
    if (action === 'dispatch') {
      return Object.freeze({
        ...base,
        fields: [
          'assignments[].target_slot_id',
          'assignments[].task',
          'assignments[].kind?',
          'assignments[].consumer_assignment_ids?',
          'assignments[].research_question?',
        ],
        instruction:
          'Set kind=research for bounded findings even on a Lean Worker, or kind=formalize for a complete original-target proof on a Lean Worker. For research on a specific gap, supply exact active/blocked proof assignment IDs in consumer_assignment_ids. Omission preserves slot defaults and automatic context. Retry with the same kind and consumers. The host supplies identity, base commit, source scope and verification targets only for formalization.',
      });
    }
    if (action === 'deliver') {
      return Object.freeze({
        ...base,
        fields: ['result.status', 'result.summary', 'result.files?', 'result.blockers?'],
        instruction:
          'Use relative assigned-workspace paths. The host freezes bytes and supplies internal identity. After a sealed delivery error, omit result to replay the host-frozen request; never rewrite a sealed delivery.',
      });
    }
    if (action === 'integrate')
      return Object.freeze({
        ...base,
        fields: ['deliveries[].target_slot_id', 'deliveries[].delivery_id'],
        instruction: 'Copy the actual durable delivery selectors unchanged. Host verifies the original target.',
      });
    if (action === 'status')
      return Object.freeze({
        ...base,
        fields: ['target_slot_ids?'],
        instruction:
          'Omit all fields for one full snapshot. Dispatch only useful independent work when capacity exists.',
      });
  }
  switch (action) {
    case 'dispatch':
      return Object.freeze({
        ...base,
        fields: ['assignments[].target_slot_id', 'assignments[].idempotency_key'],
        task_form: ['task: non-empty text or {objective}', 'base_commit: full Git object ID', 'math: stage context'],
        alternative: 'Use assignment with the existing v1 contract instead of task; never both.',
        math: {
          stages: ['diversify', 'replan', 'formalize', 'review'],
          formalize: 'Requires actual FAST_CHECK, frozen problemContract and exact alignment; do not invent checks.',
          exploration: 'Requires a researchContract or problemContract; choose an advisory Worker.',
        },
        constraints: [
          'Use the injected Worker IDs. One independent assignment per idle Worker.',
          'Artifact work uses a Lean Worker; branch and worktree are runtime-owned.',
          'Preserve the same idempotency key only for an unchanged request.',
        ],
      });
    case 'deliver': {
      const contract = createResearchTeamResultContract(capability);
      return Object.freeze({
        ...base,
        fields: ['result'],
        result: {
          field_naming: 'camelCase',
          required: contract.required,
          ...(contract.one_of ? { one_of: contract.one_of } : {}),
          dispositions: MATHEMATICS_RESULT_DISPOSITIONS,
        },
        instruction:
          'Correct the reported fields using the current assignment resultContract. Keep the same assignment; never fabricate receipts.',
      });
    }
    case 'integrate':
      return Object.freeze({
        ...base,
        fields: ['deliveries[].target_slot_id'],
        exactly_one: ['delivery_id', 'assignment_id', 'result'],
        instruction:
          'Copy the durable integration_item from the Worker delivery unchanged. Do not combine selectors or reconstruct a result.',
      });
    case 'status':
      return Object.freeze({
        ...base,
        optional: ['target_slot_ids: Worker ID list'],
        instruction: 'Omit targets for one snapshot of all Workers. End the turn while work runs.',
      });
    case 'read_artifact':
      return Object.freeze({
        ...base,
        fields: ['artifact_ref', 'offset_bytes?', 'max_bytes?'],
        instruction:
          'Copy an exact math-artifact:// reference from supplied assignment inputs or an acknowledged share. Only same-run solver-visible artifacts authorized for this assignment are readable. Local file paths are not references: read authorized local files with ordinary file tools inside the assigned worktree. If no artifact was supplied, do not invent one.',
      });
    case 'describe':
      return undefined;
  }
}

export function createResearchTeamResultContract(
  capability: ResearchTeamToolCapability
): Readonly<Record<string, unknown>> {
  const isMathematics = capability.profileId === 'mathematics-research-team';
  const laneId = workerLaneId(capability);
  if (isMathematics && capability.roleKind === 'worker' && isMathLiteRunEnvironment(process.env)) {
    return Object.freeze({
      schema: 'deepscientist.math.delivery-intent.v1',
      field_naming: 'camelCase',
      required: Object.freeze(['status=completed|blocked', 'summary']),
      optional: Object.freeze(['files[]', 'blockers[] (required only for blocked)']),
      notes: Object.freeze([
        'File paths are relative to the assigned source root.',
        'The host freezes files and supplies assignment, run, target and source identities.',
        'Only independent original-target verification establishes completion.',
      ]),
    });
  }
  if (isMathematics && capability.roleKind === 'worker' && laneId) {
    return mathematicsWorkerResultContract(laneId);
  }

  const genericOptional = [
    'roleTemplateId',
    'roleKind=generic',
    'roleLabel',
    'executionMode=advisory|artifact; omission means artifact',
    'git.{branch,headCommit} required for artifact and omitted for advisory',
    'inputsUsed[]',
    'outputs[]',
    'limitations[]',
    'nextRecommendation',
    'evidence[].{id,kind,ref,claim,supports}',
    'falsification.{hypothesis,test,outcome,evidenceIds[],reason?}',
    'verification[].{command,status,summary,evidenceIds[]}',
    'artifactPaths[]',
  ];
  return Object.freeze({
    schema: RESEARCH_TEAM_RESULT_SCHEMA,
    field_naming: 'camelCase',
    source_of_truth: 'This object is the sole machine-readable result contract.',
    required: [
      `schema=${RESEARCH_TEAM_RESULT_SCHEMA}`,
      'assignmentId',
      'workflowId',
      'laneId',
      'disposition',
      'summary',
      'git.{projectRoot,baseCommit}',
      'producedAt',
    ],
    optional: isMathematics
      ? [
          'assignmentBinding',
          'math',
          'mathResearchFinding',
          'mathRouteCard',
          'mathNodeReceipt',
          'mathHelperReceipt',
          'localGateReceipt',
          'mathReview',
          'mathCheckpoint',
          'mathLessons[]',
        ]
      : genericOptional,
    ...(isMathematics
      ? {
          worker_variants: Object.freeze({
            'strategy-exploration': mathematicsWorkerResultShape('strategy-exploration'),
            'lean-engineering': mathematicsWorkerResultShape('lean-engineering'),
            'independent-review': mathematicsWorkerResultShape('independent-review'),
          }),
        }
      : {}),
    enums: isMathematics
      ? { disposition: MATHEMATICS_RESULT_DISPOSITIONS }
      : {
          disposition: ['accepted', 'refuted', 'inconclusive', 'blocked'],
          evidence_kind: ['measurement', 'source', 'code', 'review', 'artifact'],
          falsification_outcome: ['survived', 'refuted', 'inconclusive', 'not_run'],
          verification_status: ['passed', 'failed', 'not_run'],
        },
    notes: [
      'Artifact results use the assigned branch and full head commit; advisory results omit delivery identity.',
      ...(isMathematics
        ? [
            'Mathematics assignment identity and derived state must match the durable assignment.',
            'The Lead runs OFFICIAL_GATE on the unchanged reviewed commit.',
          ]
        : []),
      ...(!isMathematics
        ? [
            'Every evidence[].supports value is a JSON boolean.',
            'falsification.reason is required when outcome=not_run.',
          ]
        : []),
      RETRY_NOTE,
    ],
  });
}

function mathematicsWorkerResultContract(
  laneId: MathematicsLaneId,
  variant: MathematicsWorkerResultVariant = 'complete'
): Readonly<Record<string, unknown>> {
  if (variant === 'direct-formalization') {
    return Object.freeze({
      schema: RESEARCH_TEAM_RESULT_SCHEMA,
      lane_id: laneId,
      ...mathematicsWorkerResultShape(laneId, variant),
    });
  }
  return Object.freeze({
    schema: RESEARCH_TEAM_RESULT_SCHEMA,
    field_naming: 'camelCase',
    source_of_truth: 'This object is the sole machine-readable result contract.',
    lane_id: laneId,
    ...mathematicsWorkerResultShape(laneId, variant),
  });
}

export function createMathematicsWorkerResultContract(
  laneId: string,
  variant: MathematicsWorkerResultVariant = 'complete'
): Readonly<Record<string, unknown>> {
  if (!['strategy-exploration', 'lean-engineering', 'independent-review'].includes(laneId)) {
    throw new TypeError(`Unknown Mathematics Worker lane: ${laneId}`);
  }
  return mathematicsWorkerResultContract(laneId as MathematicsLaneId, variant);
}

function mathematicsWorkerResultShape(
  laneId: MathematicsLaneId,
  variant: MathematicsWorkerResultVariant = 'complete'
): Readonly<Record<string, unknown>> {
  if (laneId === 'strategy-exploration') {
    if (variant === 'research-finding') return mathematicsResearchFindingResultShape();
    return Object.freeze({
      required: ['assignmentId', 'summary'],
      one_of: Object.freeze([
        Object.freeze({ name: 'surviving_route_candidate', required: ['mathRouteCard'] }),
        Object.freeze({ name: 'research_finding', required: ['mathResearchFinding'] }),
        Object.freeze({ name: 'resumable_stop', required: ['disposition', 'math'] }),
      ]),
      optional: [
        `action=${MATHEMATICS_WORKER_ACTIONS.join('|')}`,
        `mathResearchFinding {kind=literature|example|computation|counterexample|proof_step|conjecture_update|obstruction|critique,mechanism?,nextProbeKind=${MATH_RESEARCH_PROBE_KINDS.join('|')},mainlineImpact=mainline_advanced|route_refuted|supporting|stalled,bottleneckUpdate{target,outcome=resolved|narrowed|unchanged|refuted,category?=${MATH_FAILURE_CATEGORIES.join('|')},diagnosis?,repair?},helperRequest{bottleneck,probeKind,objective}?,problemFamilyProbe{instances[1..5]{input,outcome=supports|counterexample|inconclusive,observation?},sharedMechanism?,firstCounterexample?,generalization=supported|refuted|inconclusive}?,solutionSketchRef?,summary,evidenceRefs[],establishedClaims[],conjectureUpdates[],eliminatedApproaches[],openObligations[],nextAction}`,
        'Runtime returns probe_roi with probe kind, prior attempt/no-change counts, cost, state-change counts, value, and next_probe_priority; use recommended_probe_kind when the evidence indicates that a different probe is useful.',
        'mathRouteCard {structuralCommitment,decisiveLemma,decisiveTest,falsificationSignal,premiseBundle{strategySketch,leanSkeleton,premises[],coverage[],unresolvedNeeds[]},planNodes[1..7] or [8..128]+extendedPlanReason,bridges[],expectedInformationGain,estimatedCost,formalizationRisk}; plan nodes use roles goal|reduction|auxiliary|case_split|bridge, kinds theorem|definition|api_bridge|ported_helper, and statuses proposed|sourced|counterexample_checked; use one goal node, connect dependencies explicitly, and attach the decisive probe evidence to a checked node; default to one whole candidate or the shortest useful linear plan, and use a branching DAG only for independent lemmas',
        'resumable-stop math {routeDisposition,nextSingleObjective,infraStatus,evidenceDelta?[{kind,ref,summary}]}',
        'mathCheckpoint {failureCategory,doNotRepeatRefs?} only at a pause/resume, route-change, or infrastructure-failure boundary',
        'mathLessons[] only for a reusable result',
      ],
      runtime_supplied: [
        MATHEMATICS_RUNTIME_SHELL,
        'assignmentBinding and route identity',
        'advancing-route disposition and MathProgressDelta',
        'route root, frontier, bottleneck, proposer session, and checkpoint identity when present',
      ],
      prohibited: ['Git delivery identity', 'mathRouteCard.assessment', 'runtime-derived fields'],
      enums: MATHEMATICS_PROGRESS_ENUMS,
      notes: [
        'Return mathResearchFinding for ordinary discovery. After structural failure or runtime-directed replanning, routeProposalMode=candidate proposes, decisively probes, and retains one surviving mathRouteCard in this assignment.',
        'Advancing routes are advisory and structurally distinct.',
        RETRY_NOTE,
      ],
    });
  }
  if (laneId === 'lean-engineering') {
    if (variant === 'direct-formalization') {
      return Object.freeze({
        required: ['assignmentId', 'summary', 'git.headCommit'],
        one_of: Object.freeze([
          Object.freeze({
            name: 'solved',
            required: ['math.openGoalCountBefore', 'math.openGoalCountAfter', 'math.routeDisposition'],
            constraints: [
              'math.openGoalCountBefore > 0',
              'math.openGoalCountAfter = 0',
              'math.routeDisposition = advance',
              'git.headCommit differs from assignment git.baseCommit',
            ],
          }),
          Object.freeze({
            name: 'progress_or_blocked',
            required_any_of: [
              'math.openGoalCountBefore + math.openGoalCountAfter',
              'math.firstLeanErrorBefore + math.firstLeanErrorAfter',
              'math.openGoalAfter',
              'math.routeDisposition=reject',
              'math.infraStatus!=ready',
            ],
          }),
        ]),
        optional: [
          `action=${MATHEMATICS_WORKER_ACTIONS.join('|')}`,
          'math {openGoalCountBefore?,openGoalCountAfter?,openGoalAfter?,firstLeanErrorBefore?,firstLeanErrorAfter?,routeDisposition?,nextSingleObjective?,infraStatus?}',
        ],
        notes: [
          'Return the full committed head. Runtime restores identity and verifies source progress and receipts.',
          'A lookup miss is nonterminal. Deliver only a compiling improvement, smaller goal, later first error, exact route refutation, real infrastructure failure, or solved theorem.',
          RETRY_NOTE,
        ],
      });
    }
    return Object.freeze({
      required: ['assignmentId', 'summary', 'git.headCommit'],
      optional: [
        `action=${MATHEMATICS_WORKER_ACTIONS.join('|')}`,
        'disposition inferred from the receipt or progress outcome when omitted',
        "math {openGoalCountBefore?,openGoalCountAfter?,openGoalAfter?,firstLeanErrorBefore?,firstLeanErrorAfter?,firstLeanErrorOffsetBefore?,firstLeanErrorOffsetAfter?,wholeProofProbe?,verifiedPlanNodeIdsAdded?,planExpansion?,sourceProgress?,routeDisposition?,nextSingleObjective?,infraStatus?,executionPolicy?,evidenceDelta?[{kind,ref,summary}]}; sourceProgress is runtime-supplied declaration-level source evidence and must never be self-reported; it does not imply kernel verification; executionPolicy is runtime-owned and echoes the tactic/query/model cursor; wholeProofProbe and verifiedPlanNodeIdsAdded are runtime-owned for directAttempt; report openGoalAfter when it explains a premise-shaped failure or stall; runtime proofPack carries a live-goal premiseRetrieval query with the current source file/imports, and sketch_revision lazily materializes one compact project-local sketch when no ref exists while preserving the failed node's direct dependents",
        'mathNodeReceipt for a closed non-root node',
        'mathHelperReceipt for a kernel-verified helper added by planExpansion beneath the active node',
        'localGateReceipt only when the runtime supplied a real stored receipt; never fabricate or repeat an already passing directAttempt merely to obtain one',
        'mathCheckpoint only at a pause/resume, route-change, or infrastructure-failure boundary',
        'mathLessons[] only for structured, reusable, checkpoint-bound lessons; omit free-form lesson strings',
      ],
      runtime_supplied: [
        MATHEMATICS_RUNTIME_SHELL,
        'git.branch from the prepared assignment worktree',
        'disposition and default MathProgressDelta counters from receipts or observations',
        'assignmentBinding, statement and route identity, activePlanNodeId',
        'planBefore and planAfter rebuilt from the verified-node delta and validated planExpansion; directAttempt receives a synthetic direct-goal plan only for a verified helper expansion',
      ],
      prohibited: ['invented runtime identity', 'invented action telemetry', 'self-reported plan snapshots'],
      enums: MATHEMATICS_PROGRESS_ENUMS,
      notes: [
        'Return the new full head commit; the assigned branch and base commit are recovered from the durable worktree receipt.',
        'kernel_declaration and helper_declaration evidence are runtime-bound to a stored receipt; omit them when no receipt exists.',
        'sourceProgress records a runtime-verified changed Lean declaration and may be accumulated across incomplete direct episodes; it is source evidence only and the independent evaluator remains authoritative.',
        'Only a directAttempt whose activePlanNodeId is `direct-goal` may be solver-complete. For that whole-problem claim without a stored receipt, report a positive openGoalCountBefore, openGoalCountAfter=0, and routeDisposition=advance; the external evaluator remains authoritative.',
        'A directAttempt helper receipt is local progress: the runtime keeps the whole-problem goal open, routeDisposition=blocked, and continues the same solver episode.',
        'A directAttempt with a custom activePlanNodeId is one disjoint declaration cluster: report its own closed-goal progress, let the runtime merge it, and never emit a whole-problem completion marker for that delivery.',
        'Treat the assignment as one solver episode: repeat Lean/compiler feedback and repair internally, then deliver only the best retained state or a terminal boundary.',
        'A direct FORMALIZE delivery with an unchanged non-empty goal is rejected before Lead wake-up. Continue until a kernel/helper receipt, smaller goal, later or resolved first error, formal route refutation, or exact infrastructure failure is present.',
        'Obey formalizationPolicy when supplied. Missing library declarations are dependency milestones while infraStatus remains ready; retain a compiled helper or smaller goal instead of reporting them as infrastructure failure.',
        RETRY_NOTE,
      ],
    });
  }
  return Object.freeze({
    required: ['assignmentId', 'summary', 'mathReview'],
    optional: [
      `action=${MATHEMATICS_WORKER_ACTIONS.join('|')}`,
      'mathReview {verdict=sound|gap|wrong,firstFault?,repairTarget?,evidenceRefs[],findings[{severity=blocker|major|minor|note,kind,message,repairTarget?,evidenceRefs[]}],replayReceiptId?,replayTheoremName?,replayProofHash?,replayTheoremDeclarationHash?,replaySourceDeclarationHash?}',
      'math.reviewAction is runtime-supplied: advance means proceed to OFFICIAL_GATE, repair means preserve this candidate and repair the cited finding, reject means abandon this route and select a structurally distinct route.',
    ],
    runtime_supplied: [
      MATHEMATICS_RUNTIME_SHELL,
      'assignmentBinding, frozen receipt and review identity',
      'disposition, MathProgressDelta, and review recovery state',
    ],
    prohibited: ['Git delivery identity', 'restated frozen receipt', 'runtime-derived progress or checkpoint'],
    enums: {},
    notes: [
      'Review is advisory, read-only, and bound to the frozen candidate.',
      'Inspect statement alignment, assumptions, declaration meaning, and proof gaps. Lean replay is optional; the Lead runs the official comparator after a sound review.',
      RETRY_NOTE,
    ],
  });
}

function mathematicsResearchFindingResultShape(): Readonly<Record<string, unknown>> {
  return Object.freeze({
    required: [
      'assignmentId',
      'summary',
      'mathResearchFinding.{kind,nextProbeKind,mainlineImpact,summary,evidenceRefs[],establishedClaims[],conjectureUpdates[],eliminatedApproaches[],openObligations[],nextAction}',
    ],
    optional: [
      `mathResearchFinding.{mechanism,bottleneckUpdate{target,outcome=resolved|narrowed|unchanged|refuted,category?=${MATH_FAILURE_CATEGORIES.join('|')},diagnosis?,repair?},helperRequest{bottleneck,probeKind=${MATH_RESEARCH_PROBE_KINDS.join('|')},objective}?,problemFamilyProbe{instances[1..5]{input,outcome=supports|counterexample|inconclusive,observation?},sharedMechanism?,firstCounterexample?,generalization=supported|refuted|inconclusive}?,solutionSketchRef?}`,
      'mathCheckpoint {failureCategory,doNotRepeatRefs?} only at a real pause, route change, or infrastructure boundary',
      'mathLessons[] only for a reusable result',
    ],
    runtime_supplied: [
      MATHEMATICS_RUNTIME_SHELL,
      'assignmentBinding, route identity, disposition, and MathProgressDelta',
    ],
    prohibited: ['Git delivery identity', 'mathRouteCard', 'runtime-derived fields'],
    enums: Object.freeze({
      'mathResearchFinding.kind': Object.freeze([
        'literature',
        'example',
        'computation',
        'counterexample',
        'proof_step',
        'conjecture_update',
        'obstruction',
        'critique',
      ]),
      'mathResearchFinding.nextProbeKind': MATH_RESEARCH_PROBE_KINDS,
      'mathResearchFinding.mainlineImpact': Object.freeze([
        'mainline_advanced',
        'route_refuted',
        'supporting',
        'stalled',
      ]),
    }),
    notes: [
      'Return exactly one focused research finding. A stalled finding must name the unchanged bottleneck and next decisive action.',
      RETRY_NOTE,
    ],
  });
}

function workerLaneId(capability: ResearchTeamToolCapability): MathematicsLaneId | undefined {
  if (capability.roleKind !== 'worker') return undefined;
  const laneId = capability.roster.find((member) => member.slotId === capability.slotId)?.laneId;
  return laneId === 'strategy-exploration' || laneId === 'lean-engineering' || laneId === 'independent-review'
    ? laneId
    : undefined;
}
