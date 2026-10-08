import { mathWorkspaceRoleActions } from "./mathToolContract";
/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

import { applyMathematicsResearchPolicy, type MathematicsResearchPolicyId } from "./mathematicsResearchPolicy";
import {
  RESEARCH_TEAM_PROFILE_SCHEMA,
  createResearchTeamPoolContract,
  type ResearchTeamAuthority,
  type ResearchTeamLaneContract,
  type ResearchTeamProfile,
  type ResearchTeamRoleContract,
  type ResearchTeamToolActionPolicy,
} from "../../types/team/researchTeamContracts";

const MATHEMATICS_PROFILE_ID = 'mathematics-research-team';
const MATHEMATICS_LEAD_ROLE_ID = `${MATHEMATICS_PROFILE_ID}-lead`;

/** Slot specialization never replaces the authenticated assignment's scope. */
export const MATHEMATICS_WORKER_ASSIGNMENT_SCOPE = [
  'Read assignment.kind, objective, inputs and acceptance; they define authority. Slot and lane only indicate skills.',
  'For kind="research", answer only the assigned question; keep proof files read-only; use private scoped sourceProbe; share assumptions, evidence and uncertainty. Deliver a report; do not use owner-only search, checkout, execute or certify.',
  'For kind="formalize", own the complete original target through authorized proof and verification. Proof-owner instructions below apply only to this kind.',
  'When all useful work awaits a question, share wait_for_question_ids:["<question_id>"] and end the turn. The host freezes source/evidence; new finding, source change or ended producer releases it; [] clears it. Do not wait for every active Worker.',
].join('\n');

const LEAD_AUTHORITY: ResearchTeamAuthority = Object.freeze({
  dispatchAssignments: true,
  writeAssignedWorktree: false,
  integrateWorkerCommits: true,
  runCanonicalEvaluation: false,
  mutateCanonicalRegistry: true,
  checkpointProject: true,
  publishReport: false,
});

const WORKER_AUTHORITY: ResearchTeamAuthority = Object.freeze({
  dispatchAssignments: false,
  writeAssignedWorktree: true,
  integrateWorkerCommits: false,
  runCanonicalEvaluation: false,
  mutateCanonicalRegistry: false,
  checkpointProject: false,
  publishReport: false,
});

const WORKER_EVIDENCE_TOOLS: readonly ResearchTeamToolActionPolicy[] = Object.freeze([
  Object.freeze({ toolName: 'research_team', actions: Object.freeze(['deliver', 'share', 'read_artifact', 'read_feedback']) }),
  Object.freeze({ toolName: 'research_evidence', actions: Object.freeze(['search', 'read']) }),
]);

const MATHEMATICS_FORMALIZER_ALLOWED_TOOLS: readonly ResearchTeamToolActionPolicy[] = Object.freeze([
  ...WORKER_EVIDENCE_TOOLS,
  Object.freeze({ toolName: 'math_portfolio', actions: Object.freeze(['get']) }),
  Object.freeze({ toolName: 'math_portfolio', actions: Object.freeze(['bootstrap']) }),
  Object.freeze({ toolName: 'lean_workspace', actions: mathWorkspaceRoleActions('formalizer') }),
]);

const MATHEMATICS_RESEARCHER_ALLOWED_TOOLS: readonly ResearchTeamToolActionPolicy[] = Object.freeze([
  ...WORKER_EVIDENCE_TOOLS,
  Object.freeze({
    toolName: 'lean_workspace',
    actions: Object.freeze([...new Set([...mathWorkspaceRoleActions('researcher'), 'probe'])]),
  }),
  Object.freeze({ toolName: 'math_portfolio', actions: Object.freeze(['get']) }),
]);

const MATHEMATICS_WORKER_DENIED_TOOLS: readonly ResearchTeamToolActionPolicy[] = Object.freeze([
  Object.freeze({ toolName: 'science_artifact', actions: Object.freeze(['publish']) }),
  Object.freeze({ toolName: 'project_workspace', actions: Object.freeze(['checkpoint']) }),
  Object.freeze({
    toolName: 'math_portfolio',
    actions: Object.freeze(['submit', 'request_review', 'submit_review']),
  }),
]);

const MATHEMATICS_LANES: readonly ResearchTeamLaneContract[] = Object.freeze([
  makeLane('strategy-exploration', 'Mathematical Researcher', 'Perform one highest-information discovery action.', [
    'research finding',
    'research-state update',
  ]),
  makeLane(
    'lean-engineering',
    'Lean Engineer',
    'Own one whole candidate or one dependency-ready proof node in a stateful assignment.',
    ['Lean proof artifact', 'solver episode result', 'node or local gate receipt']
  ),
  makeLane('independent-review', 'Independent Reviewer', 'Freshly audit a locally verified candidate.', [
    'CandidateReview',
    'kernel receipt audit',
  ]),
]);

export function createHeadlessMathematicsTeamProfile(
  researchPolicy?: MathematicsResearchPolicyId,
  options: Readonly<{
    unlimitedTokens?: boolean;
    benchmarkMethod?: 'deepscientist_team' | 'single_worker';
    secondProofOwner?: boolean;
  }> = {}
): ResearchTeamProfile {
  const singleWorker = options.benchmarkMethod === 'single_worker';
  const secondProofOwner = options.secondProofOwner === true && !singleWorker;
  const agentLimit = singleWorker ? 1 : 3;
  const workerLanes = createMathematicsWorkerLanes(MATHEMATICS_LANES, agentLimit, secondProofOwner);
  const profile: ResearchTeamProfile = Object.freeze({
    schema: RESEARCH_TEAM_PROFILE_SCHEMA,
    version: 1,
    id: MATHEMATICS_PROFILE_ID,
    workflowId: 'science.mathematics.v1',
    displayName: 'Mathematics Research Team',
    leadRoleId: MATHEMATICS_LEAD_ROLE_ID,
    pool: createResearchTeamPoolContract({ executionProfile: 'assist', agentLimit, reasoningConcurrency: agentLimit }),
    lanes: MATHEMATICS_LANES,
    roles: Object.freeze([
      createLeadRole(secondProofOwner),
      ...workerLanes.map((lane, index) => createWorkerRole(lane, occurrence(workerLanes, lane.id, index))),
    ]),
    exclusiveCapabilities: Object.freeze([]),
    coordinationRules: Object.freeze([
      'The Lead chooses objectives, dependencies and assignment order. Available slots do not prescribe a workflow.',
      singleWorker
        ? 'This baseline has one Worker. The Lead coordinates that Worker and integrates its evidence; do not provision additional Workers.'
        : 'Delegate distinct useful work; integrate completed deliveries before declaring the complete problem solved.',
    ]),
  });
  return researchPolicy ? applyMathematicsResearchPolicy(profile, researchPolicy, options) : profile;
}

function createLeadRole(secondProofOwner: boolean): ResearchTeamRoleContract {
  return Object.freeze({
    id: MATHEMATICS_LEAD_ROLE_ID,
    kind: 'lead',
    displayName: 'Mathematics Lead',
    authority: LEAD_AUTHORITY,
    allowedTools: Object.freeze([
      { toolName: 'research_team', actions: Object.freeze(['describe', 'dispatch', 'status', 'integrate', 'read_artifact']) },
      { toolName: 'project_workspace', actions: Object.freeze(['status', 'checkpoint']) },
      { toolName: 'lean_workspace', actions: mathWorkspaceRoleActions('lead') },
    ]),
    deniedTools: Object.freeze([{ toolName: 'formal_verifier', actions: '*' as const }]),
    prompt: [
      'You are the Mathematics Lead and sole integrator. Own the frozen original target, established facts and the decisive missing implication. Explain how proposed lemmas connect to the target.',
      'Workers may change mathematical approach, introduce useful lemmas and search relevant facts without route approval. Use current source, real Lean feedback and durable deliveries to decide whether to continue, request independent research or integrate.',
      'Name each gap with research_question:{statement,assumptions,targetConnection}. observation.research_graph shows IDs, evidence versions, producers, consumers and provisional reports. Rewording cannot duplicate question/evidence; the graph organizes work and never certifies truth. Proof owners may wait for a bound question while independent work runs.',
      'Dispatch kind=research for bounded auxiliary proof production or scrutiny, with a concise report, or kind=formalize for complete targets. Bind research consumers with exact active/blocked proof IDs from status. Retry the same kind and consumers; slot labels do not change acceptance.',
      'Use at most two complementary research tasks. Start independent necessary helpers with known inputs and stable consumer interfaces in the initial wave; do not wait until the owner reaches each blocker. Request checked auxiliary Lean code for a stable required claim, or a decisive test for an uncertain conjecture. Supply exact hypotheses and the intended call. Researchers may question an auxiliary goal. Delegate only residual gaps and overlap production with downstream explicit-parameter work; cyclic conditions prove neither claim. Simple repairs stay with the owner; leave unnecessary slots idle.',
      `${secondProofOwner ? 'Coordinate the proof owners (the primary Lean Engineer and, when you use it, the second one on a different decomposition)' : 'Coordinate the persistent proof owner'} rather than privately solving a competing full proof. Choose research or formalization from the bottleneck; neither lane must run first. A nonterminal share can justify independent research without ending the proof assignment. Send the precise question, its role in the argument and authorized evidence. Avoid duplicate objectives merely because capacity is idle. Use research_team dispatch, status and integrate; only accepted dispatches represent work. Return findings to the same proof owner through the lawful path. Wait for notifications while Workers run instead of polling.`,
      'Integrate useful results into the main argument and inspect remaining gaps. Only a valid original-target receipt establishes completion; partial and blocked results remain research inputs.',
      'Short conditional use or a decisive mechanism check should shape uncertain claims. A residual goal may come from the chosen route, not the original theorem: seek an actual alternative connection when evidence warrants it. If the producer changes L0 to L1, preserve the consumer via a checked L1-to-L0 adapter when possible; otherwise repair the affected use. Revisit old work only with a new fact or targeted revision. Consume findings without waiting for a whole batch; resolve challenges before adoption. Avoid mandatory rituals. When integration backs up, stop new research. Notes are not proof authority.',
      'Never read reference answers, previous solution runs or evaluator-private material. Independent evaluation is outside this Team.',
    ].join('\n'),
  });
}

function createWorkerRole(workerLane: ResearchTeamLaneContract, laneOccurrence: number): ResearchTeamRoleContract {
  const suffix = laneOccurrence > 1 ? `-${laneOccurrence}` : '';
  const displaySuffix = laneOccurrence > 1 ? ` ${laneOccurrence}` : '';
  return Object.freeze({
    id: `${MATHEMATICS_PROFILE_ID}-worker-${workerLane.id}${suffix}`,
    kind: 'worker',
    displayName: `${workerLane.displayName}${displaySuffix}`,
    laneId: workerLane.id,
    authority: WORKER_AUTHORITY,
    allowedTools: workerLane.id === 'lean-engineering' ? MATHEMATICS_FORMALIZER_ALLOWED_TOOLS : MATHEMATICS_RESEARCHER_ALLOWED_TOOLS,
    deniedTools: MATHEMATICS_WORKER_DENIED_TOOLS,
    prompt: [
      MATHEMATICS_WORKER_ASSIGNMENT_SCOPE,
      'Use assignment-bound lean_workspace probe for checked Lean feedback. Omit assignmentId to bind the current task automatically; never reconstruct an opaque ID. Inspect local files and Git changes through the terminal. project_workspace status and checkpoint belong to the Lead and are not Worker tools.',
      ...(workerLane.id === 'lean-engineering' && laneOccurrence > 1
        ? [
            'For kind="formalize": You are the second proof owner. Prove the complete original theorem through a decomposition that is structurally different from the primary Lean Engineer\'s route, as named in your assignment; do not read or copy another Worker\'s worktree. The first host-verified integration wins and the other assignment is superseded automatically.',
          ]
        : []),
      'Preserve target and checked work; no route approval. Keep gaps and next action in RESEARCH.md. Never restore the original seed merely because the target is unfinished; retain compiling helpers and their Git checkpoints.',
      workerLane.id === 'lean-engineering'
        ? 'Own the original target. A residual goal is not automatically necessary: trace helper/representation burdens; seek checked connections. Share exact goals and original hypotheses. Do not always select the hardest, easiest or weakest lemma.'
        : 'For a missing construction, name the object type and required relations; justify a candidate form, substitute it and refine unmet conditions. Separate sufficient choices from necessary ones; one failed family does not refute the target. Trace route-added premises and return a checked local connection, revised claim or exact obstruction; unproved claims remain unknown.',
      workerLane.id === 'lean-engineering'
        ? 'Before retries distinguish errors, missing premises, counterexamples and open gaps. Failure to prove is not refutation. Recheck old witnesses. Check the whole candidate with lean_workspace action="probe", probeMode="compile", probeSourceFile set to the project-relative assigned source path. Use sourceProbe only for a specific tactic span, never as a substitute for whole-file compilation. Repair the first syntax or type diagnostic directly in the current file, then check the changed candidate; do not wait for Lead approval or repeat a blocker report for a local repair. Terminal checks are not frozen evidence. Check delivered bytes.'
        : 'Explore interfaces. Producers prove stable required claims; test uncertain mechanisms first. Consumers use private explicit parameters. Feed sourceProbe goals and diagnostics back before long work. Once a required auxiliary claim compiles in private Aux.lean, freeze that file as source evidence and deliver it immediately with its exact hypotheses, dependencies and intended call; do not wait for other helpers or polish the report. The Lead can adopt it while the main proof continues. Send corrected claims to earlier recipients lawfully. A closed local sourceProbe span does not establish whole-file success. Conditional work proves neither premise nor target; preserve consumers via a checked adapter. Canonical files read-only; check private Aux.lean with scoped sourceProbe and frozen Lean; no axioms or final-target authority.',
      workerLane.id === 'lean-engineering'
        ? 'Query the intended transformation via lean_workspace searchMode=premises, premiseQuery and live goal; applyBest=false prevents adoption. Read full local types (#check @/#print), instantiate here; delegate only residual gaps, preserving formulas/witnesses.'
        : 'Query authorized local library files with available tools, else request frozen findings via Lead. Read full types (#check @/#print), try private sourceProbe; return calls, conditions and goals/mismatch. Reuse findings; no match is not refutation.',
      ...(workerLane.id === 'lean-engineering'
        ? [
            'Read frozen auxiliary source via research_team action="read_artifact", artifact_ref copied exactly from supplied findings; follow nextOffsetBytes until the relevant declarations and dependencies are complete. read_feedback retrieves findings, not artifact bytes. Prefer adopting that proof to proving it again: order dependencies in Submission.lean; preserve original definitions; check section variables, implicit parameters and instances. No active peer reads/new imports. Share mismatches; derive premises from the original problem. A direct simpler proof remains allowed.',
          ]
        : []),
      'Use read_artifact only when helpful. Align objects, operations, assumptions and return to target: theorem reuse differs from mechanism transfer. Never invent structure. Recheck applicability when hypotheses change. Isolate conjectures. Unused helpers are not adopted. Original-target completion requires independent verification; a research assignment completes with its scoped report.',
    ].join('\n'),
  });
}

function createMathematicsWorkerLanes(
  lanes: readonly ResearchTeamLaneContract[],
  agentLimit: number,
  secondProofOwner = false
): readonly ResearchTeamLaneContract[] {
  const strategy = lanes.find((lane) => lane.id === 'strategy-exploration');
  const lean = lanes.find((lane) => lane.id === 'lean-engineering');
  if (!strategy || !lean) throw new Error('Mathematics Team lanes are incomplete');
  // A second proof owner takes one Strategy slot; the Team size stays agentLimit.
  const leanCount = secondProofOwner && agentLimit >= 3 ? 2 : 1;
  return Object.freeze([
    ...Array.from({ length: Math.max(0, agentLimit - leanCount) }, () => strategy),
    ...Array.from({ length: leanCount }, () => lean),
  ]);
}

function makeLane(
  id: string,
  displayName: string,
  purpose: string,
  deliverables: readonly string[]
): ResearchTeamLaneContract {
  return Object.freeze({ id, displayName, purpose, deliverables: Object.freeze([...deliverables]) });
}

function occurrence(lanes: readonly ResearchTeamLaneContract[], laneId: string, currentIndex: number): number {
  return lanes.slice(0, currentIndex + 1).filter((candidateLane) => candidateLane.id === laneId).length;
}
