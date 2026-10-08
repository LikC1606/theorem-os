import { mathWorkspaceRoleActions } from "./mathToolContract";
/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

import { createFactorResearchTeamProfile } from "../finance/factorResearchTeamProfile";
import { applyMathematicsResearchPolicy, type MathematicsResearchPolicyId } from "./mathematicsResearchPolicy";
import type { ModeStack } from "../../types/modes/types";
import { BUILTIN_IOAI_COMPETITION_NAME, BUILTIN_SCIENCE_ARTIFACT_NAME } from "../../config/builtinMcpConstants";
import { BUILTIN_RESEARCH_EVIDENCE_NAME, BUILTIN_USER_INPUT_NAME } from "../../config/builtinMcpConstants";
import {
  RESEARCH_TEAM_PROFILE_SCHEMA,
  RESEARCH_TEAM_MIN_AGENT_LIMIT,
  createResearchTeamPoolContract,
  type ResearchTeamAuthority,
  type ResearchTeamLaneContract,
  type ResearchTeamProfile,
  type ResearchTeamRoleContract,
  type ResearchTeamToolActionPolicy,
} from "../../types/team/researchTeamContracts";
import { DEEPSCIENTIST_TEAM_MIN_AGENT_LIMIT, type DeepScientistTeamConfig } from "./deepScientistTeam";

export type DeepScientistTeamModeProfileId =
  | 'science-research-team'
  | 'medical-evidence-team'
  | 'target-discovery-team'
  | 'mathematics-research-team'
  | 'financial-research-team'
  | 'project-research-team'
  | 'financial-factor-research';

/** Slot specialization never replaces the authenticated assignment's scope. */
export const MATHEMATICS_WORKER_ASSIGNMENT_SCOPE = [
  'Read assignment.kind, objective, inputs and acceptance; they define authority. Slot and lane only indicate skills.',
  'For kind="research", answer only the assigned question; keep proof files read-only; use private scoped sourceProbe; share assumptions, evidence and uncertainty. Deliver a report; do not use owner-only search, checkout, execute or certify.',
  'For kind="formalize", own the complete original target through authorized proof and verification. Proof-owner instructions below apply only to this kind.',
  'When all useful work awaits a question, share wait_for_question_ids:["<question_id>"] and end the turn. The host freezes source/evidence; new finding, source change or ended producer releases it; [] clears it. Do not wait for every active Worker.',
].join('\n');

/**
 * Every managed Team uses the same coordination and evidence substrate.
 * Domain MCPs are appended for the Lead, while Workers stay bounded to
 * delivery plus read-only evidence retrieval.
 */
export const DEEPSCIENTIST_TEAM_LEAD_BASE_MCP_NAMES = Object.freeze([
  BUILTIN_IOAI_COMPETITION_NAME,
  BUILTIN_SCIENCE_ARTIFACT_NAME,
  BUILTIN_RESEARCH_EVIDENCE_NAME,
  BUILTIN_USER_INPUT_NAME,
]);

export const DEEPSCIENTIST_TEAM_WORKER_BASE_MCP_NAMES = Object.freeze([
  BUILTIN_IOAI_COMPETITION_NAME,
  BUILTIN_RESEARCH_EVIDENCE_NAME,
]);

export function getDeepScientistTeamRequiredMcpNames(
  role: ResearchTeamRoleContract,
  modeRequiredMcpNames: readonly string[]
): readonly string[] {
  if (role.kind === 'lead') {
    return Array.from(new Set([...DEEPSCIENTIST_TEAM_LEAD_BASE_MCP_NAMES, ...modeRequiredMcpNames]));
  }
  const needsLeanWorkspace = role.laneId === 'lean-engineering' || role.laneId === 'independent-review';
  return Array.from(
    new Set([
      ...DEEPSCIENTIST_TEAM_WORKER_BASE_MCP_NAMES,
      ...(role.laneId === 'strategy-exploration' && role.id.startsWith('mathematics-research-team')
        ? [BUILTIN_SCIENCE_ARTIFACT_NAME]
        : []),
      ...(needsLeanWorkspace ? [BUILTIN_SCIENCE_ARTIFACT_NAME] : []),
    ])
  );
}

type ProfileDescriptor = Readonly<{
  id: Exclude<DeepScientistTeamModeProfileId, 'financial-factor-research'>;
  workflowId: string;
  displayName: string;
  leadName: string;
  lanes: readonly ResearchTeamLaneContract[];
  leadInstructions: readonly string[];
  publicationGate: string;
  exclusiveTool?: Readonly<{ toolName: string; actions: readonly string[] }>;
}>;

const LEAD_AUTHORITY: ResearchTeamAuthority = Object.freeze({
  dispatchAssignments: true,
  writeAssignedWorktree: false,
  integrateWorkerCommits: true,
  runCanonicalEvaluation: true,
  mutateCanonicalRegistry: true,
  checkpointProject: true,
  publishReport: true,
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

const LEAD_ALLOWED_TOOLS: readonly ResearchTeamToolActionPolicy[] = Object.freeze([
  Object.freeze({ toolName: 'research_team', actions: '*' as const }),
  Object.freeze({ toolName: 'research_evidence', actions: '*' as const }),
  Object.freeze({ toolName: 'science_artifact', actions: '*' as const }),
  Object.freeze({ toolName: 'project_workspace', actions: '*' as const }),
  Object.freeze({ toolName: 'user_input', actions: '*' as const }),
]);

const WORKER_ALLOWED_TOOLS: readonly ResearchTeamToolActionPolicy[] = Object.freeze([
  Object.freeze({ toolName: 'research_team', actions: Object.freeze(['deliver']) }),
  Object.freeze({ toolName: 'research_evidence', actions: Object.freeze(['search', 'read']) }),
]);

// Runtime injects the mathematics assignment and result contracts. Workers
// only need the delivery action from the orchestration surface.
const MATHEMATICS_WORKER_ALLOWED_TOOLS: readonly ResearchTeamToolActionPolicy[] = Object.freeze([
  Object.freeze({ toolName: 'research_team', actions: Object.freeze(['deliver']) }),
  Object.freeze({ toolName: 'research_evidence', actions: Object.freeze(['search', 'read']) }),
  Object.freeze({ toolName: 'lean_workspace', actions: mathWorkspaceRoleActions('researcher') }),
]);

const MATHEMATICS_FORMALIZER_ALLOWED_TOOLS: readonly ResearchTeamToolActionPolicy[] = Object.freeze([
  ...MATHEMATICS_WORKER_ALLOWED_TOOLS.filter((policy) => policy.toolName !== 'lean_workspace'),
  Object.freeze({ toolName: 'math_portfolio', actions: Object.freeze(['get']) }),
  Object.freeze({ toolName: 'math_portfolio', actions: Object.freeze(['bootstrap']) }),
  Object.freeze({
    toolName: 'lean_workspace',
    actions: mathWorkspaceRoleActions('formalizer'),
  }),
]);

const MATHEMATICS_REVIEWER_ALLOWED_TOOLS: readonly ResearchTeamToolActionPolicy[] = Object.freeze([
  ...MATHEMATICS_WORKER_ALLOWED_TOOLS,
  Object.freeze({ toolName: 'math_portfolio', actions: Object.freeze(['get']) }),
]);

const MATHEMATICS_STRATEGY_ALLOWED_TOOLS: readonly ResearchTeamToolActionPolicy[] = Object.freeze([
  ...MATHEMATICS_WORKER_ALLOWED_TOOLS,
  Object.freeze({ toolName: 'math_portfolio', actions: Object.freeze(['get']) }),
]);

const WORKER_DENIED_TOOLS: readonly ResearchTeamToolActionPolicy[] = Object.freeze([
  Object.freeze({ toolName: 'science_artifact', actions: Object.freeze(['publish']) }),
  Object.freeze({ toolName: 'project_workspace', actions: Object.freeze(['checkpoint']) }),
  Object.freeze({ toolName: 'target_portfolio', actions: Object.freeze(['submit']) }),
  Object.freeze({ toolName: 'factor_submit', actions: '*' as const }),
]);

const MATHEMATICS_WORKER_DENIED_TOOLS: readonly ResearchTeamToolActionPolicy[] = Object.freeze([
  ...WORKER_DENIED_TOOLS,
  Object.freeze({
    toolName: 'math_portfolio',
    actions: Object.freeze(['submit', 'request_review', 'submit_review']),
  }),
]);

const SHARED_WORKER_INSTRUCTIONS = [
  'Accept one atomic assignment with acceptance and failure criteria, a falsification plan, and an explicit executionMode.',
  'For executionMode=artifact, work only in the assigned isolated worktree, commit attributable artifacts, and return the exact branch plus full head commit.',
  'For executionMode=advisory, do not edit files or create commits; return the bounded structured analysis directly.',
  'Deliver evidence, an explicit falsification outcome, and verification commands through research_team(action="deliver").',
  'Do not dispatch another Agent, alter canonical project state, submit a target or factor, checkpoint, publish, or poll shared state.',
  'Never call Codex native spawn_agent, wait, wait_agent, or yield_control; DeepScientist Workers are Core-managed conversations, not Codex child threads.',
].join('\n');

const DESCRIPTORS: Readonly<
  Record<Exclude<DeepScientistTeamModeProfileId, 'financial-factor-research'>, ProfileDescriptor>
> = Object.freeze({
  'science-research-team': makeDescriptor(
    'science-research-team',
    'science.research.v1',
    'Science Research Team',
    'Science Lead',
    [
      makeLane('hypothesis', 'Hypothesis Scout', 'Develop distinct falsifiable explanations.', [
        'hypothesis brief',
        'decisive test',
      ]),
      makeLane('experiment', 'Experiment Designer', 'Design reproducible analyses and controls.', [
        'analysis plan',
        'implementation artifact',
      ]),
      makeLane('evidence', 'Evidence Auditor', 'Find and appraise directly relevant evidence.', [
        'evidence map',
        'applicability limits',
      ]),
      makeLane('reproducibility', 'Reproducibility Reviewer', 'Challenge methods, results, and provenance.', [
        'failure analysis',
        'verification record',
      ]),
    ],
    [
      'Separate independent hypotheses before parallel work; do not split one tightly coupled operation across Workers.',
    ],
    'Before publishing a report, independently review integrated evidence, failed tests, reproducibility, and claim boundaries; then make one Lead-owned second confirmation.'
  ),
  'medical-evidence-team': makeDescriptor(
    'medical-evidence-team',
    'medical.evidence.v1',
    'Medical Evidence Team',
    'Evidence Lead',
    [
      makeLane('retrieval', 'Retrieval Specialist', 'Search current primary and authoritative sources.', [
        'search record',
        'source set',
      ]),
      makeLane('appraisal', 'Evidence Appraiser', 'Assess bias, certainty, and indirectness.', [
        'appraisal table',
        'certainty notes',
      ]),
      makeLane('applicability', 'Clinical Applicability Reviewer', 'Audit population fit, safety, and boundaries.', [
        'applicability memo',
        'safety limits',
      ]),
      makeLane('synthesis', 'Synthesis Auditor', 'Test whether conclusions follow from cited evidence.', [
        'contradiction audit',
        'recommendation',
      ]),
    ],
    [
      'Keep retrieval, appraisal, applicability, and synthesis attributable; never let source count replace quality assessment.',
    ],
    'Before publishing the evidence report, verify every material claim against registered evidence and perform one Lead-owned safety and applicability review.'
  ),
  'target-discovery-team': makeDescriptor(
    'target-discovery-team',
    'science.target-discovery.v1',
    'Target Discovery Team',
    'Target Discovery Lead',
    [
      makeLane('causality', 'Genetics & Causality', 'Test human genetics and causal support.', [
        'causal evidence map',
        'confounder audit',
      ]),
      makeLane('dependency', 'Omics & Dependency', 'Test disease-context dependency and expression.', [
        'context matrix',
        'robustness result',
      ]),
      makeLane('tractability', 'Tractability & Safety', 'Assess modality, selectivity, and liabilities.', [
        'tractability brief',
        'safety flags',
      ]),
      makeLane('validation', 'Validation Falsifier', 'Design decisive validation and counterexamples.', [
        'validation ladder',
        'discard criteria',
      ]),
    ],
    [
      'Keep target identity, disease context, evidence channel, and release provenance explicit in every assignment.',
      'Dispatch only independent causality, dependency, tractability/safety, or validation/falsification lanes. Treat a failed or missing delivery as an explicit evidence gap; never simulate consensus or silently replace it.',
    ],
    'Before target_portfolio(action="submit"), review every integrated candidate, evidence id, contrary result, identity mapping, and validation gap; then make one Lead-owned second confirmation. Workers never submit targets.',
    { toolName: 'target_portfolio', actions: ['submit'] }
  ),
  'mathematics-research-team': makeDescriptor(
    'mathematics-research-team',
    'science.mathematics.v1',
    'Mathematics Research Team',
    'Mathematics Lead',
    [
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
    ],
    [
      'Workflow: UNDERSTAND -> SOLVE_LOOP -> ANSWER; formal work may continue FORMALIZE -> REVIEW -> OFFICIAL_VERIFY. Bound role and assignment contracts are authoritative; call describe only after a concrete schema rejection.',
      'UNDERSTAND records objective, obligations, known results, failures, and one mainline bottleneck. SOLVE_LOOP probes only decision-changing questions; Lean is optional.',
      'At intake, record feasibility and consult math_portfolio feasibilityRanking when useful. Prefer the cheapest executable milestone with the highest solve probability.',
      'The Lead plan is the route decision. In proof-mainline mode start the single Lean Worker immediately; do not wait for advisory handoffs or create duplicate proof branches. In bound route-discovery mode obtain one actionable advisory bridge first, then start that Lean Worker without waiting for additional advisory handoffs.',
      'Before full assembly, run one bounded semantic viability probe for premise domains, invariants, boundary cases, and terminal closure. Unknown or refuted checks return to decomposition.',
      'Repeated stalls use route_replan with a structurally distinct route. Declaration count controls artifact partition only after a route exists.',
      'During FORMALIZE, use math_progress_control for verified progress and resource constraints. Choose mathematical work from the evidence: repair locally in the same assignment, or propose a better main route for the Lead to accept or reject. A supported in-place route revision retains the same Worker and worktree. Missing APIs are dependencies; retain compiled helpers; catalogs are not terminal.',
      'Before FORMALIZE/REVIEW, satisfy typed contract, FAST_CHECK, alignment, route, and stage preflight. REVIEW uses one fresh read-only Reviewer on the unchanged reviewed commit; sound advances, gap repairs, wrong returns.',
      'OFFICIAL_VERIFY calls formal_verifier(action="official_compare") once on the unchanged reviewed commit; publish only when statement, kernel, review, and comparator agree.',
    ],
    'Before publishing, review assumptions, gaps, counterexamples, and kernel verification, then confirm once.',
    { toolName: 'math_portfolio', actions: ['submit', 'patch', 'request_review', 'submit_review', 'official_gate'] }
  ),
  'financial-research-team': makeDescriptor(
    'financial-research-team',
    'finance.research.v1',
    'Financial Research Team',
    'Financial Research Lead',
    [
      makeLane('data', 'Data Provenance Auditor', 'Audit timestamps, coverage, and field semantics.', [
        'data contract',
        'leakage audit',
      ]),
      makeLane('method', 'Method Researcher', 'Develop testable financial hypotheses.', [
        'method brief',
        'simulation plan',
      ]),
      makeLane('risk', 'Risk Reviewer', 'Stress assumptions, costs, and regimes.', ['risk register', 'stress result']),
      makeLane('replication', 'Replication Reviewer', 'Reproduce and challenge reported performance.', [
        'replication record',
        'failure analysis',
      ]),
    ],
    [
      'Keep research, simulation, and real trading strictly separated; real trading remains prohibited.',
      'Route the financial task contract before dispatch. Factor research uses the XAlpha/generic Team route and one Lead-owned factor_submit handoff; other contracts remain on their selected financial route.',
    ],
    'Before publishing or registering any result, independently review point-in-time safety, costs, robustness, evidence, and failed tests; then make one Lead-owned second confirmation.'
  ),
  'project-research-team': makeDescriptor(
    'project-research-team',
    'project.general.v1',
    'Project Team',
    'Project Lead',
    [
      makeLane('implementation', 'Implementation Worker', 'Produce one bounded implementation.', [
        'committed change',
        'verification',
      ]),
      makeLane('review', 'Independent Reviewer', 'Audit correctness and regressions.', ['review memo', 'risk list']),
      makeLane('evidence', 'Evidence Worker', 'Collect attributable supporting evidence.', [
        'evidence set',
        'claim map',
      ]),
      makeLane('falsification', 'Falsification Worker', 'Try to disprove the proposed result.', [
        'counterexample',
        'decision recommendation',
      ]),
    ],
    ['Use parallel Workers only for independent, bounded work that can be merged through exact Git commits.'],
    'Before user-facing publication, the Lead reviews exact integrated commits, evidence, verification, and falsification, then makes one final confirmation.'
  ),
});

export function createDeepScientistModeTeamProfile(
  modeStack: ModeStack,
  config: DeepScientistTeamConfig
): ResearchTeamProfile {
  if (modeStack.primary === 'financial-factor-mining' || modeStack.overlays.includes('factor-research')) {
    return createFactorResearchTeamProfile({
      executionProfile: 'parallel',
      agentLimit: config.agentLimit,
      reasoningConcurrency: config.reasoningConcurrency,
    });
  }
  const profileDescriptor = resolveDescriptor(modeStack);
  const isMathematics = profileDescriptor.id === 'mathematics-research-team';
  // One persistent proof owner; auxiliary capacity is available only for useful disjoint work.
  const pool = createResearchTeamPoolContract(
    {
      executionProfile: isMathematics ? 'assist' : 'parallel',
      agentLimit: isMathematics ? Math.min(3, config.agentLimit) : config.agentLimit,
      reasoningConcurrency: isMathematics ? Math.min(3, config.reasoningConcurrency) : config.reasoningConcurrency,
    },
    {
      minimumAgentLimit: isMathematics ? RESEARCH_TEAM_MIN_AGENT_LIMIT : DEEPSCIENTIST_TEAM_MIN_AGENT_LIMIT,
      maximumAgentLimit: 50,
      maximumReasoningConcurrency: 10,
    }
  );
  const workerLanes = isMathematics
    ? createMathematicsWorkerLanes(
        profileDescriptor.lanes,
        pool.agentLimit,
        config.mathematicsSecondProofOwner === true
      )
    : Array.from(
        { length: pool.agentLimit },
        (_, index) => profileDescriptor.lanes[index % profileDescriptor.lanes.length]
      );
  const leadRoleId = `${profileDescriptor.id}-lead`;
  const roles = Object.freeze([
    createLeadRole(profileDescriptor, leadRoleId),
    ...workerLanes.map((workerLane, index) =>
      createWorkerRole(profileDescriptor, workerLane, occurrence(workerLanes, workerLane.id, index))
    ),
  ]);
  const exclusiveCapabilities = [
    Object.freeze({
      id: 'project-checkpoint',
      ownerRoleId: leadRoleId,
      toolName: 'project_workspace',
      actions: Object.freeze(['checkpoint']),
    }),
    Object.freeze({
      id: 'report-publication',
      ownerRoleId: leadRoleId,
      toolName: 'science_artifact',
      actions: Object.freeze(['publish']),
    }),
    ...(profileDescriptor.exclusiveTool
      ? [
          Object.freeze({
            id: `${profileDescriptor.exclusiveTool.toolName}-canonical-write`,
            ownerRoleId: leadRoleId,
            toolName: profileDescriptor.exclusiveTool.toolName,
            actions: Object.freeze([...profileDescriptor.exclusiveTool.actions]),
          }),
        ]
      : []),
  ];
  return Object.freeze({
    schema: RESEARCH_TEAM_PROFILE_SCHEMA,
    version: 1,
    id: profileDescriptor.id,
    workflowId: profileDescriptor.workflowId,
    displayName: profileDescriptor.displayName,
    leadRoleId,
    pool,
    lanes: profileDescriptor.lanes,
    roles,
    exclusiveCapabilities: Object.freeze(exclusiveCapabilities),
    coordinationRules: Object.freeze(
      isMathematics
        ? [
            'Keep one persistent proof owner and up to two optional complementary researchers. Do not fill slots or wait for a whole batch; act on usable findings while checking unresolved dependencies.',
            'Choose disjoint structural extraction, backward reasoning, targeted challenge or independent auxiliary proofs from the current gap. Only the Lead integrates the mainline proof and owns submission.',
            profileDescriptor.publicationGate,
          ]
        : [
            'The Lead plans independent bounded assignments. The first wave uses at most one Worker per distinct lane; later waves may add a duplicate lane only for a new, explicitly disjoint evidence source, method, or review question.',
            'No wave exceeds reasoningConcurrency, and unused reusable Worker slots stay idle.',
            'Artifact Workers use isolated Git worktrees and deliver exact commits. Advisory Workers return read-only structured analysis without branch creation or integration.',
            'Delivery is event-driven. The Lead ends its turn while Workers run and does not poll unchanged status.',
            'Only the Lead integrates reviewed commits, mutates canonical state, checkpoints, submits, or publishes.',
            profileDescriptor.publicationGate,
          ]
    ),
  });
}

/** Projection for the existing proof runner, not a separately selectable mode. */
export function createHeadlessMathematicsTeamProfile(
  researchPolicy?: MathematicsResearchPolicyId,
  options: Readonly<{
    unlimitedTokens?: boolean;
    mathematicsRouteDiscovery?: boolean;
    benchmarkMethod?: 'deepscientist_team' | 'single_worker';
    secondProofOwner?: boolean;
  }> = {}
): ResearchTeamProfile {
  if (researchPolicy)
    return applyMathematicsResearchPolicy(
      createHeadlessMathematicsTeamProfile(undefined, options),
      researchPolicy,
      options
    );
  const baseProfile = createDeepScientistModeTeamProfile(
    { schema: 'deepscientist.mode_stack.v1', primary: 'science', overlays: ['mathematical-research'] },
    {
      agentLimit: 3,
      reasoningConcurrency: 3,
      mathematicsRouteDiscovery: options.mathematicsRouteDiscovery ?? true,
      mathematicsSecondProofOwner: options.secondProofOwner === true && options.benchmarkMethod !== 'single_worker',
    }
  );
  const profile =
    options.benchmarkMethod === 'single_worker'
      ? {
          ...baseProfile,
          pool: Object.freeze({ ...baseProfile.pool, agentLimit: 1, reasoningConcurrency: 1 }),
          roles: baseProfile.roles.filter((role) => role.kind === 'lead' || role.laneId === 'lean-engineering'),
        }
      : baseProfile;
  return Object.freeze({
    ...profile,
    exclusiveCapabilities: Object.freeze([]),
    coordinationRules: Object.freeze([
      'The Lead chooses objectives, dependencies and assignment order. Available slots do not prescribe a workflow.',
      options.benchmarkMethod === 'single_worker'
        ? 'This baseline has one Worker. The Lead coordinates that Worker and integrates its evidence; do not provision additional Workers.'
        : 'Delegate distinct useful work; integrate completed deliveries before declaring the complete problem solved.',
    ]),
    roles: Object.freeze(
      profile.roles.map((role) =>
        Object.freeze({
          ...role,
          ...(role.kind === 'lead'
            ? {
                authority: Object.freeze({ ...role.authority, runCanonicalEvaluation: false, publishReport: false }),
                allowedTools: Object.freeze([
                  {
                    toolName: 'research_team',
                    actions: Object.freeze(['describe', 'dispatch', 'status', 'integrate', 'read_artifact']),
                  },
                  { toolName: 'project_workspace', actions: Object.freeze(['status', 'checkpoint']) },
                  { toolName: 'lean_workspace', actions: mathWorkspaceRoleActions('lead') },
                ]),
                deniedTools: Object.freeze([
                  ...role.deniedTools,
                  { toolName: 'formal_verifier', actions: '*' as const },
                ]),
              }
            : {
                allowedTools: Object.freeze(
                  role.allowedTools
                    .filter((tool) => tool.toolName !== 'math_research')
                    .map((tool) =>
                      tool.toolName === 'research_team'
                        ? Object.freeze({
                            ...tool,
                            actions: Object.freeze(['deliver', 'share', 'read_artifact', 'read_feedback']),
                          })
                        : tool.toolName === 'lean_workspace' && role.laneId === 'strategy-exploration'
                          ? Object.freeze({ ...tool, actions: Object.freeze([...new Set([...tool.actions, 'probe'])]) })
                          : tool
                    )
                ),
              }),
          prompt:
            role.kind === 'lead'
              ? [
                  'You are the Mathematics Lead and sole integrator. Own the frozen original target, established facts and the decisive missing implication. Explain how proposed lemmas connect to the target.',
                  'Workers may change mathematical approach, introduce useful lemmas and search relevant facts without route approval. Use current source, real Lean feedback and durable deliveries to decide whether to continue, request independent research or integrate.',
                  'Name each gap with research_question:{statement,assumptions,targetConnection}. observation.research_graph shows IDs, evidence versions, producers, consumers and provisional reports. Rewording cannot duplicate question/evidence; the graph organizes work and never certifies truth. Proof owners may wait for a bound question while independent work runs.',
                  'Dispatch kind=research for bounded auxiliary proof production or scrutiny, with a concise report, or kind=formalize for complete targets. Bind research consumers with exact active/blocked proof IDs from status. Retry the same kind and consumers; slot labels do not change acceptance.',
                  'Use at most two complementary research tasks. Start independent necessary helpers with known inputs and stable consumer interfaces in the initial wave; do not wait until the owner reaches each blocker. Request checked auxiliary Lean code for a stable required claim, or a decisive test for an uncertain conjecture. Supply exact hypotheses and the intended call. Researchers may question an auxiliary goal. Delegate only residual gaps and overlap production with downstream explicit-parameter work; cyclic conditions prove neither claim. Simple repairs stay with the owner; leave unnecessary slots idle.',
                  `${options.secondProofOwner === true && options.benchmarkMethod !== 'single_worker' ? 'Coordinate the proof owners (the primary Lean Engineer and, when you use it, the second one on a different decomposition)' : 'Coordinate the persistent proof owner'} rather than privately solving a competing full proof. Choose research or formalization from the bottleneck; neither lane must run first. A nonterminal share can justify independent research without ending the proof assignment. Send the precise question, its role in the argument and authorized evidence. Avoid duplicate objectives merely because capacity is idle. Use research_team dispatch, status and integrate; only accepted dispatches represent work. Return findings to the same proof owner through the lawful path. Wait for notifications while Workers run instead of polling.`,
                  'Integrate useful results into the main argument and inspect remaining gaps. Only a valid original-target receipt establishes completion; partial and blocked results remain research inputs.',
                  'Short conditional use or a decisive mechanism check should shape uncertain claims. A residual goal may come from the chosen route, not the original theorem: seek an actual alternative connection when evidence warrants it. If the producer changes L0 to L1, preserve the consumer via a checked L1-to-L0 adapter when possible; otherwise repair the affected use. Revisit old work only with a new fact or targeted revision. Consume findings without waiting for a whole batch; resolve challenges before adoption. Avoid mandatory rituals. When integration backs up, stop new research. Notes are not proof authority.',
                  'Never read reference answers, previous solution runs or evaluator-private material. Independent evaluation is outside this Team.',
                ].join('\n')
              : [
                  MATHEMATICS_WORKER_ASSIGNMENT_SCOPE,
                  'Use assignment-bound lean_workspace probe for checked Lean feedback. Omit assignmentId to bind the current task automatically; never reconstruct an opaque ID. Inspect local files and Git changes through the terminal. project_workspace status and checkpoint belong to the Lead and are not Worker tools.',
                  ...(role.laneId === 'lean-engineering' && role.id.endsWith('-2')
                    ? [
                        'For kind="formalize": You are the second proof owner. Prove the complete original theorem through a decomposition that is structurally different from the primary Lean Engineer\'s route, as named in your assignment; do not read or copy another Worker\'s worktree. The first host-verified integration wins and the other assignment is superseded automatically.',
                      ]
                    : []),
                  'Preserve target and checked work; no route approval. Keep gaps and next action in RESEARCH.md. Never restore the original seed merely because the target is unfinished; retain compiling helpers and their Git checkpoints.',
                  role.laneId === 'lean-engineering'
                    ? 'Own the original target. A residual goal is not automatically necessary: trace helper/representation burdens; seek checked connections. Share exact goals and original hypotheses. Do not always select the hardest, easiest or weakest lemma.'
                    : 'For a missing construction, name the object type and required relations; justify a candidate form, substitute it and refine unmet conditions. Separate sufficient choices from necessary ones; one failed family does not refute the target. Trace route-added premises and return a checked local connection, revised claim or exact obstruction; unproved claims remain unknown.',
                  role.laneId === 'lean-engineering'
                    ? 'Before retries distinguish errors, missing premises, counterexamples and open gaps. Failure to prove is not refutation. Recheck old witnesses. Check the whole candidate with lean_workspace action="probe", probeMode="compile", probeSourceFile set to the project-relative assigned source path. Use sourceProbe only for a specific tactic span, never as a substitute for whole-file compilation. Repair the first syntax or type diagnostic directly in the current file, then check the changed candidate; do not wait for Lead approval or repeat a blocker report for a local repair. Terminal checks are not frozen evidence. Check delivered bytes.'
                    : 'Explore interfaces. Producers prove stable required claims; test uncertain mechanisms first. Consumers use private explicit parameters. Feed sourceProbe goals and diagnostics back before long work. Once a required auxiliary claim compiles in private Aux.lean, freeze that file as source evidence and deliver it immediately with its exact hypotheses, dependencies and intended call; do not wait for other helpers or polish the report. The Lead can adopt it while the main proof continues. Send corrected claims to earlier recipients lawfully. A closed local sourceProbe span does not establish whole-file success. Conditional work proves neither premise nor target; preserve consumers via a checked adapter. Canonical files read-only; check private Aux.lean with scoped sourceProbe and frozen Lean; no axioms or final-target authority.',
                  role.laneId === 'lean-engineering'
                    ? 'Query the intended transformation via lean_workspace searchMode=premises, premiseQuery and live goal; applyBest=false prevents adoption. Read full local types (#check @/#print), instantiate here; delegate only residual gaps, preserving formulas/witnesses.'
                    : 'Query authorized local library files with available tools, else request frozen findings via Lead. Read full types (#check @/#print), try private sourceProbe; return calls, conditions and goals/mismatch. Reuse findings; no match is not refutation.',
                  ...(role.laneId === 'lean-engineering'
                    ? [
                        'Read frozen auxiliary source via research_team action="read_artifact", artifact_ref copied exactly from supplied findings; follow nextOffsetBytes until the relevant declarations and dependencies are complete. read_feedback retrieves findings, not artifact bytes. Prefer adopting that proof to proving it again: order dependencies in Submission.lean; preserve original definitions; check section variables, implicit parameters and instances. No active peer reads/new imports. Share mismatches; derive premises from the original problem. A direct simpler proof remains allowed.',
                      ]
                    : []),
                  'Use read_artifact only when helpful. Align objects, operations, assumptions and return to target: theorem reuse differs from mechanism transfer. Never invent structure. Recheck applicability when hypotheses change. Isolate conjectures. Unused helpers are not adopted. Original-target completion requires independent verification; a research assignment completes with its scoped report.',
                ].join('\n'),
        })
      )
    ),
  });
}

function resolveDescriptor(modeStack: ModeStack): ProfileDescriptor {
  if (modeStack.overlays.includes('target-discovery')) return DESCRIPTORS['target-discovery-team'];
  if (modeStack.overlays.includes('mathematical-research')) return DESCRIPTORS['mathematics-research-team'];
  if (modeStack.primary === 'medical-evidence') return DESCRIPTORS['medical-evidence-team'];
  if (modeStack.primary === 'financial') return DESCRIPTORS['financial-research-team'];
  if (modeStack.primary === 'science') return DESCRIPTORS['science-research-team'];
  return DESCRIPTORS['project-research-team'];
}

function createLeadRole(profileDescriptor: ProfileDescriptor, roleId: string): ResearchTeamRoleContract {
  const allowedTools = profileDescriptor.exclusiveTool
    ? Object.freeze([
        ...LEAD_ALLOWED_TOOLS,
        Object.freeze({
          toolName: profileDescriptor.exclusiveTool.toolName,
          actions: Object.freeze([...profileDescriptor.exclusiveTool.actions]),
        }),
      ])
    : LEAD_ALLOWED_TOOLS;
  const isMathematics = profileDescriptor.id === 'mathematics-research-team';
  const sharedInstructions = isMathematics
    ? [
        'You are the sole Mathematics Team Lead and canonical integrator.',
        'Keep one persistent Lean Engineer as original-target owner. Use the live roster, never a hardcoded slot alias. Assign up to two complementary research questions only when their inputs and distinct purpose are ready; do not wait for a batch or duplicate a full proof. End the turn for Core events instead of polling. Never call Codex native spawn_agent, wait, wait_agent, or yield_control; these are not Core-managed workers.',
        'In the first wave dispatch at most one Worker per lane. Keep the second strategy slot idle until a delivery exposes a disjoint question; assign only that bounded task.',
        'The owner retains the main candidate; auxiliary drafts remain isolated. Integrate its checked complete candidate, then use the independent evaluator.',
      ]
    : [
        'You are the sole DeepScientist Team Lead and the only canonical integrator.',
        'First inspect the task and current Project Git state. Delegate only independent bounded work that materially improves speed or review quality.',
        'For the first non-trivial coordination step, call research_team(action="describe") once. Use only research_team for managed dispatch, status, and integration; never route this work through a generic Team member or message tool. Use the short roster agent_id in compatibility target_slot_id fields.',
        'The bounded wait surface is Lead-only: use research_team(action="status", wait_level="1m"|"5m"|"10m") at most once when a transition needs observation, then end the turn. Never call Codex native spawn_agent, wait, wait_agent, or yield_control; they cannot observe DeepScientist Workers. Workers never poll; Core wakes the Lead with delivery or terminal-failure events.',
        'Before dispatch, build one shared capability preflight covering execution surface, required tools or CLI, credential presence (never values), network, data, compute, and any paid or submission authorization. Reuse it across assignments; do not make every Worker rediscover the same missing capability.',
        'Before each wave, make a compact route slate: route/lane, independent evidence surface, dependencies, expected information gain, cost, and acceptance signal. Dispatch the smallest set that can change the decision; one route is correct when it is dominant, and multiple routes are justified only when they are independent and materially improve coverage. Never dispatch by slot quota.',
        'In the first wave use at most one Worker per distinct lane. Keep duplicate-lane slots idle until a delivery exposes a new, explicitly disjoint evidence source, method, or review question. Never exceed reasoningConcurrency.',
        'Preserve each receipt and end the turn while Workers run. For a long external job, submit once, persist its job or attempt id, and resume on an event or bounded backoff; do not hold a reasoning turn in a tight wait loop.',
        'Accept reviewed advisory deliveries directly. For artifact work, integrate only exact reviewed Worker commits and reject foreign branches, missing evidence, incomplete falsification, and unverified claims.',
      ];
  return Object.freeze({
    id: roleId,
    kind: 'lead',
    displayName: profileDescriptor.leadName,
    authority: LEAD_AUTHORITY,
    allowedTools,
    deniedTools: Object.freeze([]),
    prompt: [...sharedInstructions, ...profileDescriptor.leadInstructions, profileDescriptor.publicationGate].join(
      '\n'
    ),
  });
}

function createWorkerRole(
  profileDescriptor: ProfileDescriptor,
  workerLane: ResearchTeamLaneContract,
  laneOccurrence: number
): ResearchTeamRoleContract {
  const suffix = laneOccurrence > 1 ? `-${laneOccurrence}` : '';
  const displaySuffix = laneOccurrence > 1 ? ` ${laneOccurrence}` : '';
  const isMathematics = profileDescriptor.id === 'mathematics-research-team';
  const sharedWorkerInstructions = isMathematics
    ? [
        'Accept one atomic assignment with acceptance and failure criteria and an explicit executionMode.',
        'Deliver through research_team(action="deliver"). Do not dispatch, mutate canonical state, submit, checkpoint, publish, or poll.',
        'Never call Codex native spawn_agent, wait, wait_agent, or yield_control; DeepScientist Workers are Core-managed conversations, not Codex child threads.',
        'Bound diagnostic output at the command source: filter process inspection before printing, write large symbolic intermediates to the workspace, and keep visible output to the factorization, zero residual, or certificate summary needed by the assignment.',
      ].join('\n')
    : SHARED_WORKER_INSTRUCTIONS;
  const allowedTools =
    workerLane.id === 'strategy-exploration' && isMathematics
      ? MATHEMATICS_STRATEGY_ALLOWED_TOOLS
      : workerLane.id === 'lean-engineering'
        ? MATHEMATICS_FORMALIZER_ALLOWED_TOOLS
        : workerLane.id === 'independent-review'
          ? MATHEMATICS_REVIEWER_ALLOWED_TOOLS
          : isMathematics
            ? MATHEMATICS_WORKER_ALLOWED_TOOLS
            : WORKER_ALLOWED_TOOLS;
  const mathematicsInstructions = isMathematics
    ? [
        'Follow the assignment resultContract as the sole return schema; it is injected by the runtime. Do not call describe. Do not reconstruct runtime-supplied fields from this prompt.',
        'Use math.actionContract as the compact working context: start from activeObligation, requiredEvidence, nextAction and failureTransition. Do not restate or reread the full research archive when those fields are sufficient; request more research context only for a missing field or an explicitly changed bottleneck.',
        'Read the researchContract first. Its insights are a bounded archive: use only entries whose usableWhen applies to the activeBottleneck, and do not replay an archived failure without its listed repair or changed conditions. When a MathProblemContract is present, also reject any mismatch between the informal statement, Lean statement, hashes, assumptions, target commit, or official acceptance command.',
        ...(workerLane.id === 'strategy-exploration'
          ? [
              'For ordinary discovery, perform exactly one assigned function: strategy, literature/theorem retrieval, experiment or counterexample search, bounded problem-family transfer, natural-language proof development, or adversarial critique. Return mathResearchFinding with a short mechanism naming the mathematical idea shared by cosmetic route variants, mainlineImpact (mainline_advanced, route_refuted, supporting, or stalled), nextProbeKind (literature, example, computation, counterexample, problem_family, proof_step, obstruction, or critique), and bottleneckUpdate when the active bottleneck changes. Runtime evidence, not the self-reported impact or amount of prose, decides whether the mainline advanced. bottleneckUpdate must name one target, mark it resolved/narrowed/unchanged/refuted, and include diagnosis plus the smallest repair when a failure category is present. If an independent lookup, computation, counterexample, or problem-family check would unblock that bottleneck, request a helperRequest tied to it; each helper is short-lived and must return a result, not open another route. A problem_family probe must return nearby instances, each marked supports/counterexample/inconclusive, plus sharedMechanism or firstCounterexample and an overall generalization outcome; never assign one Agent per instance. Use solutionSketchRef only for an existing short project-local reference; never inline a long proof sketch in the contract. What changed, evidence, remaining obligations, and one next action are still required. Choose nextProbeKind by the current bottleneck, not by the function just completed. Mark stalled when the active bottleneck and next decisive action are unchanged. Do not create a proof DAG.',
              'This lane is a single bounded episode. A targeted retrieval or one assignment-bound discriminating probe is enough to establish an actionable bridge, falsification, or exact missing dependency. As soon as that evidence exists, stop using the terminal and make research_team(action="deliver") the next tool call in the same turn. A precise missing Mathlib declaration is valid route evidence for the Lead; it does not terminate the original theorem, and it does not justify another open-ended search loop.',
              'This strategy lane may use only lean_workspace counterexample for an assignment-bound bounded falsification probe. It is not authorized for lean_workspace probe, search, execute, certify, preflight, package adoption, or any source-writing action. The host creates and removes the disposable probe file; keep canonical source unchanged and never claim a proof receipt from sampled evidence.',
              'The injected methodContract is runtime-owned and mandatory. Stay inside its single method and routeBoundary, obey every prohibited action, and deliver as soon as its requiredOutcome or stopRule is met. A symbolic or API lane must not drift into numerical route search; a computation lane must convert its bounded experiment into a symbolic claim or obstruction instead of extending the sweep.',
              'Use lean_workspace counterexample for bounded experiments. Deliver its observationEvidence.reference and exact statement with the finding so the runtime can authenticate the observation. A finite sample does not prove a universal claim. Leave proof compilation and canonical source changes to the Lean Engineer.',
              'When math.mechanismCapsules are supplied, inspect the capsules before exploring. Reuse every capsule whose structural mechanism fits the active bottleneck and state the match reason in the finding; otherwise continue independently and briefly state why a capsule does not apply. Capsules are search priors, not proof or verification evidence.',
              'Only routeProposalMode=candidate enters formal proof planning. It may be used before FORMALIZE when target inspection finds no concrete route, after a direct candidate fails structurally, or when the runtime directs replanning. In this one route-candidate episode, propose one structurally distinct route, state its mathematical mechanism in structuralCommitment, execute its cheapest decisive test, and discard it if refuted. Competing candidates must differ in mechanism, not just wording or route fingerprint. Return one whole candidate or the shortest linear proof plan; use a branching DAG only when genuinely independent lemmas justify parallel work. Keep one goal, provisional Lean statements, one mathematical/Lean-use bridge per edge, and node-complete premise coverage.',
              'An advancing route must expose its decisive test, falsification signal, and retained probe evidence. Leave cross-candidate selection to the Lead. On a resumable stop, record the first useful fault and avoid repeating a known route pattern.',
              'When the assignment explicitly asks for obstruction synthesis, compare the supplied failed routes and return one obstruction finding with the shared mechanism, evidence, affected approaches, and one decisive next action. Do not propose another cosmetic route variation.',
              'Obey math.sessionContinuation. Candidate repair reuses the source Worker slot and its context. Critic work always arrives on a different slot with an independent context. Alternate-route and bottleneck-helper work uses a different compatible slot when one exists; a minimal Team may reuse the source slot, while an alternate route must still change its route fingerprint. A bottleneck helper preserves the source route and returns its finding to the Lead. Work read-only without edits or commits, and do not self-certify the route assessment.',
            ]
          : workerLane.id === 'lean-engineering'
            ? [
                ...(laneOccurrence > 1
                  ? [
                      "You are the second proof owner. Prove the complete original theorem through a decomposition that is structurally different from the primary Lean Engineer's route, as named in your assignment; do not read or copy another Worker's worktree. The first host-verified integration wins and the other assignment is superseded automatically.",
                    ]
                  : []),
                'Use only the assigned persistent worktree and commit each retained checkpoint. This is the proof-mainline Worker: own the complete candidate, preserve the global proof context, and continue from the first unresolved Lean diagnostic.',
                'When reporting firstLeanErrorOffsetBefore/After, use only non-negative character offsets from the diagnostic text, or omit the fields. Never put a file:line:column string in an offset field; keep source locations inside firstLeanErrorBefore/After.',
                'Use lean_workspace probe or search with proofSession.sourceFile and the current expectedSourceHash to continue a persistent proof session. Search returns a draft; applyBest explicitly accepts it only if the source is unchanged. Inspect remainingGoals and diagnostics, then continue the next unresolved dependency. Session results are local feedback, not final kernel acceptance.',
                'Use lean_workspace branches and checkout to resume saved alternatives after a stall. Select goalIndex when several goals remain; continue candidate batches with nextCandidateOffset instead of repeating exhausted actions. Compare branch obligations and retain verified dependencies.',
                'This proof episode has no token or wall-clock cutoff. Drive it by semantic state: after each meaningful source edit, changed goal fingerprint, or newly verified helper, continue from that evidence. Begin with a concrete candidate in the assigned worktree and compile it before any broad library reconnaissance. Once a targeted lookup and the resulting Lean diagnostic identify an exact semantic bottleneck, stop widening the search: construct the smallest helper or revise the route. To surface the bottleneck, use research_team(action="share") with the best retained checkpoint, the first unresolved dependency, the evidence already collected, and one concrete next action; share keeps this assignment and its context, deliver ends it. A missing declaration alone is not a theorem impossibility.',
                'Obey the runtime-supplied formalizationPolicy. Missing Mathlib theorems, high-level APIs, and domain constructions on a concrete route are proof dependencies, not infrastructure failures: map the dependency graph, implement the smallest helper in authorized files, compile that boundary, retain the best compiling state, and continue from the next dependency. Report blocked only when Lean or a required execution service cannot run, or the authorized files cannot be written; do not deliver a catalog of missing APIs.',
                'When directAttempt=true, own the complete whole-problem claim named by the assignment; no proofPack or routeSelection is needed in proof-mainline mode. Treat the assignment as one continuous solver episode: repeat Lean/compiler feedback and concrete non-duplicate repairs on the same candidate until the complete theorem closes or infrastructure fails. A refuted route or a failed candidate family is a reason to revise the route inside this assignment, not to end it. Keep ordinary helper checkpoints inside the current assignment and worktree; do not deliver them as completed work. Revise local decomposition when evidence supports it; a better premise can justify proposing a main-route change even without refutation. Keep the current main route until the Lead accepts the exact proposal through the supported assignment adapter. Validate premiseHints against the live Lean goal. After unknown_identifier, type_mismatch, or a real proof stall, consider targeted premise retrieval when it can change the next proof step. Reuse candidates only while their full source and dependency context remains unchanged.',
                'For a fresh proof, read the target once and confirm that the assignment supplies, or the target immediately reveals, a controlling lemma, invariant, direct tactic, or dependency-ordered Lean skeleton. Only then make the first meaningful proof edit. If no mathematical route exists, return one route-not-ready result naming the missing bridge so Strategy can repair it. Along a concrete route, absence of a convenient declaration is not route-not-ready: work one dependency-ready theorem or shared-helper cluster at a time, check at that semantic boundary, and let the first real compiler error drive one targeted premise lookup. Prefer direct library lemmas, simpa using, omega, norm_num, and small local helper lemmas over repeated exploratory automation.',
                'Treat any injected failure or proof-state history as recovery memory, not an action taxonomy: do not replay a listed failed action or visited state, and continue adaptively from the best novel state.',
                'Keep the complete candidate in this one Worker episode. Repair only the first unresolved bottleneck, retain compatible kernel-verified lemmas, and checkpoint only for pause/resume, route change, or infrastructure failure. Never invent runtime identity, plan snapshots, classifier output, or verification receipts.',
              ]
            : [
                'Start fresh only after a local-gate receipt. Work read-only without file edits, commits, or Lean execution; independently compare the named declaration with both problem statements and audit the frozen kernel receipt. Record sound, gap, or wrong. For gap, identify the first fault and one repair target on the same candidate; for wrong, identify the structural reason to abandon the route.',
              ]),
      ].join('\n')
    : '';
  return Object.freeze({
    id: `${profileDescriptor.id}-worker-${workerLane.id}${suffix}`,
    kind: 'worker',
    displayName: `${workerLane.displayName}${displaySuffix}`,
    laneId: workerLane.id,
    authority: WORKER_AUTHORITY,
    allowedTools,
    deniedTools: isMathematics ? MATHEMATICS_WORKER_DENIED_TOOLS : WORKER_DENIED_TOOLS,
    prompt: `${sharedWorkerInstructions}\n${mathematicsInstructions ? `${mathematicsInstructions}\n` : ''}Lane purpose: ${workerLane.purpose}\nRequired deliverables: ${workerLane.deliverables.join('; ')}.`,
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

function makeDescriptor(
  id: ProfileDescriptor['id'],
  workflowId: string,
  displayName: string,
  leadName: string,
  lanes: readonly ResearchTeamLaneContract[],
  leadInstructions: readonly string[],
  publicationGate: string,
  exclusiveTool?: ProfileDescriptor['exclusiveTool']
): ProfileDescriptor {
  return Object.freeze({
    id,
    workflowId,
    displayName,
    leadName,
    lanes: Object.freeze(lanes),
    leadInstructions: Object.freeze(leadInstructions),
    publicationGate,
    exclusiveTool,
  });
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
