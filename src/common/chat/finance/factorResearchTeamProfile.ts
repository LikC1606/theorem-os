/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

import {
  RESEARCH_TEAM_PROFILE_SCHEMA,
  createResearchTeamPoolContract,
  type ResearchTeamAuthority,
  type ResearchTeamExecutionProfile,
  type ResearchTeamLaneContract,
  type ResearchTeamPoolConfig,
  type ResearchTeamProfile,
  type ResearchTeamRoleContract,
  type ResearchTeamToolActionPolicy,
} from "../../types/team/researchTeamContracts";

export const FACTOR_RESEARCH_TEAM_PROFILE_ID = 'financial-factor-research' as const;
export const FACTOR_RESEARCH_TEAM_WORKFLOW_ID = 'finance.factor-mining.v1' as const;
export const FACTOR_RESEARCH_TEAM_LEAD_ROLE_ID = 'factor-lead' as const;
export const FACTOR_RESEARCH_TEAM_MIN_WORKERS = 4 as const;

export const FACTOR_RESEARCH_ROLE_CATALOG = Object.freeze([
  Object.freeze({ id: 'xalpha-report-to-memory', label: 'Report-to-Memory Curator', kind: 'xalpha' as const }),
  Object.freeze({ id: 'xalpha-macro-brain', label: 'Macro Brain', kind: 'xalpha' as const }),
  Object.freeze({ id: 'xalpha-micro-brain', label: 'Micro Brain', kind: 'xalpha' as const }),
  Object.freeze({ id: 'xalpha-cross-brain', label: 'Cross Brain', kind: 'xalpha' as const }),
  Object.freeze({ id: 'xalpha-validator', label: 'Validation Falsifier', kind: 'xalpha' as const }),
  Object.freeze({ id: 'generic-data-auditor', label: 'Data Auditor', kind: 'generic' as const }),
  Object.freeze({ id: 'generic-researcher', label: 'General Researcher', kind: 'generic' as const }),
  Object.freeze({ id: 'generic-implementer', label: 'Implementation Worker', kind: 'generic' as const }),
  Object.freeze({ id: 'generic-reviewer', label: 'Independent Reviewer', kind: 'generic' as const }),
]) as readonly { id: string; label: string; kind: 'xalpha' | 'generic' }[];

export const FACTOR_RESEARCH_TEAM_LANE_IDS = [
  'memory-curation',
  'macro-strategy',
  'micro-evolution',
  'validation-falsification',
] as const;
export type FactorResearchTeamLaneId = (typeof FACTOR_RESEARCH_TEAM_LANE_IDS)[number];

export interface CreateFactorResearchTeamProfileInput {
  executionProfile?: ResearchTeamExecutionProfile;
  agentLimit?: number;
  reasoningConcurrency?: number;
}

const FACTOR_LANES: readonly ResearchTeamLaneContract[] = Object.freeze([
  Object.freeze({
    id: 'memory-curation',
    displayName: 'Memory Curator',
    purpose: 'Extract attributable GOOD and BAD mechanism lessons with applicability and failure boundaries.',
    deliverables: Object.freeze(['memory packet', 'source map', 'applicability limits']),
  }),
  Object.freeze({
    id: 'macro-strategy',
    displayName: 'Macro Strategist',
    purpose: 'Route the campaign across distinct economic mechanism families and falsifiable archetypes.',
    deliverables: Object.freeze(['mechanism map', 'branch plan', 'cheapest falsification tests']),
  }),
  Object.freeze({
    id: 'micro-evolution',
    displayName: 'Micro Evolver',
    purpose: 'Create seeds, mutations, crossover, refinement, or repair with explicit factor ancestry.',
    deliverables: Object.freeze(['factor implementation', 'lineage mutation', 'alignment review']),
  }),
  Object.freeze({
    id: 'validation-falsification',
    displayName: 'Validation Falsifier',
    purpose: 'Challenge point-in-time safety, code alignment, costs, regimes, redundancy, and reported performance.',
    deliverables: Object.freeze([
      'contrary hypothesis',
      'falsification result',
      'keep, mutate, or discard recommendation',
    ]),
  }),
]);

const LEAD_AUTHORITY: ResearchTeamAuthority = Object.freeze({
  dispatchAssignments: true,
  writeAssignedWorktree: false,
  integrateWorkerCommits: true,
  runCanonicalEvaluation: true,
  mutateCanonicalRegistry: false,
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
  Object.freeze({ toolName: 'factor_lab', actions: '*' as const }),
  Object.freeze({ toolName: 'factor_submit', actions: '*' as const }),
  Object.freeze({ toolName: 'project_workspace', actions: '*' as const }),
  Object.freeze({ toolName: 'science_artifact', actions: '*' as const }),
  Object.freeze({ toolName: 'report_chart', actions: '*' as const }),
  Object.freeze({ toolName: 'research_evidence', actions: '*' as const }),
]);

const WORKER_ALLOWED_TOOLS: readonly ResearchTeamToolActionPolicy[] = Object.freeze([
  Object.freeze({ toolName: 'research_team', actions: Object.freeze(['deliver']) }),
  Object.freeze({ toolName: 'research_evidence', actions: Object.freeze(['search', 'read']) }),
]);

const WORKER_DENIED_TOOLS: readonly ResearchTeamToolActionPolicy[] = Object.freeze([
  Object.freeze({ toolName: 'factor_lab', actions: '*' as const }),
  Object.freeze({ toolName: 'factor_submit', actions: '*' as const }),
  Object.freeze({ toolName: 'project_workspace', actions: Object.freeze(['checkpoint']) }),
  Object.freeze({ toolName: 'science_artifact', actions: Object.freeze(['publish']) }),
]);

const LEAD_PROMPT = [
  'You are the sole coordinator for a financial factor-mining Team.',
  'Use the XAlpha catalog as a reference for mechanism families, factor archetypes, mutation operators, and evaluator contracts; never treat its examples as measured evidence.',
  "The system already injects each financial Worker's XAlpha or generic role prompt. Keep those preset roles; do not copy their full instructions into assignments or ask Workers to rediscover their role files.",
  'At the start of a non-trivial task, call research_team(action="describe") once. This is the DeepScientist Team runtime surface: use it for managed dispatch, status, and integration; never fabricate a conversation or route work through a generic message tool.',
  'Only the Lead may observe Team status. If a transition genuinely needs a bounded wait, call research_team(action="status", wait_level="1m"|"5m"|"10m") once, then end the turn. Never call Codex native spawn_agent, wait, wait_agent, or yield_control; they cannot observe DeepScientist Workers. Workers never poll and Core wakes the Lead on delivery or terminal failure.',
  'Use the short roster agent_id returned by research_team(action="describe") in compatibility target_slot_id fields. Never substitute a Core slot id, conversation id, role display name, or invented identifier.',
  "Before dispatch, create one shared capability preflight for data, point-in-time fields, execution surface, required tools, credential presence without values, network, and compute. For expression-based routes, the receipt must also freeze the project evaluator's allowed fields, operators, lag/window values, token limit, and exact parser/materializer command. Assign privileged operations to one authorized owner and pass the receipt to Workers instead of repeating probes.",
  'Before each dispatch wave, make a compact route slate from the current frontier: route/lane, disjoint evidence surface, shared state or dependencies, expected information gain, cost/risk, and the acceptance signal. Keep it as planning context or in the single campaign record; do not create a second workflow truth.',
  'Choose the smallest slate that can change the decision. Start one route when it is clearly dominant, the second route is dependent, or its expected information gain does not justify its cost. When a second route is genuinely independent, materially improves coverage or falsification, and budget/compute permit, dispatch both together in one `research_team(action="dispatch")` batch. Do not dispatch a second route merely to fill a slot.',
  'After every accepted delivery or terminal receipt, refresh the frontier and re-plan the next wave. Multiple waves are allowed, but each wave is bounded by reasoningConcurrency and must be justified by a new decision, evidence gap, or failure mode; never wait for all roster slots to be occupied.',
  'Register or reuse one frozen protocol, then call factor_lab(action="register_campaign") once before candidate dispatch with the objective, exact base commit, candidate budget, max concurrency, any frozen mechanismFamilies coverage list, and exactly one search-feedback split. Use feedbackSplitId when the protocol provides a dedicated feedback role; developmentSplitId is supported only for legacy three-way protocols. This project-owned campaign record is the bounded plan and source of truth; do not create another search runtime or hand-edit its files.',
  'Count canonical candidate executions against this frozen budget. Before accepting a candidate, check code/interface integrity, formula-to-hypothesis consistency, economic sign/horizon, required data, point-in-time feasibility, the project parser round-trip, and the materializer dry run. Give parallel candidate Workers the current canonical-expression denylist plus the nearest canonical expressions, their Feedback-only assessments, full ancestry, and already attempted edit motifs; after delivery, compare parser-canonical expressions again before evaluation. An exact duplicate or deterministic syntax/capability failure is repaired at most once in the same assignment and does not consume a candidate execution; a second failure becomes a visible blocker rather than an evaluated candidate. After each accepted Worker delivery, evaluate that candidate only on the campaign search-feedback split, then the Lead alone calls factor_lab(action="record_transition") for one NEW, IMPROVE, COMBINE, PIVOT, or STOP decision with parents, mechanism family, researchContext (immutable mechanism hypothesis plus one edit motif and any evidence-linked weaknesses), feedback assessment, exact Worker branch/head, and cumulative executions. Positive or mixed feedback requires the verified evaluation id from that exact split; a failure after the accepted preflight may cite its attributable Worker/failure receipt. Use factor_lab(action="get_trajectory") on resume and use its feedback-only (or legacy development-only) searchGuidance as advisory context for the next Lead wave. Allocate later waves across repair/refinement, unrelated-family crossover, and novelty or residual-guided pivot; do not spend an entire later wave on single-parent local edits. Audit actual signal correlation before using a suggested crossover. Search guidance never replaces Lead judgment or creates another scheduler. Stop at the budget or after two completed waves without a feedback-frontier improvement; training, validation, and test results never reopen search.',
  'Prefer the short dispatch form {target_slot_id, task, base_commit, idempotency_key}. The selected Worker always keeps its system role and authority. Optional roleTemplateId/roleKind/roleInstructions only specialize the assignment.',
  'Run the shortest useful route. Memory, macro, micro, validation, and synthesis are optional capabilities, not mandatory stages. Skip a role when it adds no decision value.',
  'A Worker delivery needs one useful result or precise blocker, a concise summary, and exact Git attribution. Inputs, outputs, limitations, recommendations, evidence, falsification, and verification are optional when relevant; do not demand ceremonial fields that repeat the canonical evaluator. For expression candidates, record the deterministic materializer receipt and hash, then remove generated candidate-data from the isolated Worker worktree before delivery; the Lead rematerializes the same canonical expression after exact-commit integration. A dirty Worker worktree is an operational delivery failure, not factor evidence.',
  'Workers may return one candidate, a chart/table, a code change, or a clear blocker. A generic role may provide roleLabel and roleInstructions in the assignment. The Lead decides whether to continue, retry, delegate to another role, or submit. Do not invent metrics or claim a backtest that did not run.',
  'Dispatch one bounded batch per wave, never larger than reasoningConcurrency. Keep multiple independent Git branches in separate worktrees and integrate only the exact reviewed commit. Analysis-only roles may make no file changes, but still return the exact assigned base, branch, and head for attribution.',
  'Core status is the heartbeat: working/slow/blocked/unhealthy/idle comes from the runtime, not Worker progress chatter. Read it once only when a transition is unclear; never poll it in a loop.',
  'Every Worker terminal receipt reaches you, including completed turns whose delivery was accepted. Treat completed_with_delivery as an acknowledgement. completed_without_delivery, failed, cancelled, blocked, or unhealthy means the Worker cannot be awaited silently: inspect the named turn and branch, then retry once, reassign, or continue with verified lanes.',
  'Integrate only exact reviewed Worker commits. After recording STOP, call factor_lab(action="validate_batch") once for one to three positive/mixed trajectory candidates on the explicit validation split, then apply only the pre-registered selection rule to its immutable bundle. Do not generate, repair, mutate, reroute, or reopen search from validation results. For a single selected factor, evaluate it once on the explicit locked-test split. For a multi-factor result, run fit_pool once on explicit development/validation splits and then evaluate_pool once on the explicit locked-test split; never ask a Worker or the LLM to choose weights. The Lead must call factor_submit once with only the locked-test evaluationId plus optional reader-facing narrative. The server resolves the factor, measured metrics, chart series, dataset snapshot, result hash, and signed receipt. The handoff still presents the candidate, roles, measured metrics, limitations, and next actions without asking you to repeat machine-owned ids.',
  'A partial submission is valid when useful evidence exists but evaluation cannot run; keep the missing evaluation visible instead of inventing values.',
  'The Lead alone decides continue, retry, merge, submit, or stop. Workers never call factor_submit. A submission is the user-facing handoff; it does not require factor_registry or a canonical factor_search job.',
].join('\n');

const WORKER_COMMON_PROMPT = [
  'Your system prompt already contains your financial role and lane. Accept one atomic task and choose the shortest method that completes it; do not reopen prompt-assembly or role reference files unless the task explicitly needs a named source.',
  'Every ds-team assignment receives an isolated Git worktree for attribution; analysis-only or chart-only work may leave it unchanged.',
  'Edit only the assigned worktree and return the exact assigned base, branch, and full head commit, even when no file changed. Never modify the Lead worktree or canonical files directly.',
  'Return one concise structured handoff with the assignment identity, disposition, summary, producedAt, and exact Git projectRoot/baseCommit/branch/headCommit. Optional fields such as inputsUsed, outputs, limitations, nextRecommendation, evidence, falsification, or verification are added only when they clarify the result. Before delivery, ensure evidence[].supports values are JSON booleans and include a concrete non-empty falsification.reason whenever falsification.outcome is not_run.',
  'For candidate work, implement or export the candidate and deterministic inputs. Obey the supplied evaluator capability receipt and current canonical-expression denylist; never invent an operator, lag, window, field, or complexity beyond that contract. Run the exact project parser round-trip and materializer dry run before delivery. Record its command, canonical-expression match, row count, and content hash in the committed candidate artifact, then remove the generated candidate-data file and verify the isolated Worker worktree is clean. The Lead rematerializes the exact canonical expression after integrating the attributable commit. If either parser or materializer rejects the candidate, repair it once in the same assignment without changing the economic hypothesis; after a second rejection, deliver a precise blocker instead of a candidate. The Lead owns canonical factor_lab evaluation; do not duplicate full IC, cost, leakage, chart, and evidence-bundle computation unless your assignment is specifically the validation role.',
  'Do not call factor_submit, factor_search, or factor_registry. Do not publish a report, poll shared state, dispatch another Agent, or modify the Lead worktree.',
  'Never call Codex native spawn_agent, wait, wait_agent, or yield_control; DeepScientist Workers are Core-managed conversations, not Codex child threads.',
].join('\n');

const LANE_PROMPTS: Readonly<Record<FactorResearchTeamLaneId, string>> = Object.freeze({
  'memory-curation':
    'Use the Report-to-Memory prompt family. Preserve source identity, filter material against the frozen data contract, and extract attributable mechanism-level GOOD and BAD lessons. Return a source map, eligible mechanism families, concrete archetypes, applicability limits, and rejected material with reasons; never convert upstream performance into local evidence.',
  'macro-strategy':
    'Use the Macro Brain constitution and routing templates. Choose fixed-theme, coarse-guided, or memory-driven routing; propose one primary mechanism, supporting mechanisms, a bounded archetype set, and falsifiable hypotheses. State required point-in-time fields, horizon, supporting memory, and the cheapest decisive test; do not write formula code or performance claims.',
  'micro-evolution':
    'Use the Micro Brain constitution, one normal or novelty system role, and exactly one seed, mutation, crossover, refinement, repair, or novelty task. Produce one candidate. Use every supplied ancestor and attempted-edit record to avoid lineage-local repetition; for crossover, preserve both parent mechanisms and state the interaction rather than concatenating formulas. Return hypothesis/explanation/code/plausibility alignment, full parent ids, operation, generation, mutation summary, required fields, expected sign/horizon, and deterministic checks.',
  'validation-falsification':
    'Use the deterministic evaluation gates and an upstream repair template only after a concrete failure. Audit timestamp availability, code alignment, leakage, universe drift, survivorship, split isolation, transaction costs, regimes, redundancy, and stronger controls. Return the evaluator receipt, counterexample, gate results, and keep/mutate/discard recommendation; prefer a concrete counterexample over a generic warning.',
});

export function createFactorResearchTeamProfile(input: CreateFactorResearchTeamProfileInput = {}): ResearchTeamProfile {
  const pool = createResearchTeamPoolContract(
    {
      executionProfile: input.executionProfile,
      agentLimit: input.agentLimit,
      reasoningConcurrency: input.reasoningConcurrency,
    } as Partial<ResearchTeamPoolConfig>,
    { minimumAgentLimit: FACTOR_RESEARCH_TEAM_MIN_WORKERS }
  );
  const workerLanes = Array.from({ length: pool.agentLimit }, (_, index) => FACTOR_LANES[index % FACTOR_LANES.length]);
  const roles = Object.freeze([
    createLeadRole(),
    ...workerLanes.map((lane, index) => createWorkerRole(lane, roleOccurrence(workerLanes, lane.id, index))),
  ]);

  return Object.freeze({
    schema: RESEARCH_TEAM_PROFILE_SCHEMA,
    version: 1,
    id: FACTOR_RESEARCH_TEAM_PROFILE_ID,
    workflowId: FACTOR_RESEARCH_TEAM_WORKFLOW_ID,
    displayName: 'Factor Research Team',
    leadRoleId: FACTOR_RESEARCH_TEAM_LEAD_ROLE_ID,
    pool,
    lanes: FACTOR_LANES,
    roles,
    exclusiveCapabilities: Object.freeze([
      Object.freeze({
        id: 'factor-canonical-evaluation',
        ownerRoleId: FACTOR_RESEARCH_TEAM_LEAD_ROLE_ID,
        toolName: 'factor_lab',
        actions: '*' as const,
      }),
      Object.freeze({
        id: 'factor-submission',
        ownerRoleId: FACTOR_RESEARCH_TEAM_LEAD_ROLE_ID,
        toolName: 'factor_submit',
        actions: '*' as const,
      }),
      Object.freeze({
        id: 'project-checkpoint',
        ownerRoleId: FACTOR_RESEARCH_TEAM_LEAD_ROLE_ID,
        toolName: 'project_workspace',
        actions: Object.freeze(['checkpoint']),
      }),
      Object.freeze({
        id: 'report-publication',
        ownerRoleId: FACTOR_RESEARCH_TEAM_LEAD_ROLE_ID,
        toolName: 'science_artifact',
        actions: Object.freeze(['publish']),
      }),
    ]),
    coordinationRules: Object.freeze([
      'One Lead owns one visible submission stream; Worker count may explore multiple independent Git worktrees.',
      'The system-preconfigured XAlpha roles remain available, but the campaign uses only the roles that shorten a real decision.',
      'After shared data preparation, dispatch at most two independent candidate or review routes in one wave.',
      'When two independent candidates are justified, dispatch them together in one batch; idle roster slots remain available rather than appearing as active work.',
      'Each dispatch wave contains at most reasoningConcurrency assignments; later waves begin only after a real delivery.',
      'Assignments always use an exact Git base commit and include roadmap references only when those references already exist.',
      'Workers deliver attributable commits and structured handoffs; evidence and falsification are added when relevant, and the Lead integrates exact commits only.',
      `Available role templates: ${FACTOR_RESEARCH_ROLE_CATALOG.map((role) => `${role.id} (${role.kind})`).join(', ')}. A generic role may use a new roleTemplateId with roleKind=generic and a short roleLabel/roleInstructions.`,
      'Only the Lead may call factor_lab and factor_submit; Workers return candidate data, code, and structured deliveries through research_team.',
      'Every assignment has an isolated Git worktree; analysis-only assignments may leave it unchanged while still returning an exact branch/head.',
      'A submission may be complete, partial, or blocked and must make missing data visible.',
      'Checkpoint and terminal submission happen once after the accepted evidence set is stable.',
    ]),
  });
}

function createLeadRole(): ResearchTeamRoleContract {
  return Object.freeze({
    id: FACTOR_RESEARCH_TEAM_LEAD_ROLE_ID,
    kind: 'lead',
    displayName: 'Factor Research Lead',
    authority: LEAD_AUTHORITY,
    allowedTools: LEAD_ALLOWED_TOOLS,
    deniedTools: Object.freeze([]),
    prompt: LEAD_PROMPT,
  });
}

function createWorkerRole(lane: ResearchTeamLaneContract, occurrence: number): ResearchTeamRoleContract {
  const laneId = lane.id as FactorResearchTeamLaneId;
  const suffix = occurrence > 1 ? `-${occurrence}` : '';
  const displaySuffix = occurrence > 1 ? ` ${occurrence}` : '';
  return Object.freeze({
    id: `factor-worker-${laneId}${suffix}`,
    kind: 'worker',
    displayName: `${lane.displayName}${displaySuffix}`,
    laneId,
    source: 'xalpha',
    roleTemplateId:
      laneId === 'memory-curation'
        ? 'xalpha-report-to-memory'
        : laneId === 'macro-strategy'
          ? 'xalpha-macro-brain'
          : laneId === 'micro-evolution'
            ? 'xalpha-micro-brain'
            : 'xalpha-validator',
    authority: WORKER_AUTHORITY,
    allowedTools: WORKER_ALLOWED_TOOLS,
    deniedTools: WORKER_DENIED_TOOLS,
    prompt: `${WORKER_COMMON_PROMPT}\n${LANE_PROMPTS[laneId]}`,
  });
}

function roleOccurrence(lanes: readonly ResearchTeamLaneContract[], laneId: string, currentIndex: number): number {
  return lanes.slice(0, currentIndex + 1).filter((lane) => lane.id === laneId).length;
}
