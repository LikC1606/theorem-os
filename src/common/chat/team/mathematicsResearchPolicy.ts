import type { ResearchTeamProfile } from "../../types/team/researchTeamContracts";

export const MATHEMATICS_RESEARCH_POLICY_ENV = 'DEEPSCIENTIST_MATH_RESEARCH_POLICY';
export const MATHEMATICS_RESEARCH_POLICIES = ['B', 'C', 'E', 'E-R', 'E-L'] as const;
export type MathematicsResearchPolicyId = (typeof MATHEMATICS_RESEARCH_POLICIES)[number];

export function mathematicsResearchPolicy(value: unknown) {
  if (typeof value !== 'string' || !MATHEMATICS_RESEARCH_POLICIES.includes(value as MathematicsResearchPolicyId)) {
    throw new Error('Mathematics research policy must be B, C, E, E-R or E-L.');
  }
  const id = value as MathematicsResearchPolicyId;
  return Object.freeze({
    schema: 'deepscientist.mathematics.research-policy.v1' as const,
    id,
    implementation: 'deepscientist-local-v7-v1',
    baselineOrigin:
      id === 'B' ? 'local-mathematics-adaptation' : id === 'C' ? 'local-strong-mathematics-baseline' : 'local-v7',
    organization:
      id === 'B'
        ? 'hypothesis-generation-selection'
        : id === 'C'
          ? 'autonomous-mathematics'
          : 'mathematical-feedback-and-dependencies',
    retrievalLoop: id === 'E' || id === 'E-L',
    explorationLoop: id === 'E' || id === 'E-R',
    candidateLimit: id === 'C' ? null : 4,
    findingsLimit: id === 'C' ? null : 15,
    retrievalRoundLimit: 2,
    explorationVersionLimit: 2,
    unproductiveExplorationLimit: 2,
    totalTokenLimit: 64_000,
    routePivotThreshold: 2,
  });
}

export type MathematicsResearchPolicy = ReturnType<typeof mathematicsResearchPolicy>;

/** Organization varies by experiment; the underlying mathematics permissions remain shared. */
export function applyMathematicsResearchPolicy(
  profile: ResearchTeamProfile,
  id: MathematicsResearchPolicyId,
  options: Readonly<{ unlimitedTokens?: boolean; mathematicsRouteDiscovery?: boolean }> = {}
): ResearchTeamProfile {
  const policy = mathematicsResearchPolicy(id);
  const estimatedMode = typeof process !== 'undefined' && process.env?.DEEPSCIENTIST_MATH_ALLOW_ESTIMATE === '1';
  const unlimitedTokens = options.unlimitedTokens === true;
  const shared = [
    `Frozen research configuration: ${policy.id} (${policy.implementation}). Keep this configuration for the entire run.`,
    'All configurations may prove directly, search the shared corpus, introduce helpers, revise a blueprint, inspect failures and keep ordinary working notes. Use only this run and problem as research memory.',
    'After a failed check, read the actual feedback and perform useful new work in the same Worker and assignment. A direct success needs no decomposition or research detour.',
    'Ordinary helper checkpoints stay inside the active assignment, Worker and worktree. Do not use a terminal delivery for an ordinary helper checkpoint; continue from it until the original target is ready, the route is refuted, or infrastructure blocks execution.',
    'The Formalizer may propose a better main route when stronger premises become available. The Lead accepts or rejects the exact proposed revision; until accepted, the current main route stays active. Local repairs do not need another assignment.',
    'Compiler observations and conditional connections are not kernel receipts. Recheck the complete original target after integration. Unknown or missing evidence remains unknown.',
    unlimitedTokens
      ? 'There is no cumulative token admission limit for this run. Continue useful proof work until the theorem is solved or the runtime ends.'
      : 'Every model request, retry and context summary shares the same run budget. Do not request extra calls to fill a candidate quota or write a routine error summary.',
    'Use math_research record to retain dependencies, failed routes with evidence, findings and the next step; read get after a context restart. Notes are organizational memory, never kernel receipts.',
    'Use math_research for the durable organizational record when a main-route proposal or specialized entry is needed. The Lead initializes it with the existing assignment and Worker, and owns decide_route. Workers use propose_route, enter, advance and return with the current revision. get is read-only. None of these actions establishes proof success.',
  ];
  if (estimatedMode && !unlimitedTokens) {
    shared.splice(
      0,
      shared.length,
      `Estimated budget run ${policy.id}: use the durable broker and local tokenizer estimate; every retry shares the run budget.`,
      'Work only from this run and problem. Read actual Lean feedback, keep the main route, and recheck the original target after changes.',
      'Use math_research only for route decisions and relevant premises. Conditional connections do not establish proof success.'
    );
  }
  const organization =
    policy.id === 'B'
      ? 'Organize research as hypothesis generation, concrete execution and candidate selection. Score up to four useful candidates against their observed results; keep up to fifteen relevant findings. Feedback from execution informs the next candidate or repairs the current one. This is a local mathematics adaptation of the three-stage architecture.'
      : policy.id === 'C'
        ? 'Act as a strong autonomous mathematics agent. Allocate effort among direct proofs, helper lemmas, dynamic blueprints, related facts and failure-driven revisions. Choose the next action from the mathematical evidence. This is a local strong baseline, with no prescribed retrieval or exploration loop.'
        : 'Organize work by mathematical evaluation, dependent obligations and stage feedback. Update structured notes at a stage return, important result or context compression, relating facts and evidence to the parent goal. Keep ordinary compiler errors in their logs.';
  const retrieval = policy.retrievalLoop
    ? 'The specialized retrieval loop is available when a route lacks a key premise or changes structurally: specify the missing property, retrieve from the frozen corpus, test instantiation at the actual Lean source position, then revise the route using the result. Skip it when premises suffice. Use at most two rounds for a bottleneck version; a failed or unchanged lookup returns control to the main proof.'
    : 'No specialized retrieval loop is scheduled. Ordinary searches and autonomous route improvements remain available.';
  const exploration = policy.explorationLoop
    ? 'The specialized exploration loop may investigate one relevant candidate at a time. Track its proof separately from a connection that assumes the exact candidate as a local parameter. Revise from real feedback, with at most two versions per entry. A changed statement invalidates its old connection. Only integrate a verified candidate into the original goal and recheck the result; a conditional connection never completes the parent. Exit this loop after two consecutive unproductive entries and continue the main proof or propose a revised route.'
    : 'No specialized exploration loop is scheduled. Ordinary helper lemmas, related propositions and blueprint revisions remain available.';
  return Object.freeze({
    ...profile,
    coordinationRules: Object.freeze([...profile.coordinationRules, ...shared, organization, retrieval, exploration]),
    roles: Object.freeze(
      profile.roles.map((role) =>
        Object.freeze(
          Object.assign({}, role, {
            allowedTools: Object.freeze([
              ...role.allowedTools.filter((tool) => tool.toolName !== 'math_research'),
              {
                toolName: 'math_research',
                actions: Object.freeze(
                  role.kind === 'lead'
                    ? ['overview', 'get', 'initialize', 'decide_route', 'record']
                    : ['get', 'propose_route', 'enter', 'advance', 'return', 'record']
                ),
              },
            ]),
            prompt: [role.prompt, ...shared, organization, retrieval, exploration].join('\n'),
          })
        )
      )
    ),
  });
}
