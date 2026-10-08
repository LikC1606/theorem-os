import type { FinanceSpecialistModeId, FinanceTaskRoute } from "./taskRouter";

export const FINANCIAL_MODE_ID = 'financial' as const;
export const FINANCIAL_MODE_SKILL_NAME = 'ds-financial' as const;
export const FINANCIAL_REPORT_SKILL_NAME = 'financial-report-research' as const;
export const ALPHA_DOJO_FINANCE_SKILL_NAME = 'market-data-research' as const;
export const FINANCIAL_SESSION_SCHEMA = 'deepscientist.finance.session.v1' as const;

export type FinancialConversationExtra = {
  enabled: true;
  mode: typeof FINANCIAL_MODE_ID;
  schema: typeof FINANCIAL_SESSION_SCHEMA;
  projectRoot?: string;
  defaultSkill: typeof FINANCIAL_MODE_SKILL_NAME;
  tradeCapability: 'disabled';
  taskRoute?: FinanceTaskRoute & {
    activeSpecialists: FinanceSpecialistModeId[];
    alphaDojoProviderStatus: AlphaDojoProviderStatus;
  };
};

export type AlphaDojoProviderStatus =
  | 'not_required'
  | 'plugin_disabled'
  | 'endpoint_missing'
  | 'configured'
  | 'healthy'
  | 'degraded'
  | 'unavailable';

export type FinancialModeRouteContext = {
  route?: FinanceTaskRoute;
  activeSpecialists?: FinanceSpecialistModeId[];
  alphaDojoProviderStatus?: AlphaDojoProviderStatus;
};

export const buildFinancialConversationExtra = (
  projectRoot?: string,
  routeContext: FinancialModeRouteContext = {}
): FinancialConversationExtra => ({
  enabled: true,
  mode: FINANCIAL_MODE_ID,
  schema: FINANCIAL_SESSION_SCHEMA,
  projectRoot,
  defaultSkill: FINANCIAL_MODE_SKILL_NAME,
  tradeCapability: 'disabled',
  ...(routeContext.route
    ? {
        taskRoute: {
          ...routeContext.route,
          activeSpecialists: routeContext.activeSpecialists ?? [],
          alphaDojoProviderStatus: routeContext.alphaDojoProviderStatus ?? 'not_required',
        },
      }
    : {}),
});

const formatCandidate = (candidate: {
  id: string;
  version: string;
  contractHash: string;
  sopReference: string;
  specialistModeId: string;
}): string =>
  `- ${candidate.id} | version=${candidate.version} | contractHash=${candidate.contractHash} | specialist=${candidate.specialistModeId} | sop=${candidate.sopReference}`;

const buildFinancialRoutePrompt = (context: FinancialModeRouteContext): string[] => {
  const route = context.route;
  if (!route) return [];
  const activeSpecialists = new Set(context.activeSpecialists ?? []);
  if (route.status === 'selected') {
    const specialistActive = activeSpecialists.has(route.specialistModeId);
    const providerStatus = context.alphaDojoProviderStatus ?? 'not_required';
    const providerNeedsFallback = !['configured', 'healthy'].includes(providerStatus);
    const availabilityLines = !specialistActive
      ? [
          `- Required specialist ${route.specialistModeId} was explicitly disabled. Report the gap once and point to “Settings → Capability Center → Modes → Financial Mode”; do not silently substitute another specialist.`,
        ]
      : route.specialistModeId === 'market-data-research' && providerNeedsFallback
        ? [
            `- Market-data and simulation provider status: ${providerStatus}. The bundled provider is enabled by default and should start automatically. Treat this as a local runtime startup fault, not as a missing user setting. If one finance-data call reports provider_error, endpoint_missing, connection, timeout, or retry_exhausted, state that fault once, skip that call after the adapter retry budget, and continue only the portions supported by user-provided data, independent finance calls, or primary-source evidence. Publish a clearly labelled partial result when reviewable evidence remains; only block when no reviewable route remains. Never replace missing quotes or rankings with generic web search. The diagnostic controls are at “Settings → Capability Center → Modes → Financial Mode → Market data and simulation”.`,
          ]
        : ['- The required specialist is active. Follow only the selected contract and its SOP reference.'];
    return [
      '',
      '## Runtime Financial Task Route',
      '- Route status: selected',
      `- Contract id: ${route.contract.id}`,
      `- Contract version: ${route.contract.version}`,
      `- Contract hash: ${route.contract.contractHash}`,
      `- Route source: ${route.contract.routeSource}`,
      `- Task kind: ${route.taskKind}`,
      `- Specialist: ${route.specialistModeId}`,
      `- SOP reference: ${route.sopReference}`,
      ...availabilityLines,
      '- Copy this exact contract reference into the Finance completion manifest. Never guess or recompute its hash.',
    ];
  }

  return [
    '',
    '## Runtime Financial Task Route',
    `- Route status: ${route.status}`,
    '- Select the best matching candidate yourself from the latest user request. Do not ask the user to choose between factor research and general financial research.',
    '- Prefer factor research when the request explicitly mentions a factor, alpha signal, formula, IC/ICIR, backtest, leakage, or robustness validation; otherwise prefer the most specific market-data candidate. For a mixed sequence, execute the market-data step as input to the factor workflow and use the factor contract as the completion contract.',
    '- Use the exact id, version, hash, specialist, and SOP of the chosen candidate. Never invent or recompute a contract hash.',
    ...route.candidates.map(formatCandidate),
  ];
};

export const buildFinancialModePrompt = (
  projectRoot?: string,
  _preferredLocale?: string,
  routeContext: FinancialModeRouteContext = {}
): string =>
  [
    '# DeepScientist Financial Mode',
    '',
    'Financial Mode routes each request to one versioned FinanceTaskContract before specialist work.',
    projectRoot
      ? `- Authorized project root: ${projectRoot}`
      : '- This run is not bound to a project. Keep it read-only and record an unbound_read_only preflight gate.',
    '- Read `report-authoring` for the reader-first outline and visual decision, then `financial-report-research` and `ds-financial` for the selected versioned contract. Use `market-data-research` only when the selected route requires its managed provider. Factor discovery belongs in Financial Factor Mining Mode and must not be improvised in this report workflow.',
    '- Treat the injected Runtime Financial Task Route as authoritative. If it contains multiple or unresolved candidates, infer the best route yourself from the request and do not ask a second routing question. Ask the user only when a missing business fact would materially change the analysis itself.',
    '- Follow the `ds-financial` Skill for project preflight, evidence, checkpoint, report, and completion details. Do not recreate that SOP from chat or inspect guessed paths.',
    '- If Team Mode is active, its injected Lead/Worker role contract exclusively governs dispatch, integration, and role-owned tools; this mode prompt does not define a second Team policy.',
    '- Establish market, timezone, currency, time window, asOf, coverage, and data freshness before interpreting results. Preserve real zero values and distinguish missing data from no change.',
    '- A single provider failure is not a reason to abandon the whole research run: skip the failed read after the adapter retry budget and make every omitted field and resulting limitation visible in the partial report.',
    '- Financial Report Mode must finish with exactly one structured Science Report whenever any reviewable answer, evidence, calculation, or visual exists. This includes a clearly labelled Partial Report after an allowed provider failure; only a terminal preflight with no reviewable output may finish without publishing.',
    '- Maintain a compact persistent research state for long runs: the user question, acceptance criteria, evidence already collected, open items, and the next action. When resuming, inspect and update the existing report and stable cards instead of restarting the analysis or creating duplicate terminal reports.',
    '- When the reader uses Chinese, a Chinese broker-style layout is an optional presentation choice: put a concise answer and “investment points” near the top, then show supported industry/company drivers, key assumptions and forecasts, valuation or sensitivity only when requested and evidenced, followed by scenarios, risks, disclaimer, and sources. Do not invent a rating, target price, or empty broker section just to imitate a template.',
    '- Treat visual selection as part of report completion. When verified structured values support comparison, trend, distribution, interval, exposure, or scenario analysis, publish one lead chart and use two to four total chart/cards only for distinct reader questions. Put the visual result before long evidence and risk detail. If no meaningful visual data exists, pass only `payload.internalVisualWaiverReason` as private validation metadata; never expose that reason to the reader or manufacture points.',
    '- Write the required reader-first financial note: answer the user in the first paragraph, then show scope/asOf, key metrics and the lead visual, drivers, scenarios and invalidation triggers, conditional next actions, and sources/method. Organize by the question, not by tool-call order. Reuse registered evidence and cards; do not manufacture a target price, force empty modules, or hand-write an HTML dashboard.',
    '- Every chart/card needs a named reader question, units/denominator/period, source or evidence ids, and one short “what this means” interpretation. Raw evidence, provider errors, and JSON belong below the answer or in collapsible detail; they must not replace the report.',
    '- Real trading is disabled. A simulated research portfolio is not a real account, market correlation is not causality, and a factor candidate is not validated until its required checks pass.',
    ...buildFinancialRoutePrompt(routeContext),
  ].join('\n');
