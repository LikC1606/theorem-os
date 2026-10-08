import type {
  FinanceTaskContract,
  FinanceTaskContractId,
  FinanceTaskContractRef,
  FinanceToolRequirementCondition,
} from "./types";

type FinanceTaskContractDefinition = Omit<FinanceTaskContract, 'contractHash'>;

const PROVIDER_PARTIAL_REASONS = ['provider_error', 'timeout', 'retry_exhausted'] as const;

const definitions: Record<FinanceTaskContractId, FinanceTaskContractDefinition> = {
  'finance.market-theme.v1': {
    id: 'finance.market-theme.v1',
    version: '1.0.1',
    taskKind: 'market_theme',
    sopReference: 'market-data-research/references/market-theme-scan.md',
    requiredCapabilities: ['finance.market.read', 'finance.sector.read', 'finance.security.screen'],
    requiredTools: [
      { name: 'finance_market_overview', when: 'always' },
      { name: 'finance_sector_movers', when: 'always' },
      { name: 'finance_security_screen', when: 'always' },
      { name: 'finance_news_events', when: 'when_catalyst_claimed' },
      { name: 'finance_price_series', when: 'when_price_claimed' },
      { name: 'science_artifact', when: 'always' },
    ],
    requiredArtifactKinds: ['market_theme'],
    requiredReport: {
      sectionRoles: ['market_status', 'themes', 'evidence', 'limitations'],
      cardKinds: ['ranked_list', 'evidence_list'],
      requiresResultSummary: false,
      requiresLimitations: true,
    },
    confirmationGates: ['change_research_scope', 'create_watchlist', 'create_monitor'],
    allowedPartialReasons: [
      'market_closed',
      'coverage_incomplete',
      'news_unavailable',
      'price_series_unavailable',
      ...PROVIDER_PARTIAL_REASONS,
    ],
  },
  'finance.news-impact.v1': {
    id: 'finance.news-impact.v1',
    version: '1.0.1',
    taskKind: 'event_impact',
    sopReference: 'market-data-research/references/news-impact-chain.md',
    requiredCapabilities: ['finance.news.read', 'finance.relationship.derive', 'finance.price.read'],
    requiredTools: [
      { name: 'finance_news_events', when: 'always' },
      { name: 'finance_relationship_map', when: 'always' },
      { name: 'finance_security_screen', when: 'always' },
      { name: 'finance_price_series', when: 'always' },
      { name: 'science_artifact', when: 'always' },
    ],
    requiredArtifactKinds: ['event_impact'],
    requiredReport: {
      sectionRoles: ['event_facts', 'impact_paths', 'price_confirmation', 'counterevidence', 'limitations'],
      cardKinds: ['ranked_list', 'timeseries', 'evidence_list'],
      requiresResultSummary: false,
      requiresLimitations: true,
    },
    confirmationGates: ['create_simulated_portfolio', 'route_to_factor_research'],
    allowedPartialReasons: [
      'price_series_unavailable',
      'relationship_incomplete',
      'coverage_incomplete',
      ...PROVIDER_PARTIAL_REASONS,
    ],
  },
  'finance.company-research.v1': {
    id: 'finance.company-research.v1',
    version: '1.0.1',
    taskKind: 'company_research',
    sopReference: 'market-data-research/references/company-research.md',
    requiredCapabilities: ['finance.security.read', 'finance.price.read', 'finance.news.read'],
    requiredTools: [
      { name: 'finance_sector_search', when: 'always' },
      { name: 'finance_security_snapshot', when: 'always' },
      { name: 'finance_price_series', when: 'always' },
      { name: 'finance_news_events', when: 'always' },
      { name: 'science_artifact', when: 'always' },
    ],
    requiredArtifactKinds: ['company_research'],
    requiredReport: {
      sectionRoles: ['identity', 'financials', 'price', 'events', 'risks', 'limitations'],
      cardKinds: ['metric_strip', 'timeseries', 'data_table', 'ranked_list', 'evidence_list'],
      requiresResultSummary: false,
      requiresLimitations: true,
    },
    confirmationGates: ['resolve_ambiguous_security', 'change_comparison_basis', 'create_watchlist'],
    allowedPartialReasons: [
      'financials_unavailable',
      'price_series_unavailable',
      'news_unavailable',
      ...PROVIDER_PARTIAL_REASONS,
    ],
  },
  'finance.simulated-portfolio.v1': {
    id: 'finance.simulated-portfolio.v1',
    version: '1.0.1',
    taskKind: 'research_portfolio',
    sopReference: 'market-data-research/references/simulated-research-portfolio.md',
    requiredCapabilities: ['finance.security.read', 'finance.price.read', 'finance.portfolio.simulate'],
    requiredTools: [
      { name: 'user_input', when: 'always' },
      { name: 'finance_security_snapshot', when: 'always' },
      { name: 'finance_price_series', when: 'always' },
      { name: 'finance_research_portfolio', when: 'when_user_consented' },
      { name: 'science_artifact', when: 'always' },
    ],
    requiredArtifactKinds: ['research_portfolio'],
    requiredReport: {
      sectionRoles: ['simulation_policy', 'performance', 'holdings', 'risk', 'limitations'],
      cardKinds: ['metric_strip', 'timeseries', 'data_table', 'ranked_list'],
      requiresResultSummary: true,
      requiresLimitations: true,
    },
    confirmationGates: ['simulation_protocol'],
    allowedPartialReasons: [
      'missing_price_history',
      'coverage_incomplete',
      'benchmark_unavailable',
      ...PROVIDER_PARTIAL_REASONS,
    ],
  },
  'finance.holdings-diagnosis.v1': {
    id: 'finance.holdings-diagnosis.v1',
    version: '1.0.1',
    taskKind: 'holdings_diagnosis',
    sopReference: 'market-data-research/references/holdings-screenshot-diagnosis.md',
    requiredCapabilities: ['finance.holdings.parse', 'finance.security.read'],
    requiredTools: [
      { name: 'user_input', when: 'always' },
      { name: 'finance_holdings_parse', when: 'when_user_consented' },
      { name: 'finance_security_snapshot', when: 'always' },
      { name: 'finance_price_series', when: 'when_price_claimed' },
      { name: 'science_artifact', when: 'always' },
    ],
    requiredArtifactKinds: ['holdings_diagnosis'],
    requiredReport: {
      sectionRoles: ['holdings', 'exposure', 'risks', 'data_gaps', 'limitations'],
      cardKinds: ['data_table', 'metric_strip', 'ranked_list', 'evidence_list'],
      requiresResultSummary: false,
      requiresLimitations: true,
    },
    confirmationGates: ['image_processing_scope', 'low_confidence_rows'],
    allowedPartialReasons: [
      'low_confidence_rows',
      'unresolved_symbols',
      'price_series_unavailable',
      ...PROVIDER_PARTIAL_REASONS,
    ],
  },
  'finance.monitor.v1': {
    id: 'finance.monitor.v1',
    version: '1.0.1',
    taskKind: 'monitor',
    sopReference: 'market-data-research/references/continuous-monitoring.md',
    requiredCapabilities: ['finance.monitor.read', 'cron'],
    requiredTools: [
      { name: 'cron', when: 'always' },
      { name: 'science_artifact', when: 'always' },
    ],
    requiredArtifactKinds: ['monitor'],
    requiredReport: {
      sectionRoles: ['policy', 'latest_changes', 'runs', 'errors'],
      cardKinds: ['metric_strip', 'ranked_list'],
      requiresResultSummary: false,
      requiresLimitations: true,
    },
    confirmationGates: ['create_monitor', 'modify_monitor', 'pause_monitor', 'resume_monitor'],
    allowedPartialReasons: ['market_closed', 'no_change', ...PROVIDER_PARTIAL_REASONS],
  },
  'finance.factor-research.v1': {
    id: 'finance.factor-research.v1',
    version: '2.0.0',
    taskKind: 'factor_research',
    sopReference: 'financial-factor-discovery/SKILL.md',
    requiredCapabilities: [],
    requiredTools: [
      { name: 'factor_submit', when: 'when_terminal_report' },
    ],
    requiredArtifactKinds: ['factor_research'],
    requiredArtifactsWhen: 'when_terminal_report',
    requiredReport: {
      when: 'when_terminal_report',
      sectionRoles: ['protocol', 'result', 'visuals', 'evidence', 'limitations'],
      cardKinds: ['metric_strip', 'timeseries', 'data_table'],
      requiresResultSummary: true,
      requiresLimitations: true,
    },
    confirmationGates: ['change_factor_protocol', 'high_cost_backtest', 'external_submission', 'promote_factor'],
    allowedPartialReasons: [
      'runtime_unavailable',
      'data_invalid',
      'exploration_incomplete',
      'evaluation_pending',
      'data_gap',
    ],
  },
};

const CONTRACT_HASHES: Record<FinanceTaskContractId, string> = {
  'finance.market-theme.v1': 'fd3846bf84885c975444073624ea34c2391acb4c16b019469bf62b6923847bec',
  'finance.news-impact.v1': 'a674c4e524d47defb6ccae3d36252fd60e83c0ba60ccbd6d5e85d38941cf2dbc',
  'finance.company-research.v1': '2c6f771242b4978841ecee722ca07d0ee8f073b0d755f810f9ce0335f4a526d1',
  'finance.simulated-portfolio.v1': 'f3ba94735f3202615045920d8f8abff408e8d20758ecd2d30ab45c7ec6588cb9',
  'finance.holdings-diagnosis.v1': 'da5c5602de0ead05e7092499d96b195542a52e2996f741897365aab93b5383d2',
  'finance.monitor.v1': '51a98d343801489fb8a4d2e90ff5d39a8c371859830bafd99f56bc2aa69bdfc3',
  'finance.factor-research.v1': '33ff3fc98f7094d5a4338c2bbb2d609ee5d52e9a61431f5aca4808f630655edc',
};

const stableContractValue = (value: unknown): unknown => {
  if (Array.isArray(value)) return value.map(stableContractValue);
  if (!value || typeof value !== 'object') return value;
  return Object.fromEntries(
    Object.entries(value as Record<string, unknown>)
      .toSorted(([left], [right]) => left.localeCompare(right))
      .map(([key, item]) => [key, stableContractValue(item)])
  );
};

export const canonicalizeFinanceTaskContract = (definition: FinanceTaskContractDefinition): string =>
  JSON.stringify(stableContractValue(definition));

export const FINANCE_TASK_CONTRACTS: readonly FinanceTaskContract[] = Object.values(definitions).map((definition) =>
  Object.assign({}, definition, { contractHash: CONTRACT_HASHES[definition.id] })
);

const contractsById = new Map(FINANCE_TASK_CONTRACTS.map((contract) => [contract.id, contract]));

export const getFinanceTaskContract = (id: FinanceTaskContractId | string): FinanceTaskContract | undefined =>
  contractsById.get(id as FinanceTaskContractId);

export const resolveFinanceTaskContract = (ref: FinanceTaskContractRef): FinanceTaskContract | undefined => {
  const contract = getFinanceTaskContract(ref.id);
  return contract && contract.version === ref.version && contract.contractHash === ref.contractHash
    ? contract
    : undefined;
};

export const getRequiredFinanceContractTools = (
  contract: FinanceTaskContract,
  activeConditions: ReadonlySet<FinanceToolRequirementCondition> = new Set(['always'])
) =>
  contract.requiredTools
    .filter((requirement) => activeConditions.has(requirement.when))
    .map((requirement) => requirement.name);

export const getFinanceTaskContractDefinitions = (): readonly FinanceTaskContractDefinition[] =>
  Object.values(definitions);
