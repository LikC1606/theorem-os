import { FINANCE_TASK_CONTRACTS, getFinanceTaskContract } from "./taskContracts";
import type { FinanceTaskContractId, FinanceTaskContractRef, FinanceTaskKind } from "./types";

export type FinanceSpecialistModeId = 'factor-research' | 'market-data-research';

export type FinanceTaskRouteCandidate = {
  id: FinanceTaskContractId;
  version: string;
  contractHash: string;
  taskKind: FinanceTaskKind;
  sopReference: string;
  specialistModeId: FinanceSpecialistModeId;
};

export type FinanceTaskRoute =
  | {
      status: 'selected';
      contract: FinanceTaskContractRef;
      taskKind: FinanceTaskKind;
      sopReference: string;
      specialistModeId: FinanceSpecialistModeId;
    }
  | {
      status: 'ambiguous';
      reason: 'mixed_intent';
      candidates: FinanceTaskRouteCandidate[];
    }
  | {
      status: 'unresolved';
      reason: 'no_deterministic_match';
      candidates: FinanceTaskRouteCandidate[];
    };

type FinanceRouteRule = {
  contractId: FinanceTaskContractId;
  strong: RegExp;
  supporting: RegExp;
  wrapper?: boolean;
};

const ROUTE_RULES: readonly FinanceRouteRule[] = [
  {
    contractId: 'finance.monitor.v1',
    strong: /(?:监控|监测|定时|定期|每日更新|每天更新|每周更新|提醒|continuous\s+monitor|scheduled?\s+monitor)/i,
    supporting: /(?:monitor|schedule|watch\s+for|alert)/i,
    wrapper: true,
  },
  {
    contractId: 'finance.holdings-diagnosis.v1',
    strong: /(?:持仓截图|账户截图|仓位截图|持仓诊断|持仓分析|holdings?\s+(?:screenshot|diagnosis|analysis))/i,
    supporting: /(?:持仓|仓位|我的组合|holdings?|positions?)/i,
    wrapper: true,
  },
  {
    contractId: 'finance.simulated-portfolio.v1',
    strong:
      /(?:模拟(?:研究)?组合|研究组合模拟|虚拟组合|观察列表|自选列表|simulat(?:e|ed|ion).*portfolio|research\s+portfolio|watchlist)/i,
    supporting: /(?:组合回测|组合表现|portfolio)/i,
    wrapper: true,
  },
  {
    contractId: 'finance.factor-research.v1',
    strong:
      /(?:因子|因子库|因子组合|因子验证|因子回测|量价信号|worldquant|\bbrain\b|\bqlib\b|\bfactors?\b|\bbacktest(?:ing)?\b|\balpha\s+(?:signal|factor|research|mining)\b|\brank[-_\s]*ic(?:ir)?\b|\bic(?:ir)?\b)/i,
    supporting: /(?:表达式验证|稳健性检验|泄漏检查|收益预测信号|signal\s+validation)/i,
  },
  {
    contractId: 'finance.news-impact.v1',
    strong:
      /(?:新闻影响|事件影响|政策影响|冲击链|影响链|催化链|产业链影响|受影响公司|news\s+impact|event\s+impact|impact\s+chain|catalyst\s+chain)/i,
    supporting: /(?:新闻|事件|政策|催化|冲突|news|event|catalyst)/i,
  },
  {
    contractId: 'finance.company-research.v1',
    strong:
      /(?:公司研究|个股研究|基本面|估值分析|财报分析|盈利分析|company\s+research|stock\s+research|fundamental|valuation|earnings?\s+analysis)/i,
    supporting: /(?:公司|个股|股票|财报|估值|营收|利润|company|stock|earnings|financials)/i,
  },
  {
    contractId: 'finance.market-theme.v1',
    strong:
      /(?:市场扫描|市场主题|盘面分析|大盘分析|板块轮动|行业轮动|领涨板块|领跌板块|市场宽度|(?:今日|今天|本日|全球|跨市场).{0,12}(?:市场|行情)|(?:市场|行情).{0,12}(?:值得关注|有什么|汇总|总结)|market\s+(?:overview|theme|scan)|(?:today(?:'s)?|global|cross[-\s]?market).{0,24}markets?|markets?.{0,24}(?:watch|matter|summary|today)|sector\s+movers?|market\s+breadth)/i,
    supporting: /(?:市场|大盘|盘面|板块|行业|行情|主题|领涨|领跌|market|sector|breadth|movers?)/i,
  },
];

const EXPLICIT_CROSS_ROUTE_SEQUENCE =
  /(?:(?:先|首先).{0,120}(?:再|然后|接着)|(?:first|start\s+by).{0,160}(?:then|after\s+that|followed\s+by))/i;

const specialistForContract = (contractId: FinanceTaskContractId): FinanceSpecialistModeId =>
  contractId === 'finance.factor-research.v1' ? 'factor-research' : 'market-data-research';

const toCandidate = (contractId: FinanceTaskContractId): FinanceTaskRouteCandidate => {
  const contract = getFinanceTaskContract(contractId);
  if (!contract) throw new Error(`Finance task contract is not registered: ${contractId}`);
  return {
    id: contract.id,
    version: contract.version,
    contractHash: contract.contractHash,
    taskKind: contract.taskKind,
    sopReference: contract.sopReference,
    specialistModeId: specialistForContract(contract.id),
  };
};

const selectedRoute = (contractId: FinanceTaskContractId): FinanceTaskRoute => {
  const candidate = toCandidate(contractId);
  return {
    status: 'selected',
    contract: {
      id: candidate.id,
      version: candidate.version,
      contractHash: candidate.contractHash,
      routeSource: 'deterministic',
    },
    taskKind: candidate.taskKind,
    sopReference: candidate.sopReference,
    specialistModeId: candidate.specialistModeId,
  };
};

const ambiguousRoute = (rules: readonly FinanceRouteRule[]): FinanceTaskRoute => ({
  status: 'ambiguous',
  reason: 'mixed_intent',
  candidates: rules.map((rule) => toCandidate(rule.contractId)),
});

export function routeFinanceTask(input: string): FinanceTaskRoute {
  const normalized = input.normalize('NFKC').trim().toLowerCase();
  if (!normalized) {
    return {
      status: 'unresolved',
      reason: 'no_deterministic_match',
      candidates: FINANCE_TASK_CONTRACTS.map((contract) => toCandidate(contract.id)),
    };
  }

  const strongMatches = ROUTE_RULES.filter((rule) => rule.strong.test(normalized));
  const factorMatch = strongMatches.find((rule) => rule.contractId === 'finance.factor-research.v1');
  const wrapperMatches = strongMatches.filter((rule) => rule.wrapper);

  // Monitoring, holdings diagnosis, and simulation define the outer protocol.
  // Factor work remains a separate contract, so an explicit cross-route request
  // must be confirmed instead of silently collapsing into either workflow.
  if (wrapperMatches.length === 1 && !factorMatch) return selectedRoute(wrapperMatches[0].contractId);
  if (wrapperMatches.length > 1 || (wrapperMatches.length === 1 && factorMatch)) {
    return ambiguousRoute(Array.from(new Set([...wrapperMatches, ...(factorMatch ? [factorMatch] : [])])));
  }
  // A company, market, or news term may describe the source data for factor work
  // rather than a second task (for example, "fundamental factor mining"). Keep
  // genuinely sequenced cross-route requests ambiguous, but otherwise let an
  // explicit factor/backtest/IC intent select the factor workflow.
  if (factorMatch && !EXPLICIT_CROSS_ROUTE_SEQUENCE.test(normalized)) {
    return selectedRoute(factorMatch.contractId);
  }
  if (strongMatches.length === 1) return selectedRoute(strongMatches[0].contractId);
  if (strongMatches.length > 1) return ambiguousRoute(strongMatches);

  const supportingMatches = ROUTE_RULES.filter((rule) => rule.supporting.test(normalized));
  if (supportingMatches.length === 1) return selectedRoute(supportingMatches[0].contractId);
  if (supportingMatches.length > 1) return ambiguousRoute(supportingMatches);

  return {
    status: 'unresolved',
    reason: 'no_deterministic_match',
    candidates: FINANCE_TASK_CONTRACTS.map((contract) => toCandidate(contract.id)),
  };
}

export function getFinanceTaskRouteSpecialists(route?: FinanceTaskRoute): FinanceSpecialistModeId[] {
  if (!route) return [];
  if (route.status === 'selected') return [route.specialistModeId];
  // An unresolved finance request still needs one immutable capability snapshot
  // before the Agent can refine the exact contract. Mount the general market-data
  // surface by default; mounting factor research as well would select the factor
  // Team profile for ordinary financial questions and hide the finance_* tools.
  if (route.status === 'unresolved') return ['market-data-research'];
  return Array.from(new Set(route.candidates.map((candidate) => candidate.specialistModeId)));
}
