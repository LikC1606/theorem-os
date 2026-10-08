/**
 * @license
 * Copyright 2026 DeepScientist (deepscientist.cc)
 * SPDX-License-Identifier: Apache-2.0
 */

import {
  FINANCIAL_FACTOR_POOL_SCHEMA,
  type FinancialFactorEvaluationProtocol,
  type FinancialFactorEvaluationRow,
  type FinancialFactorPoolCandidateDecision,
  type FinancialFactorPoolCandidateSpec,
  type FinancialFactorPoolCandidateStatistics,
  type FinancialFactorPoolModel,
  type FinancialFactorPoolPolicy,
  type FinancialFactorPoolRidgeScore,
} from "./financialFactor";

export interface FinancialFactorPoolTableRow {
  date: string;
  asset: string;
  futureReturn?: number;
  availableAt?: string;
  factorValues: Record<string, number | undefined>;
}

export interface FinancialFactorPoolFitResult {
  candidateDecisions: FinancialFactorPoolCandidateDecision[];
  selectedFactors: Array<{
    candidate: FinancialFactorPoolCandidateSpec;
    statistics: FinancialFactorPoolCandidateStatistics;
    weight: number;
  }>;
  ridge: FinancialFactorPoolModel['ridge'];
  validationRows: FinancialFactorEvaluationRow[];
  fittedDateBoundary: {
    developmentLastFitDate: string;
    validationLastFitDate: string;
  };
}

const mean = (values: number[]): number | undefined =>
  values.length ? values.reduce((total, value) => total + value, 0) / values.length : undefined;

const standardDeviation = (values: number[]): number | undefined => {
  if (values.length < 2) return undefined;
  const average = mean(values);
  if (average == null) return undefined;
  return Math.sqrt(values.reduce((total, value) => total + (value - average) ** 2, 0) / (values.length - 1));
};

const pearson = (left: number[], right: number[]): number | undefined => {
  if (left.length !== right.length || left.length < 2) return undefined;
  const leftMean = mean(left);
  const rightMean = mean(right);
  if (leftMean == null || rightMean == null) return undefined;
  let covariance = 0;
  let leftVariance = 0;
  let rightVariance = 0;
  for (let index = 0; index < left.length; index += 1) {
    const leftDelta = left[index] - leftMean;
    const rightDelta = right[index] - rightMean;
    covariance += leftDelta * rightDelta;
    leftVariance += leftDelta ** 2;
    rightVariance += rightDelta ** 2;
  }
  if (leftVariance === 0 || rightVariance === 0) return undefined;
  const correlation = covariance / Math.sqrt(leftVariance * rightVariance);
  return Math.max(-1, Math.min(1, correlation));
};

const ranks = (values: number[]): number[] => {
  const indexed = values.map((value, index) => ({ value, index })).toSorted((left, right) => left.value - right.value);
  const ranked = Array<number>(values.length);
  for (let start = 0; start < indexed.length; ) {
    let end = start + 1;
    while (end < indexed.length && indexed[end].value === indexed[start].value) end += 1;
    const rank = (start + end - 1) / 2 + 1;
    for (let index = start; index < end; index += 1) ranked[indexed[index].index] = rank;
    start = end;
  }
  return ranked;
};

const rankNormalize = (values: number[]): number[] => {
  const ranked = ranks(values);
  const average = mean(ranked) || 0;
  const deviation = standardDeviation(ranked);
  return deviation ? ranked.map((value) => (value - average) / deviation) : ranked.map(() => 0);
};

const canonicalExpression = (value: string): string => value.replace(/\s+/gu, '').toLowerCase();

const dateInRange = (date: string, start: string, end: string): boolean => {
  const timestamp = Date.parse(date);
  return Number.isFinite(timestamp) && timestamp >= Date.parse(start) && timestamp <= Date.parse(end);
};

const purgeSplitTail = (rows: FinancialFactorPoolTableRow[], tradingDays: number): FinancialFactorPoolTableRow[] => {
  if (!tradingDays) return rows;
  const dates = [...new Set(rows.map((row) => row.date))].toSorted(
    (left, right) => Date.parse(left) - Date.parse(right)
  );
  if (dates.length <= tradingDays) {
    throw new Error('Factor-pool split has no fitting dates after the configured label-boundary purge.');
  }
  const retainedDates = new Set(dates.slice(0, -tradingDays));
  return rows.filter((row) => retainedDates.has(row.date));
};

const groupByDate = (rows: FinancialFactorPoolTableRow[]): Map<string, FinancialFactorPoolTableRow[]> => {
  const grouped = new Map<string, FinancialFactorPoolTableRow[]>();
  const identities = new Set<string>();
  rows.forEach((row) => {
    const identity = `${row.date}\u0000${row.asset}`;
    if (identities.has(identity)) throw new Error(`Duplicate factor-pool row for ${row.date}/${row.asset}.`);
    identities.add(identity);
    grouped.set(row.date, [...(grouped.get(row.date) || []), row]);
  });
  return grouped;
};

const dailyCandidateIcs = (
  rowsByDate: Map<string, FinancialFactorPoolTableRow[]>,
  candidateId: string,
  rankBased = false
): Array<[string, number]> =>
  [...rowsByDate.entries()]
    .toSorted(([left], [right]) => Date.parse(left) - Date.parse(right))
    .flatMap(([date, rows]): Array<[string, number]> => {
      const valid = rows.filter(
        (row): row is FinancialFactorPoolTableRow & { futureReturn: number } =>
          Number.isFinite(row.factorValues[candidateId]) && Number.isFinite(row.futureReturn)
      );
      if (valid.length < 2) return [];
      const factorValues = valid.map((row) => row.factorValues[candidateId] as number);
      const futureReturns = valid.map((row) => row.futureReturn);
      const value = pearson(
        rankBased ? ranks(factorValues) : factorValues,
        rankBased ? ranks(futureReturns) : futureReturns
      );
      return value == null ? [] : [[date, value]];
    });

const splitIntoFolds = <T>(items: T[], foldCount: number): T[][] =>
  Array.from({ length: foldCount }, (_, foldIndex) => {
    const start = Math.floor((foldIndex * items.length) / foldCount);
    const end = Math.floor(((foldIndex + 1) * items.length) / foldCount);
    return items.slice(start, end);
  });

const candidateStatistics = (
  rowsByDate: Map<string, FinancialFactorPoolTableRow[]>,
  candidate: FinancialFactorPoolCandidateSpec,
  policy: FinancialFactorPoolPolicy,
  annualizationFactor: number
): FinancialFactorPoolCandidateStatistics => {
  const icPoints = dailyCandidateIcs(rowsByDate, candidate.id);
  const rankIcPoints = dailyCandidateIcs(rowsByDate, candidate.id, true);
  const rawMeanIc = mean(icPoints.map(([, value]) => value)) || 0;
  const direction: -1 | 1 = rawMeanIc < 0 ? -1 : 1;
  const dates = [...rowsByDate.keys()].toSorted((left, right) => Date.parse(left) - Date.parse(right));
  const icByDate = new Map(icPoints);
  const foldIcs = splitIntoFolds(dates, policy.stabilityFolds).map((foldDates) => {
    const foldMean = mean(foldDates.flatMap((date) => (icByDate.has(date) ? [icByDate.get(date) as number] : [])));
    return (foldMean || 0) * direction;
  });
  const coverageByDate = [...rowsByDate.values()].map((rows) => {
    if (!rows.length) return 0;
    return (
      rows.filter((row) => Number.isFinite(row.factorValues[candidate.id]) && Number.isFinite(row.futureReturn))
        .length / rows.length
    );
  });
  const directedIcs = icPoints.map(([, value]) => value * direction);
  const icDeviation = standardDeviation(directedIcs);
  return {
    direction,
    coverage: coverageByDate.length ? Math.min(...coverageByDate) : 0,
    meanIc: mean(directedIcs) || 0,
    rankIc: (mean(rankIcPoints.map(([, value]) => value)) || 0) * direction,
    selectionScore: 0,
    ...(icDeviation ? { icir: ((mean(directedIcs) || 0) / icDeviation) * Math.sqrt(annualizationFactor) } : {}),
    worstFoldIc: foldIcs.length ? Math.min(...foldIcs) : 0,
    positiveFoldCount: foldIcs.filter((value) => value > 0).length,
    foldIcs,
  };
};

const normalizedCandidateSignals = (
  rowsByDate: Map<string, FinancialFactorPoolTableRow[]>,
  candidates: Array<{ candidate: FinancialFactorPoolCandidateSpec; direction: -1 | 1 }>
): Map<string, Map<string, number>> => {
  const signals = new Map(candidates.map(({ candidate }) => [candidate.id, new Map<string, number>()]));
  rowsByDate.forEach((rows, date) => {
    candidates.forEach(({ candidate, direction }) => {
      const valid = rows.filter((row) => Number.isFinite(row.factorValues[candidate.id]));
      const normalized = rankNormalize(valid.map((row) => row.factorValues[candidate.id] as number));
      valid.forEach((row, index) =>
        signals.get(candidate.id)?.set(`${date}\u0000${row.asset}`, normalized[index] * direction)
      );
    });
  });
  return signals;
};

const signalCorrelation = (left: Map<string, number>, right: Map<string, number>): number | undefined => {
  const common = [...left.keys()].filter((key) => right.has(key));
  return pearson(
    common.map((key) => left.get(key) as number),
    common.map((key) => right.get(key) as number)
  );
};

const normalizeCandidateScores = (values: number[]): number[] => {
  if (!values.length) return [];
  const minimum = Math.min(...values);
  const maximum = Math.max(...values);
  if (maximum === minimum) return values.map(() => 0.5);
  return values.map((value) => (value - minimum) / (maximum - minimum));
};

const equalWeightPoolDailyIcs = (
  rowsByDate: Map<string, FinancialFactorPoolTableRow[]>,
  selected: Array<{ candidate: FinancialFactorPoolCandidateSpec; direction: -1 | 1 }>,
  signals: Map<string, Map<string, number>>
): Array<[string, number]> => {
  if (!selected.length) return [];
  return [...rowsByDate.entries()]
    .toSorted(([left], [right]) => Date.parse(left) - Date.parse(right))
    .flatMap(([date, rows]): Array<[string, number]> => {
      const valid = rows.flatMap((row) => {
        if (!Number.isFinite(row.futureReturn)) return [];
        const values = selected.flatMap(({ candidate }) => {
          const value = signals.get(candidate.id)?.get(`${row.date}\u0000${row.asset}`);
          return Number.isFinite(value) ? [value as number] : [];
        });
        return values.length ? [{ value: mean(values) as number, target: row.futureReturn as number }] : [];
      });
      const ic = pearson(
        valid.map(({ value }) => value),
        valid.map(({ target }) => target)
      );
      return ic == null ? [] : [[date, ic]];
    });
};

const equalWeightPoolIc = (
  rowsByDate: Map<string, FinancialFactorPoolTableRow[]>,
  selected: Array<{ candidate: FinancialFactorPoolCandidateSpec; direction: -1 | 1 }>,
  signals: Map<string, Map<string, number>>
): number | undefined => mean(equalWeightPoolDailyIcs(rowsByDate, selected, signals).map(([, value]) => value));

const equalWeightPoolFoldIcs = (
  rowsByDate: Map<string, FinancialFactorPoolTableRow[]>,
  selected: Array<{ candidate: FinancialFactorPoolCandidateSpec; direction: -1 | 1 }>,
  signals: Map<string, Map<string, number>>,
  foldCount: number
): number[] => {
  if (!selected.length) return Array<number>(foldCount).fill(0);
  const byDate = new Map(equalWeightPoolDailyIcs(rowsByDate, selected, signals));
  const dates = [...rowsByDate.keys()].toSorted((left, right) => Date.parse(left) - Date.parse(right));
  return splitIntoFolds(dates, foldCount).map(
    (foldDates) => mean(foldDates.flatMap((date) => (byDate.has(date) ? [byDate.get(date) as number] : []))) || 0
  );
};

const selectCandidates = (input: {
  candidates: FinancialFactorPoolCandidateSpec[];
  rowsByDate: Map<string, FinancialFactorPoolTableRow[]>;
  policy: FinancialFactorPoolPolicy;
  minimumCoverage: number;
  annualizationFactor: number;
}): FinancialFactorPoolCandidateDecision[] => {
  const initialStatistics = new Map(
    input.candidates.map((candidate) => [
      candidate.id,
      candidateStatistics(input.rowsByDate, candidate, input.policy, input.annualizationFactor),
    ])
  );
  const normalizedRankIcs = normalizeCandidateScores(
    input.candidates.map(
      (candidate) => (initialStatistics.get(candidate.id) as FinancialFactorPoolCandidateStatistics).rankIc
    )
  );
  const normalizedMeanIcs = normalizeCandidateScores(
    input.candidates.map(
      (candidate) => (initialStatistics.get(candidate.id) as FinancialFactorPoolCandidateStatistics).meanIc
    )
  );
  const statistics = new Map(
    input.candidates.map((candidate, index) => {
      const base = initialStatistics.get(candidate.id) as FinancialFactorPoolCandidateStatistics;
      return [
        candidate.id,
        {
          ...base,
          selectionScore:
            input.policy.selectionRankIcWeight * normalizedRankIcs[index] +
            input.policy.selectionIcWeight * normalizedMeanIcs[index],
        },
      ] as const;
    })
  );
  const ordered = [...input.candidates].toSorted((left, right) => {
    const leftStats = statistics.get(left.id) as FinancialFactorPoolCandidateStatistics;
    const rightStats = statistics.get(right.id) as FinancialFactorPoolCandidateStatistics;
    return (
      rightStats.selectionScore - leftStats.selectionScore ||
      rightStats.worstFoldIc - leftStats.worstFoldIc ||
      rightStats.rankIc - leftStats.rankIc ||
      rightStats.meanIc - leftStats.meanIc ||
      (rightStats.icir || 0) - (leftStats.icir || 0) ||
      left.expression.length - right.expression.length ||
      left.id.localeCompare(right.id)
    );
  });
  const signals = normalizedCandidateSignals(
    input.rowsByDate,
    ordered.map((candidate) => ({
      candidate,
      direction: (statistics.get(candidate.id) as FinancialFactorPoolCandidateStatistics).direction,
    }))
  );
  const decisions = new Map<string, FinancialFactorPoolCandidateDecision>();
  const selected: FinancialFactorPoolCandidateSpec[] = [];
  const selectedExpressions = new Map<string, string>();
  const familyCounts = new Map<string, number>();

  ordered.forEach((candidate) => {
    const candidateStats = statistics.get(candidate.id) as FinancialFactorPoolCandidateStatistics;
    const decision: FinancialFactorPoolCandidateDecision = { candidate, statistics: candidateStats, selected: false };
    const incumbentDevelopmentIc = equalWeightPoolIc(
      input.rowsByDate,
      selected.map((item) => ({
        candidate: item,
        direction: (statistics.get(item.id) as FinancialFactorPoolCandidateStatistics).direction,
      })),
      signals
    );
    const candidatePoolDevelopmentIc = equalWeightPoolIc(
      input.rowsByDate,
      [
        ...selected.map((item) => ({
          candidate: item,
          direction: (statistics.get(item.id) as FinancialFactorPoolCandidateStatistics).direction,
        })),
        { candidate, direction: candidateStats.direction },
      ],
      signals
    );
    decision.incumbentDevelopmentIc = incumbentDevelopmentIc || 0;
    decision.candidatePoolDevelopmentIc = candidatePoolDevelopmentIc || 0;
    decision.marginalDevelopmentGain = decision.candidatePoolDevelopmentIc - decision.incumbentDevelopmentIc;
    const incumbentFoldIcs = equalWeightPoolFoldIcs(
      input.rowsByDate,
      selected.map((item) => ({
        candidate: item,
        direction: (statistics.get(item.id) as FinancialFactorPoolCandidateStatistics).direction,
      })),
      signals,
      input.policy.stabilityFolds
    );
    const candidatePoolFoldIcs = equalWeightPoolFoldIcs(
      input.rowsByDate,
      [
        ...selected.map((item) => ({
          candidate: item,
          direction: (statistics.get(item.id) as FinancialFactorPoolCandidateStatistics).direction,
        })),
        { candidate, direction: candidateStats.direction },
      ],
      signals,
      input.policy.stabilityFolds
    );
    decision.marginalDevelopmentFoldGains = candidatePoolFoldIcs.map((value, index) => value - incumbentFoldIcs[index]);
    decision.positiveMarginalFoldCount = decision.marginalDevelopmentFoldGains.filter((gain) => gain > 0).length;
    if (candidateStats.coverage < input.minimumCoverage) decision.exclusionReason = 'insufficient_coverage';
    else if (candidateStats.positiveFoldCount < input.policy.minimumPositiveFolds)
      decision.exclusionReason = 'unstable_direction';
    else {
      const expressionKey = canonicalExpression(candidate.expression);
      const duplicateOf = selectedExpressions.get(expressionKey);
      if (duplicateOf) {
        decision.exclusionReason = 'duplicate_expression';
        decision.duplicateOf = duplicateOf;
      } else {
        const familyKey = candidate.family.trim().toLowerCase();
        if ((familyCounts.get(familyKey) || 0) >= input.policy.maxPerFamily) decision.exclusionReason = 'family_limit';
        else {
          const correlations = selected.flatMap((item) => {
            const value = signalCorrelation(signals.get(candidate.id) || new Map(), signals.get(item.id) || new Map());
            return value == null ? [] : [Math.abs(value)];
          });
          const maximumCorrelation = correlations.length ? Math.max(...correlations) : 0;
          decision.maximumSelectedCorrelation = maximumCorrelation;
          if (maximumCorrelation >= input.policy.maximumCorrelation) decision.exclusionReason = 'correlated_signal';
          else if (selected.length >= input.policy.maxFactors) decision.exclusionReason = 'factor_limit';
          else if (
            input.policy.minimumMarginalDevelopmentGain != null &&
            decision.marginalDevelopmentGain <= input.policy.minimumMarginalDevelopmentGain
          )
            decision.exclusionReason = 'insufficient_marginal_gain';
          else if (
            input.policy.minimumMarginalPositiveFolds != null &&
            decision.positiveMarginalFoldCount < input.policy.minimumMarginalPositiveFolds
          )
            decision.exclusionReason = 'unstable_marginal_gain';
          else {
            decision.selected = true;
            selected.push(candidate);
            decision.selectionOrder = selected.length;
            selectedExpressions.set(expressionKey, candidate.id);
            familyCounts.set(familyKey, (familyCounts.get(familyKey) || 0) + 1);
          }
        }
      }
    }
    decisions.set(candidate.id, decision);
  });
  return input.candidates.map((candidate) => decisions.get(candidate.id) as FinancialFactorPoolCandidateDecision);
};

interface RegressionExample {
  date: string;
  features: number[];
  target: number;
}

const regressionExamples = (
  rowsByDate: Map<string, FinancialFactorPoolTableRow[]>,
  selected: Array<{ candidate: FinancialFactorPoolCandidateSpec; direction: -1 | 1 }>
): RegressionExample[] => {
  const signals = normalizedCandidateSignals(rowsByDate, selected);
  return [...rowsByDate.entries()].flatMap(([date, rows]): RegressionExample[] => {
    const valid = rows.flatMap((row): Array<{ features: number[]; target: number }> => {
      if (!Number.isFinite(row.futureReturn)) return [];
      const key = `${date}\u0000${row.asset}`;
      const features = selected.map(({ candidate }) => signals.get(candidate.id)?.get(key));
      if (features.some((value) => !Number.isFinite(value))) return [];
      return [{ features: features as number[], target: row.futureReturn as number }];
    });
    const dailyMean = mean(valid.map((item) => item.target));
    if (dailyMean == null) return [];
    return valid.map((item) => ({ date, features: item.features, target: item.target - dailyMean }));
  });
};

const solveLinearSystem = (matrix: number[][], vector: number[]): number[] => {
  const size = vector.length;
  const augmented = matrix.map((row, index) => [...row, vector[index]]);
  for (let column = 0; column < size; column += 1) {
    let pivot = column;
    for (let row = column + 1; row < size; row += 1) {
      if (Math.abs(augmented[row][column]) > Math.abs(augmented[pivot][column])) pivot = row;
    }
    if (Math.abs(augmented[pivot][column]) < 1e-12) throw new Error('Ridge calibration matrix is singular.');
    [augmented[column], augmented[pivot]] = [augmented[pivot], augmented[column]];
    const divisor = augmented[column][column];
    for (let index = column; index <= size; index += 1) augmented[column][index] /= divisor;
    for (let row = 0; row < size; row += 1) {
      if (row === column) continue;
      const multiplier = augmented[row][column];
      for (let index = column; index <= size; index += 1) {
        augmented[row][index] -= multiplier * augmented[column][index];
      }
    }
  }
  return augmented.map((row) => row[size]);
};

const fitRidge = (examples: RegressionExample[], featureCount: number, lambda: number): number[] => {
  if (!examples.length) throw new Error('Ridge calibration has no complete observations.');
  const matrix = Array.from({ length: featureCount }, () => Array<number>(featureCount).fill(0));
  const vector = Array<number>(featureCount).fill(0);
  examples.forEach(({ features, target }) => {
    for (let left = 0; left < featureCount; left += 1) {
      vector[left] += features[left] * target;
      for (let right = 0; right < featureCount; right += 1) matrix[left][right] += features[left] * features[right];
    }
  });
  for (let left = 0; left < featureCount; left += 1) {
    vector[left] /= examples.length;
    for (let right = 0; right < featureCount; right += 1) matrix[left][right] /= examples.length;
    matrix[left][left] += lambda;
  }
  return solveLinearSystem(matrix, vector);
};

const normalizeWeights = (weights: number[]): number[] => {
  const scale = weights.reduce((total, weight) => total + Math.abs(weight), 0);
  if (!scale) throw new Error('Ridge calibration produced zero weights.');
  return weights.map((weight) => weight / scale);
};

const predictionIc = (examples: RegressionExample[], weights: number[]): number | undefined => {
  const byDate = new Map<string, RegressionExample[]>();
  examples.forEach((example) => byDate.set(example.date, [...(byDate.get(example.date) || []), example]));
  return mean(
    [...byDate.values()].flatMap((daily): number[] => {
      const value = pearson(
        daily.map(({ features }) => features.reduce((total, feature, index) => total + feature * weights[index], 0)),
        daily.map(({ target }) => target)
      );
      return value == null ? [] : [value];
    })
  );
};

const calibrateRidge = (
  calibrationExamples: RegressionExample[],
  fitExamples: RegressionExample[],
  featureCount: number,
  policy: FinancialFactorPoolPolicy
): {
  weights: number[];
  validationWeightsByDate: Map<string, number[]>;
  ridge: { lambda: number; factorCount: number; scores: FinancialFactorPoolRidgeScore[] };
} => {
  const dates = [...new Set(calibrationExamples.map((example) => example.date))].toSorted(
    (left, right) => Date.parse(left) - Date.parse(right)
  );
  const scores = policy.ridgeLambdas.flatMap((lambda): FinancialFactorPoolRidgeScore[] => {
    const foldIcs: number[] = [];
    for (let foldIndex = 1; foldIndex <= policy.stabilityFolds; foldIndex += 1) {
      const validationStart = Math.floor((foldIndex * dates.length) / (policy.stabilityFolds + 1));
      const validationEnd = Math.floor(((foldIndex + 1) * dates.length) / (policy.stabilityFolds + 1));
      const trainingEnd = validationStart - policy.embargoTradingDays;
      if (trainingEnd < 2 || validationEnd <= validationStart) continue;
      const trainingDates = new Set(dates.slice(0, trainingEnd));
      const validationDates = new Set(dates.slice(validationStart, validationEnd));
      const training = calibrationExamples.filter((example) => trainingDates.has(example.date));
      const validation = calibrationExamples.filter((example) => validationDates.has(example.date));
      if (!training.length || !validation.length) continue;
      const value = predictionIc(validation, fitRidge(training, featureCount, lambda));
      if (value != null) foldIcs.push(value);
    }
    const meanIc = mean(foldIcs);
    return meanIc == null
      ? []
      : [{ lambda, factorCount: featureCount, meanIc, worstFoldIc: Math.min(...foldIcs), foldIcs }];
  });
  if (!scores.length) {
    throw new Error('Ridge calibration needs more validation dates after the configured embargo.');
  }
  const selectedScore = [...scores].toSorted(
    (left, right) => right.meanIc - left.meanIc || right.worstFoldIc - left.worstFoldIc || right.lambda - left.lambda
  )[0];
  const validationWeightsByDate = new Map<string, number[]>();
  for (let foldIndex = 1; foldIndex <= policy.stabilityFolds; foldIndex += 1) {
    const validationStart = Math.floor((foldIndex * dates.length) / (policy.stabilityFolds + 1));
    const validationEnd = Math.floor(((foldIndex + 1) * dates.length) / (policy.stabilityFolds + 1));
    const trainingEnd = validationStart - policy.embargoTradingDays;
    if (trainingEnd < 2 || validationEnd <= validationStart) continue;
    const trainingDates = new Set(dates.slice(0, trainingEnd));
    const validationDates = dates.slice(validationStart, validationEnd);
    const training = calibrationExamples.filter((example) => trainingDates.has(example.date));
    if (!training.length) continue;
    const foldWeights = normalizeWeights(fitRidge(training, featureCount, selectedScore.lambda));
    validationDates.forEach((date) => validationWeightsByDate.set(date, foldWeights));
  }
  const rawWeights = fitRidge(fitExamples, featureCount, selectedScore.lambda);
  return {
    weights: normalizeWeights(rawWeights),
    validationWeightsByDate,
    ridge: { lambda: selectedScore.lambda, factorCount: featureCount, scores },
  };
};

const applyFinancialFactorPoolValidationPredictions = (input: {
  rows: FinancialFactorPoolTableRow[];
  selectedFactors: FinancialFactorPoolFitResult['selectedFactors'];
  weightsByDate: Map<string, number[]>;
}): FinancialFactorEvaluationRow[] => {
  const rowsByDate = groupByDate(input.rows);
  const selected = input.selectedFactors.map(({ candidate, statistics }) => ({
    candidate,
    direction: statistics.direction,
  }));
  const signals = normalizedCandidateSignals(rowsByDate, selected);
  return input.rows.map((row) => {
    const weights = input.weightsByDate.get(row.date);
    const key = `${row.date}\u0000${row.asset}`;
    const features = input.selectedFactors.map(({ candidate }) => signals.get(candidate.id)?.get(key));
    const factorValue =
      weights && weights.length === features.length && features.every(Number.isFinite)
        ? (features as number[]).reduce((total, value, index) => total + value * weights[index], 0)
        : undefined;
    return {
      date: row.date,
      asset: row.asset,
      factorValue,
      futureReturn: row.futureReturn,
      ...(row.availableAt ? { availableAt: row.availableAt } : {}),
    };
  });
};

export const applyFinancialFactorCandidate = (input: {
  rows: FinancialFactorPoolTableRow[];
  candidate: FinancialFactorPoolCandidateSpec;
}): FinancialFactorEvaluationRow[] =>
  input.rows.map((row) => ({
    date: row.date,
    asset: row.asset,
    factorValue: row.factorValues[input.candidate.id],
    futureReturn: row.futureReturn,
    ...(row.availableAt ? { availableAt: row.availableAt } : {}),
  }));

export const applyFinancialFactorPoolModel = (input: {
  rows: FinancialFactorPoolTableRow[];
  selectedFactors: FinancialFactorPoolModel['selectedFactors'];
}): FinancialFactorEvaluationRow[] => {
  const rowsByDate = groupByDate(input.rows);
  const selected = input.selectedFactors.map(({ candidate, statistics }) => ({
    candidate,
    direction: statistics.direction,
  }));
  const signals = normalizedCandidateSignals(rowsByDate, selected);
  return input.rows.map((row) => {
    const key = `${row.date}\u0000${row.asset}`;
    const features = input.selectedFactors.map(({ candidate }) => signals.get(candidate.id)?.get(key));
    const factorValue = features.every(Number.isFinite)
      ? (features as number[]).reduce((total, value, index) => total + value * input.selectedFactors[index].weight, 0)
      : undefined;
    return {
      date: row.date,
      asset: row.asset,
      factorValue,
      futureReturn: row.futureReturn,
      ...(row.availableAt ? { availableAt: row.availableAt } : {}),
    };
  });
};

export const fitFinancialFactorPool = (input: {
  protocol: FinancialFactorEvaluationProtocol;
  candidates: FinancialFactorPoolCandidateSpec[];
  rows: FinancialFactorPoolTableRow[];
  developmentSplitId: string;
  validationSplitId: string;
}): FinancialFactorPoolFitResult => {
  const policy = input.protocol.pool;
  if (!policy) throw new Error('The frozen protocol must define pool policy before fitting a factor pool.');
  if (new Set(input.candidates.map((candidate) => candidate.id)).size !== input.candidates.length) {
    throw new Error('Factor-pool candidate ids must be unique.');
  }
  const developmentSplit = input.protocol.splits.find((split) => split.id === input.developmentSplitId);
  const validationSplit = input.protocol.splits.find((split) => split.id === input.validationSplitId);
  if (!developmentSplit || developmentSplit.role !== 'development') {
    throw new Error('Factor-pool fitting requires a development split.');
  }
  if (!validationSplit || validationSplit.role !== 'validation') {
    throw new Error('Factor-pool calibration requires a validation split.');
  }
  if (Date.parse(developmentSplit.end) >= Date.parse(validationSplit.start)) {
    throw new Error('Factor-pool development and validation splits must be strictly chronological and disjoint.');
  }
  const allDevelopmentRows = input.rows.filter((row) =>
    dateInRange(row.date, developmentSplit.start, developmentSplit.end)
  );
  const allValidationRows = input.rows.filter((row) =>
    dateInRange(row.date, validationSplit.start, validationSplit.end)
  );
  if (!allDevelopmentRows.length || !allValidationRows.length) {
    throw new Error('Factor-pool fitting requires rows in both development and validation splits.');
  }
  const developmentRows = purgeSplitTail(allDevelopmentRows, policy.splitPurgeTradingDays);
  const validationRows = purgeSplitTail(allValidationRows, policy.splitPurgeTradingDays);
  const candidateDecisions = selectCandidates({
    candidates: input.candidates,
    rowsByDate: groupByDate(developmentRows),
    policy,
    minimumCoverage: input.protocol.evaluation.minimumCoverage,
    annualizationFactor: input.protocol.evaluation.annualizationFactor,
  });
  const developmentSelected = candidateDecisions
    .filter((decision) => decision.selected)
    .toSorted((left, right) => (left.selectionOrder || 0) - (right.selectionOrder || 0))
    .map(({ candidate, statistics }) => ({ candidate, direction: statistics.direction }));
  if (!developmentSelected.length) throw new Error('No factor-pool candidate passed the frozen selection policy.');
  const developmentByDate = groupByDate(developmentRows);
  const validationByDate = groupByDate(validationRows);
  const prefixSizes = policy.selectPoolSizeOnValidation
    ? Array.from({ length: developmentSelected.length }, (_, index) => index + 1)
    : [developmentSelected.length];
  const prefixCalibrations = prefixSizes.map((factorCount) => {
    const selected = developmentSelected.slice(0, factorCount);
    const validationExamples = regressionExamples(validationByDate, selected);
    const fitExamples = [...regressionExamples(developmentByDate, selected), ...validationExamples];
    const calibration = calibrateRidge(validationExamples, fitExamples, factorCount, policy);
    const selectedScore = calibration.ridge.scores.find(
      (score) => score.lambda === calibration.ridge.lambda && score.factorCount === factorCount
    ) as FinancialFactorPoolRidgeScore;
    return { selected, calibration, selectedScore };
  });
  const chosenPrefix = [...prefixCalibrations].toSorted(
    (left, right) =>
      right.selectedScore.meanIc - left.selectedScore.meanIc ||
      right.selectedScore.worstFoldIc - left.selectedScore.worstFoldIc ||
      left.selected.length - right.selected.length ||
      right.calibration.ridge.lambda - left.calibration.ridge.lambda
  )[0];
  const selected = chosenPrefix.selected;
  const calibration = {
    ...chosenPrefix.calibration,
    ridge: {
      ...chosenPrefix.calibration.ridge,
      scores: prefixCalibrations.flatMap(({ calibration: item }) => item.ridge.scores),
    },
  };
  if (selected.length < developmentSelected.length) {
    const selectedIds = new Set(selected.map(({ candidate }) => candidate.id));
    candidateDecisions.forEach((decision) => {
      if (decision.selected && !selectedIds.has(decision.candidate.id)) {
        decision.selected = false;
        decision.exclusionReason = 'validation_pool_limit';
      }
    });
  }
  const selectedFactors = selected.map(({ candidate }, index) => ({
    candidate,
    statistics: candidateDecisions.find((decision) => decision.candidate.id === candidate.id)
      ?.statistics as FinancialFactorPoolCandidateStatistics,
    weight: calibration.weights[index],
  }));
  return {
    candidateDecisions,
    selectedFactors,
    ridge: calibration.ridge,
    validationRows: applyFinancialFactorPoolValidationPredictions({
      rows: validationRows,
      selectedFactors,
      weightsByDate: calibration.validationWeightsByDate,
    }),
    fittedDateBoundary: {
      developmentLastFitDate: developmentRows.reduce((latest, row) => (row.date > latest ? row.date : latest), ''),
      validationLastFitDate: validationRows.reduce((latest, row) => (row.date > latest ? row.date : latest), ''),
    },
  };
};

export const createFinancialFactorPoolModelDraft = (input: {
  poolId: string;
  name: string;
  runId: string;
  protocol: FinancialFactorEvaluationProtocol;
  inputPath: string;
  datasetContentSha256: string;
  developmentSplitId: string;
  validationSplitId: string;
  fit: FinancialFactorPoolFitResult;
  calibration: FinancialFactorPoolModel['calibration'];
  fitRequestHash: string;
  modelHash: string;
  createdAt: number;
}): FinancialFactorPoolModel => {
  const development = input.protocol.splits.find((split) => split.id === input.developmentSplitId);
  const validation = input.protocol.splits.find((split) => split.id === input.validationSplitId);
  if (!input.protocol.pool || !development || !validation)
    throw new Error('Cannot materialize an incomplete pool model.');
  return {
    schema: FINANCIAL_FACTOR_POOL_SCHEMA,
    version: 1,
    poolId: input.poolId,
    name: input.name,
    runId: input.runId,
    protocolId: input.protocol.protocolId,
    datasetSnapshotId: input.protocol.dataset.snapshotId,
    datasetContentSha256: input.datasetContentSha256,
    inputPath: input.inputPath,
    developmentSplitId: input.developmentSplitId,
    validationSplitId: input.validationSplitId,
    lambdaSelectionSplitId: input.validationSplitId,
    weightFitSplitIds: [input.developmentSplitId, input.validationSplitId],
    policy: input.protocol.pool,
    candidateDecisions: input.fit.candidateDecisions,
    selectedFactors: input.fit.selectedFactors,
    ridge: input.fit.ridge,
    calibration: input.calibration,
    fitBoundary: {
      developmentStart: development.start,
      developmentEnd: development.end,
      validationStart: validation.start,
      validationEnd: validation.end,
      developmentLastFitDate: input.fit.fittedDateBoundary.developmentLastFitDate,
      validationLastFitDate: input.fit.fittedDateBoundary.validationLastFitDate,
      splitPurgeTradingDays: input.protocol.pool.splitPurgeTradingDays,
      lockedTestUsed: false,
    },
    fitRequestHash: input.fitRequestHash,
    modelHash: input.modelHash,
    createdAt: input.createdAt,
  };
};
