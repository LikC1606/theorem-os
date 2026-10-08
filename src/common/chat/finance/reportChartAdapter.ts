/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

import { REPORT_CHART_SCHEMA, normalizeReportChartSpec, type ReportChartSpecV1 } from "../reportChart";
import type { StructuredReportCard } from "./structuredReportCards";

const chartStyle = {
  palette: 'auto' as const,
  appearance: 'auto' as const,
  density: 'compact' as const,
  showGrid: false,
  showLegend: false,
  directLabels: true,
};

const uniqueEvidenceIds = (ids: string[]): string[] => [...new Set(ids)].slice(0, 32);

type FinanceChartCardBase = StructuredReportCard & {
  id: string;
  title: string;
  evidenceIds: string[];
};

type FinanceTimeseriesChartCard = FinanceChartCardBase & {
  kind: 'timeseries';
  xLabel?: string;
  yLabel?: string;
  series: Array<{
    id: string;
    label: string;
    unit?: string;
    points: Array<{ x: string | number; y: number }>;
  }>;
};

type FinanceRankedChartCard = FinanceChartCardBase & {
  kind: 'ranked_list';
  items: Array<{
    id: string;
    label: string;
    value?: string | number;
    detail?: string;
    evidenceIds?: string[];
  }>;
};

const sharedUnit = (units: Array<string | undefined>): string | undefined => {
  const definedUnits = [...new Set(units.filter((unit): unit is string => Boolean(unit)))];
  return definedUnits.length === 1 ? definedUnits[0] : undefined;
};

const timeseriesToReportChart = (card: FinanceTimeseriesChartCard): ReportChartSpecV1 | undefined => {
  const xKinds = new Set(card.series.flatMap((series) => series.points.map((point) => typeof point.x)));
  if (xKinds.size !== 1) return undefined;

  const unit = sharedUnit(card.series.map((series) => series.unit));
  return normalizeReportChartSpec({
    schema: REPORT_CHART_SCHEMA,
    id: card.id,
    kind: 'line',
    title: card.title,
    evidenceIds: uniqueEvidenceIds(card.evidenceIds),
    xAxis: {
      ...(card.xLabel ? { label: card.xLabel } : {}),
      scale: xKinds.has('string') ? 'time' : 'linear',
    },
    yAxis: {
      ...(card.yLabel ? { label: card.yLabel } : {}),
      ...(unit ? { unit } : {}),
      scale: 'linear',
    },
    style: { ...chartStyle, showLegend: card.series.length > 1 },
    series: card.series.map((series) => ({
      id: series.id,
      label: series.label,
      ...(series.unit ? { unit: series.unit } : {}),
      points: series.points.map((point) => ({
        x: point.x,
        y: point.y,
      })),
    })),
  });
};

const rankedListToReportChart = (card: FinanceRankedChartCard): ReportChartSpecV1 | undefined => {
  if (card.items.length === 0 || card.items.some((item) => typeof item.value !== 'number')) return undefined;

  return normalizeReportChartSpec({
    schema: REPORT_CHART_SCHEMA,
    id: card.id,
    kind: 'bar',
    title: card.title,
    evidenceIds: uniqueEvidenceIds(card.evidenceIds),
    orientation: 'horizontal',
    xAxis: { scale: 'linear' },
    yAxis: { scale: 'category' },
    style: chartStyle,
    data: card.items.map((item) => ({
      id: item.id,
      label: item.label,
      value: item.value as number,
      ...(item.detail ? { note: item.detail } : {}),
      evidenceIds: uniqueEvidenceIds(item.evidenceIds ?? card.evidenceIds),
    })),
  });
};

/**
 * Projects persisted finance cards into the shared report-chart contract.
 * Returning undefined is intentional: callers keep the card's established
 * renderer when a lossless, semantically valid projection is unavailable.
 */
export const structuredReportCardToReportChartSpec = (card: StructuredReportCard): ReportChartSpecV1 | undefined => {
  if (card.kind === 'timeseries') return timeseriesToReportChart(card as FinanceTimeseriesChartCard);
  if (card.kind === 'ranked_list') return rankedListToReportChart(card as FinanceRankedChartCard);
  return undefined;
};
