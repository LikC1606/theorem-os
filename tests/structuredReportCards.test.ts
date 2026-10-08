import { describe, expect, it } from 'vitest';
import {
  structuredReportCardSchema,
  validateStructuredReportCards,
} from '../src/common/chat/structuredReportCards';

const card = {
  schema: 'deepscientist.report_card.v1', kind: 'metric_strip', id: 'proof-metrics', title: 'Proof checks',
  snapshotId: 'snapshot-1', artifactRef: { artifactId: 'checks', version: 1 }, evidenceIds: ['lean-check'],
  refreshedAt: '2026-10-09T00:00:00Z', lifecycle: 'ready', freshness: 'current', completeness: 'complete',
  previewTarget: { kind: 'artifact', artifactId: 'checks' },
  metrics: [{ id: 'theorems', label: 'Checked theorems', value: 3 }],
};

describe('mathematical report cards', () => {
  it('accepts mathematical results without trading or market metadata', () => {
    expect(validateStructuredReportCards([card], {
      artifactRefs: new Set(['checks@1']), evidenceIds: new Set(['lean-check']),
    })).toMatchObject({ ok: true, cards: [{ id: 'proof-metrics' }] });
  });

  it('keeps saved generic cards readable', () => {
    expect(structuredReportCardSchema.safeParse({ ...card, dataMode: 'HISTORICAL', tradeCapability: 'disabled' }).success)
      .toBe(true);
  });

  it.each(['financial_research', 'science_factor'])('rejects the removed %s preview', kind => {
    expect(structuredReportCardSchema.safeParse({ ...card, previewTarget: { kind, artifactId: 'checks' } }).success)
      .toBe(false);
  });

  it('still rejects dangling evidence and unbound simulation assumptions', () => {
    expect(validateStructuredReportCards([card], {
      artifactRefs: new Set(['checks@1']), evidenceIds: new Set(),
    })).toMatchObject({ ok: false, errors: [expect.stringContaining('unknown evidence lean-check')] });
    expect(structuredReportCardSchema.safeParse({ ...card, dataMode: 'SIMULATION' }).success).toBe(false);
  });
});
