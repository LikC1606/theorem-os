import { describe, expect, it } from 'vitest';
import { mathDigest } from '../src/math/mathRuntimeIo';
import { finishLeadAssessment, leadAssessmentCovered, prepareLeadAssessment } from '../src/solver/leadAssessment';

const input = (text = 'input') => ({ inputDigest: mathDigest(text), evidenceDigest: mathDigest('evidence'),
  requestedAt: 10, status: 'requested' as const, workerIds: ['prover'] });

describe('durable Lead assessment lifecycle', () => {
  it('preserves one pending identity and requested time across eleven redispatches and JSON recovery', () => {
    let prepared = prepareLeadAssessment('capacity', undefined, input(), 'dispatch-0');
    const first = structuredClone(prepared.receipt);
    for (let index = 1; index <= 11; index++) {
      prepared = prepareLeadAssessment('capacity', JSON.parse(JSON.stringify(prepared.receipt)),
        { ...input(), requestedAt: 99 + index, workerIds: ['another'] }, 'dispatch-' + index);
      expect(prepared.created).toBe(false);
      expect(prepared.receipt.requestId).toBe(first.requestId);
      expect(prepared.receipt.requestedAt).toBe(first.requestedAt);
      expect(prepared.receipt.workerIds).toEqual(first.workerIds);
    }
    expect(finishLeadAssessment(prepared.receipt, first, 'dispatch-0', { at: 50, outcome: 'plan-published' })).toBe(false);
    expect(finishLeadAssessment(prepared.receipt, prepared.receipt, 'dispatch-11',
      { at: 50, outcome: 'no-independent-work', reason: 'The exact classification argument remains missing.' })).toBe(true);
    expect(prepared.receipt.outcome).toBe('no-independent-work');
  });

  it('retains the frozen basis while covering only its own graph revision with unchanged evidence', () => {
    const { receipt } = prepareLeadAssessment('capacity', undefined, input(), 'dispatch');
    const original = receipt.inputDigest, revised = mathDigest('revised graph');
    expect(finishLeadAssessment(receipt, receipt, 'dispatch', { at: 20, outcome: 'plan-published',
      currentInput: { inputDigest: revised, evidenceDigest: receipt.evidenceDigest! } })).toBe(true);
    expect(receipt.inputDigest).toBe(original);
    expect(leadAssessmentCovered(receipt, revised)).toBe(true);
  });

  it('does not acknowledge a peer finding that arrived during the old decision', () => {
    const { receipt } = prepareLeadAssessment('capacity', undefined, input(), 'dispatch');
    const next = mathDigest('new input');
    finishLeadAssessment(receipt, receipt, 'dispatch', { at: 20, outcome: 'plan-published',
      currentInput: { inputDigest: next, evidenceDigest: mathDigest('new evidence') } });
    expect(leadAssessmentCovered(receipt, next)).toBe(false);
    expect(prepareLeadAssessment('capacity', receipt, input('new input'), 'next').created).toBe(true);
  });

  it('assigns legacy pending receipts a deterministic identity without treating them as a new request', () => {
    const legacy = input(); delete legacy.evidenceDigest;
    const first = prepareLeadAssessment('stagnation', legacy, input(), 'first');
    const second = prepareLeadAssessment('stagnation', legacy, input(), 'second');
    expect(first.created).toBe(false);
    expect(first.receipt.requestId).toBe(second.receipt.requestId);
    expect(first.receipt.evidenceDigest).toBe(input().evidenceDigest);
  });
});
