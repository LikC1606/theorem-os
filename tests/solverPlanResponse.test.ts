import { describe, expect, it } from 'vitest';
import { parseMathResponse } from '../src/solver/deliveries';

const fence = (kind: string, value: unknown) => '```' + kind + '\n' +
  (typeof value === 'string' ? value : JSON.stringify(value)) + '\n```';
const plan = { tasks: [{ id: 'original', kind: 'goal', theoremName: 'original', proofPath: 'Submission.lean' }],
  groups: [], proofRoutes: [] };
const parse = (text: string) => parseMathResponse(text, 'math-plan');

describe('Lead plan response selection', () => {
  it('reads the complete plan beside an explanatory mathematical-gap JSON block', () => {
    // The live 09:21 checkpoint contained these two complete JSON fences.
    const explanation = { consumer: { taskId: 'original', taskDigest: 'current' },
      previousGap: 'No bound on the least truant', reduced: 'The small-rank cases are checked',
      remaining: 'The higher-rank escalation step', evidenceScope: 'Checked helpers only',
      reconsiderWhen: ['A classification theorem is available'] };
    const notes = '# Escalation argument\n' + fence('json', explanation) + '\n\n' + fence('math', plan);
    expect(parse(notes)).toEqual(plan);
  });

  it('ignores plan-like keys nested inside ordinary explanatory JSON', () => {
    const notes = fence('json', { construction: { tasks: ['explain the cases'], proofRoutes: ['illustration'] } }) +
      '\n' + fence('json', plan);
    expect(parse(notes)).toEqual(plan);
  });

  it.each(['math', 'json', 'math-plan', 'raw'])('keeps the supported %s plan format and explicit response bindings', kind => {
    const response = { ...plan, baseVersion: 'response-version' };
    const text = kind === 'raw' ? JSON.stringify(response) : fence(kind, response);
    expect(parseMathResponse(text, 'math-plan', { baseVersion: 'host-version', receipt: 'host-receipt' }))
      .toEqual({ ...response, receipt: 'host-receipt' });
  });

  it('gives a dedicated math-plan response priority over explanatory and inherited legacy blocks', () => {
    const notes = fence('json', { remaining: 'The proof is open' }) + '\n' +
      fence('math', { tasks: [{ id: 'old' }] }) + '\n' + fence('math-plan', plan);
    expect(parse(notes)).toEqual(plan);
  });

  it('does not fall back to a legacy plan when the dedicated response is malformed or invalid', () => {
    expect(() => parse(fence('math', plan) + '\n' + fence('math-plan', '{"tasks":'))).toThrow(SyntaxError);
    expect(() => parse(fence('math', plan) + '\n' + fence('math-plan', []))).toThrow('math_response_invalid');
  });

  it('rejects multiple dedicated responses even when they are identical', () => {
    expect(() => parse(fence('math-plan', plan) + '\n' + fence('math-plan', plan)))
      .toThrow('math_math-plan_requires_one_block');
  });

  it.each(['math', 'json'])('rejects multiple true legacy controls including a %s fence', kind => {
    expect(() => parse(fence('math', plan) + '\n' + fence(kind, { tasks: [{ id: 'other' }] })))
      .toThrow('math_math-plan_requires_one_block');
  });

  it('does not hide a malformed legacy control response behind a valid plan', () => {
    expect(() => parse(fence('json', '{"tasks":') + '\n' + fence('math', plan)))
      .toThrow('math_math-plan_requires_one_block');
    expect(() => parse(fence('math', '{"tasks":'))).toThrow(SyntaxError);
  });

  it.each([
    { kind: 'assessment', baseVersion: 'version', dispatchNonce: 'nonce', assessments: [] },
    { handoffDecisions: [{ id: 'proposal', status: 'deferred' }], challengeDecisions: [] },
  ])('retains coordination responses for downstream protocol validation', response => {
    expect(parse(fence('json', response))).toEqual(response);
  });

  it('does not promote ordinary JSON or another control response into a plan', () => {
    expect(() => parse(fence('json', { remaining: 'An open inference', metadata: { tasks: [] } })))
      .toThrow('math_math-plan_requires_one_block');
    expect(() => parse(fence('math-result', { summary: 'An advisory result' })))
      .toThrow('math_math-plan_requires_one_block');
  });
});
