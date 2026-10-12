import { describe, expect, it } from 'vitest';
import { parseLeanReferences } from '../src/math/leanReferences';

describe('Lean reference reports', () => {
  const marker = 'DS_REFERENCE_fixture:';
  const parse = (value: unknown) => parseLeanReferences(marker + JSON.stringify(value), marker, ['Submission.lean']);
  it('keeps statement and proof references distinct and normalizes duplicates', () => {
    expect(parse([[['N.Predicate', 'Submission.lean']], [['N.lemma', 'Submission.lean'], ['N.lemma', 'Submission.lean']]]))
      .toEqual({ statement: [{ name: 'N.Predicate', file: 'Submission.lean' }], proof: [{ name: 'N.lemma', file: 'Submission.lean' }] });
  });
  it('recognizes an explicit empty report, while missing output remains unknown', () => {
    expect(parse([[], []])).toEqual({ statement: [], proof: [] });
    expect(parseLeanReferences('', marker, ['Submission.lean'])).toBeUndefined();
  });
  it.each([null, [[], [['outside', '../other.lean']]], [[], [['', 'Submission.lean']]], [[], [['name']]], { proof: [] }])(
    'treats an incomplete or invalid report as unknown: %j', value => { expect(parse(value)).toBeUndefined(); });
  it('rejects ambiguous and oversized output', () => {
    const valid = marker + '[[],[]]';
    expect(parseLeanReferences(valid + '\n' + valid, marker, ['Submission.lean'])).toBeUndefined();
    expect(parseLeanReferences(marker + ' '.repeat(8001) + '[[],[]]', marker, ['Submission.lean'])).toBeUndefined();
  });
});
