import { describe, expect, it } from 'vitest';
import { parseWorkerMessage } from '../apps/web/runner';

describe('web worker protocol boundary', () => {
  it('accepts progress and a structured acceptance result', () => {
    expect(parseWorkerMessage('{"type":"progress","event":"ready","message":"Ready"}'))
      .toEqual({ type: 'progress', event: 'ready', message: 'Ready' });
    const result = { type: 'result', result: { status: 'evaluated_passed', proof: 'by rfl', report: { evaluator: { status: 'passed' } } } };
    expect(parseWorkerMessage(JSON.stringify(result))).toEqual(result);
  });

  it.each([
    'runtime console output', 'null', '[]', '{}', '{"type":"result"}',
    '{"type":"result","result":{"status":"evaluated_passed","proof":"","report":[]}}',
    '{"type":"progress","event":{},"message":"Ready"}',
    '{"type":"error","message":null}',
    JSON.stringify({ type: 'result', result: { status: 'incomplete', proof: 'x'.repeat(128 * 1024 + 1), report: {} } }),
  ])('ignores malformed or oversized protocol data (%#)', line => {
    expect(parseWorkerMessage(line)).toBeUndefined();
  });
});
