import { describe, expect, it } from 'vitest';
import { parseWorkerMessage } from '../apps/web/runner';

describe('web worker protocol boundary', () => {
  it('accepts progress and a structured acceptance result', () => {
    expect(parseWorkerMessage('{"type":"progress","event":"ready","message":"Ready"}'))
      .toEqual({ type: 'progress', event: 'ready', message: 'Ready' });
    const result = { type: 'result', result: { status: 'evaluated_passed', proof: 'by rfl', report: { evaluator: { status: 'passed' } } } };
    expect(parseWorkerMessage(JSON.stringify(result))).toEqual(result);
  });

  it('accepts a bounded Lean candidate without granting acceptance', () => {
    const artifact = { type: 'artifact', artifact: { source: 'theorem example : True := by trivial',
      workerId: 'engineer', capturedAt: '2026-10-17T00:00:00.000Z', status: 'candidate' } };
    expect(parseWorkerMessage(JSON.stringify(artifact))).toEqual(artifact);
  });

  it('accepts bounded optional structured progress without changing legacy messages', () => {
    const message = { type: 'progress', event: 'proof_checked', message: 'Checked',
      details: { workerId: 'solver', turn: 1, passed: false, conditional: false, reused: true } };
    expect(parseWorkerMessage(JSON.stringify(message))).toEqual(message);
    const legacy = { type: 'progress', event: 'proof_checked', message: 'Checked' };
    expect(parseWorkerMessage(JSON.stringify(legacy))).toEqual(legacy);
  });

  it.each([
    null, [], 'private', { workerId: '/work/private' }, { workerId: 'x'.repeat(65) },
    { turn: -1 }, { usedBytes: 1.5 }, { maxBytes: Number.MAX_SAFE_INTEGER + 1 },
    { passed: 'true' }, { status: 'private log' }, { operation: 'run-shell' }, { role: 'admin' },
    { workerId: 'solver', threadId: 'private-thread' }, { context: { apiKey: 'sk-private' } },
  ])('rejects malformed or non-allowlisted progress metadata (%#)', details => {
    expect(parseWorkerMessage(JSON.stringify({ type: 'progress', event: 'worker_activity', message: 'Working', details }))).toBeUndefined();
  });

  it.each([
    { source: '', workerId: 'solver', capturedAt: '2026-10-17T00:00:00.000Z', status: 'candidate' },
    { source: 'by trivial', workerId: '../secret', capturedAt: '2026-10-17T00:00:00.000Z', status: 'candidate' },
    { source: 'by trivial', workerId: 'solver', capturedAt: 'yesterday', status: 'candidate' },
    { source: 'by trivial', workerId: 'solver', capturedAt: '2026-10-17T00:00:00.000Z', status: 'evaluated_passed' },
    { source: 'by trivial', workerId: 'solver', capturedAt: '2026-10-17T00:00:00.000Z', status: 'candidate', path: '/etc/passwd' },
    { source: '\u8bc1'.repeat(50_000), workerId: 'solver', capturedAt: '2026-10-17T00:00:00.000Z', status: 'candidate' },
  ])('rejects invalid candidate metadata or oversized UTF-8 (%#)', artifact => {
    expect(parseWorkerMessage(JSON.stringify({ type: 'artifact', artifact }))).toBeUndefined();
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
