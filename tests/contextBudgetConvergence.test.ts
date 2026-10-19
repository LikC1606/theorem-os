import { expect, it } from 'vitest';
import { canonicalMathJson, mathDigest } from '../src/math/mathRuntimeIo';
import { compileTaskContext, type TaskContextInput } from '../src/solver/contextCompiler';
import type { SolverProblem } from '../src/solver/problem';

const problem = { receiptDigest: 'fixture-problem', baseCommit: 'a'.repeat(40), projectRelative: 'generated/p',
  ownedFiles: [], declarations: {}, trustedFiles: {}, targets: [],
  contract: { formalStatement: 'True', assumptions: [] } } as unknown as SolverProblem;
const input = (instructions = ''): TaskContextInput => ({
  problem, instructions, taskText: 'Prove the target.', maxContextBytes: 200000, maxOptionalContextBytes: 0,
});
const inline = (message: string) => JSON.parse(message.split('Context compilation manifest:\n')[1]);

it.each([10000, 100000])('converges both byte fields across the %s digit boundary', boundary => {
  const baseline = compileTaskContext(input()).manifest.usedBytes;
  const results = Array.from({ length: 12 }, (_, index) => {
    const request = input('x'.repeat(boundary - baseline - 6 + index));
    const result = compileTaskContext(request);
    const recorded = inline(result.message);
    expect(result.manifest.usedBytes).toBe(Buffer.byteLength(request.instructions) + Buffer.byteLength(result.message));
    expect(result.manifest.mandatoryBytes).toBe(result.manifest.usedBytes);
    expect(recorded.usedBytes).toBe(result.manifest.usedBytes);
    expect(recorded.mandatoryBytes).toBe(result.manifest.mandatoryBytes);
    return result.manifest.usedBytes;
  });
  expect(results.some(bytes => bytes < boundary)).toBe(true);
  expect(results.some(bytes => bytes >= boundary)).toBe(true);
});

it.each([32, 33, 99])('preserves the full %s-item omission set while sizing its preview', count => {
  const request = { ...input('x'.repeat(9000)), optional: Array.from({ length: count }, (_, index) =>
    ({ id: `hint-${index}`, kind: 'finding' as const, text: '\u6570\ud83d\ude42' })) };
  const result = compileTaskContext(request), recorded = inline(result.message);
  expect(result.manifest.omitted).toEqual(request.optional.map(item =>
    ({ id: item.id, kind: item.kind, reason: 'optional-budget' })));
  expect(result.manifest.usedBytes).toBe(Buffer.byteLength(request.instructions) + Buffer.byteLength(result.message));
  if (count <= 32) expect(recorded).toEqual(result.manifest);
  else {
    expect(recorded.omitted).toEqual(result.manifest.omitted.slice(0, 16));
    expect(recorded.omissionSet).toMatchObject({ count, digest: mathDigest(canonicalMathJson(result.manifest.omitted)) });
  }
});

it.each([8, 9, 10])('counts UTF-8 optional text and its separator against a %s-byte allowance', allowance => {
  const text = '\u6570\ud83d\ude42';
  const result = compileTaskContext({ ...input(), maxOptionalContextBytes: allowance,
    optional: [{ id: 'utf8', kind: 'finding', text }] });
  const included = result.manifest.included.find(item => item.id === 'utf8');
  expect(Boolean(included)).toBe(allowance >= 9);
  expect(result.manifest.optionalBytes).toBe(allowance >= 9 ? 9 : 0);
  if (included) expect(included.bytes).toBe(Buffer.byteLength(text));
});

it.each([99999, 999999])('enforces an exact UTF-8 hard byte boundary below %s', maxBytes => {
  const request = { ...input('\u6570'.repeat(Math.floor(maxBytes / 12))), maxContextBytes: maxBytes };
  const baseline = compileTaskContext(request);
  expect(compileTaskContext({ ...request, maxContextBytes: baseline.manifest.usedBytes })).toEqual({
    ...baseline, manifest: { ...baseline.manifest, maxBytes: baseline.manifest.usedBytes },
    message: baseline.message.replace(`"maxBytes":${maxBytes}`, `"maxBytes":${baseline.manifest.usedBytes}`),
  });
  expect(() => compileTaskContext({ ...request, maxContextBytes: baseline.manifest.usedBytes - 1 }))
    .toThrow('math_context_mandatory_overflow');
});
