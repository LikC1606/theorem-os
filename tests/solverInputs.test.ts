import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import { afterEach, describe, expect, it } from 'vitest';
import { MAX_DELIVERY_LINE_BYTES, readDeliveryLines, readMathResponse } from '../src/solver/deliveries';
import { readMathText } from '../src/math/mathRuntimeIo';

const roots: string[] = [];
const temp = () => { const root = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'math-input-'))); roots.push(root); return root; };
afterEach(() => { for (const root of roots.splice(0)) fs.rmSync(root, { recursive: true, force: true }); });

describe('solver input boundaries', () => {
  it('rejects linked research inputs while accepting ordinary Markdown', () => {
    const root = temp(), workspace = path.join(root, 'workspace'); fs.mkdirSync(workspace);
    const outside = path.join(root, 'outside.md'), response = path.join(workspace, 'RESEARCH.md');
    fs.writeFileSync(outside, '{"summary":"outside"}'); fs.symlinkSync(outside, response);
    expect(() => readMathResponse(workspace, 'math-result')).toThrow('missing_or_too_large');
    fs.unlinkSync(response); fs.writeFileSync(response, '# Research\nA useful explanation.');
    expect(readMathResponse(workspace, 'math-result', {}, 'summary').summary).toContain('useful explanation');
  });

  it('rejects oversized and invalid UTF-8 inputs', () => {
    const file = path.join(temp(), 'input');
    fs.writeFileSync(file, '数'.repeat(30));
    expect(() => readMathText(file, 64)).toThrow('too_large');
    expect(readMathText(file, 5, { headOnly: true })).toBe('数');
    fs.writeFileSync(file, Buffer.from([0xff]));
    expect(() => readMathText(file, 64)).toThrow();
  });

  it.each([false, true])('tracks log byte offsets across blank lines, CRLF and partial writes (recovery=%s)', recovery => {
    const file = path.join(temp(), 'edits.jsonl');
    const read = (offset: number) => readDeliveryLines(file, offset, recovery ? { discardingOversized: false } : undefined);
    const prefix = '\n' + JSON.stringify({ summary: '\u6570\u5b66' }) + '\r\n';
    fs.writeFileSync(file, prefix + '{"partial":');
    const batch = read(0);
    expect(batch.lines).toEqual([JSON.stringify({ summary: '\u6570\u5b66' }) + '\r']);
    expect(batch.entries?.map(entry => entry.offset)).toEqual([1, Buffer.byteLength(prefix)]);
    expect(batch.offset).toBe(Buffer.byteLength(prefix));
    expect(Object.hasOwn(batch, 'discardingOversized')).toBe(recovery);
    fs.appendFileSync(file, 'true}\n');
    const resumed = read(batch.offset);
    expect(resumed.lines).toEqual(['{"partial":true}']);
    expect(resumed.entries?.[0].offset).toBe(fs.statSync(file).size);
  });

  it.each([false, true])('rereads an incomplete UTF-8 line crossing the chunk boundary (recovery=%s)', recovery => {
    const file = path.join(temp(), 'edits.jsonl'), prefix = 'x'.repeat(MAX_DELIVERY_LINE_BYTES - 2) + '\n', tail = '\u6570\u5b66\n';
    const read = (offset: number) => readDeliveryLines(file, offset, recovery ? { discardingOversized: false } : undefined);
    fs.writeFileSync(file, prefix + tail);
    const batch = read(0);
    expect(batch.lines).toEqual([prefix.slice(0, -1)]);
    expect(batch.offset).toBe(Buffer.byteLength(prefix));
    expect(read(batch.offset)).toMatchObject({ lines: [tail.slice(0, -1)], offset: fs.statSync(file).size });
  });

  it.each([false, true])('accepts a complete line filling the read chunk (recovery=%s)', recovery => {
    const file = path.join(temp(), 'edits.jsonl'), line = 'x'.repeat(MAX_DELIVERY_LINE_BYTES);
    fs.writeFileSync(file, line + '\n');
    expect(readDeliveryLines(file, 0, recovery ? { discardingOversized: false } : undefined))
      .toMatchObject({ lines: [line], offset: MAX_DELIVERY_LINE_BYTES + 1,
        entries: [{ line, offset: MAX_DELIVERY_LINE_BYTES + 1, discardingOversized: false }] });
  });

  it.skipIf(process.platform === 'win32')('rejects FIFOs without waiting for a writer', () => {
    const root = temp(), file = path.join(root, 'RESEARCH.md');
    expect(spawnSync('mkfifo', [file], { timeout: 1000 }).status).toBe(0);
    expect(() => readDeliveryLines(file, 0)).toThrow('math_delivery_log_invalid');
    expect(() => readMathResponse(root, 'math-result')).toThrow('missing_or_too_large');
  });
});
