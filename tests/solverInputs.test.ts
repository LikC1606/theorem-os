import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import { afterEach, describe, expect, it } from 'vitest';
import { readDeliveryLines, readMathResponse } from '../src/solver/deliveries';
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

  it.skipIf(process.platform === 'win32')('rejects FIFOs without waiting for a writer', () => {
    const root = temp(), file = path.join(root, 'RESEARCH.md');
    expect(spawnSync('mkfifo', [file], { timeout: 1000 }).status).toBe(0);
    expect(() => readDeliveryLines(file, 0)).toThrow('math_delivery_log_invalid');
    expect(() => readMathResponse(root, 'math-result')).toThrow('missing_or_too_large');
  });
});
