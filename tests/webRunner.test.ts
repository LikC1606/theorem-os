import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { describe, expect, it, vi } from 'vitest';
import { readWebConfig, webDefaults } from '../apps/web/config';
import { DockerWebRunner, parseWorkerMessage } from '../apps/web/runner';
import type { WorkerInput, WorkerMessage } from '../apps/web/shared';

describe('Docker web runner', () => {
  it('routes the default sub2api request through private stdin and removes its container', async () => {
    const root = fs.mkdtempSync(path.join(os.tmpdir(), 'theoremos-docker-runner-'));
    fs.writeFileSync(path.join(root, 'docker'), `#!${process.execPath}
const fs = require('node:fs');
const path = require('node:path');
const root = __dirname;
const args = process.argv.slice(2);
fs.appendFileSync(path.join(root, 'calls.jsonl'), JSON.stringify(args) + '\\n');
const container = path.join(root, 'container');
async function main() {
  if (args[0] === 'create') {
    fs.writeFileSync(container, 'created');
  } else if (args[0] === 'start') {
    if (!fs.existsSync(container)) process.exit(1);
    let input = '';
    for await (const chunk of process.stdin) input += chunk;
    const request = JSON.parse(input);
    fs.writeFileSync(path.join(root, 'private-input.json'), input, { mode: 0o600 });
    fs.writeFileSync(path.join(root, 'metadata.json'), JSON.stringify({
      apiKeyInEnvironment: Object.values(process.env).some(value => value.includes(request.input.apiKey)),
    }));
    process.stdout.write(JSON.stringify({ type: 'result', result: {
      status: 'incomplete', proof: '', report: { fixture: true },
    } }) + '\\n');
  } else if (args[0] === 'rm') {
    fs.rmSync(container, { force: true });
  } else process.exit(1);
}
main().catch(() => process.exit(1));
`, { mode: 0o700 });
    // Only this executable can resolve as docker; the fixture uses an absolute Node shebang.
    vi.stubEnv('PATH', root);
    try {
      const config = readWebConfig({});
      const request: WorkerInput = {
        id: 'sub2api-fixture', provider: config.providers[0], input: {
          ...webDefaults, providerId: config.providers[0].id, apiKey: 'sk-private-runner-fixture',
          source: 'theorem example : True := by sorry', task: 'Offline fixture',
        },
      };
      const messages: WorkerMessage[] = [];
      await new DockerWebRunner(config).run(request, message => messages.push(message), new AbortController().signal);

      const calls = fs.readFileSync(path.join(root, 'calls.jsonl'), 'utf8').trim().split('\n')
        .map(line => JSON.parse(line) as string[]);
      expect(calls.map(args => args[0])).toEqual(['create', 'start', 'rm']);
      expect(calls[0]).toContain('--add-host=host.docker.internal:host-gateway');
      const name = `theoremos-web-${request.id}`;
      expect(calls[1]).toEqual(['start', '--attach', '--interactive', name]);
      expect(calls[2]).toEqual(['rm', '--force', '--volumes', name]);
      expect(fs.existsSync(path.join(root, 'container'))).toBe(false);

      const received = JSON.parse(fs.readFileSync(path.join(root, 'private-input.json'), 'utf8'));
      expect(received).toEqual(request);
      expect(received).toMatchObject({
        provider: { id: 'sub2api', baseUrl: 'http://host.docker.internal:8080/v1' },
        input: { model: 'deepseek-flash', effort: 'max' },
      });
      const metadata = JSON.parse(fs.readFileSync(path.join(root, 'metadata.json'), 'utf8'));
      expect(metadata).toEqual({ apiKeyInEnvironment: false });
      expect(messages).toEqual([{ type: 'result', result: {
        status: 'incomplete', proof: '', report: { fixture: true },
      } }]);
      expect(JSON.stringify({ calls, metadata, messages })).not.toContain(request.input.apiKey);
    } finally {
      vi.unstubAllEnvs();
      fs.rmSync(root, { recursive: true, force: true });
    }
  });
});

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
