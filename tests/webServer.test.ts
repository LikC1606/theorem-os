import fs from 'node:fs';
import net from 'node:net';
import os from 'node:os';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { createWebService } from '../apps/web/server';
import { readWebConfig, type WebConfig } from '../apps/web/config';
import { getLeanTaskEnvironment } from '../src/math/leanTaskEnvironment';
import type { WebRunner } from '../apps/web/runner';
import type { WebResult, WebRunInput, WebSession, WorkerInput, WorkerMessage } from '../apps/web/shared';

const key = 'sk-http-test-never-publish';
const input = (): WebRunInput => ({ providerId: 'openai', apiKey: key, model: 'gpt-6.1-sol', effort: 'xhigh',
  source: 'theorem example : True := by sorry', task: 'Prove the theorem', maxTurns: 2,
  maxRunSeconds: 30, workers: 1, coordination: 'cooperative' });
const tick = () => new Promise<void>(resolve => setImmediate(resolve));
type Call = { value: WorkerInput; signal: AbortSignal; send(message: WorkerMessage): void;
  finish(result?: WebResult): void; fail(error: Error): void };
class HttpTestRunner implements WebRunner {
  calls: Call[] = [];
  ready = true;
  async readiness() { return { ready: this.ready, message: this.ready ? 'Test worker ready' : 'Test worker unavailable' }; }
  async run(value: WorkerInput, send: (message: WorkerMessage) => void, signal: AbortSignal) {
    await new Promise<void>((resolve, reject) => {
      this.calls.push({ value, signal, send, fail: reject,
        finish: (result = { status: 'evaluated_passed', proof: 'by trivial', report: { accepted: true } }) => {
          send({ type: 'result', result }); resolve();
        } });
      signal.addEventListener('abort', () => reject(new Error('Aborted test worker')), { once: true });
      if (signal.aborted) reject(new Error('Aborted test worker'));
    });
  }
}

type Client = { cookie: string; csrf: string; session: WebSession };
describe('web HTTP boundary with disposable local servers and no model calls', () => {
  let root: string;
  let config: WebConfig;
  let runner: HttpTestRunner;
  let service: ReturnType<typeof createWebService>;
  let baseUrl: string;

  beforeEach(async () => {
    root = fs.mkdtempSync(path.join(os.tmpdir(), 'theoremos-web-http-'));
    fs.writeFileSync(path.join(root, 'index.html'), '<!doctype html><title>Local workbench</title>');
    // Reserve a local ephemeral port before constructing the service's strict expected origin.
    const reservation = net.createServer();
    await new Promise<void>(resolve => reservation.listen(0, '127.0.0.1', resolve));
    const port = (reservation.address() as net.AddressInfo).port;
    await new Promise<void>((resolve, reject) => reservation.close(error => error ? reject(error) : resolve()));
    baseUrl = `http://127.0.0.1:${port}`;
    config = { ...readWebConfig({ THEOREMOS_WEB_PORT: String(port), THEOREMOS_WEB_PUBLIC_URL: baseUrl }), staticRoot: root };
    runner = new HttpTestRunner();
    service = createWebService(config, runner);
    await new Promise<void>((resolve, reject) => {
      service.server.once('error', reject);
      service.server.listen(port, '127.0.0.1', resolve);
    });
  });
  afterEach(async () => {
    await service?.close();
    fs.rmSync(root, { recursive: true, force: true });
  });

  async function session(): Promise<Client> {
    const response = await fetch(`${baseUrl}/api/session`);
    expect(response.status).toBe(200);
    const body = await response.json() as WebSession;
    const setCookie = response.headers.get('set-cookie')!;
    expect(setCookie).toContain('HttpOnly');
    expect(setCookie).toContain('SameSite=Strict');
    expect(body.csrfToken).toMatch(/^[a-f0-9]{64}$/);
    return { cookie: setCookie.split(';')[0], csrf: body.csrfToken, session: body };
  }
  function request(route: string, client?: Client, options: { method?: string; body?: unknown; headers?: Record<string, string> } = {}) {
    return fetch(`${baseUrl}${route}`, { method: options.method || (options.body === undefined ? 'GET' : 'POST'),
      headers: { ...(client ? { Cookie: client.cookie, 'X-CSRF-Token': client.csrf } : {}),
        ...(options.body === undefined ? {} : { 'Content-Type': 'application/json' }), ...options.headers },
      body: options.body === undefined ? undefined : JSON.stringify(options.body) });
  }
  function rawStatus(route: string, headers: Record<string, string>, body = '', method = body ? 'POST' : 'GET') {
    return new Promise<number>((resolve, reject) => {
      const socket = net.createConnection({ host: '127.0.0.1', port: config.port });
      let response = '';
      socket.setEncoding('latin1');
      socket.setTimeout(5_000, () => socket.destroy(new Error('Local HTTP fixture timed out')));
      socket.on('error', reject);
      socket.on('data', chunk => { response += chunk; });
      socket.on('end', () => {
        const match = /^HTTP\/1\.1 (\d+)/.exec(response);
        if (!match) { reject(new Error('Local HTTP fixture returned no status')); return; }
        resolve(Number(match[1]));
      });
      socket.on('connect', () => {
        const lines = [`${method} ${route} HTTP/1.1`,
          'Connection: close', ...(body ? [`Content-Length: ${Buffer.byteLength(body)}`] : []),
          ...Object.entries({ Host: new URL(baseUrl).host, ...headers }).map(([name, value]) => `${name}: ${value}`), '', body];
        socket.write(Buffer.from(lines.join('\r\n'), 'latin1'));
      });
    });
  }

  it('validates custom module plans and keeps the selected configuration in the run and download', async () => {
    const alice = await session();
    const custom = { id: 'library-strategy', name: 'Library strategy', slot: 'M1', mode: 'replace',
      enabled: true, instructions: 'Search installed lemmas before constructing a longer proof.' };
    const modulePlan = { scheduler: 'critical-path', context: 'essential', custom: [custom,
      { ...custom, id: 'optional-module', enabled: false, mode: 'append', instructions: '' }] };
    for (const invalid of [
      { ...modulePlan, custom: [custom, { ...custom, id: 'conflicting-module' }] },
      { ...modulePlan, custom: [{ ...custom, slot: 'M2' }] },
      { ...modulePlan, custom: [{ ...custom, instructions: '' }] },
      { ...modulePlan, custom: [{ ...custom, instructions: '证'.repeat(1_334) }] },
      { ...modulePlan, custom: [{ ...custom, script: '/untrusted/plugin.ts' }] },
    ]) expect((await request('/api/runs', alice, { body: { ...input(), modulePlan: invalid } })).status).toBe(400);
    expect(runner.calls).toHaveLength(0);
    const created = await request('/api/runs', alice, { body: { ...input(), modulePlan } });
    expect(created.status).toBe(201);
    const run = (await created.json()).run;
    expect(run.modulePlan).toEqual(modulePlan);
    await tick();
    expect(runner.calls[0].value.input.modulePlan).toEqual(modulePlan);
    modulePlan.custom[0].instructions = 'A later client-side edit';
    const current = await request(`/api/runs/${run.id}`, alice);
    expect((await current.json()).run.modulePlan).toEqual(run.modulePlan);
    runner.calls[0].finish(); await tick();
    const downloaded = await request(`/api/runs/${run.id}/download`, alice);
    expect((await downloaded.json()).run.modulePlan).toEqual(run.modulePlan);
  });

  it('requires a session and a matching CSRF token before accepting a run', async () => {
    expect((await request('/api/runs')).status).toBe(401);
    expect((await request('/api/runs', undefined, { body: input() })).status).toBe(401);
    const alice = await session();
    expect(alice.session.providers.map(provider => provider.id)).toEqual(['openai']);
    const refresh = await request('/api/session', alice);
    expect((await refresh.json()).csrfToken).toBe(alice.csrf);
    const missingCsrf = await request('/api/runs', alice, { body: input(), headers: { 'X-CSRF-Token': '' } });
    expect(missingCsrf.status).toBe(403);
    expect(missingCsrf.headers.get('set-cookie')).toBeNull();
    expect((await request('/api/runs', alice, { body: input(), headers: { 'X-CSRF-Token': '0'.repeat(64) } })).status).toBe(403);
    expect(runner.calls).toHaveLength(0);
    const created = await request('/api/runs', alice, { body: input() });
    expect(created.status).toBe(201);
    const run = (await created.json()).run;
    expect(run.id).toMatch(/^[a-f0-9-]{36}$/);
    expect(run.environment).toBe('standard');
    await tick();
    expect(runner.calls).toHaveLength(1);
    expect(runner.calls[0].value.input.apiKey).toBe(key);
    expect(runner.calls[0].value.input.environment).toBe('standard');
    runner.calls[0].finish();
  });

  it('renews the same browser cookie during polling without changing ownership or CSRF, then expires after inactivity', async () => {
    config.sessionTtlMs = 60_000;
    let now = Date.now();
    const clock = vi.spyOn(Date, 'now').mockImplementation(() => now);
    try {
      const alice = await session();
      const { run } = await (await request('/api/runs', alice, { body: input() })).json();
      await tick();
      runner.calls[0].finish();
      await tick();
      for (let poll = 0; poll < 2; poll++) {
        now += 45_000;
        const response = await request('/api/runs', alice);
        expect(response.status).toBe(200);
        expect((await response.json()).runs.map((run: { id: string }) => run.id)).toEqual([run.id]);
        const cookie = response.headers.get('set-cookie')!;
        expect(cookie.split(';')[0]).toBe(alice.cookie);
        expect(cookie).toContain('Path=/; HttpOnly; SameSite=Strict; Max-Age=60');
      }
      const refreshed = await request('/api/session', alice);
      expect((await refreshed.json()).csrfToken).toBe(alice.csrf);
      expect(refreshed.headers.get('set-cookie')!.split(';')[0]).toBe(alice.cookie);
      const cancelled = await request(`/api/runs/${run.id}/cancel`, alice, { method: 'POST' });
      expect(cancelled.status).toBe(200);
      expect(cancelled.headers.get('set-cookie')!.split(';')[0]).toBe(alice.cookie);

      now += 60_001;
      const expired = await request('/api/runs', alice);
      expect(expired.status).toBe(401);
      expect(expired.headers.get('set-cookie')).toBeNull();
      expect((await request(`/api/runs/${run.id}`, alice)).status).toBe(401);
      const renewed = await request('/api/session', alice);
      const renewedCookie = renewed.headers.get('set-cookie')!.split(';')[0];
      expect(renewedCookie).not.toBe(alice.cookie);
      const renewedBody = await renewed.json() as WebSession;
      expect(renewedBody.csrfToken).not.toBe(alice.csrf);
      const fresh = { cookie: renewedCookie, csrf: renewedBody.csrfToken, session: renewedBody };
      expect((await request(`/api/runs/${run.id}`, fresh)).status).toBe(404);
    } finally { clock.mockRestore(); }
  });

  it('advertises pinned trusted environments and defaults the web form to Mathlib', async () => {
    const alice = await session();
    expect(alice.session.defaults.environment).toBe('mathlib');
    expect(alice.session.environments.map(environment => environment.id)).toEqual(['standard', 'mathlib']);
    for (const environment of alice.session.environments) {
      const trusted = getLeanTaskEnvironment(environment.id);
      expect(environment.toolchain).toBe(trusted.toolchain);
      expect(environment.mathlibRevision).toBe(trusted.mathlibRevision);
      expect(environment).not.toHaveProperty('files');
      expect(environment).not.toHaveProperty('dependencyDigest');
    }
    const template = alice.session.templates.find(template => template.id === 'polynomial');
    expect(template?.environment).toBe('mathlib');
    expect(template?.source).toContain('import Mathlib');
    expect(alice.session.templates.every(template => ['standard', 'mathlib'].includes(template.environment))).toBe(true);
    const created = await request('/api/runs', alice, { body: { ...input(), environment: 'mathlib', source: template!.source } });
    expect(created.status).toBe(201);
    const { run } = await created.json();
    expect(run.environment).toBe('mathlib');
    await tick();
    expect(runner.calls[0].value.input.environment).toBe('mathlib');
    expect(runner.calls[0].value.input.source).toBe(template!.source.trim());
    runner.calls[0].finish();
    await tick();
    for (const route of ['/api/runs', `/api/runs/${run.id}`, `/api/runs/${run.id}/download`]) {
      const response = await request(route, alice);
      expect(response.status).toBe(200);
      const body = await response.json();
      expect((body.run || body.runs[0]).environment).toBe('mathlib');
    }
  });

  it('rejects foreign origins and host headers before exposing a session or executing work', async () => {
    expect((await request('/api/session', undefined, { headers: { Origin: 'https://other.example' } })).status).toBe(403);
    const alice = await session();
    for (const route of ['/api/session', '/api/runs']) {
      const foreign = await request(route, alice, { headers: { Origin: 'null' } });
      expect(foreign.status).toBe(403);
      expect(foreign.headers.get('set-cookie')).toBeNull();
    }
    expect((await request('/api/runs', alice, { body: input(), headers: { Origin: 'https://other.example' } })).status).toBe(403);
    expect(await rawStatus('/api/session', { Host: 'attacker.example' })).toBe(403);
    expect(runner.calls).toHaveLength(0);
  });

  it('rejects malformed non-ASCII CSRF tokens with a denial instead of a server error', async () => {
    const alice = await session();
    // Node's HTTP API can send Latin-1 headers, which differ in byte length after UTF-8 encoding.
    const status = await rawStatus('/api/runs', {
      Cookie: alice.cookie, 'X-CSRF-Token': `é${alice.csrf.slice(1)}`, 'Content-Type': 'application/json',
    }, JSON.stringify(input()));
    expect(status).toBe(403);
    expect(runner.calls).toHaveLength(0);
  });

  it('rejects arbitrary providers, unrecognized fields and inputs exceeding every enforced budget', async () => {
    const alice = await session();
    const invalid = [
      { providerId: 'unconfigured' }, { baseUrl: 'https://attacker.example/v1' }, { extra: true },
      { maxTurns: 21 }, { maxTurns: 0 }, { maxRunSeconds: 901 }, { maxRunSeconds: 29 }, { workers: 5 },
      { workers: 0 }, { maxTurns: 1.5 }, { source: '数'.repeat(11_000) }, { task: '数'.repeat(2_800) },
      { effort: 'unlimited' }, { coordination: 'unknown' }, { model: '--model-flag' }, { apiKey: 'short' },
      { environment: 'custom' }, { environment: 'https://attacker.example/mathlib' }, { environment: null },
      { environment: { id: 'mathlib', url: 'https://attacker.example' } }, { mathlibRevision: 'attacker-revision' },
    ];
    for (const override of invalid) {
      const response = await request('/api/runs', alice, { body: { ...input(), ...override } });
      expect(response.status, JSON.stringify(override)).toBe(400);
      expect(await response.text()).not.toContain(key);
    }
    expect(runner.calls).toHaveLength(0);
    const atLimits = await request('/api/runs', alice, { body: { ...input(), maxTurns: 20, maxRunSeconds: 900, workers: 4 } });
    expect(atLimits.status).toBe(201);
  });

  it('rejects wrong content types, invalid JSON and oversized bodies without echoing credentials', async () => {
    const alice = await session();
    const headers = { Cookie: alice.cookie, 'X-CSRF-Token': alice.csrf };
    const wrongType = await fetch(`${baseUrl}/api/runs`, { method: 'POST', headers, body: JSON.stringify(input()) });
    expect(wrongType.status).toBe(415);
    const broken = await fetch(`${baseUrl}/api/runs`, { method: 'POST', headers: { ...headers, 'Content-Type': 'application/json' }, body: `{"apiKey":"${key}",` });
    expect(broken.status).toBe(400);
    expect(await broken.text()).not.toContain(key);
    const large = await request('/api/runs', alice, { body: { ...input(), source: 'x'.repeat(170 * 1024) } });
    expect(large.status).toBe(413);
    expect(await large.text()).not.toContain(key);
    expect(runner.calls).toHaveLength(0);
  });

  it('isolates two sessions across listing, lookup, cancellation and result downloads', async () => {
    const alice = await session();
    const bob = await session();
    expect(alice.cookie).not.toBe(bob.cookie);
    expect(alice.csrf).not.toBe(bob.csrf);
    const created = await request('/api/runs', alice, { body: { ...input(), task: `Test ${key}`, source: `-- ${key}\ntheorem example : True := by sorry` } });
    expect(created.status).toBe(201);
    const createdText = await created.text();
    expect(createdText).not.toContain(key);
    const run = JSON.parse(createdText).run;
    expect((await (await request('/api/runs', bob)).json()).runs).toEqual([]);
    expect((await request(`/api/runs/${run.id}`, bob)).status).toBe(404);
    expect((await request(`/api/runs/${run.id}/download`, bob)).status).toBe(404);
    expect((await request(`/api/runs/${run.id}/cancel`, bob, { method: 'POST' })).status).toBe(404);
    expect((await request(`/api/runs/${run.id}/download`, alice)).status).toBe(409);
    await tick();
    expect(runner.calls[0].signal.aborted).toBe(false);
    runner.calls[0].send({ type: 'progress', event: 'provider', message: `Provider diagnostics: ${key}` });
    runner.calls[0].finish({ status: 'evaluated_passed', proof: `-- ${key}\nby trivial`,
      report: { message: `Validated ${key}`, nested: { credential: key } } });
    await tick();
    for (const route of ['/api/runs', `/api/runs/${run.id}`, `/api/runs/${run.id}/download`]) {
      const response = await request(route, alice);
      expect(response.status).toBe(200);
      const text = await response.text();
      expect(text).not.toContain(key);
      expect(text).toContain('[REDACTED]');
      const data = JSON.parse(text);
      const visible = data.run || data.runs[0];
      expect(visible).not.toHaveProperty('apiKey');
      expect(visible.status).toBe('completed');
      if (route.endsWith('/download')) {
        expect(response.headers.get('content-disposition')).toContain(`theoremos-${run.id}.json`);
        expect(data.schema).toBe('theorem-os.web-export.v1');
      }
    }
    expect((await request(`/api/runs/${run.id}/download`, bob)).status).toBe(404);
    expect(runner.calls[0].value.input.apiKey).toBe('');
  });

  it('redacts provider failures and exports their archive without inventing a result', async () => {
    const alice = await session();
    const response = await request('/api/runs', alice, { body: input() });
    const { run } = await response.json();
    await tick();
    runner.calls[0].fail(new Error(`Provider refused key ${key}`));
    await tick();
    const failed = await request(`/api/runs/${run.id}`, alice);
    const text = await failed.text();
    expect(text).not.toContain(key);
    const data = JSON.parse(text);
    expect(data.run.status).toBe('error');
    expect(data.run.error).toContain('[REDACTED]');
    const download = await request(`/api/runs/${run.id}/download`, alice);
    expect(download.status).toBe(200);
    expect(await download.json()).toEqual({ schema: 'theorem-os.web-export.v1', run: data.run });
    expect(data.run).not.toHaveProperty('result');
    expect(await (await request('/api/runs', alice)).text()).not.toContain(key);
    expect(runner.calls[0].value.input.apiKey).toBe('');
  });

  it.each(['completed', 'cancelled', 'error'] as const)('exports a private complete %s archive, including submitted text and diagnostics', async status => {
    const alice = await session();
    const bob = await session();
    const submitted = { ...input(), source: `-- Keep source ${key}\ntheorem example : True := by sorry`, task: `Keep task ${key}` };
    const { run } = await (await request('/api/runs', alice, { body: submitted })).json();
    await tick();
    runner.calls[0].send({ type: 'progress', event: 'worker_activity', message: `Diagnostic ${key}` });
    if (status === 'completed') runner.calls[0].finish();
    else if (status === 'error') runner.calls[0].fail(new Error(`Provider failed ${key}`));
    else expect((await request(`/api/runs/${run.id}/cancel`, alice, { method: 'POST' })).status).toBe(200);
    await tick();
    const route = `/api/runs/${run.id}/download`;
    expect((await request(route)).status).toBe(401);
    expect((await request(route, bob)).status).toBe(404);
    const response = await request(route, alice);
    expect(response.status).toBe(200);
    expect(response.headers.get('content-disposition')).toContain(`theoremos-${run.id}.json`);
    const text = await response.text();
    expect(text).not.toContain(key);
    const archive = JSON.parse(text);
    expect(archive.schema).toBe('theorem-os.web-export.v1');
    expect(archive.run).toEqual((await (await request(`/api/runs/${run.id}`, alice)).json()).run);
    expect(archive.run.status).toBe(status);
    expect(archive.run.source).toBe(submitted.source.replaceAll(key, '[REDACTED]'));
    expect(archive.run.task).toBe(submitted.task.replaceAll(key, '[REDACTED]'));
    expect(archive.run).not.toHaveProperty('apiKey');
    expect(archive.run.events.some((event: { message: string }) => event.message === 'Diagnostic [REDACTED]')).toBe(true);
    if (status !== 'completed') expect(archive.run).not.toHaveProperty('result');
    if (status === 'error') expect(archive.run.error).toBe('Provider failed [REDACTED]');
    expect(runner.calls[0].value.input.apiKey).toBe('');
  });

  it('rejects unfinished archives without a result but still exports a result received by a running worker', async () => {
    const alice = await session();
    const first = (await (await request('/api/runs', alice, { body: input() })).json()).run;
    const second = (await (await request('/api/runs', alice, { body: input() })).json()).run;
    await tick();
    expect((await (await request(`/api/runs/${first.id}`, alice)).json()).run.status).toBe('running');
    expect((await (await request(`/api/runs/${second.id}`, alice)).json()).run.status).toBe('queued');
    for (const run of [first, second]) {
      const unfinished = await request(`/api/runs/${run.id}/download`, alice);
      expect(unfinished.status).toBe(409);
      expect(await unfinished.text()).not.toContain(key);
    }
    const result: WebResult = { status: 'evaluated_passed', proof: 'by trivial', report: { accepted: true } };
    runner.calls[0].send({ type: 'result', result });
    const received = await request(`/api/runs/${first.id}/download`, alice);
    expect(received.status).toBe(200);
    const archive = await received.json();
    expect(archive.schema).toBe('theorem-os.web-export.v1');
    expect(archive.run.status).toBe('running');
    expect(archive.run.result).toEqual(result);
    expect(runner.calls[0].signal.aborted).toBe(false);
    runner.calls[0].finish();
    await tick();
    expect(runner.calls[1].value.id).toBe(second.id);
    runner.calls[1].finish();
  });

  it('requires the owning session, CSRF token, expected origin and host before deleting history', async () => {
    const alice = await session();
    const bob = await session();
    const { run } = await (await request('/api/runs', alice, { body: input() })).json();
    await tick();
    runner.calls[0].finish();
    await tick();
    const route = `/api/runs/${run.id}`;
    expect((await request(route, undefined, { method: 'DELETE' })).status).toBe(401);
    for (const token of ['', '0'.repeat(64), bob.csrf]) {
      const denied = await request(route, alice, { method: 'DELETE', headers: { 'X-CSRF-Token': token } });
      expect(denied.status).toBe(403);
      expect(denied.headers.get('set-cookie')).toBeNull();
    }
    const foreign = await request(route, alice, { method: 'DELETE', headers: { Origin: 'https://other.example' } });
    expect(foreign.status).toBe(403);
    expect(foreign.headers.get('set-cookie')).toBeNull();
    expect(await rawStatus(route, { Host: 'attacker.example', Cookie: alice.cookie, 'X-CSRF-Token': alice.csrf }, '', 'DELETE')).toBe(403);
    expect((await request(route, bob, { method: 'DELETE' })).status).toBe(404);
    expect((await request('/api/runs/00000000-0000-0000-0000-000000000000', alice, { method: 'DELETE' })).status).toBe(404);
    expect((await (await request(route, alice)).json()).run.status).toBe('completed');
    expect((await (await request('/api/runs', alice)).json()).runs.map((item: { id: string }) => item.id)).toEqual([run.id]);
    const deleted = await request(route, alice, { method: 'DELETE', headers: { Origin: baseUrl } });
    expect(deleted.status).toBe(200);
    expect(await deleted.json()).toEqual({ deletedId: run.id });
  });

  it('refuses to delete queued and running jobs without aborting them or disturbing other work', async () => {
    const alice = await session();
    const first = (await (await request('/api/runs', alice, { body: input() })).json()).run;
    const second = (await (await request('/api/runs', alice, { body: input() })).json()).run;
    await tick();
    for (const run of [first, second]) {
      const denied = await request(`/api/runs/${run.id}`, alice, { method: 'DELETE' });
      expect(denied.status).toBe(409);
      expect(await denied.text()).not.toContain(key);
    }
    expect((await (await request(`/api/runs/${first.id}`, alice)).json()).run.status).toBe('running');
    expect((await (await request(`/api/runs/${second.id}`, alice)).json()).run.status).toBe('queued');
    expect(runner.calls).toHaveLength(1);
    expect(runner.calls[0].signal.aborted).toBe(false);
    expect(runner.calls[0].value.input.apiKey).toBe(key);
    runner.calls[0].finish();
    await tick();
    expect(runner.calls[1].value.id).toBe(second.id);
    expect((await request(`/api/runs/${first.id}`, alice, { method: 'DELETE' })).status).toBe(200);
    expect(runner.calls[1].signal.aborted).toBe(false);
    expect(runner.calls[1].value.input.apiKey).toBe(key);
    runner.calls[1].finish();
    await tick();
    const remaining = (await (await request('/api/runs', alice)).json()).runs;
    expect(remaining.map((run: { id: string }) => run.id)).toEqual([second.id]);
    expect(remaining[0].status).toBe('completed');
    expect(runner.calls[1].value.input.apiKey).toBe('');
  });

  it.each(['completed', 'cancelled', 'error'] as const)('deletes a %s record once and removes access through every run endpoint', async status => {
    const alice = await session();
    const { run } = await (await request('/api/runs', alice, { body: input() })).json();
    await tick();
    if (status === 'completed') runner.calls[0].finish();
    else if (status === 'error') runner.calls[0].fail(new Error('Test worker failed'));
    else expect((await request(`/api/runs/${run.id}/cancel`, alice, { method: 'POST' })).status).toBe(200);
    await tick();
    expect((await (await request(`/api/runs/${run.id}`, alice)).json()).run.status).toBe(status);
    const response = await request(`/api/runs/${run.id}`, alice, { method: 'DELETE' });
    expect(response.status).toBe(200);
    expect(await response.json()).toEqual({ deletedId: run.id });
    expect(response.headers.get('set-cookie')!.split(';')[0]).toBe(alice.cookie);
    expect((await request(`/api/runs/${run.id}`, alice, { method: 'DELETE' })).status).toBe(404);
    expect((await request(`/api/runs/${run.id}`, alice)).status).toBe(404);
    expect((await request(`/api/runs/${run.id}/download`, alice)).status).toBe(404);
    expect((await request(`/api/runs/${run.id}/cancel`, alice, { method: 'POST' })).status).toBe(404);
    expect((await (await request('/api/runs', alice)).json()).runs).toEqual([]);
    expect(runner.calls[0].value.input.apiKey).toBe('');
  });

  it('accepts a new run after deleting finished history at the 20-record limit without changing another session', async () => {
    const alice = await session();
    const history: string[] = [];
    for (let index = 0; index < 20; index++) {
      const created = await request('/api/runs', alice, { body: { ...input(), task: `History ${index}` } });
      expect(created.status).toBe(201);
      history.push((await created.json()).run.id);
      await tick();
      runner.calls[index].finish();
      await tick();
    }
    const full = await request('/api/runs', alice, { body: input() });
    expect(full.status).toBe(429);
    expect((await full.json()).error).toMatch(/20.*删除已结束.*重试/);
    const bob = await session();
    const other = (await (await request('/api/runs', bob, { body: input() })).json()).run;
    await tick();
    const deleted = await request(`/api/runs/${history[0]}`, alice, { method: 'DELETE' });
    expect(deleted.status).toBe(200);
    expect(await deleted.json()).toEqual({ deletedId: history[0] });
    const created = await request('/api/runs', alice, { body: input() });
    expect(created.status).toBe(201);
    const next = (await created.json()).run;
    expect(next.status).toBe('queued');
    const remaining = (await (await request('/api/runs', alice)).json()).runs;
    expect(remaining).toHaveLength(20);
    expect(remaining.map((run: { id: string }) => run.id)).not.toContain(history[0]);
    expect((await (await request('/api/runs', bob)).json()).runs.map((run: { id: string }) => run.id)).toEqual([other.id]);
    expect(runner.calls[20].signal.aborted).toBe(false);
    expect(runner.calls[20].value.input.apiKey).toBe(key);
    runner.calls[20].finish();
    await tick();
    expect(runner.calls[21].value.id).toBe(next.id);
    runner.calls[21].finish();
    await tick();
    expect((await (await request(`/api/runs/${next.id}`, alice)).json()).run.status).toBe('completed');
    expect(runner.calls.every(call => call.value.input.apiKey === '')).toBe(true);
  });

  it('reports worker unreadiness and refuses a new run', async () => {
    runner.ready = false;
    const alice = await session();
    expect(alice.session.runtime.ready).toBe(false);
    expect((await request('/api/runs', alice, { body: input() })).status).toBe(503);
    expect(runner.calls).toHaveLength(0);
  });

  it('exposes queue pressure and lets owners cancel both queued and active runs', async () => {
    config.queueLimit = 2;
    const alice = await session();
    const first = (await (await request('/api/runs', alice, { body: input() })).json()).run;
    const second = (await (await request('/api/runs', alice, { body: input() })).json()).run;
    expect(second.status).toBe('queued');
    expect((await request('/api/runs', alice, { body: input() })).status).toBe(429);
    expect((await (await request(`/api/runs/${second.id}/cancel`, alice, { method: 'POST' })).json()).run.status).toBe('cancelled');
    expect((await (await request(`/api/runs/${first.id}/cancel`, alice, { method: 'POST' })).json()).run.status).toBe('cancelled');
    await tick();
    expect(runner.calls).toHaveLength(1);
    expect(runner.calls[0].signal.aborted).toBe(true);
    expect(runner.calls[0].value.input.apiKey).toBe('');
  });

  it('expires sessions, cancels their work and gives a refreshed visitor a new identity', async () => {
    config.sessionTtlMs = 50;
    const alice = await session();
    const { run } = await (await request('/api/runs', alice, { body: input() })).json();
    await new Promise(resolve => setTimeout(resolve, 80));
    expect((await request('/api/runs', alice)).status).toBe(401);
    await tick();
    expect(runner.calls[0].signal.aborted).toBe(true);
    expect(runner.calls[0].value.input.apiKey).toBe('');
    const renewed = await session();
    expect(renewed.cookie).not.toBe(alice.cookie);
    expect((await request(`/api/runs/${run.id}`, renewed)).status).toBe(404);
  });

  it('serves only files within the static root and sends browser security headers', async () => {
    const home = await request('/');
    expect(home.status).toBe(200);
    expect(home.headers.get('cache-control')).toBe('no-store');
    expect(home.headers.get('x-content-type-options')).toBe('nosniff');
    expect(home.headers.get('x-frame-options')).toBe('DENY');
    expect(home.headers.get('content-security-policy')).toContain("connect-src 'self'");
    expect(await home.text()).toContain('Local workbench');
    const head = await request('/', undefined, { method: 'HEAD' });
    expect(head.status).toBe(200);
    expect(await head.text()).toBe('');
    expect((await request('/%2e%2e%2fpackage.json')).status).toBe(404);
    const outside = fs.mkdtempSync(path.join(os.tmpdir(), 'theoremos-web-outside-'));
    try {
      fs.writeFileSync(path.join(outside, 'secret.txt'), 'PRIVATE-OUTSIDE-STATIC-ROOT');
      fs.symlinkSync(path.join(outside, 'secret.txt'), path.join(root, 'direct.txt'));
      fs.symlinkSync(outside, path.join(root, 'linked'), 'dir');
      expect((await request('/direct.txt')).status).toBe(404);
      const escaped = await request('/linked/secret.txt');
      expect(escaped.status).toBe(404);
      expect(await escaped.text()).not.toContain('PRIVATE-OUTSIDE-STATIC-ROOT');
    } finally { fs.rmSync(outside, { recursive: true, force: true }); }
  });
});
