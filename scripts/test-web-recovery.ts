#!/usr/bin/env bun
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { chromium, type BrowserContext, type Page, type Route } from 'playwright';
import { readWebConfig } from '../apps/web/config';
import { createWebService } from '../apps/web/server';
import type { WebRunner } from '../apps/web/runner';
import type { WebResult, WebRun } from '../apps/web/shared';
import { fillConfig, refreshHistory, withSettings } from './web-ui-controls';
import { deferred, freePort, ready, type RequestRecord, type ScenarioSuite, startBrowser, webScenario, writeScenarioReport } from './web-scenario';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const output = path.join(root, 'out/web-ui-smoke');
const reportFile = path.join(output, 'recovery-report.json');
await fs.access(path.join(root, 'out/web/app.js')).catch(() => { throw new Error('Run bun run build:web before the recovery check.'); });
await fs.mkdir(output, { recursive: true });
await fs.rm(reportFile, { force: true });
const port = await freePort();
const origin = `http://127.0.0.1:${port}`;
const credential = `sk-theoremos-recovery-fixture-${crypto.randomUUID()}`;
const controls = new Map<string, (result: WebResult) => void>();
const workerStarts: string[] = [];
const runner: WebRunner = {
  async readiness() { return { ready: true, message: 'Local recovery fixture' }; },
  async run(input, send, signal) {
    workerStarts.push(input.id);
    await new Promise<void>((resolve, reject) => {
      const abort = () => { controls.delete(input.id); reject(new Error('Cancelled fixture')); };
      signal.addEventListener('abort', abort, { once: true });
      controls.set(input.id, result => {
        signal.removeEventListener('abort', abort);
        controls.delete(input.id);
        send({ type: 'result', result });
        resolve();
      });
      if (signal.aborted) abort();
    });
  },
};
const service = createWebService(readWebConfig({ THEOREMOS_WEB_PORT: String(port), THEOREMOS_WEB_PUBLIC_URL: origin,
  THEOREMOS_WEB_STATIC_ROOT: path.join(root, 'out/web'), THEOREMOS_WEB_CONCURRENCY: '4' }), runner);
type Harness = {
  page: Page;
  context: BrowserContext;
  requests: RequestRecord[];
  intercept?: (route: Route) => Promise<boolean>;
  releases: Array<() => void>;
};
type Check = { name: string; elapsedMs: number; requests: RequestRecord[] };
const checks: Check[] = [];
let browser: Awaited<ReturnType<typeof chromium.launch>> | undefined;
const suite: ScenarioSuite = { origin, output, checks, failedScenario: '' };
let timeoutElapsedMs: number | undefined;
const isList = (route: Route) => route.request().method() === 'GET' && new URL(route.request().url()).pathname === '/api/runs';
const isSession = (route: Route) => new URL(route.request().url()).pathname === '/api/session';
const isSubmit = (route: Route) => route.request().method() === 'POST' && new URL(route.request().url()).pathname === '/api/runs';
const count = (h: Harness, method: string, pathname: string) => h.requests.filter(item => item.method === method && item.pathname === pathname).length;
async function disconnected(page: Page) {
  await page.locator('#submit-run:disabled').waitFor();
  await page.locator('#global-notice').waitFor({ state: 'visible' });
  assert.equal(await page.locator('#source').isEnabled(), true, 'source must remain editable while disconnected');
  assert.equal(await page.locator('#task').isEnabled(), true, 'task must remain editable while disconnected');
}
async function open(h: Harness) { await h.page.goto(origin); await ready(h.page); }
const scenario = (name: string, run: (h: Harness) => Promise<void>) => webScenario<Harness>(browser!, suite, name, run, {
  context: { viewport: { width: 1440, height: 900 } }, harness: (page, context) => ({ page, context, requests: [], releases: [] }),
  routes: 'api', timeout: { label: 'Recovery', seconds: 35 }, failure: { prefix: 'recovery-', fullPage: true },
  cleanup: ({ releases }) => { for (const release of releases) release(); },
});
async function draft(page: Page) {
  const values = { source: 'theorem recovery_draft : True := by\n  trivial\n', task: 'Recovery draft\nKeep this exact task.', model: 'fixture-recovery-model', 'max-turns': '3', 'max-seconds': '90', workers: '2' };
  await withSettings(page, async () => {
    for (const [id, value] of Object.entries(values)) if (id !== 'task') await page.locator(`#${id}`).fill(value);
  });
  await page.locator('#task').fill(values.task);
  return values;
}
async function assertDraft(page: Page, values: Record<string, string>) {
  for (const [id, value] of Object.entries(values)) assert.equal(await page.locator(`#${id}`).inputValue(), value, `draft field ${id} changed`);
}
async function post(page: Page): Promise<WebRun> {
  await fillConfig(page, 'api-key', credential);
  const response = page.waitForResponse(response => new URL(response.url()).pathname === '/api/runs' && response.request().method() === 'POST');
  await page.locator('#submit-run').click();
  const result = await response;
  assert.equal(result.status(), 201);
  const { run } = await result.json() as { run: WebRun };
  await page.locator(`[data-run-id="${run.id}"]`).waitFor({ state: 'attached' });
  await page.locator('#detail-tab-overview').click();
  return run;
}
async function transition(page: Page, type: 'pagehide' | 'pageshow') {
  await page.evaluate(type => window.dispatchEvent(new PageTransitionEvent(type, { persisted: true })), type);
}
const writeReport = (status: 'passed' | 'failed', error?: unknown) => writeScenarioReport(reportFile, suite, status, error,
  'Real HTTP service and Chromium with controlled response failures and an in-process worker fixture. No Docker, Lean or model provider is called.',
  { checks, workerStarts: workerStarts.length, timeoutElapsedMs });
try {
  browser = await startBrowser(service.server, port);

  await scenario('Offline polling disables submission, keeps drafts editable, and online restores the draft', async h => {
    await open(h);
    const values = await draft(h.page);
    await h.context.setOffline(true);
    await refreshHistory(h.page);
    await disconnected(h.page);
    await assertDraft(h.page, values);
    values.task += '\nEdited while offline.';
    await h.page.locator('#task').fill(values.task);
    await h.context.setOffline(false);
    await h.page.evaluate(() => window.dispatchEvent(new Event('online')));
    await ready(h.page);
    await h.page.locator('#global-notice').waitFor({ state: 'hidden' });
    await assertDraft(h.page, values);
    assert.equal(count(h, 'POST', '/api/runs'), 0);
  });

  await scenario('A 401 recovers with GET requests only and keeps the existing draft', async h => {
    await open(h);
    const values = await draft(h.page);
    const sessionGate = deferred(), sessionSeen = deferred();
    h.releases.push(sessionGate.resolve);
    let expire = true;
    h.intercept = async route => {
      if (isList(route) && expire) {
        expire = false;
        await route.fulfill({ status: 401, json: { error: 'Expired fixture session' } });
        return true;
      }
      if (isSession(route)) { sessionSeen.resolve(); await sessionGate.promise; }
      return false;
    };
    await refreshHistory(h.page);
    await sessionSeen.promise;
    await disconnected(h.page);
    sessionGate.resolve();
    await ready(h.page);
    await assertDraft(h.page, values);
    assert.equal(count(h, 'GET', '/api/session'), 2);
    assert.equal(count(h, 'POST', '/api/runs'), 0);
  });

  await scenario('A session response alone cannot enable submission; recovery is single-flight until list success', async h => {
    let listFails = true;
    const sessionGate = deferred(), sessionSeen = deferred(), listGate = deferred(), listSeen = deferred();
    h.releases.push(sessionGate.resolve, listGate.resolve);
    let holdRecovery = false;
    h.intercept = async route => {
      if (isSession(route) && holdRecovery) { sessionSeen.resolve(); await sessionGate.promise; }
      if (isList(route)) {
        if (listFails) { await route.fulfill({ status: 500, json: { error: 'List unavailable fixture' } }); return true; }
        listSeen.resolve(); await listGate.promise;
      }
      return false;
    };
    await h.page.goto(origin);
    await disconnected(h.page);
    const values = await draft(h.page);
    listFails = false; holdRecovery = true;
    await h.page.locator('#retry-connection').click();
    await sessionSeen.promise;
    await h.page.evaluate(() => {
      window.dispatchEvent(new Event('online'));
      window.dispatchEvent(new PageTransitionEvent('pageshow', { persisted: true }));
      window.dispatchEvent(new Event('online'));
    });
    await h.page.waitForTimeout(250);
    assert.equal(count(h, 'GET', '/api/session'), 2, 'concurrent recovery triggers must share one session request');
    sessionGate.resolve();
    await listSeen.promise;
    await disconnected(h.page);
    listGate.resolve();
    await ready(h.page);
    await h.page.waitForTimeout(250);
    assert.equal(count(h, 'GET', '/api/session'), 2, 'completed recovery must not trigger another queued session request');
    await assertDraft(h.page, values);
  });

  await scenario('CSRF 403 refreshes the session without replaying the rejected POST', async h => {
    await open(h);
    const values = await draft(h.page);
    let rejectPost = true;
    h.intercept = async route => {
      if (isSubmit(route) && rejectPost) {
        rejectPost = false;
        await route.continue({ headers: { ...route.request().headers(), 'x-csrf-token': 'invalid-fixture-token' } });
        return true;
      }
      return false;
    };
    await fillConfig(h.page, 'api-key', credential);
    await h.page.locator('#submit-run').click();
    await h.page.waitForFunction(() => !(document.querySelector('#form-error') as HTMLElement).hidden);
    await h.page.waitForFunction(() => !(document.querySelector('#submit-run') as HTMLButtonElement).disabled);
    assert.ok(count(h, 'GET', '/api/session') >= 2, 'CSRF failure must refresh the session');
    await h.page.waitForTimeout(5600);
    assert.equal(count(h, 'POST', '/api/runs'), 1);
    assert.equal(await h.page.locator('[data-run-id]').count(), 0);
    await assertDraft(h.page, values);
  });

  await scenario('An accepted POST with a lost response is reconciled by GET without a duplicate worker', async h => {
    await open(h);
    const values = await draft(h.page);
    const accepted = deferred();
    let acceptedRun: WebRun | undefined;
    const startsBefore = workerStarts.length;
    h.intercept = async route => {
      if (!isSubmit(route)) return false;
      if (acceptedRun) {
        await route.fulfill({ status: 500, json: { error: 'Unexpected duplicate submission fixture' } });
      } else {
        const response = await route.fetch();
        assert.equal(response.status(), 201);
        acceptedRun = (await response.json() as { run: WebRun }).run;
        accepted.resolve();
        await route.abort('failed');
      }
      return true;
    };
    await fillConfig(h.page, 'api-key', credential);
    await h.page.locator('#submit-run').click();
    await accepted.promise;
    await h.page.locator('#form-error').waitFor({ state: 'visible' });
    await h.page.locator(`[data-run-id="${acceptedRun!.id}"]`).waitFor({ state: 'attached' });
    await ready(h.page);
    await h.page.waitForTimeout(5600);
    assert.equal(count(h, 'POST', '/api/runs'), 1);
    assert.equal(workerStarts.length - startsBefore, 1);
    await assertDraft(h.page, values);
    controls.get(acceptedRun!.id)!({ status: 'incomplete', proof: acceptedRun!.source, report: { fixture: true } });
  });

  await scenario('Full list responses update selected run results while the detail endpoint is unavailable', async h => {
    await open(h);
    let detailRequests = 0;
    h.intercept = async route => {
      if (route.request().method() === 'GET' && /^\/api\/runs\/[^/]+$/.test(new URL(route.request().url()).pathname)) {
        detailRequests++;
        await route.fulfill({ status: 500, json: { error: 'Detail unavailable fixture' } });
        return true;
      }
      return false;
    };
    const run = await post(h.page);
    const before = detailRequests;
    controls.get(run.id)!({ status: 'evaluated_passed', proof: run.source.replace('by sorry', 'by ring'), report: { fixture: true } });
    await refreshHistory(h.page);
    await h.page.locator('.result-banner.passed').waitFor();
    assert.equal(detailRequests, before, 'polling must not depend on an additional detail GET');
    assert.equal(await h.page.locator('.run-row.selected .badge.passed').count(), 1);
  });

  await scenario('A poll settling after pagehide cannot restart the stopped polling timer', async h => {
    await open(h);
    const held = deferred(), release = deferred(), settled = deferred();
    h.releases.push(release.resolve);
    let hold = true;
    h.intercept = async route => {
      if (!isList(route) || !hold) return false;
      hold = false;
      const response = await route.fetch();
      held.resolve(); await release.promise;
      await route.fulfill({ response }).catch(() => {});
      settled.resolve();
      return true;
    };
    await held.promise;
    await transition(h.page, 'pagehide');
    const listCount = count(h, 'GET', '/api/runs');
    release.resolve(); await settled.promise;
    await h.page.waitForTimeout(5600);
    assert.equal(count(h, 'GET', '/api/runs'), listCount, 'late completion restarted polling after pagehide');
    const restoredList = h.page.waitForResponse(response => new URL(response.url()).pathname === '/api/runs' && response.status() === 200);
    await transition(h.page, 'pageshow');
    await restoredList;
    await h.page.waitForFunction(() => !(document.querySelector('#submit-run') as HTMLButtonElement).disabled);
    await h.page.waitForTimeout(5600);
    assert.ok(count(h, 'GET', '/api/runs') >= listCount + 2, 'pageshow must restore initial list fetch and polling');
  });

  await scenario('A late 401 from before pagehide cannot disconnect a successfully restored page', async h => {
    await open(h);
    const held = deferred(), release = deferred(), settled = deferred();
    h.releases.push(release.resolve);
    let hold = true;
    h.intercept = async route => {
      if (!isList(route) || !hold) return false;
      hold = false; held.resolve(); await release.promise;
      await route.fulfill({ status: 401, json: { error: 'Stale pre-restore response fixture' } }).catch(() => {});
      settled.resolve();
      return true;
    };
    await refreshHistory(h.page);
    await held.promise;
    await transition(h.page, 'pagehide');
    const restoredList = h.page.waitForResponse(response => new URL(response.url()).pathname === '/api/runs' && response.status() === 200);
    await transition(h.page, 'pageshow');
    await restoredList;
    await h.page.waitForFunction(() => !(document.querySelector('#submit-run') as HTMLButtonElement).disabled);
    const sessions = count(h, 'GET', '/api/session');
    release.resolve(); await settled.promise;
    await h.page.waitForTimeout(250);
    assert.equal(await h.page.locator('#submit-run').isEnabled(), true);
    assert.equal(await h.page.locator('#global-notice').isVisible(), false);
    assert.equal(count(h, 'GET', '/api/session'), sessions, 'stale 401 triggered another recovery');
  });

  await scenario('A hung GET times out within the request limit and permits subsequent recovery', async h => {
    await open(h);
    const values = await draft(h.page);
    const held = deferred(), release = deferred();
    h.releases.push(release.resolve);
    let hold = true;
    h.intercept = async route => {
      if (!isList(route) || !hold) return false;
      hold = false; held.resolve(); await release.promise;
      await route.fulfill({ status: 200, json: { runs: [] } }).catch(() => {});
      return true;
    };
    await refreshHistory(h.page);
    await held.promise;
    const started = performance.now();
    await h.page.locator('#global-notice').waitFor({ state: 'visible', timeout: 19_000 });
    timeoutElapsedMs = Math.round(performance.now() - started);
    assert.ok(timeoutElapsedMs >= 14_000 && timeoutElapsedMs <= 18_500, `unexpected timeout duration ${timeoutElapsedMs}ms`);
    await disconnected(h.page);
    release.resolve();
    await h.page.locator('#retry-connection').click();
    await ready(h.page);
    await assertDraft(h.page, values);
  });

  await writeReport('passed');
  console.log(`Recovery report: ${reportFile}`);
} catch (error) {
  await writeReport('failed', error);
  throw error;
} finally {
  await browser?.close();
  await service.close();
}
