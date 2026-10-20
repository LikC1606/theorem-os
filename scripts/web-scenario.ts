import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import type http from 'node:http';
import net from 'node:net';
import path from 'node:path';
import { chromium, type Browser, type BrowserContext, type BrowserContextOptions, type Page, type Route } from 'playwright';
import type { WebRun, WebRunInput } from '../apps/web/shared';

export type RequestRecord = { method: string; pathname: string };
export type ScenarioHarness = { page: Page; context: BrowserContext; requests: RequestRecord[]; intercept?: (route: Route) => Promise<boolean> };
/** Report state shared by one check script's scenarios; `harness` is the latest scenario's harness. */
export type ScenarioSuite = { origin: string; output: string; checks: object[]; failedScenario: string; failureScreenshot?: string;
  harness?: ScenarioHarness };

/** Reserve a loopback port by binding and releasing it before the service listens. */
export async function freePort() {
  const probe = net.createServer();
  await new Promise<void>(resolve => probe.listen(0, '127.0.0.1', resolve));
  const port = (probe.address() as net.AddressInfo).port;
  await new Promise<void>((resolve, reject) => probe.close(error => error ? reject(error) : resolve()));
  return port;
}
/** Start the service on the reserved loopback port, then launch headless Chromium. */
export async function startBrowser(server: http.Server, port: number) {
  await new Promise<void>((resolve, reject) => { server.once('error', reject); server.listen(port, '127.0.0.1', resolve); });
  return chromium.launch({ headless: true });
}

export async function settled(page: Page) {
  await page.evaluate(() => new Promise<void>(resolve => requestAnimationFrame(() => requestAnimationFrame(() => resolve()))));
}

/** Report fields of the scenario that was running when `error` stopped the check. */
export const scenarioFailure = (suite: ScenarioSuite, error: unknown) => ({ failedScenario: suite.failedScenario,
  error: error instanceof Error ? error.message : String(error), failureScreenshot: suite.failureScreenshot });
/** Write the standard report envelope; a `credential` must not appear anywhere in it. */
export async function writeScenarioReport(file: string, suite: ScenarioSuite, status: 'passed' | 'failed', error: unknown,
  mode: string, fields: object, options: { credential?: string; failureRequests?: true } = {}) {
  const report = { status, checkedAt: new Date().toISOString(), mode, paidModelCalls: false, ...fields,
    ...(error ? { ...scenarioFailure(suite, error), ...options.failureRequests && { failureRequests: suite.harness?.requests } } : {}) };
  if (options.credential !== undefined) assert.equal(JSON.stringify(report).includes(options.credential), false);
  await fs.writeFile(file, JSON.stringify(report, null, 2) + '\n');
}

export type ScenarioOptions<H extends ScenarioHarness> = {
  context: BrowserContextOptions; init?: (context: BrowserContext) => Promise<unknown> | undefined;
  harness: (page: Page, context: BrowserContext) => H;
  /** `local` aborts and later asserts non-origin requests (`local` is the message), records `/api/` requests, then lets
   * `blockWrites` abort non-GET ones or `h.intercept` answer them; `api` routes only `/api/**`; `observe` records without routing. */
  routes: { local: string; blockWrites?: true } | 'api' | 'observe';
  /** `true` loads the workbench and waits for an enabled submit button before the deadline starts. */
  open?: true | ((h: H) => Promise<void>);
  timeout: { label: string; seconds: number };
  /** Assert scenario invariants and return its check record; the default records name, elapsed time and requests. */
  verify?: (h: H, elapsedMs: () => number) => Promise<object> | object;
  failure?: { prefix?: string; fullPage?: true; capture?: (page: Page, image: string) => Promise<unknown> };
  cleanup?: (h: H) => Promise<void> | void;
};

/** Run one scenario in a fresh context: fail on page errors, a missed deadline or `verify`, screenshot failures, and always
 * run `cleanup` before closing the context. */
export async function webScenario<H extends ScenarioHarness>(browser: Browser, suite: ScenarioSuite, name: string,
  run: (h: H) => Promise<void>, options: ScenarioOptions<H>) {
  suite.failedScenario = name;
  const started = performance.now();
  const context = await browser.newContext(options.context);
  await options.init?.(context);
  const page = await context.newPage();
  page.setDefaultTimeout(10_000);
  const h = options.harness(page, context); suite.harness = h;
  const errors: string[] = [], external: string[] = [], routes = options.routes;
  page.on('pageerror', error => errors.push(error.message));
  if (routes === 'observe') page.on('request', request => {
    const pathname = new URL(request.url()).pathname;
    if (pathname.startsWith('/api/')) h.requests.push({ method: request.method(), pathname });
  });
  else if (routes === 'api') await page.route('**/api/**', async route => {
    h.requests.push({ method: route.request().method(), pathname: new URL(route.request().url()).pathname });
    if (await h.intercept?.(route)) return;
    await route.continue();
  });
  else await context.route(/^https?:\/\//, async route => {
    const url = new URL(route.request().url());
    if (url.origin !== suite.origin) { external.push(url.href); await route.abort(); return; }
    if (url.pathname.startsWith('/api/')) {
      h.requests.push({ method: route.request().method(), pathname: url.pathname });
      if (routes.blockWrites && route.request().method() !== 'GET') { await route.abort(); return; }
      if (await h.intercept?.(route)) return;
    }
    await route.continue();
  });
  let deadline: ReturnType<typeof setTimeout> | undefined;
  try {
    if (options.open === true) { await page.goto(suite.origin); await page.locator('#submit-run:enabled').waitFor(); }
    else await options.open?.(h);
    const { label, seconds } = options.timeout;
    await Promise.race([run(h), new Promise<never>((_, reject) => {
      deadline = setTimeout(() => reject(new Error(`${label} scenario exceeded ${seconds} seconds: ${name}`)), seconds * 1000);
    })]);
    assert.deepEqual(errors, [], 'uncaught browser errors');
    if (typeof routes === 'object') assert.deepEqual(external, [], routes.local);
    const elapsedMs = () => Math.round(performance.now() - started);
    suite.checks.push(await options.verify?.(h, elapsedMs) ?? { name, elapsedMs: elapsedMs(), requests: h.requests });
    console.log(`PASS ${name}`);
  } catch (error) {
    const { prefix = '', fullPage, capture } = options.failure ?? {};
    suite.failureScreenshot = `${prefix}failure-${suite.checks.length + 1}.png`;
    await (capture ? capture(page, suite.failureScreenshot)
      : page.screenshot({ path: path.join(suite.output, suite.failureScreenshot), fullPage })).catch(() => {});
    throw error;
  } finally {
    clearTimeout(deadline);
    try { await options.cleanup?.(h); } finally { await context.close(); }
  }
}

export const normalize = (source: string) => source.replace(/\r\n?/g, '\n');
export const ready = (page: Page) => page.locator('#submit-run:enabled').waitFor();
export function deferred() {
  let resolve!: () => void;
  const promise = new Promise<void>(done => { resolve = done; });
  return { promise, resolve };
}
export async function readRun(h: { page: Page }, id: string): Promise<WebRun> {
  return h.page.evaluate(async id => (await (await fetch(`/api/runs/${id}`)).json()).run as WebRun, id);
}
/** Create a fixture run through the page's own session and CSRF token; `label` prefixes the creation error. */
export async function postRun(h: { page: Page }, input: WebRunInput, label = 'Fixture'): Promise<WebRun> {
  return h.page.evaluate(async ({ input, label }) => {
    const session = await (await fetch('/api/session')).json();
    const response = await fetch('/api/runs', { method: 'POST', headers: { 'Content-Type': 'application/json', 'X-CSRF-Token': session.csrfToken }, body: JSON.stringify(input) });
    if (response.status !== 201) throw new Error(`${label} creation failed: ${response.status}`);
    return (await response.json()).run as WebRun;
  }, { input, label });
}
