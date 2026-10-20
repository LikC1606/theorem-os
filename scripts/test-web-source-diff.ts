#!/usr/bin/env bun
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { chromium, type BrowserContext, type Page } from 'playwright';
import { readWebConfig } from '../apps/web/config';
import { createWebService } from '../apps/web/server';
import type { WebRunner } from '../apps/web/runner';
import type { WebResult, WebRun, WebRunInput } from '../apps/web/shared';
import { fillConfig, refresh, selectHistoryRun } from './web-ui-controls';
import { freePort, postRun, ready, type RequestRecord, type ScenarioSuite, startBrowser, webScenario, writeScenarioReport } from './web-scenario';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const output = path.join(root, 'out/web-ui-smoke');
const reportFile = path.join(output, 'source-diff-report.json');
const storageKey = 'theorem-os.web-draft.v1';
const credential = `sk-theoremos-diff-fixture-${crypto.randomUUID()}`;
const markup = '<img data-diff-injection src=x onerror="window.__diffInjected=true">';
const widths = [1440, 375, 320];
await fs.access(path.join(root, 'out/web/app.js')).catch(() => { throw new Error('Run bun run build:web before the source diff check.'); });
await fs.mkdir(output, { recursive: true });
await fs.rm(reportFile, { force: true });
const port = await freePort();
const origin = `http://127.0.0.1:${port}`;
type Control = { emit(value: WebResult): void; finish(value?: WebResult): void };
const controls = new Map<string, Control>();
let workerStarts = 0;
const runner: WebRunner = {
  async readiness() { return { ready: true, message: 'Local source diff fixture' }; },
  async run(input, send, signal) {
    workerStarts++;
    await new Promise<void>((resolve, reject) => {
      const cleanup = () => { signal.removeEventListener('abort', abort); controls.delete(input.id); };
      const abort = () => { cleanup(); reject(new Error('Cancelled fixture')); };
      signal.addEventListener('abort', abort, { once: true });
      controls.set(input.id, {
        emit: value => send({ type: 'result', result: value }),
        finish: value => { if (value) send({ type: 'result', result: value }); cleanup(); resolve(); },
      });
      if (signal.aborted) abort();
    });
  },
};
const service = createWebService(readWebConfig({ THEOREMOS_WEB_PORT: String(port), THEOREMOS_WEB_PUBLIC_URL: origin,
  THEOREMOS_WEB_STATIC_ROOT: path.join(root, 'out/web'), THEOREMOS_WEB_CONCURRENCY: '8', THEOREMOS_WEB_QUEUE_LIMIT: '32' }), runner);
type Harness = { page: Page; context: BrowserContext; requests: RequestRecord[]; runIds: string[]; savedDraft: string | null };
type DiffRow = { type: 'added' | 'removed' | 'context'; old: number | null; next: number | null; text: string };
const checks: Array<{ name: string; elapsedMs: number; fixtureCreates: number; featureApiWrites: number; requests: RequestRecord[] }> = [];
const screenshots: string[] = [];
const downloads: Array<{ status: string; bytes: number }> = [];
let browser: Awaited<ReturnType<typeof chromium.launch>> | undefined;
const suite: ScenarioSuite = { origin, output, checks, failedScenario: '' };
const result = (proof: string, status = 'incomplete'): WebResult => ({ status, proof, report: { fixture: 'source-diff' } });
const sourceRows = (page: Page) => page.locator('#detail-panel').locator('.diff-scroll tr.diff-added, .diff-scroll tr.diff-removed, .diff-scroll tr.diff-context');

const scenario = (name: string, run: (h: Harness) => Promise<void>) => webScenario<Harness>(browser!, suite, name, run, {
  context: { viewport: { width: 1440, height: 900 }, permissions: ['clipboard-read', 'clipboard-write'] },
  harness: (page, context) => ({ page, context, requests: [], runIds: [], savedDraft: null }), routes: 'api',
  open: async h => {
    await h.page.goto(origin); await ready(h.page);
    await fillConfig(h.page, 'source', 'theorem unrelated_composer : True := by sorry');
    await h.page.locator('#task').fill('Preserve this separate composer draft');
    await fillConfig(h.page, 'api-key', credential);
    await h.page.waitForFunction(key => JSON.parse(sessionStorage.getItem(key) || 'null')?.draft?.task === 'Preserve this separate composer draft', storageKey);
    h.savedDraft = await h.page.evaluate(key => sessionStorage.getItem(key), storageKey);
  },
  timeout: { label: 'Source diff', seconds: 35 },
  verify: async ({ page, requests, runIds, savedDraft }, elapsedMs) => {
    const writes = requests.filter(request => request.method !== 'GET');
    assert.equal(writes.length, runIds.length, 'only explicit fixture creation may write the API');
    assert.equal(writes.every(request => request.method === 'POST' && request.pathname === '/api/runs'), true);
    const history = await page.evaluate(async () => (await (await fetch('/api/runs')).json()).runs as WebRun[]);
    assert.deepEqual(history.map(run => run.id).sort(), [...runIds].sort(), 'source inspection must preserve history');
    assert.equal(await page.evaluate(key => sessionStorage.getItem(key), storageKey), savedDraft, 'source inspection must preserve saved composer draft');
    assert.equal(await page.locator('#source').inputValue(), 'theorem unrelated_composer : True := by sorry');
    assert.equal(await page.locator('#task').inputValue(), 'Preserve this separate composer draft');
    assert.equal(await page.locator('#api-key').inputValue(), credential);
    return { name, elapsedMs: elapsedMs(), fixtureCreates: runIds.length, featureApiWrites: writes.length - runIds.length, requests };
  },
  failure: { prefix: 'source-diff-', fullPage: true }, cleanup: ({ runIds }) => { for (const id of runIds) controls.get(id)?.finish(); },
});
async function createRun(h: Harness, title: string, source: string, completed: WebResult | null): Promise<WebRun> {
  const input: WebRunInput = { providerId: 'openai', apiKey: credential, model: 'fixture-diff-model', effort: 'low',
    environment: 'standard', source, task: title, maxTurns: 2, maxRunSeconds: 60, workers: 1, coordination: 'independent' };
  const run = await postRun(h, input);
  h.runIds.push(run.id);
  assert.ok(controls.has(run.id), 'fixture worker must have started');
  if (completed) controls.get(run.id)!.finish(completed);
  return h.page.evaluate(async id => (await (await fetch(`/api/runs/${id}`)).json()).run as WebRun, run.id);
}
async function selectSource(h: Harness, id: string, diff = true) {
  await refresh(h);
  await selectHistoryRun(h.page, id);
  await h.page.locator('#detail-tab-source').click();
  if (diff) {
    await h.page.locator('button[data-source-view="diff"]').click();
    assert.equal(await h.page.locator('button[data-source-view="diff"]').getAttribute('aria-pressed'), 'true');
  }
}
async function rows(page: Page): Promise<DiffRow[]> {
  return sourceRows(page).evaluateAll(nodes => nodes.map(node => ({
    type: node.classList.contains('diff-added') ? 'added' : node.classList.contains('diff-removed') ? 'removed' : 'context',
    old: node.hasAttribute('data-old-line') ? Number(node.getAttribute('data-old-line')) : null,
    next: node.hasAttribute('data-new-line') ? Number(node.getAttribute('data-new-line')) : null,
    text: node.querySelector('[data-diff-text]')!.textContent!,
  })));
}
async function count(page: Page, selector: string, expected: number) {
  assert.equal(Number((await page.locator('#detail-panel').locator(selector).innerText()).replace(/[^0-9]/g, '')), expected, selector);
}
async function position(page: Page, expected: string) {
  assert.equal((await page.locator('#diff-position').innerText()).replace(/\s/g, ''), expected);
}
async function changeVisible(page: Page, index: number) {
  const inView = await page.locator('#detail-panel .diff-scroll').evaluate((scroll, index) => {
    const row = scroll.querySelector(`[data-change-start="${index}"]`)!.getBoundingClientRect();
    const frame = scroll.getBoundingClientRect();
    const heading = scroll.querySelector('thead')!.getBoundingClientRect();
    return row.top >= frame.top + heading.height - 1 && row.bottom <= frame.bottom + 1;
  }, index);
  assert.equal(inView, true, `change ${index + 1} must be visible below the table header`);
}
async function noInjection(page: Page) {
  assert.equal(await page.locator('[data-diff-injection]').count(), 0, 'source markup must be escaped');
  assert.equal(await page.evaluate(() => (window as unknown as Record<string, unknown>).__diffInjected), undefined);
}
async function screenshot(page: Page, name: string) {
  await page.screenshot({ path: path.join(output, name), fullPage: true });
  screenshots.push(name);
}
async function copyProof(page: Page, proof: string) {
  await page.locator('[data-action="copy-source"]').click();
  assert.equal(await page.evaluate(() => navigator.clipboard.readText()), proof, 'diff copy must preserve proof, never generated patch');
}
async function downloadProof(page: Page, run: WebRun, proof: string) {
  const pending = page.waitForEvent('download');
  await page.locator('[data-action="download-proof"]').click();
  const downloaded = await pending;
  assert.equal(downloaded.suggestedFilename(), `${run.id}-Submission.lean`);
  const bytes = await fs.readFile((await downloaded.path())!);
  assert.deepEqual(bytes, Buffer.from(proof), 'Lean download must preserve original bytes');
  downloads.push({ status: run.result?.status ?? 'missing', bytes: bytes.length });
}
async function horizontalFit(page: Page, selector: string, width: number) {
  assert.equal(await page.evaluate(() => document.documentElement.scrollWidth <= innerWidth), true, `document overflow at ${width}px`);
  const bounds = await page.locator(selector).boundingBox();
  assert.ok(bounds && bounds.x >= 0 && bounds.x + bounds.width <= width + 1, `${selector} overflows ${width}px viewport`);
}
const writeReport = (status: 'passed' | 'failed', error?: unknown) => writeScenarioReport(reportFile, suite, status, error,
  'Real HTTP service and Chromium with controlled worker results. No Docker, Lean or model provider is called.',
  { workerStarts, fixtureCreates: checks.reduce((sum, check) => sum + check.fixtureCreates, 0),
    featureApiWrites: checks.reduce((sum, check) => sum + check.featureApiWrites, 0), checks, widths, screenshots, downloads });

try {
  browser = await startBrowser(service.server, port);

  await scenario('Complete line diffs retain exact code, blank lines, whitespace, Unicode and old/new line numbers', async h => {
    const before = ['namespace Fixture', '', `-- old ${markup}`, 'theorem sample : True := by', '  sorry', '', '-- space: x \t', '-- \u03b1', 'end Fixture'];
    const after = ['namespace Fixture', '', `-- new ${markup}`, 'theorem sample : True := by', '  trivial', '  -- inserted', '', '-- space: x\t', '-- \u03b2', 'end Fixture'];
    const run = await createRun(h, 'Exact line changes', before.join('\n'), result(after.join('\n')));
    await selectSource(h, run.id);
    assert.equal(await h.page.locator('#diff-changes-only').isChecked(), true);
    await h.page.locator('#diff-changes-only').uncheck();
    const expected: DiffRow[] = [
      { type: 'context', old: 1, next: 1, text: before[0]! }, { type: 'context', old: 2, next: 2, text: '' },
      { type: 'removed', old: 3, next: null, text: before[2]! }, { type: 'added', old: null, next: 3, text: after[2]! },
      { type: 'context', old: 4, next: 4, text: before[3]! }, { type: 'removed', old: 5, next: null, text: before[4]! },
      { type: 'added', old: null, next: 5, text: after[4]! }, { type: 'added', old: null, next: 6, text: after[5]! },
      { type: 'context', old: 6, next: 7, text: '' }, { type: 'removed', old: 7, next: null, text: before[6]! },
      { type: 'removed', old: 8, next: null, text: before[7]! }, { type: 'added', old: null, next: 8, text: after[7]! },
      { type: 'added', old: null, next: 9, text: after[8]! }, { type: 'context', old: 9, next: 10, text: before[8]! },
    ];
    assert.deepEqual(await rows(h.page), expected);
    await count(h.page, '.diff-count-added', 5); await count(h.page, '.diff-count-removed', 4);
    assert.equal(await h.page.locator('#detail-panel [data-change-start]').count(), 3);
    assert.ok(await h.page.locator('#detail-panel .diff-no-newline[data-eof-side="both"]').count() > 0);
    await noInjection(h.page);
    await screenshot(h.page, 'source-diff-desktop-exact.png');
  });

  await scenario('Three-line context folds distant changes and previous/next navigation reaches each group', async h => {
    const before = Array.from({ length: 48 }, (_, index) => `-- context ${String(index + 1).padStart(3, '0')}`);
    const after = [...before];
    for (const index of [6, 24, 42]) after[index] = `-- changed ${index + 1}`;
    const run = await createRun(h, 'Three distant changes', before.join('\n'), result(after.join('\n')));
    await selectSource(h, run.id);
    if (!(await h.page.locator('#diff-changes-only').isChecked())) await h.page.locator('#diff-changes-only').check();
    assert.equal(await h.page.locator('#detail-panel .diff-gap').count(), 4);
    assert.equal(await h.page.locator('#detail-panel .diff-context').count(), 18);
    assert.equal(await h.page.locator('#detail-panel [data-change-start]').count(), 3);
    await position(h.page, '1/3');
    await h.page.locator('[data-action="diff-next"]').click(); await position(h.page, '2/3');
    await h.page.locator('[data-action="diff-next"]').click(); await position(h.page, '3/3');
    await h.page.locator('[data-action="diff-prev"]').click(); await position(h.page, '2/3');
    await h.page.locator('#diff-changes-only').uncheck();
    assert.equal(await h.page.locator('#detail-panel .diff-gap').count(), 0);
    assert.equal((await rows(h.page)).length, 51);
    assert.equal(await h.page.locator('#detail-panel .diff-context').count(), 45);
    await h.page.locator('[data-action="diff-next"]').click();
    await position(h.page, '3/3'); await changeVisible(h.page, 2);
    await h.page.locator('button[data-source-view="input"]').click();
    await h.page.locator('button[data-source-view="diff"]').click();
    await position(h.page, '3/3'); await changeVisible(h.page, 2);
    await h.page.locator('#detail-tab-overview').click();
    await h.page.locator('#detail-tab-source').click();
    assert.equal(await h.page.locator('button[data-source-view="diff"]').getAttribute('aria-pressed'), 'true');
    await position(h.page, '3/3'); await changeVisible(h.page, 2);
    await screenshot(h.page, 'source-diff-desktop-navigation.png');
  });

  await scenario('Diff copy and Lean download preserve candidate and accepted proofs rather than generating patches', async h => {
    for (const status of ['evaluated_failed', 'evaluated_passed']) {
      const source = 'namespace Download\n\ntheorem unchanged : True := by sorry\nend Download';
      const proof = `namespace Download\r\n-- ${markup}\r\ntheorem unchanged : True := by trivial\r\nend Download\r\n`;
      const run = await createRun(h, `Original downloads ${status}`, source, result(proof, status));
      await selectSource(h, run.id);
      assert.equal(await h.page.locator('button[data-source-view="proof"]').innerText(), status === 'evaluated_passed' ? '\u9a8c\u6536\u8bc1\u660e' : '\u5019\u9009\u6e90\u7801');
      await copyProof(h.page, proof); await downloadProof(h.page, run, proof);
      await h.page.locator('button[data-source-view="proof"]').click();
      assert.equal(await h.page.locator('#detail-panel .code-scroll code').textContent(), proof.replace(/\r\n/g, '\n'));
      await h.page.locator('button[data-source-view="input"]').click();
      assert.equal(await h.page.locator('#detail-panel .code-scroll code').textContent(), run.source);
      await h.page.locator('[data-action="copy-source"]').click();
      assert.equal(await h.page.evaluate(() => navigator.clipboard.readText()), run.source);
      await h.page.locator('button[data-source-view="diff"]').click();
      await copyProof(h.page, proof); await noInjection(h.page);
    }
  });

  await scenario('Identical source and CRLF-only differences are explicit while final-newline changes remain real diffs', async h => {
    const source = 'namespace Format\n-- keep spacing \t\nend Format';
    for (const [title, before, proof, formatOnly] of [
      ['Identical source', source, source, false],
      ['CRLF-only source', source.replace(/\n/g, '\r\n'), source, true],
    ] as const) {
      const run = await createRun(h, title, before, result(proof));
      await selectSource(h, run.id);
      await h.page.locator('#detail-panel .diff-identical').waitFor();
      if (formatOnly) assert.match(await h.page.locator('#detail-panel .diff-identical').innerText(), /\u4ec5\u6362\u884c\u683c\u5f0f\u4e0d\u540c/);
      assert.equal(await sourceRows(h.page).count(), 0);
      assert.equal(await h.page.locator('[data-action="diff-next"]').count(), 0);
      await copyProof(h.page, proof);
    }
    const run = await createRun(h, 'Final newline is a real change', 'theorem final_newline : True := by trivial', result('theorem final_newline : True := by trivial\n'));
    await selectSource(h, run.id);
    await count(h.page, '.diff-count-added', 1); await count(h.page, '.diff-count-removed', 1);
    assert.equal(await h.page.locator('#detail-panel .diff-identical').count(), 0);
    assert.equal(await h.page.locator('#detail-panel .diff-removed .diff-no-newline[data-eof-side="old"]').count(), 1);
    assert.equal(await h.page.locator('#detail-panel .diff-added .diff-no-newline').count(), 0);
  });

  await scenario('Pending results and empty proof strings have no diff control and retain original input', async h => {
    for (const completed of [null, result('')]) {
      const run = await createRun(h, completed ? 'Empty proof result' : 'Result not ready', 'theorem original_only : True := by sorry', completed);
      await selectSource(h, run.id, false);
      assert.equal(await h.page.locator('button[data-source-view="diff"]').count(), 0);
      assert.equal(await h.page.locator('#detail-panel .diff-scroll').count(), 0);
      assert.equal(await h.page.locator('#detail-panel .code-scroll code').textContent(), run.source);
      await h.page.locator('[data-action="copy-source"]').click();
      assert.equal(await h.page.evaluate(() => navigator.clipboard.readText()), run.source);
    }
  });

  await scenario('An early passed result remains candidate source while the run is still active', async h => {
    const proof = 'theorem early_candidate : True := by trivial';
    const run = await createRun(h, 'Early result while running', 'theorem early_candidate : True := by sorry', null);
    controls.get(run.id)!.emit(result(proof, 'evaluated_passed'));
    await selectSource(h, run.id);
    assert.equal(await h.page.locator('button[data-source-view="proof"]').innerText(), '\u5019\u9009\u6e90\u7801');
    assert.match(await h.page.locator('[data-action="copy-source"]').getAttribute('aria-label') ?? '', /\u5019\u9009/);
    await copyProof(h.page, proof);
    const actual = await h.page.evaluate(async id => (await (await fetch(`/api/runs/${id}`)).json()).run as WebRun, run.id);
    assert.equal(actual.status, 'running');
    assert.equal(actual.result?.status, 'evaluated_passed');
    await h.page.locator('#detail-tab-overview').click();
    assert.equal(await h.page.locator('.result-banner.passed').count(), 0);
  });

  await scenario('Large full views cap at 2000 source rows and display truncation without losing the original proof', async h => {
    const before = Array.from({ length: 2500 }, (_, index) => `-- ${index + 1}`);
    const after = [...before]; after[2499] = '-- changed last line';
    const proof = after.join('\n');
    const run = await createRun(h, 'Bounded full diff', before.join('\n'), result(proof));
    await selectSource(h, run.id);
    if (!(await h.page.locator('#diff-changes-only').isChecked())) await h.page.locator('#diff-changes-only').check();
    assert.ok((await rows(h.page)).some(row => row.type === 'added' && row.text === '-- changed last line'));
    await count(h.page, '.diff-count-added', 1); await count(h.page, '.diff-count-removed', 1);
    await h.page.locator('#diff-changes-only').uncheck();
    assert.equal(await sourceRows(h.page).count(), 2000);
    await h.page.locator('#detail-panel .diff-truncated').waitFor();
    assert.match(await h.page.locator('#detail-panel .diff-truncated').innerText(), /501/);
    await copyProof(h.page, proof); await downloadProof(h.page, run, proof);
    await h.page.locator('#diff-changes-only').check();
    assert.ok((await rows(h.page)).some(row => row.type === 'added' && row.text === '-- changed last line'));
    assert.equal(await h.page.locator('#detail-panel .diff-truncated').count(), 0);
    await screenshot(h.page, 'source-diff-desktop-bounded.png');
  });

  await scenario('Algorithm limits degrade explicitly and leave source switching, copy and downloads responsive', async h => {
    const before = Array.from({ length: 1001 }, (_, index) => `old_${index}`).join('\n');
    const proof = Array.from({ length: 1001 }, (_, index) => `new_${index}`).join('\n');
    const run = await createRun(h, 'Bounded diff algorithm', before, result(proof));
    const started = performance.now();
    await selectSource(h, run.id);
    await h.page.locator('#detail-panel .diff-unavailable').waitFor();
    assert.ok(performance.now() - started < 5000, 'bounded algorithm must leave the page responsive');
    assert.equal(await sourceRows(h.page).count(), 0);
    assert.equal(await h.page.locator('[data-action="diff-next"]').count(), 0);
    await copyProof(h.page, proof); await downloadProof(h.page, run, proof);
    await h.page.locator('button[data-source-view="input"]').click();
    assert.equal(await h.page.locator('#detail-panel .code-scroll code').textContent(), before);
    await h.page.locator('button[data-source-view="proof"]').click();
    assert.equal(await h.page.locator('#detail-panel .code-scroll code').textContent(), proof);
    await h.page.locator('button[data-source-view="diff"]').click();
    await h.page.locator('#detail-panel .diff-unavailable').waitFor();
    await screenshot(h.page, 'source-diff-desktop-unavailable.png');
  });

  await scenario('Diff controls and long escaped code fit 320, 375 and 1440 pixel layouts with local scrolling', async h => {
    const before = Array.from({ length: 28 }, (_, index) => `-- context ${index + 1}`);
    before[6] = `-- old ${'long_identifier_'.repeat(18)}${markup}`;
    const after = [...before]; after[6] = `-- new ${'long_identifier_'.repeat(18)}${markup}`; after[21] = '-- another change';
    const run = await createRun(h, 'Responsive source changes', before.join('\n'), result(after.join('\n'), 'evaluated_passed'));
    await selectSource(h, run.id);
    if (!(await h.page.locator('#diff-changes-only').isChecked())) await h.page.locator('#diff-changes-only').check();
    for (const width of widths) {
      await h.page.setViewportSize({ width, height: width > 850 ? 900 : 812 });
      if (width <= 850) await h.page.locator('#mobile-runs').click();
      await horizontalFit(h.page, '.source-topline', width);
      await horizontalFit(h.page, '#detail-panel .diff-scroll', width);
      for (const selector of ['button[data-source-view="diff"]', '[data-action="copy-source"]', '[data-action="download-proof"]',
        '[data-action="diff-prev"]', '[data-action="diff-next"]', '#diff-changes-only']) await horizontalFit(h.page, selector, width);
      assert.equal(await h.page.locator('.diff-scroll-hint').isVisible(), width <= 560,
        `mobile diff scrolling hint visibility at ${width}px`);
      const overlap = await h.page.locator('.source-topline button').evaluateAll(buttons => buttons.some((left, index) => {
        const a = left.getBoundingClientRect();
        return buttons.slice(index + 1).some(right => {
          const b = right.getBoundingClientRect();
          return a.left < b.right - 1 && a.right > b.left + 1 && a.top < b.bottom - 1 && a.bottom > b.top + 1;
        });
      }));
      assert.equal(overlap, false, `source buttons overlap at ${width}px`);
      assert.equal(await h.page.locator('#detail-panel .diff-scroll').evaluate(scroll => scroll.scrollWidth > scroll.clientWidth), true, 'long code must scroll inside diff');
      await noInjection(h.page);
      await screenshot(h.page, `source-diff-${width}-changes.png`);
    }
  });

  await writeReport('passed');
  console.log(`Source diff report: ${reportFile}`);
} catch (error) {
  await writeReport('failed', error);
  throw error;
} finally {
  await browser?.close();
  await service.close();
}
