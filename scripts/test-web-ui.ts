#!/usr/bin/env bun
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import net from 'node:net';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { chromium } from 'playwright';
import { readWebConfig, webTemplates } from '../apps/web/config';
import { createWebService } from '../apps/web/server';
import type { WebRunner } from '../apps/web/runner';
import type { WebResult, WebRun, WorkerInput } from '../apps/web/shared';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const output = path.join(root, 'out/web-ui-smoke');
await fs.access(path.join(root, 'out/web/app.js')).catch(() => { throw new Error('Run bun run build:web before the browser check.'); });
await fs.mkdir(output, { recursive: true });
await fs.rm(path.join(output, 'report.json'), { force: true });
const probe = net.createServer();
await new Promise<void>(resolve => probe.listen(0, '127.0.0.1', resolve));
const port = (probe.address() as net.AddressInfo).port;
await new Promise<void>((resolve, reject) => probe.close(error => error ? reject(error) : resolve()));
const origin = `http://127.0.0.1:${port}`;
const credential = `sk-theoremos-ui-fixture-${crypto.randomUUID()}`;
type Control = { progress(event: string): void; finish(result: WebResult): void };
const controls = new Map<string, Control>();
const received: WorkerInput[] = [];
const runner: WebRunner = {
  async readiness() { return { ready: true, message: '本地 UI 验证环境' }; },
  async run(input, send, signal) {
    received.push(input);
    await new Promise<void>((resolve, reject) => {
      const abort = () => { controls.delete(input.id); reject(new Error('Cancelled fixture')); };
      signal.addEventListener('abort', abort, { once: true });
      const complete = (result: WebResult) => {
        signal.removeEventListener('abort', abort);
        controls.delete(input.id); send({ type: 'result', result }); resolve();
      };
      controls.set(input.id, { progress: event => send({ type: 'progress', event, message: 'Fixture activity' }), finish: complete });
      if (signal.aborted) abort();
    });
  },
};
const service = createWebService(readWebConfig({ THEOREMOS_WEB_PORT: String(port), THEOREMOS_WEB_PUBLIC_URL: origin,
  THEOREMOS_WEB_STATIC_ROOT: path.join(root, 'out/web') }), runner);
const checks: string[] = [];
const screenshots: string[] = [];
const mark = (check: string) => { checks.push(check); console.log(`PASS ${check}`); };
let browser: Awaited<ReturnType<typeof chromium.launch>> | undefined;
try {
  await new Promise<void>((resolve, reject) => { service.server.once('error', reject); service.server.listen(port, '127.0.0.1', resolve); });
  browser = await chromium.launch({ headless: true });
  const context = await browser.newContext({ viewport: { width: 1440, height: 900 }, permissions: ['clipboard-read', 'clipboard-write'] });
  const page = await context.newPage();
  const errors: string[] = [];
  let creationRequests = 0;
  page.on('request', request => { if (new URL(request.url()).pathname === '/api/runs' && request.method() === 'POST') creationRequests++; });
  page.on('pageerror', error => errors.push(error.message));
  await page.goto(origin);
  await page.locator('#submit-run:enabled').waitFor();
  assert.equal(await page.locator('#environment').inputValue(), 'mathlib');
  const template = webTemplates.find(template => template.id === 'polynomial')!;
  assert.equal(await page.locator('#source').inputValue(), template.source);
  const initialWidths = [1440, 375, 320];
  const previewValue = (name: string) => page.locator(`#draft-preview [data-preview-value="${name}"]`);
  async function assertPreviewSource() {
    const source = await page.locator('#source').inputValue();
    await page.waitForFunction(source => Array.from(document.querySelectorAll('#draft-preview-code code'))
      .map(code => code.textContent ?? '').join('\n') === source, source);
  }
  async function assertPreviewConnection() {
    assert.equal(await previewValue('model').innerText(), await page.locator('#model').inputValue());
    const environment = await page.locator('#environment option:checked').innerText();
    assert.ok((await previewValue('environment').innerText()).includes(environment));
    const seconds = await page.locator('#max-seconds').inputValue();
    const formatted = `${String(Math.floor(Number(seconds) / 60)).padStart(2, '0')}:${String(Number(seconds) % 60).padStart(2, '0')}`;
    const budget = await previewValue('budget').innerText();
    assert.ok(budget.includes(seconds) || budget.includes(formatted), 'preview budget must match the entered seconds');
    assert.ok((await previewValue('workers').innerText()).includes(await page.locator('#workers').inputValue()));
  }
  await page.locator('#draft-preview').waitFor();
  assert.equal(await page.locator('#draft-preview .preview-status').innerText(), '未提交');
  await assertPreviewSource();
  await assertPreviewConnection();
  for (const width of initialWidths) {
    const height = width > 850 ? 900 : 812;
    await page.setViewportSize({ width, height });
    if (width <= 850) await page.locator('#mobile-compose').click();
    const compose = await page.evaluate(() => {
      window.scrollTo(0, 0);
      document.querySelector('#form-fields')!.scrollTop = 0;
      const source = document.querySelector('#source')!, task = document.querySelector('#task')!, model = document.querySelector('#model')!;
      const bounds = source.getBoundingClientRect();
      const headings = Array.from(document.querySelectorAll('#form-fields .section-heading h2')).map(heading => heading.textContent);
      return { overflow: document.documentElement.scrollWidth > innerWidth, sourceTop: bounds.top,
        visibleSourceBottom: bounds.top + Math.min(80, bounds.height),
        sourceBeforeModel: Boolean(source.compareDocumentPosition(model) & Node.DOCUMENT_POSITION_FOLLOWING),
        taskBeforeModel: Boolean(task.compareDocumentPosition(model) & Node.DOCUMENT_POSITION_FOLLOWING),
        sourceAboveModel: bounds.top < model.getBoundingClientRect().top,
        taskAboveModel: task.getBoundingClientRect().top < model.getBoundingClientRect().top,
        taskSection: headings.indexOf('研究任务'), modelSection: headings.indexOf('模型连接') };
    });
    assert.equal(compose.overflow, false, `initial composer overflows ${width}px`);
    assert.ok(compose.taskSection >= 0 && compose.taskSection < compose.modelSection, 'research must precede model connection');
    assert.ok(compose.sourceBeforeModel && compose.taskBeforeModel && compose.sourceAboveModel && compose.taskAboveModel,
      `research fields must appear before model connection at ${width}px`);
    assert.ok(compose.sourceTop >= 0 && compose.visibleSourceBottom <= height, `source is not readable in the initial ${width}x${height} viewport`);
    await screenshot(width === 1440 ? 'desktop-initial-preview.png' : `mobile-${width}-initial.png`);
    if (width <= 850) await page.locator('#mobile-runs').click();
    await page.locator('#draft-preview').waitFor();
    for (const selector of ['#draft-preview', '#draft-preview .preview-source', '#draft-preview .draft-source-scroll']) {
      const bounds = await page.locator(selector).boundingBox();
      assert.ok(bounds && bounds.x >= 0 && bounds.x + bounds.width <= width + 1, `${selector} overflows initial ${width}px view`);
    }
    assert.equal(await page.evaluate(() => document.documentElement.scrollWidth <= innerWidth), true, `initial preview overflows ${width}px`);
    assert.equal(await page.locator('#draft-preview .preview-status').innerText(), '未提交');
    await assertPreviewSource();
    if (width <= 850) await page.locator('#mobile-compose').click();
  }
  await page.setViewportSize({ width: 1440, height: 900 });
  mark('initial 1440, 375 and 320px views show research before model connection, readable first-screen source and an unsubmitted preview');

  const previewSource = 'namespace Preview\n\n-- α preview\ntheorem preview : True := by\n  trivial\nend Preview\n';
  const previewTask = '预览更新任务\n保留原始 Lean 声明。';
  await page.locator('#environment').selectOption('standard');
  await page.locator('#source').fill(previewSource);
  await page.locator('#task').fill(previewTask);
  await page.locator('#model').fill('fixture-preview-model');
  await page.locator('#max-turns').fill('4');
  await page.locator('#max-seconds').fill('125');
  await page.locator('#workers').fill('3');
  await assertPreviewSource();
  await assertPreviewConnection();
  await page.waitForFunction(task => document.querySelector('#draft-preview')?.textContent?.includes(task), previewTask);

  const longPreviewLines = Array.from({ length: 180 }, (_, index) => index === 0
    ? `-- <img data-preview-injection src="fixture"> & ${'long Lean source '.repeat(30)}`
    : `-- source line ${index + 1}`);
  const longPreviewSource = longPreviewLines.join('\n');
  await page.locator('#source').fill(longPreviewSource);
  await page.waitForFunction(source => document.querySelector('#draft-preview-code code')?.textContent === source,
    longPreviewLines.slice(0, 160).join('\n'));
  assert.equal(await page.locator('#source').inputValue(), longPreviewSource);
  assert.match(await page.locator('.preview-source-heading > span').innerText(), /前 160 \/ 180 行/);
  assert.equal(await page.locator('#draft-preview-code [data-preview-injection]').count(), 0, 'source markup must stay escaped');
  assert.deepEqual((await page.locator('.preview-line-numbers').textContent())?.split('\n'),
    Array.from({ length: 160 }, (_, index) => String(index + 1)));
  for (const width of initialWidths) {
    await page.setViewportSize({ width, height: width > 850 ? 900 : 812 });
    if (width <= 850) await page.locator('#mobile-runs').click();
    const scrolled = await page.locator('.draft-source-scroll').evaluate(scroll => {
      scroll.scrollTop = 120;
      scroll.scrollLeft = 120;
      return { top: scroll.scrollTop, left: scroll.scrollLeft, height: scroll.getBoundingClientRect().height };
    });
    assert.ok(scrolled.top > 0 && scrolled.left > 0, `long source must scroll both ways at ${width}px`);
    assert.equal(scrolled.height, width > 850 ? 280 : 240, `preview height must stay bounded at ${width}px`);
    if (width <= 850) await page.locator('#mobile-compose').click();
    const model = `fixture-preview-model-${width}`;
    await page.locator('#model').fill(model);
    if (width <= 850) await page.locator('#mobile-runs').click();
    await page.waitForFunction(model => document.querySelector('[data-preview-value="model"]')?.textContent === model, model);
    const afterEdit = await page.locator('.draft-source-scroll').evaluate(scroll => ({
      top: scroll.scrollTop, left: scroll.scrollLeft, height: scroll.getBoundingClientRect().height,
    }));
    assert.deepEqual(afterEdit, scrolled, `editing the model must preserve source scrolling and height at ${width}px`);
    assert.equal(await page.locator('#draft-preview-code code').textContent(), longPreviewLines.slice(0, 160).join('\n'));
    if (width <= 850) await page.locator('#mobile-compose').click();
  }
  mark('long draft previews cap at 160 lines, escape source markup and preserve bounded height and both scroll positions after model edits');

  const resizedModel = 'fixture-preview-desktop-resize';
  await page.locator('#model').fill(resizedModel);
  await page.setViewportSize({ width: 1440, height: 900 });
  await page.waitForFunction(model => document.querySelector('[data-preview-value="model"]')?.textContent === model, resizedModel);
  await assertPreviewConnection();
  mark('a draft edited in the 320px composer updates its preview when resizing directly to desktop');

  await page.locator('#source').fill(previewSource);
  await assertPreviewSource();
  await page.locator('#api-key').fill(credential);
  await page.locator('#toggle-key').click();
  assert.equal((await page.locator('#draft-preview').innerHTML()).includes(credential), false);
  for (const id of ['max-turns', 'max-seconds', 'workers']) await page.locator(`#${id}`).fill('');
  assert.equal(await previewValue('budget').innerText(), '未设置');
  assert.equal(await previewValue('workers').innerText(), '未设置');
  assert.equal((await page.locator('#draft-preview').innerText()).includes('NaN'), false);
  assert.equal((await page.locator('#draft-preview').innerHTML()).includes(credential), false);
  await page.locator('#reset-form').click();
  assert.equal(await page.locator('#source').inputValue(), template.source);
  assert.equal(await page.locator('#environment').inputValue(), 'mathlib');
  assert.equal(await page.locator('#api-key').inputValue(), '');
  assert.equal(await page.locator('#api-key').getAttribute('type'), 'password');
  assert.equal(await page.locator('#draft-preview .preview-status').innerText(), '未提交');
  await assertPreviewSource();
  await assertPreviewConnection();
  assert.equal(creationRequests, 0, 'preview changes and reset must not submit runs');
  assert.equal(received.length, 0, 'preview changes must not start a worker');
  assert.equal(await page.locator('#run-count').innerText(), '0');
  mark('draft preview mirrors source, task, model, environment and budget, handles empty numbers, excludes the API key and resets without POST requests');

  await page.locator('#task').fill('实数平方展开\n保留原始题目，使用 Mathlib 构造并验证证明。');
  const task = await page.locator('#task').inputValue();
  await page.locator('#max-turns').fill('3');
  await page.locator('#max-seconds').fill('90');
  await page.locator('#workers').fill('2');
  await page.locator('input[name="coordination"][value="independent"]').check();
  async function submit(): Promise<WebRun> {
    await page.locator('#api-key').fill(credential);
    const response = page.waitForResponse(response => new URL(response.url()).pathname === '/api/runs' && response.request().method() === 'POST');
    await page.locator('#submit-run').click();
    const posted = await response;
    assert.equal(posted.status(), 201);
    const payload = await posted.json() as { run: WebRun };
    assert.equal(JSON.stringify(payload).includes(credential), false);
    await page.waitForFunction(() => (document.querySelector('#api-key') as HTMLInputElement).value === '');
    return payload.run;
  }
  async function screenshot(name: string) {
    await page.locator('#toast').waitFor({ state: 'hidden' });
    await page.evaluate(() => { if (innerWidth > 850) document.querySelector('#form-fields')!.scrollTop = 0; });
    await page.screenshot({ path: path.join(output, name), fullPage: true });
    screenshots.push(name);
  }
  async function stage(label: string) {
    await page.waitForFunction(label => document.querySelector('.progress-step.active .step-label')?.textContent === label, label);
  }
  const primary = await submit();
  await stage('准备环境');
  assert.equal(await page.locator('[data-solving-clock]').innerText(), '尚未开始');
  const before = await page.locator('[data-total-clock]').innerText();
  await page.waitForFunction(before => document.querySelector('[data-total-clock]')?.textContent !== before, before);
  assert.equal(await page.locator('[data-solving-clock]').innerText(), '尚未开始');
  await screenshot('desktop-preparing.png');
  mark('Mathlib preparation has a live total clock and leaves the solving clock unstarted');

  const queued = await submit();
  await stage('排队');
  assert.equal(controls.has(queued.id), false);
  await page.locator('[data-action="cancel"]').click();
  await page.locator('.result-banner').filter({ hasText: '运行已取消' }).waitFor();
  assert.equal(await page.locator('.progress-step.skipped').count(), 3);
  assert.equal(controls.has(queued.id), false);
  await page.locator(`[data-run-id="${primary.id}"]`).click();
  await stage('准备环境');
  mark('queued cancellation skips all unexecuted phases and never starts a worker');

  const control = controls.get(primary.id)!;
  control.progress('solve_started');
  for (let index = 0; index < 210; index++) control.progress('worker_activity');
  await stage('构造证明');
  await page.waitForFunction(() => !['尚未开始', '00:00', '--:--', ''].includes(document.querySelector('[data-solving-clock]')?.textContent ?? ''));
  control.progress('evaluation_started');
  await stage('独立验收');
  const solvingTime = await page.locator('[data-solving-clock]').innerText();
  await page.reload();
  await page.locator('#submit-run:enabled').waitFor();
  await page.locator(`[data-run-id="${primary.id}"]`).click();
  await stage('独立验收');
  assert.equal(await page.locator('[data-solving-clock]').innerText(), solvingTime);
  const stored = await page.evaluate(async id => (await (await fetch(`/api/runs/${id}`)).json()).run as WebRun, primary.id);
  assert.equal(stored.events.some(event => event.type === 'solve_started'), false);
  assert.ok(stored.timings?.preparing && stored.timings.solving && stored.timings.evaluating);
  mark('phase clocks survive 200-event rotation and page reload; evaluation freezes solving time');

  const proof = primary.source.replace('by sorry', 'by ring');
  assert.notEqual(proof, primary.source);
  control.finish({ status: 'evaluated_passed', proof, report: { status: 'evaluated_passed', fixture: true, environment: 'mathlib' } });
  await page.locator('.result-banner.passed').waitFor();
  await page.locator('[data-action="cancel"]').waitFor({ state: 'hidden' });
  await page.waitForFunction(() => document.querySelector('.facts')?.textContent?.includes('结束时间'));
  assert.equal(await page.locator('.progress-step.done').count(), 4);
  const completedTime = await page.locator('[data-total-clock]').innerText();
  await page.waitForTimeout(1100);
  assert.equal(await page.locator('[data-total-clock]').innerText(), completedTime);
  await screenshot('desktop-completed.png');
  mark('completed phase clocks freeze and successful acceptance remains explicit');

  await page.locator('#detail-tab-source').click();
  assert.equal(await page.locator('#detail-panel .code-scroll code').textContent(), proof);
  await page.locator('[data-action="copy-source"]').click();
  assert.equal(await page.evaluate(() => navigator.clipboard.readText()), proof);
  await page.locator('[data-source-view="input"]').click();
  assert.equal(await page.locator('#detail-panel .code-scroll code').textContent(), primary.source);
  await page.locator('[data-action="copy-source"]').click();
  assert.equal(await page.evaluate(() => navigator.clipboard.readText()), primary.source);
  await page.locator('[data-source-view="proof"]').click();
  const download = page.waitForEvent('download');
  await page.locator('[data-action="download-proof"]').click();
  const downloaded = await download;
  assert.equal(await fs.readFile((await downloaded.path())!, 'utf8'), proof);
  await screenshot('desktop-proof.png');
  mark('proof and immutable input switch independently; copy and Lean download match the displayed proof');

  await page.locator('#environment').selectOption('standard');
  await page.locator('#task').fill('Changed draft');
  await page.locator('#api-key').fill(credential);
  await page.locator('[data-action="reuse-run"]').click();
  assert.equal(await page.locator('#environment').inputValue(), 'mathlib');
  assert.equal(await page.locator('#source').inputValue(), primary.source);
  assert.equal(await page.locator('#task').inputValue(), task);
  assert.equal(await page.locator('#max-turns').inputValue(), '3');
  assert.equal(await page.locator('#max-seconds').inputValue(), '90');
  assert.equal(await page.locator('#workers').inputValue(), '2');
  assert.equal(await page.locator('input[name="coordination"]:checked').inputValue(), 'independent');
  assert.equal(await page.locator('#api-key').inputValue(), '');
  assert.equal(await page.locator('#api-key').getAttribute('type'), 'password');
  assert.equal(await page.locator('#template').inputValue(), '');
  assert.equal(received.length, 1);
  assert.equal(await page.locator('#run-count').innerText(), '2');
  mark('reuse restores original task, environment and budget, clears the key and does not submit a run');

  const requestsBeforeEditing = creationRequests;
  await page.locator('#template').selectOption('polynomial');
  const imported = 'import Mathlib\r\n\r\ntheorem imported_sum (x : ℝ) : x + 0 = x := by\r\n  sorry\r\n';
  await page.locator('#source-file').setInputFiles({ name: 'sample.LEAN', mimeType: 'text/plain', buffer: Buffer.from(imported) });
  await page.waitForFunction(source => (document.querySelector('#source') as HTMLTextAreaElement).value === source.replace(/\r\n/g, '\n'), imported);
  assert.equal(await page.locator('#template').inputValue(), '');
  assert.equal(await page.locator('#environment').inputValue(), 'mathlib');
  assert.equal(await page.locator('#task').inputValue(), '保留原题声明，补全 Lean 证明并通过独立验收。');
  const importedDraft = await page.locator('#source').inputValue();
  await page.locator('#task').fill('自定义导入任务');
  await page.locator('#source-file').setInputFiles({ name: 'again.lean', mimeType: 'text/plain', buffer: Buffer.from(imported) });
  await page.locator('#toast').filter({ hasText: 'Lean 文件已载入' }).waitFor();
  assert.equal(await page.locator('#task').inputValue(), '自定义导入任务');
  for (const file of [{ name: 'wrong.txt', buffer: Buffer.from('not Lean') }, { name: 'large.lean', buffer: Buffer.alloc(32 * 1024 + 1, 'a') }]) {
    await page.locator('#source-file').setInputFiles({ ...file, mimeType: 'text/plain' });
    await page.locator('#source-error').waitFor();
    assert.equal(await page.locator('#source').inputValue(), importedDraft);
  }
  await page.evaluate(() => {
    const original = File.prototype.arrayBuffer;
    File.prototype.arrayBuffer = async function () {
      File.prototype.arrayBuffer = original;
      const data = await original.call(this);
      await new Promise<void>(resolve => { (window as unknown as { releaseImport: () => void }).releaseImport = resolve; });
      return data;
    };
  });
  await page.locator('#source-file').setInputFiles({ name: 'late.lean', mimeType: 'text/plain', buffer: Buffer.from(imported) });
  await page.waitForFunction(() => typeof (window as unknown as { releaseImport?: () => void }).releaseImport === 'function');
  const newerDraft = importedDraft + '\n-- Updated during file read';
  await page.locator('#source').fill(newerDraft);
  await page.evaluate(() => (window as unknown as { releaseImport: () => void }).releaseImport());
  await page.locator('#toast').filter({ hasText: '草稿已变化，未导入文件' }).waitFor();
  assert.equal(await page.locator('#source').inputValue(), newerDraft);
  mark('Lean import stays local, preserves environment and custom task, rejects invalid files and cannot overwrite a newer draft');

  await page.locator('#expand-source').click();
  await page.locator('#source-editor[open]').waitFor();
  assert.equal(await page.locator('#expanded-source').evaluate(node => node === document.activeElement), true);
  await page.locator('#expanded-source').fill('discarded');
  await page.locator('#cancel-editor').click();
  assert.equal(await page.locator('#source').inputValue(), newerDraft);
  await page.locator('#expand-source').click();
  await page.locator('#expanded-source').fill('discarded by Escape');
  await page.keyboard.press('Escape');
  await page.locator('#source-editor[open]').waitFor({ state: 'hidden' });
  assert.equal(await page.locator('#source').inputValue(), newerDraft);
  assert.equal(await page.locator('#expand-source').evaluate(node => node === document.activeElement), true);
  await page.locator('#expand-source').click();
  await page.locator('#expanded-source').fill(' ');
  await page.locator('#apply-editor').click();
  await page.locator('#editor-error').waitFor();
  await page.locator('#expanded-source').fill('a'.repeat(32 * 1024 + 1));
  await page.locator('#apply-editor').click();
  assert.ok((await page.locator('#editor-error').innerText()).includes('大小'));
  assert.equal(await page.locator('#source').inputValue(), newerDraft);
  const edited = newerDraft + '\n-- Applied in expanded editor';
  await page.locator('#expanded-source').fill(edited);
  await screenshot('desktop-source-editor.png');
  await page.locator('#apply-editor').click();
  assert.equal(await page.locator('#source').inputValue(), edited);
  assert.equal(creationRequests, requestsBeforeEditing);
  assert.equal(await page.locator('#api-key').inputValue(), '');
  await page.locator('[data-action="reuse-run"]').click();
  mark('expanded editing applies atomically, validates size and restores focus; Cancel and Escape preserve the composer');

  await page.locator('#environment').selectOption('standard');
  await page.locator('#template').selectOption('addition');
  await page.locator('#run-filter').selectOption('error');
  await page.locator('#run-search').fill('not-a-current-run');
  const incomplete = await submit();
  assert.equal(await page.locator('#run-filter').inputValue(), 'all');
  assert.equal(await page.locator('#run-search').inputValue(), '');
  await stage('准备环境');
  controls.get(incomplete.id)!.progress('solve_started');
  controls.get(incomplete.id)!.finish({ status: 'incomplete', proof: incomplete.source,
    report: { status: 'incomplete', fixture: true, environment: 'standard' } });
  await page.locator('.result-banner.warning').waitFor();
  assert.equal(await page.locator('.progress-step').nth(3).getAttribute('class'), 'progress-step skipped');
  assert.equal(await page.locator('.result-banner.passed').count(), 0);
  await page.locator('#detail-tab-source').click();
  assert.equal(await page.locator('[data-source-view="proof"]').innerText(), '候选源码');
  mark('an incomplete standard-library attempt stays unaccepted and leaves evaluation unexecuted');

  await page.locator('#run-filter').selectOption('passed');
  assert.equal(await page.locator('[data-run-id]').count(), 1);
  assert.equal(await page.locator('#run-count').innerText(), '1/3');
  assert.equal(await page.locator('[data-run-id]').getAttribute('data-run-id'), primary.id);
  assert.ok((await page.locator('.detail-identifier').innerText()).includes(incomplete.id));
  await page.locator('#run-search').fill(`MATHLIB ${primary.model.toUpperCase()}`);
  assert.equal(await page.locator('[data-run-id]').count(), 1);
  await page.locator('#run-search').fill('no-matching-run');
  await page.locator('[data-clear-filters]').waitFor();
  assert.equal(await page.locator('[data-run-id]').count(), 0);
  await page.locator('#clear-run-search').click();
  assert.equal(await page.locator('#run-filter').inputValue(), 'passed');
  assert.equal(await page.locator('[data-run-id]').count(), 1);
  await page.locator('#run-search').fill('no-matching-run');
  await page.locator('[data-clear-filters]').click();
  assert.equal(await page.locator('#run-filter').inputValue(), 'all');
  assert.equal(await page.locator('[data-run-id]').count(), 3);
  await page.locator('#run-filter').selectOption('unproved');
  await page.locator(`[data-run-id="${incomplete.id}"]`).click();
  await page.keyboard.press('ArrowDown');
  assert.equal(await page.locator('.run-row.selected').getAttribute('data-run-id'), incomplete.id);
  await page.locator('#run-filter').selectOption('cancelled');
  assert.equal(await page.locator('[data-run-id]').getAttribute('data-run-id'), queued.id);
  await page.locator('#run-filter').selectOption('all');
  await page.locator('[data-run-id]').first().focus();
  await page.keyboard.press('End');
  assert.equal(await page.locator('.run-row.selected').getAttribute('data-run-id'), primary.id);
  mark('history combines status and text, retains hidden selection, distinguishes accepted results and navigates only filtered rows');

  await page.locator(`[data-run-id="${primary.id}"]`).click();
  await page.locator('.result-banner.passed').waitFor();
  const widths = [1440, 1250, 1024, 851, 850, 375, 320];
  for (const width of widths) {
    const height = width > 850 ? 640 : 812;
    await page.setViewportSize({ width, height });
    if (width <= 850) await page.locator('#mobile-compose').click();
    assert.equal(await page.evaluate(() => document.documentElement.scrollWidth <= innerWidth), true, `compose overflow at ${width}`);
    if (width > 850) {
      const submit = await page.locator('#submit-run').boundingBox();
      assert.ok(submit && submit.y >= 0 && submit.y + submit.height <= height, `submit outside ${width}x${height}`);
      assert.equal(await page.evaluate(() => document.documentElement.scrollHeight <= innerHeight), true, `desktop page scrolls at ${width}`);
    } else {
      await page.locator('#mobile-runs').click();
      const selected = await page.locator('.run-row.selected').boundingBox();
      assert.ok(selected && selected.x >= 0 && selected.x + selected.width <= width, `selected history item hidden at ${width}`);
    }
    assert.equal(await page.evaluate(() => document.documentElement.scrollWidth <= innerWidth), true, `detail overflow at ${width}`);
    const positions = await page.locator('.step-label').evaluateAll(labels => labels.map(label => {
      const rect = label.getBoundingClientRect(); return { left: rect.left, right: rect.right };
    }));
    positions.slice(1).forEach((position, index) => assert.ok(position.left >= positions[index].right, `step labels overlap at ${width}`));
    await page.locator('#detail-tab-source').click();
    assert.equal(await page.evaluate(() => document.documentElement.scrollWidth <= innerWidth), true, `source overflow at ${width}`);
    if (width === 320) await screenshot('mobile-320-proof.png');
    await page.locator('#detail-tab-overview').click();
    if (width === 1024) await screenshot('desktop-1024-completed.png');
    if (width === 375 || width === 320) {
      await screenshot(`mobile-${width}-completed.png`);
      await page.locator('[data-action="reuse-run"]').click();
      assert.equal(await page.locator('#source').isVisible(), true);
      assert.equal(await page.locator('#api-key').inputValue(), '');
      assert.equal(await page.locator('#environment').inputValue(), 'mathlib');
      await page.locator('#expand-source').click();
      const editor = await page.locator('#source-editor').boundingBox();
      const apply = await page.locator('#apply-editor').boundingBox();
      assert.ok(editor && editor.x >= 0 && editor.x + editor.width <= width && editor.y >= 0 && editor.y + editor.height <= height);
      assert.ok(apply && apply.y >= 0 && apply.y + apply.height <= height && apply.x + apply.width <= width);
      assert.equal(await page.locator('#source-editor').evaluate(node => node.scrollWidth <= node.clientWidth), true);
      await screenshot(`mobile-${width}-source-editor.png`);
      await page.locator('#cancel-editor').click();
      await page.locator('#mobile-runs').click();
    }
  }
  assert.deepEqual(errors, []);
  assert.equal(await page.evaluate(key => JSON.stringify(localStorage).includes(key) || JSON.stringify(sessionStorage).includes(key), credential), false);
  mark('320–1440px views fit; desktop submission stays visible at 640px height; mobile reuse and source controls work');
  const report = { status: 'passed', checkedAt: new Date().toISOString(), mode: 'Real HTTP service and Chromium; controlled worker fixture. No Docker, Lean or model provider is called.',
    paidModelCalls: false, checks, widths, initialWidths, screenshots };
  await fs.writeFile(path.join(output, 'report.json'), JSON.stringify(report, null, 2) + '\n');
  console.log(`Browser report: ${path.join(output, 'report.json')}`);
} finally {
  await browser?.close();
  await service.close();
}
