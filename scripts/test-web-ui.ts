#!/usr/bin/env bun
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { chromium } from 'playwright';
import { readWebConfig, webTemplates } from '../apps/web/config';
import { createWebService } from '../apps/web/server';
import type { WebRunner } from '../apps/web/runner';
import type { WebResult, WebRun, WorkerInput } from '../apps/web/shared';
import { closeHistory, closeSettings, discardSourceEditor, fillConfig, openHistory, openSettings, selectConfig, selectHistoryRun,
  showArtifacts, showChat, withSettings } from './web-ui-controls';
import { freePort, startBrowser } from './web-scenario';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const output = path.join(root, 'out/web-ui-smoke');
await fs.access(path.join(root, 'out/web/app.js')).catch(() => { throw new Error('Run bun run build:web before the browser check.'); });
await fs.mkdir(output, { recursive: true });
await fs.rm(path.join(output, 'report.json'), { force: true });
const port = await freePort();
const origin = `http://127.0.0.1:${port}`;
const credential = `sk-theoremos-ui-fixture-${crypto.randomUUID()}`;
type Control = { progress(event: string, message?: string): void; artifact(source: string, workerId?: string): void; finish(result: WebResult): void };
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
      controls.set(input.id, {
        progress: (event, message = 'Fixture activity') => send({ type: 'progress', event, message }),
        artifact: (source, workerId = 'engineer') => send({ type: 'artifact', artifact: {
          source, workerId, capturedAt: new Date().toISOString(), status: 'candidate',
        } }),
        finish: complete,
      });
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
  browser = await startBrowser(service.server, port);
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
    await showChat(page);
    const compose = await page.evaluate(() => {
      const task = document.querySelector('#task')!.getBoundingClientRect();
      const submit = document.querySelector('#submit-run')!.getBoundingClientRect();
      const chat = document.querySelector('#compose-panel')!.getBoundingClientRect();
      const artifacts = document.querySelector('#runs-panel')!.getBoundingClientRect();
      return { overflow: document.documentElement.scrollWidth > innerWidth, task: { top: task.top, bottom: task.bottom },
        submit: { top: submit.top, bottom: submit.bottom }, chat: { left: chat.left, right: chat.right },
        artifacts: { left: artifacts.left, right: artifacts.right } };
    });
    assert.equal(compose.overflow, false, `initial composer overflows ${width}px`);
    assert.ok(compose.task.top >= 0 && compose.task.bottom <= height, `chat input is outside the initial ${width}x${height} viewport`);
    assert.ok(compose.submit.top >= 0 && compose.submit.bottom <= height, `send control is outside the initial ${width}x${height} viewport`);
    assert.equal(await page.locator('#run-settings').isVisible(), false, 'configuration must start collapsed');
    if (width > 850) {
      assert.ok(compose.chat.right <= compose.artifacts.left + 1, 'desktop chat must sit to the left of the Lean workspace');
      assert.ok(compose.chat.right - compose.chat.left >= 300, 'desktop chat must retain a readable width');
      assert.ok(compose.artifacts.right - compose.artifacts.left >= 400, 'desktop source must retain a readable width');
    } else {
      assert.equal(await page.locator('#mobile-compose').getAttribute('aria-selected'), 'true');
      assert.equal(await page.locator('#runs-panel').isVisible(), false);
    }
    await screenshot(width === 1440 ? 'desktop-initial-preview.png' : `mobile-${width}-initial.png`);
    await openSettings(page);
    const settings = await page.locator('#run-settings').boundingBox();
    assert.ok(settings && settings.x >= 0 && settings.y >= 0 && settings.x + settings.width <= width + 1
      && settings.y + settings.height <= height + 1, `settings dialog overflows ${width}x${height}`);
    assert.equal(await page.locator('#run-settings').evaluate(dialog => dialog.scrollWidth <= dialog.clientWidth), true);
    await closeSettings(page);
    assert.equal(await page.locator('#open-settings').evaluate(node => node === document.activeElement), true);
    await showArtifacts(page);
    await page.locator('#draft-preview').waitFor();
    for (const selector of ['#draft-preview', '#draft-preview .preview-source', '#draft-preview .draft-source-scroll']) {
      const bounds = await page.locator(selector).boundingBox();
      assert.ok(bounds && bounds.x >= 0 && bounds.x + bounds.width <= width + 1, `${selector} overflows initial ${width}px view`);
    }
    assert.equal(await page.evaluate(() => document.documentElement.scrollWidth <= innerWidth), true, `initial preview overflows ${width}px`);
    assert.equal(await page.locator('#draft-preview .preview-status').innerText(), '未提交');
    await assertPreviewSource();
    await screenshot(width === 1440 ? 'desktop-initial-source.png' : `mobile-${width}-initial-source.png`);
    if (width <= 850) {
      assert.equal(await page.locator('#mobile-runs').getAttribute('aria-selected'), 'true');
      assert.equal(await page.locator('#compose-panel').isVisible(), false);
    }
    await showChat(page);
  }
  await page.setViewportSize({ width: 1440, height: 900 });
  mark('desktop shows chat left and Lean source right; mobile chat/workspace tabs, first-screen sending and settings dialogs fit 1440, 375 and 320px views');

  const separator = page.locator('#pane-resizer');
  await separator.focus();
  const originalPaneWidth = Number(await separator.getAttribute('aria-valuenow'));
  await page.keyboard.press('ArrowRight');
  assert.ok(Number(await separator.getAttribute('aria-valuenow')) > originalPaneWidth);
  await page.keyboard.press('ArrowLeft');
  assert.equal(Number(await separator.getAttribute('aria-valuenow')), originalPaneWidth);
  for (const key of ['Home', 'End']) {
    await page.keyboard.press(key);
    const value = Number(await separator.getAttribute('aria-valuenow'));
    assert.equal(value, Number(await separator.getAttribute(key === 'Home' ? 'aria-valuemin' : 'aria-valuemax')));
    const panes = await page.locator('#compose-panel,#runs-panel').evaluateAll(nodes => nodes.map(node => {
      const bounds = node.getBoundingClientRect(); return { left: bounds.left, right: bounds.right, width: bounds.width };
    }));
    assert.ok(panes[0].right <= panes[1].left && panes[0].width >= 340 && panes[1].width >= 350);
  }
  await page.keyboard.press('Home');
  for (let index = 0; index < 6; index++) await page.keyboard.press('ArrowRight');
  mark('keyboard resizing changes the desktop pane width within readable limits and exposes its current value accessibly');

  const previewSource = 'namespace Preview\n\n-- α preview\ntheorem preview : True := by\n  trivial\nend Preview\n';
  const previewTask = '预览更新任务\n保留原始 Lean 声明。';
  await selectConfig(page, 'environment', 'standard');
  await fillConfig(page, 'source', previewSource);
  await page.locator('#task').fill(previewTask);
  await withSettings(page, async () => {
    await page.locator('#model').fill('fixture-preview-model');
    await page.locator('#max-turns').fill('4');
    await page.locator('#max-seconds').fill('125');
    await page.locator('#workers').fill('3');
  });
  await assertPreviewSource();
  await assertPreviewConnection();
  await page.waitForFunction(task => document.querySelector('#draft-preview')?.textContent?.includes(task), previewTask);

  const longPreviewLines = Array.from({ length: 180 }, (_, index) => index === 0
    ? `-- <img data-preview-injection src="fixture"> & ${'long Lean source '.repeat(30)}`
    : `-- source line ${index + 1}`);
  const longPreviewSource = longPreviewLines.join('\n');
  await fillConfig(page, 'source', longPreviewSource);
  await page.waitForFunction(source => document.querySelector('#draft-preview-code code')?.textContent === source,
    longPreviewLines.slice(0, 160).join('\n'));
  assert.equal(await page.locator('#source').inputValue(), longPreviewSource);
  assert.match(await page.locator('.preview-source-heading > span').innerText(), /前 160 \/ 180 行/);
  assert.equal(await page.locator('#draft-preview-code [data-preview-injection]').count(), 0, 'source markup must stay escaped');
  assert.deepEqual((await page.locator('.preview-line-numbers').textContent())?.split('\n'),
    Array.from({ length: 160 }, (_, index) => String(index + 1)));
  for (const width of initialWidths) {
    await page.setViewportSize({ width, height: width > 850 ? 900 : 812 });
    await showArtifacts(page);
    const scrolled = await page.locator('.draft-source-scroll').evaluate(scroll => {
      scroll.scrollTop = 120;
      scroll.scrollLeft = 120;
      return { top: scroll.scrollTop, left: scroll.scrollLeft, height: scroll.getBoundingClientRect().height };
    });
    assert.ok(scrolled.top > 0 && scrolled.left > 0, `long source must scroll both ways at ${width}px`);
    assert.ok(scrolled.height > 0 && scrolled.height <= (width > 850 ? 900 : 812), `preview height must stay bounded at ${width}px`);
    const model = `fixture-preview-model-${width}`;
    await fillConfig(page, 'model', model);
    await showArtifacts(page);
    await page.waitForFunction(model => document.querySelector('[data-preview-value="model"]')?.textContent === model, model);
    const afterEdit = await page.locator('.draft-source-scroll').evaluate(scroll => ({
      top: scroll.scrollTop, left: scroll.scrollLeft, height: scroll.getBoundingClientRect().height,
    }));
    assert.deepEqual(afterEdit, scrolled, `editing the model must preserve source scrolling and height at ${width}px`);
    assert.equal(await page.locator('#draft-preview-code code').textContent(), longPreviewLines.slice(0, 160).join('\n'));
    await showChat(page);
  }
  mark('long draft previews cap at 160 lines, escape source markup and preserve bounded height and both scroll positions after model edits');

  const resizedModel = 'fixture-preview-desktop-resize';
  await fillConfig(page, 'model', resizedModel);
  await page.setViewportSize({ width: 1440, height: 900 });
  await page.waitForFunction(model => document.querySelector('[data-preview-value="model"]')?.textContent === model, resizedModel);
  await assertPreviewConnection();
  mark('a draft edited in the 320px composer updates its preview when resizing directly to desktop');

  await fillConfig(page, 'source', previewSource);
  await assertPreviewSource();
  await withSettings(page, async () => {
    await page.locator('#api-key').fill(credential);
    await page.locator('#toggle-key').click();
  });
  assert.equal((await page.locator('#draft-preview').innerHTML()).includes(credential), false);
  await withSettings(page, async () => {
    for (const id of ['max-turns', 'max-seconds', 'workers']) await page.locator(`#${id}`).fill('');
  });
  assert.equal(await previewValue('budget').innerText(), '未设置');
  assert.equal(await previewValue('workers').innerText(), '未设置');
  assert.equal((await page.locator('#draft-preview').innerText()).includes('NaN'), false);
  assert.equal((await page.locator('#draft-preview').innerHTML()).includes(credential), false);
  await withSettings(page, () => page.locator('#reset-form').click());
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
  await page.locator('#submit-run').click();
  await page.locator('#run-settings[open]').waitFor();
  assert.equal(await page.locator('#api-key').evaluate(node => node === document.activeElement), true,
    'a missing API key must open settings and focus the required field');
  assert.equal(creationRequests, 0, 'incomplete settings must never create a run');
  await closeSettings(page);
  mark('draft preview mirrors source, task, model, environment and budget, handles empty numbers, excludes the API key and resets without POST requests');

  await page.locator('#task').fill('实数平方展开\n保留原始题目，使用 Mathlib 构造并验证证明。');
  const task = await page.locator('#task').inputValue();
  await withSettings(page, async () => {
    await page.locator('#max-turns').fill('3');
    await page.locator('#max-seconds').fill('90');
    await page.locator('#workers').fill('2');
    await page.locator('input[name="coordination"][value="independent"]').check();
  });
  async function submit(method: 'button' | 'enter' = 'button'): Promise<WebRun> {
    await fillConfig(page, 'api-key', credential);
    const response = page.waitForResponse(response => new URL(response.url()).pathname === '/api/runs' && response.request().method() === 'POST');
    if (method === 'enter') await page.locator('#task').press('Enter');
    else await page.locator('#submit-run').click();
    const posted = await response;
    assert.equal(posted.status(), 201);
    const payload = await posted.json() as { run: WebRun };
    assert.equal(JSON.stringify(payload).includes(credential), false);
    await page.waitForFunction(() => (document.querySelector('#api-key') as HTMLInputElement).value === '');
    assert.equal(await page.locator('#task').inputValue(), '', 'a successful send must clear the chat input');
    if ((page.viewportSize()?.width ?? 1440) <= 850) {
      assert.equal(await page.locator('#mobile-compose').getAttribute('aria-selected'), 'true', 'mobile send must retain the conversation');
      assert.equal(await page.locator('#conversation .chat-message.user .message-body').innerText(), payload.run.task);
    }
    await showArtifacts(page);
    await page.locator('#detail-tab-overview').click();
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
  await page.setViewportSize({ width: 375, height: 812 });
  await fillConfig(page, 'api-key', credential);
  await page.locator('#task').dispatchEvent('keydown', { key: 'Enter', isComposing: true, bubbles: true, cancelable: true });
  assert.equal(creationRequests, 0, 'IME confirmation must not submit a request');
  await page.locator('#task').press('Control+End');
  await page.locator('#task').press('Shift+Enter');
  assert.equal(await page.locator('#task').inputValue(), task + '\n');
  assert.equal(creationRequests, 0, 'Shift+Enter must insert a newline without submitting');
  await page.locator('#task').fill(task);
  const primary = await submit('enter');
  await page.setViewportSize({ width: 1440, height: 900 });
  mark('IME Enter and Shift+Enter never submit; Enter sends once, clears the input and keeps the mobile conversation visible');
  await stage('准备环境');
  assert.equal(await page.locator('[data-solving-clock]').innerText(), '尚未开始');
  const before = await page.locator('#detail-panel [data-total-clock]').innerText();
  await page.waitForFunction(before => document.querySelector('#detail-panel [data-total-clock]')?.textContent !== before, before);
  assert.equal(await page.locator('[data-solving-clock]').innerText(), '尚未开始');
  await screenshot('desktop-preparing.png');
  mark('Mathlib preparation has a live total clock and leaves the solving clock unstarted');

  await page.locator('#task').fill(task);
  const queued = await submit();
  await stage('排队');
  assert.equal(controls.has(queued.id), false);
  await page.locator('[data-action="cancel"]').click();
  await page.locator('.result-banner').filter({ hasText: '运行已取消' }).waitFor();
  assert.equal(await page.locator('.progress-step.skipped').count(), 3);
  assert.equal(controls.has(queued.id), false);
  await selectHistoryRun(page, primary.id);
  await page.locator('#detail-tab-overview').click();
  await stage('准备环境');
  mark('queued cancellation skips all unexecuted phases and never starts a worker');

  const control = controls.get(primary.id)!;
  control.progress('solve_started');
  const firstCandidate = primary.source.replace('by sorry', 'by\n  sorry') + '-- First live candidate\n';
  const latestCandidate = primary.source.replace('by sorry', 'by\n  ring') + '-- <img data-artifact-injection src=x>\n';
  await page.locator('#detail-tab-source').click();
  control.artifact(firstCandidate);
  await page.waitForFunction(source => document.querySelector('#detail-panel .code-scroll code')?.textContent === source, firstCandidate);
  assert.equal(await page.locator('[data-source-view="proof"]').innerText(), '候选源码');
  assert.equal(await page.locator('.source-status.verified').count(), 0);
  await page.locator('[data-source-view="input"]').click();
  control.artifact(latestCandidate, 'researcher-1');
  await page.waitForFunction(() => document.querySelector('#detail-panel .source-status')?.textContent?.includes('原始题目'));
  assert.equal(await page.locator('#detail-panel .code-scroll code').textContent(), primary.source);
  await page.locator('[data-source-view="proof"]').click();
  await page.waitForFunction(source => document.querySelector('#detail-panel .code-scroll code')?.textContent === source, latestCandidate);
  assert.equal(await page.locator('[data-artifact-injection]').count(), 0, 'live source markup must remain escaped');
  assert.ok((await page.locator('.source-status').innerText()).includes('researcher-1'));
  assert.equal(await page.locator('.source-status.verified').count(), 0);
  await page.locator('[data-action="copy-source"]').click();
  assert.equal(await page.evaluate(() => navigator.clipboard.readText()), latestCandidate);
  await screenshot('desktop-live-candidate.png');
  await page.setViewportSize({ width: 320, height: 812 });
  await showArtifacts(page);
  await screenshot('mobile-320-live-candidate.png');
  await page.setViewportSize({ width: 1440, height: 900 });
  await page.locator('#detail-tab-overview').click();
  mark('live worker snapshots update candidate Lean code without implying acceptance or changing the frozen original source');
  for (let index = 0; index < 30; index++) control.progress('worker_activity', `Research step ${index + 1}: inspect the current candidate`);
  await page.waitForFunction(() => (document.querySelectorAll('#conversation .timeline-event').length >= 30));
  const conversation = page.locator('#conversation-scroll');
  assert.equal(await conversation.evaluate(scroll => scroll.scrollHeight > scroll.clientHeight + 240), true);
  await conversation.evaluate(scroll => { scroll.scrollTop = 120; });
  await page.waitForFunction(() => Math.abs(document.querySelector('#conversation-scroll')!.scrollTop - 120) < 1);
  await page.locator('#latest-message').waitFor();
  control.progress('worker_activity', 'Research update while reading earlier activity');
  await page.waitForFunction(() => document.querySelector('#conversation')?.textContent?.includes('Research update while reading earlier activity'));
  assert.ok(Math.abs(await conversation.evaluate(scroll => scroll.scrollTop) - 120) < 1,
    'new activity must preserve the reading position while scrolled up');
  await page.locator('#latest-message').click();
  await page.waitForFunction(() => {
    const scroll = document.querySelector('#conversation-scroll')!;
    return scroll.scrollHeight - scroll.scrollTop - scroll.clientHeight < 2;
  });
  await page.locator('#latest-message').waitFor({ state: 'hidden' });
  control.progress('worker_activity', 'Research update while following the latest activity');
  await page.waitForFunction(() => document.querySelector('#conversation')?.textContent?.includes('Research update while following the latest activity'));
  await page.waitForFunction(() => {
    const scroll = document.querySelector('#conversation-scroll')!;
    return scroll.scrollHeight - scroll.scrollTop - scroll.clientHeight < 2;
  });
  mark('live activity preserves earlier reading positions; the latest-message control returns to the bottom and resumes following updates');
  for (let index = 0; index < 210; index++) control.progress('worker_activity');
  await stage('构造证明');
  await page.waitForFunction(() => !['尚未开始', '00:00', '--:--', ''].includes(document.querySelector('[data-solving-clock]')?.textContent ?? ''));
  control.progress('evaluation_started');
  await stage('独立验收');
  const solvingTime = await page.locator('[data-solving-clock]').innerText();
  await page.reload();
  await page.locator('#submit-run:enabled').waitFor();
  await selectHistoryRun(page, primary.id);
  await page.locator('#detail-tab-overview').click();
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
  control.artifact('-- Late snapshot must not override the final proof\n');
  await page.locator('[data-action="cancel"]').waitFor({ state: 'hidden' });
  await page.waitForFunction(() => document.querySelector('.facts')?.textContent?.includes('结束时间'));
  assert.equal(await page.locator('.progress-step.done').count(), 4);
  const completedTime = await page.locator('#detail-panel [data-total-clock]').innerText();
  await page.waitForTimeout(1100);
  assert.equal(await page.locator('#detail-panel [data-total-clock]').innerText(), completedTime);
  await screenshot('desktop-completed.png');
  mark('completed phase clocks freeze and successful acceptance remains explicit');

  await page.locator('#detail-tab-source').click();
  assert.equal(await page.locator('#detail-panel .code-scroll code').textContent(), proof);
  assert.equal(await page.locator('.source-status.verified').count(), 1, 'only the final accepted proof may show verified status');
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

  await selectConfig(page, 'environment', 'standard');
  await page.locator('#task').fill('Changed draft');
  await fillConfig(page, 'api-key', credential);
  await page.locator('[data-action="reuse-run"]').click();
  await closeSettings(page);
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
  await selectConfig(page, 'template', 'polynomial');
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
  await openSettings(page);
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
  await fillConfig(page, 'source', newerDraft);
  await page.evaluate(() => (window as unknown as { releaseImport: () => void }).releaseImport());
  await page.locator('#toast').filter({ hasText: '草稿已变化，未导入文件' }).waitFor();
  assert.equal(await page.locator('#source').inputValue(), newerDraft);
  mark('Lean import stays local, preserves environment and custom task, rejects invalid files and cannot overwrite a newer draft');

  await openSettings(page);
  await page.locator('#expand-source').click();
  await page.locator('#source-editor[open]').waitFor();
  assert.equal(await page.locator('#expanded-source').evaluate(node => node === document.activeElement), true);
  await page.locator('#expanded-source').fill('discarded');
  await discardSourceEditor(page);
  await page.locator('#run-settings[open]').waitFor();
  assert.equal(await page.locator('#source').inputValue(), newerDraft);
  await openSettings(page);
  await page.locator('#expand-source').click();
  await page.locator('#expanded-source').fill('discarded by Escape');
  await discardSourceEditor(page, () => page.keyboard.press('Escape'));
  await page.locator('#run-settings[open]').waitFor();
  assert.equal(await page.locator('#source').inputValue(), newerDraft);
  assert.equal(await page.locator('#expand-source').evaluate(node => node === document.activeElement), true);
  await openSettings(page);
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
  await page.locator('#run-settings[open]').waitFor();
  assert.equal(await page.locator('#source').inputValue(), edited);
  assert.equal(creationRequests, requestsBeforeEditing);
  assert.equal(await page.locator('#api-key').inputValue(), '');
  await closeSettings(page);
  await selectHistoryRun(page, primary.id);
  await page.locator('[data-action="reuse-run"]').click();
  await closeSettings(page);
  mark('expanded editing applies atomically, validates size and restores focus; Cancel and Escape preserve the composer');

  await selectConfig(page, 'environment', 'standard');
  await selectConfig(page, 'template', 'addition');
  await openHistory(page);
  await page.locator('#run-filter').selectOption('error');
  await page.locator('#run-search').fill('not-a-current-run');
  await closeHistory(page);
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

  await openHistory(page);
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
  await page.locator(`[data-run-id="${incomplete.id}"]`).focus();
  await page.keyboard.press('ArrowDown');
  assert.equal(await page.locator('.run-row.selected').getAttribute('data-run-id'), incomplete.id);
  await openHistory(page);
  await page.locator('#run-filter').selectOption('cancelled');
  assert.equal(await page.locator('[data-run-id]').getAttribute('data-run-id'), queued.id);
  await page.locator('#run-filter').selectOption('all');
  await page.locator('[data-run-id]').first().focus();
  await page.keyboard.press('End');
  assert.equal(await page.locator('.run-row.selected').getAttribute('data-run-id'), primary.id);
  mark('history combines status and text, retains hidden selection, distinguishes accepted results and navigates only filtered rows');

  await selectHistoryRun(page, primary.id);
  await page.locator('#detail-tab-overview').click();
  await page.locator('.result-banner.passed').waitFor();
  const widths = [1440, 1250, 1024, 851, 850, 375, 320];
  for (const width of widths) {
    const height = width > 850 ? 640 : 812;
    await page.setViewportSize({ width, height });
    await showChat(page);
    assert.equal(await page.evaluate(() => document.documentElement.scrollWidth <= innerWidth), true, `compose overflow at ${width}`);
    if (width > 850) {
      const submit = await page.locator('#submit-run').boundingBox();
      assert.ok(submit && submit.y >= 0 && submit.y + submit.height <= height, `submit outside ${width}x${height}`);
      assert.equal(await page.evaluate(() => document.documentElement.scrollHeight <= innerHeight), true, `desktop page scrolls at ${width}`);
    } else {
      await openHistory(page);
      const selected = await page.locator('.run-row.selected').boundingBox();
      assert.ok(selected && selected.x >= 0 && selected.x + selected.width <= width, `selected history item hidden at ${width}`);
      await closeHistory(page);
    }
    await showArtifacts(page);
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
      await openSettings(page);
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
      await page.locator('#run-settings[open]').waitFor();
      await closeSettings(page);
      await selectHistoryRun(page, primary.id);
      await page.locator('#detail-tab-overview').click();
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
