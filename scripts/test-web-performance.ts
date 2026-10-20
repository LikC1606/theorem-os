#!/usr/bin/env bun
import assert from 'node:assert/strict';
import crypto from 'node:crypto';
import fs from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { chromium, type Page } from 'playwright';
import { readWebConfig } from '../apps/web/config';
import { createWebService } from '../apps/web/server';
import type { WebRunner } from '../apps/web/runner';
import type { WebResult, WebRun } from '../apps/web/shared';
import { closeSettings, fillConfig, openSettings, showArtifacts, showChat, withSettings } from './web-ui-controls';
import { freePort, startBrowser } from './web-scenario';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const output = path.join(root, 'out/web-performance');
const bundle = await fs.readFile(path.join(root, 'out/web/app.js')).catch(() => { throw new Error('Run bun run build:web before the performance check.'); });
await fs.mkdir(output, { recursive: true });
const port = await freePort();
const origin = `http://127.0.0.1:${port}`;
const credential = `sk-theoremos-performance-fixture-${crypto.randomUUID()}`;
type Control = { progress(message: string): void; artifact(source: string): void; finish(result: WebResult): void };
const controls = new Map<string, Control>();
const runner: WebRunner = {
  async readiness() { return { ready: true, message: 'Local performance fixture' }; },
  async run(input, send, signal) {
    await new Promise<void>((resolve, reject) => {
      const cleanup = () => { controls.delete(input.id); signal.removeEventListener('abort', abort); };
      const abort = () => { cleanup(); reject(new Error('Cancelled performance fixture')); };
      signal.addEventListener('abort', abort, { once: true });
      controls.set(input.id, {
        progress: message => send({ type: 'progress', event: 'worker_activity', message }),
        artifact: source => send({ type: 'artifact', artifact: {
          source, workerId: 'engineer', capturedAt: new Date().toISOString(), status: 'candidate',
        } }),
        finish: result => { send({ type: 'result', result }); cleanup(); resolve(); },
      });
      send({ type: 'progress', event: 'solve_started', message: 'Fixture solving started' });
      if (signal.aborted) abort();
    });
  },
};
const service = createWebService(readWebConfig({ THEOREMOS_WEB_PORT: String(port), THEOREMOS_WEB_PUBLIC_URL: origin,
  THEOREMOS_WEB_STATIC_ROOT: path.join(root, 'out/web') }), runner);
type MutationCounts = { childLists: number; added: number; removed: number; addedSubtree: number;
  removedSubtree: number; addedTextCharacters: number; characterData: number };
type Measurement = { name: string; elapsedIncludingPollingMs: number; retained: Record<string, boolean>;
  retainedText: Record<string, boolean>; mutations: Record<string, MutationCounts>;
  focus: { sameNode: boolean; before: string | null; after: string | null };
  selection: { before: string; after: string };
  scroll: { before: { top: number; left: number }; after: { top: number; left: number } } };
type ResizeMeasurement = { name: string; pointerEvents: number; synchronousWrites: number; writesAfterTwoFrames: number };
type ResizeSnapshot = { width: number; stored: string | null; resizing: boolean };
type ResizeCommitMeasurement = { name: string; targetPercent: number; immediately: ResizeSnapshot; afterTwoFrames: ResizeSnapshot };
const errors: string[] = [];
const measurements: Array<Measurement | ResizeMeasurement | ResizeCommitMeasurement> = [];
const screenshots: string[] = [];
const checks: string[] = [];
let browser: Awaited<ReturnType<typeof chromium.launch>> | undefined;
let page: Page | undefined;
let apiWrites = 0;
const mark = (check: string) => { checks.push(check); console.log(`PASS ${check}`); };

async function begin(page: Page, name: string, selectors: Record<string, string>, scrollSelector: string) {
  await page.evaluate(({ name, selectors, scrollSelector }) => {
    const scope = window as unknown as { __renderProbe: unknown };
    const roots = ['#run-detail', '#conversation'];
    const mutations = Object.fromEntries(roots.map(root => [root, {
      childLists: 0, added: 0, removed: 0, addedSubtree: 0, removedSubtree: 0, addedTextCharacters: 0, characterData: 0,
    }]));
    const observers = roots.map(root => {
      const observer = new MutationObserver(records => {
        const result = mutations[root]!;
        for (const record of records) {
          if (record.type === 'characterData') { result.characterData++; continue; }
          result.childLists++;
          for (const node of Array.from(record.addedNodes)) {
            result.added++;
            result.addedSubtree += 1 + (node instanceof Element ? node.querySelectorAll('*').length : 0);
            result.addedTextCharacters += node.textContent?.length ?? 0;
          }
          for (const node of Array.from(record.removedNodes)) {
            result.removed++;
            result.removedSubtree += 1 + (node instanceof Element ? node.querySelectorAll('*').length : 0);
          }
        }
      });
      observer.observe(document.querySelector(root)!, { childList: true, subtree: true, characterData: true });
      return observer;
    });
    const nodes = Object.fromEntries(Object.entries(selectors).map(([id, selector]) => [id, document.querySelector(selector)]));
    const scroll = document.querySelector<HTMLElement>(scrollSelector)!;
    scope.__renderProbe = { name, selectors, nodes, textNodes: Object.fromEntries(Object.entries(nodes).map(([id, node]) => [id, node?.firstChild])),
      mutations, observers, scrollSelector, beforeScroll: { top: scroll.scrollTop, left: scroll.scrollLeft },
      focus: document.activeElement, selection: getSelection()?.toString() ?? '', startedAt: performance.now() };
  }, { name, selectors, scrollSelector });
}

async function nextPaint(page: Page) {
  await page.evaluate(() => new Promise<void>(resolve => requestAnimationFrame(() => requestAnimationFrame(() => resolve()))));
}

async function end(page: Page): Promise<Measurement> {
  await nextPaint(page);
  const result = await page.evaluate(() => {
    type Probe = { name: string; selectors: Record<string, string>; nodes: Record<string, Element | null>; textNodes: Record<string, Node | null>;
      mutations: Record<string, MutationCounts>; observers: MutationObserver[]; scrollSelector: string;
      beforeScroll: { top: number; left: number }; focus: Element | null; selection: string; startedAt: number };
    const scope = window as unknown as { __renderProbe: Probe };
    const sample = scope.__renderProbe;
    for (const observer of sample.observers) observer.disconnect();
    const scroll = document.querySelector<HTMLElement>(sample.scrollSelector)!;
    const label = (element: Element | null) => element?.id || element?.getAttribute('aria-label') || element?.getAttribute('data-action') || element?.tagName || null;
    return { name: sample.name, elapsedIncludingPollingMs: Math.round(performance.now() - sample.startedAt),
      retained: Object.fromEntries(Object.entries(sample.selectors).map(([id, selector]) => [id,
        sample.nodes[id] !== null && sample.nodes[id] === document.querySelector(selector)])),
      retainedText: Object.fromEntries(Object.entries(sample.selectors).map(([id, selector]) => [id,
        sample.textNodes[id] !== null && sample.textNodes[id] === document.querySelector(selector)?.firstChild])),
      mutations: sample.mutations, focus: { sameNode: sample.focus === document.activeElement,
        before: label(sample.focus), after: label(document.activeElement) }, selection: { before: sample.selection, after: getSelection()?.toString() ?? '' },
      scroll: { before: sample.beforeScroll, after: { top: scroll.scrollTop, left: scroll.scrollLeft } } };
  });
  measurements.push(result);
  console.log(JSON.stringify(result));
  return result;
}

function retains(sample: Measurement, names: string[], textNames: string[] = []) {
  for (const name of names) assert.equal(sample.retained[name], true, `${sample.name} replaced ${name}`);
  for (const name of textNames) assert.equal(sample.retainedText[name], true, `${sample.name} replaced the unchanged ${name} text node`);
  assert.equal(sample.focus.sameNode, true, `${sample.name} replaced the focused element`);
  assert.deepEqual(sample.scroll.after, sample.scroll.before, `${sample.name} moved the reading position`);
}

async function sourceMatches(page: Page, selector: string, expected: string) {
  await page.waitForFunction(({ selector, expected }) => document.querySelector(selector)?.textContent === expected, { selector, expected });
}

function listedActivity(page: Page, message: string) {
  return page.waitForResponse(async response => {
    if (new URL(response.url()).pathname !== '/api/runs' || response.request().method() !== 'GET' || response.status() !== 200) return false;
    const payload = await response.json() as { runs: WebRun[] };
    return payload.runs.some(run => run.events.some(event => event.message === message));
  });
}

async function screenshot(page: Page, name: string) {
  await page.screenshot({ path: path.join(output, name), fullPage: true });
  screenshots.push(name);
}

async function writeReport(status: 'passed' | 'failed', error?: unknown) {
  const report = { status, mode: 'Real HTTP service and Chromium with a controlled runner; no Docker, Lean or model provider is called.',
    checkedAt: new Date().toISOString(), bundleSha256: crypto.createHash('sha256').update(bundle).digest('hex'), viewport: { width: 1440, height: 900 },
    notes: ['Mutation counts include clocks and icon hydration in each observed root.', 'Elapsed timings include the polling interval and do not estimate CPU rendering time.',
      'Resize sends 80 synthetic pointermove events in one task after a real mouse pointerdown.',
      'Pointerup commits the final queued width in the same task before any animation frame.'],
    paidModelCalls: false, apiWrites, checks, measurements, screenshots, ...(error ? { error: error instanceof Error ? error.message : String(error) } : {}) };
  assert.equal(JSON.stringify(report).includes(credential), false);
  await fs.writeFile(path.join(output, 'report.json'), JSON.stringify(report, null, 2) + '\n');
}

try {
  browser = await startBrowser(service.server, port);
  const context = await browser.newContext({ viewport: { width: 1440, height: 900 } });
  page = await context.newPage();
  page.setDefaultTimeout(12_000);
  page.on('pageerror', error => errors.push(error.message));
  page.on('request', request => { if (new URL(request.url()).pathname.startsWith('/api/') && request.method() !== 'GET') apiWrites++; });
  await page.goto(origin);
  await page.locator('#submit-run:enabled').waitFor();
  const source = Array.from({ length: 150 }, (_, index) => `-- source line ${index + 1} ${'long_identifier_'.repeat(12)}`).join('\n')
    + '\n\ntheorem performance_fixture : True := by\n  sorry\n';
  await withSettings(page, async () => {
    await page.locator('#environment').selectOption('standard');
    await page.locator('#source').fill(source);
  });
  await page.locator('#task').fill('Inspect the original declaration.');
  await sourceMatches(page, '#draft-preview-code code', source);
  await page.locator('.draft-source-scroll').evaluate(scroll => { scroll.scrollTop = 120; scroll.scrollLeft = 80; });
  await page.locator('#task').focus();
  const draftNodes = { preview: '#draft-preview', heading: '.preview-heading', sourceScroll: '.draft-source-scroll', sourceCode: '#draft-preview-code code' };
  await begin(page, 'draft-task-typing-5-characters', draftNodes, '.draft-source-scroll');
  await page.locator('#task').pressSequentially(' beta', { delay: 15 });
  await page.waitForFunction(() => document.querySelector('#draft-preview-task')?.textContent?.endsWith(' beta'));
  const taskSample = await end(page);
  retains(taskSample, Object.keys(draftNodes), ['sourceCode']);
  assert.equal(taskSample.mutations['#conversation']!.childLists, 0, 'task typing must not rebuild unchanged chat icons');
  mark('Task typing keeps the unchanged source nodes, focus and both scroll positions');
  await openSettings(page);
  await page.locator('#model').focus();
  await begin(page, 'draft-model-typing-5-characters', draftNodes, '.draft-source-scroll');
  await page.locator('#model').pressSequentially('-perf', { delay: 15 });
  const model = await page.locator('#model').inputValue();
  await sourceMatches(page, '[data-preview-value="model"]', model);
  const modelSample = await end(page);
  retains(modelSample, Object.keys(draftNodes), ['sourceCode']);
  assert.equal(modelSample.mutations['#conversation']!.childLists, 0, 'model typing must not rebuild unchanged chat icons');
  mark('Model typing patches metadata without replacing the source or losing focus');
  await closeSettings(page);
  await screenshot(page, 'draft.png');

  await fillConfig(page, 'api-key', credential);
  const response = page.waitForResponse(response => new URL(response.url()).pathname === '/api/runs' && response.request().method() === 'POST');
  await page.locator('#submit-run').click();
  const posted = await response;
  assert.equal(posted.status(), 201);
  const run = (await posted.json() as { run: WebRun }).run;
  assert.ok(controls.has(run.id));
  const control = controls.get(run.id)!;
  for (let index = 0; index < 24; index++) control.progress(`Initial research step ${index + 1}`);
  const firstCandidate = run.source.replace('  sorry', '  trivial') + '\n-- Candidate version 0\n';
  control.artifact(firstCandidate);
  await sourceMatches(page, '#detail-panel .code-scroll code', firstCandidate);
  const runNodes = { detailHeading: '#run-detail > .detail-heading', detailTabs: '#run-detail > .detail-tabs',
    panel: '#detail-panel', sourceScroll: '#detail-panel .code-scroll', sourceCode: '#detail-panel .code-scroll code' };
  for (let index = 1; index <= 3; index++) {
    await page.locator('#detail-panel .code-scroll').evaluate(scroll => { scroll.scrollTop = 120; scroll.scrollLeft = 80; });
    await page.locator('#detail-panel .code-scroll').focus();
    await begin(page, `candidate-update-${index}`, runNodes, '#detail-panel .code-scroll');
    const candidate = firstCandidate.replace('version 0', `version ${index}`);
    control.artifact(candidate);
    await sourceMatches(page, '#detail-panel .code-scroll code', candidate);
    const sample = await end(page);
    retains(sample, ['detailHeading', 'detailTabs', 'panel', 'sourceScroll']);
    assert.equal(sample.mutations['#conversation']!.childLists, 0, 'candidate text updates must not rebuild unchanged chat content');
  }
  mark('Three live candidate changes preserve the detail shell, source scroller, focus and reading position');
  await screenshot(page, 'candidate.png');

  await page.waitForFunction(() => document.querySelectorAll('#conversation .timeline-event').length >= 24);
  await page.locator('#conversation [data-chat-action="source"]').focus();
  await page.locator('#conversation-scroll').evaluate(scroll => { scroll.scrollTop = 120; });
  await page.waitForFunction(() => Math.abs(document.querySelector('#conversation-scroll')!.scrollTop - 120) < 1);
  await page.evaluate(() => {
    const text = document.querySelector('#conversation .chat-message.user .message-body')!.firstChild!;
    const range = document.createRange(); range.setStart(text, 0); range.setEnd(text, 7);
    getSelection()!.removeAllRanges(); getSelection()!.addRange(range);
  });
  const eventNodes = { user: '#conversation .chat-message.user', userAttachment: '#conversation .message-attachment',
    userAttachmentIcon: '#conversation .message-attachment svg',
    assistant: '#conversation .chat-message.assistant', timeline: '#conversation .research-timeline',
    firstTimelineRow: '#conversation .timeline-event:first-child', detailHeading: '#run-detail > .detail-heading',
    sourceCode: '#detail-panel .code-scroll code' };
  Object.assign(eventNodes, Object.fromEntries(Array.from({ length: await page.locator('#conversation .timeline-event').count() }, (_, index) =>
    [`timelineRow${index + 1}`, `#conversation .timeline-event:nth-child(${index + 1})`])));
  for (let index = 1; index <= 3; index++) {
    await begin(page, `event-append-${index}`, eventNodes, '#conversation-scroll');
    const message = `Measured research update ${index}`;
    control.progress(message);
    await page.waitForFunction(message => document.querySelector('#conversation')?.textContent?.includes(message), message);
    const sample = await end(page);
    retains(sample, Object.keys(eventNodes), ['sourceCode']);
    assert.equal(sample.selection.before.length, 7);
    assert.equal(sample.selection.after, sample.selection.before, 'an event append must preserve selected text');
  }
  mark('Event appends retain old messages, timeline rows, source text, focused attachment, selection and reading position');
  const latestPosition = await page.locator('#latest-message').evaluate(button => {
    const latest = button.getBoundingClientRect();
    const input = document.querySelector('#run-form')!.getBoundingClientRect();
    const conversation = document.querySelector('#conversation-scroll')!.getBoundingClientRect();
    return { top: latest.top, bottom: latest.bottom, formTop: input.top, conversationTop: conversation.top };
  });
  assert.ok(latestPosition.top >= latestPosition.conversationTop && latestPosition.bottom < latestPosition.formTop,
    'the latest-message control must sit above preparation hints and the composer');
  await screenshot(page, 'events.png');

  await page.setViewportSize({ width: 375, height: 812 });
  await showChat(page);
  const conversation = page.locator('#conversation-scroll');
  await conversation.evaluate(scroll => { scroll.scrollTop = scroll.scrollHeight; });
  await page.waitForFunction(() => {
    const scroll = document.querySelector('#conversation-scroll')!;
    return scroll.scrollHeight - scroll.scrollTop - scroll.clientHeight < 2;
  });
  const mobileNodes = { user: '#conversation .chat-message.user', timeline: '#conversation .research-timeline' };
  await begin(page, 'mobile-hidden-bottom-follow', mobileNodes, '#conversation-scroll');
  await showArtifacts(page);
  assert.equal(await page.locator('#compose-panel').isVisible(), false);
  const followingMessage = 'Activity received while the mobile conversation follows the latest message';
  const followingList = listedActivity(page, followingMessage);
  control.progress(followingMessage);
  await followingList;
  await nextPaint(page);
  await showChat(page);
  await page.waitForFunction(message => document.querySelector('#conversation')?.textContent?.includes(message), followingMessage);
  await page.waitForFunction(() => {
    const scroll = document.querySelector('#conversation-scroll')!;
    return scroll.scrollHeight - scroll.scrollTop - scroll.clientHeight < 2;
  });
  const followingSample = await end(page);
  assert.equal(followingSample.retained.user, true);
  assert.equal(followingSample.retained.timeline, true);
  await page.locator('#latest-message').waitFor({ state: 'hidden' });
  mark('Returning to a mobile conversation that was at the bottom continues following hidden activity');
  await screenshot(page, 'mobile-following.png');

  await conversation.evaluate(scroll => { scroll.scrollTop = 120; });
  await page.waitForFunction(() => Math.abs(document.querySelector('#conversation-scroll')!.scrollTop - 120) < 1);
  await page.locator('#latest-message').waitFor();
  await begin(page, 'mobile-hidden-reading-position', mobileNodes, '#conversation-scroll');
  await showArtifacts(page);
  const readingMessage = 'Activity received while the mobile reader reviews earlier messages';
  const readingList = listedActivity(page, readingMessage);
  control.progress(readingMessage);
  await readingList;
  await nextPaint(page);
  await showChat(page);
  await page.waitForFunction(message => document.querySelector('#conversation')?.textContent?.includes(message), readingMessage);
  const readingSample = await end(page);
  assert.equal(readingSample.retained.user, true);
  assert.equal(readingSample.retained.timeline, true);
  assert.deepEqual(readingSample.scroll.after, readingSample.scroll.before, 'hidden mobile activity must retain the earlier reading position');
  await page.locator('#latest-message').waitFor();
  mark('Returning to a mobile conversation being read earlier preserves its scroll position');
  await screenshot(page, 'mobile-reading.png');
  await page.setViewportSize({ width: 1440, height: 900 });

  const separator = page.locator('#pane-resizer');
  const bounds = await separator.boundingBox();
  assert.ok(bounds);
  await page.mouse.move(bounds.x + bounds.width / 2, bounds.y + bounds.height / 2);
  await page.mouse.down();
  const resize = await page.evaluate(async () => {
    const workspace = document.querySelector<HTMLElement>('.workspace')!;
    const separator = document.querySelector<HTMLElement>('#pane-resizer')!;
    const original = CSSStyleDeclaration.prototype.setProperty;
    let writes = 0;
    CSSStyleDeclaration.prototype.setProperty = function(name, value, priority) {
      if (this === workspace.style && name === '--chat-width') writes++;
      return original.call(this, name, value, priority);
    };
    try {
      const bounds = workspace.getBoundingClientRect();
      for (let index = 0; index < 80; index++) separator.dispatchEvent(new PointerEvent('pointermove', {
        pointerId: 1, pointerType: 'mouse', buttons: 1, bubbles: true, clientX: bounds.left + bounds.width * (0.38 + index / 1000),
      }));
      const synchronousWrites = writes;
      await new Promise<void>(resolve => requestAnimationFrame(() => resolve()));
      await new Promise<void>(resolve => requestAnimationFrame(() => resolve()));
      return { name: 'resize-pointer-burst', pointerEvents: 80, synchronousWrites, writesAfterTwoFrames: writes };
    } finally { CSSStyleDeclaration.prototype.setProperty = original; }
  });
  await page.mouse.up();
  measurements.push(resize);
  console.log(JSON.stringify(resize));
  assert.equal(resize.synchronousWrites, 0, 'pointer handlers must defer layout writes to an animation frame');
  assert.ok(resize.writesAfterTwoFrames > 0 && resize.writesAfterTwoFrames <= 2, 'a pointer burst must be coalesced into frame updates');
  mark('Eighty pointer moves coalesce into frame updates instead of synchronous layout writes');

  const commitBounds = await separator.boundingBox();
  assert.ok(commitBounds);
  await page.mouse.move(commitBounds.x + commitBounds.width / 2, commitBounds.y + commitBounds.height / 2);
  await page.mouse.down();
  const commit = await page.evaluate(async () => {
    const workspace = document.querySelector<HTMLElement>('.workspace')!;
    const separator = document.querySelector<HTMLElement>('#pane-resizer')!;
    const bounds = workspace.getBoundingClientRect();
    const targetPercent = 52;
    const snapshot = (): ResizeSnapshot => ({ width: Number(separator.getAttribute('aria-valuenow')),
      stored: sessionStorage.getItem('theoremos-pane-width-v1'), resizing: document.body.classList.contains('resizing') });
    const pointer = { pointerId: 1, pointerType: 'mouse', bubbles: true, clientX: bounds.left + bounds.width * targetPercent / 100 };
    separator.dispatchEvent(new PointerEvent('pointermove', { ...pointer, buttons: 1 }));
    separator.dispatchEvent(new PointerEvent('pointerup', { ...pointer, buttons: 0 }));
    const immediately = snapshot();
    await new Promise<void>(resolve => requestAnimationFrame(() => requestAnimationFrame(() => resolve())));
    return { name: 'resize-pointerup-commits-pending-width', targetPercent, immediately, afterTwoFrames: snapshot() };
  });
  await page.mouse.up();
  measurements.push(commit);
  console.log(JSON.stringify(commit));
  assert.ok(Math.abs(commit.immediately.width - commit.targetPercent) < 0.001, 'pointerup must immediately flush the last queued width');
  assert.ok(commit.immediately.stored !== null && Math.abs(Number(commit.immediately.stored) - commit.targetPercent) < 0.001,
    'pointerup must persist the last queued width before the next frame');
  assert.equal(commit.immediately.resizing, false, 'pointerup must clear the resizing state');
  assert.deepEqual(commit.afterTwoFrames, commit.immediately, 'a stale animation frame must not undo the committed width');
  mark('Immediate pointerup commits and persists the last queued width without reverting on later frames');
  assert.deepEqual(errors, []);
  assert.equal(apiWrites, 1);
  await writeReport('passed');
  console.log(`Performance report: ${path.join(output, 'report.json')}`);
} catch (error) {
  if (page) await screenshot(page, 'failure.png').catch(() => {});
  await writeReport('failed', error);
  throw error;
} finally {
  await browser?.close();
  await service.close();
}
