#!/usr/bin/env bun
import assert from 'node:assert/strict';
import crypto from 'node:crypto';
import fs from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { chromium, type BrowserContext, type Page } from 'playwright';
import { readWebConfig } from '../apps/web/config';
import { createWebService } from '../apps/web/server';
import type { WebRunner } from '../apps/web/runner';
import type { WebResult, WebRun } from '../apps/web/shared';
import { closeHistory, closeSettings, openHistory, openSettings, showArtifacts, showChat, withSettings } from './web-ui-controls';
import { freePort, type RequestRecord, scenarioFailure, type ScenarioSuite, startBrowser, webScenario } from './web-scenario';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const output = path.join(root, 'out/web-motion');
const bundle = await fs.readFile(path.join(root, 'out/web/app.js')).catch(() => { throw new Error('Run bun run build:web before the motion check.'); });
await fs.mkdir(output, { recursive: true });
const port = await freePort();
const origin = `http://127.0.0.1:${port}`;
const credential = `sk-theoremos-motion-fixture-${crypto.randomUUID()}`;
const source = Array.from({ length: 120 }, (_, index) => `-- line ${index + 1} ${'long_identifier_'.repeat(12)}`).join('\n')
  + '\n\ntheorem motion_fixture : True := by\n  sorry\n';
type Control = { progress(message: string): void; artifact(value: string): void; finish(result: WebResult): void };
const controls = new Map<string, Control>();
const runner: WebRunner = {
  async readiness() { return { ready: true, message: 'Local motion fixture' }; },
  async run(input, send, signal) {
    await new Promise<void>((resolve, reject) => {
      const cleanup = () => { controls.delete(input.id); signal.removeEventListener('abort', abort); };
      const abort = () => { cleanup(); reject(new Error('Cancelled motion fixture')); };
      signal.addEventListener('abort', abort, { once: true });
      controls.set(input.id, {
        progress: message => send({ type: 'progress', event: 'worker_activity', message }),
        artifact: value => send({ type: 'artifact', artifact: {
          source: value, workerId: 'engineer', capturedAt: new Date().toISOString(), status: 'candidate',
        } }),
        finish: result => { send({ type: 'result', result }); cleanup(); resolve(); },
      });
      send({ type: 'progress', event: 'solve_started', message: 'Motion fixture solving started' });
      if (signal.aborted) abort();
    });
  },
};
const service = createWebService(readWebConfig({ THEOREMOS_WEB_PORT: String(port), THEOREMOS_WEB_PUBLIC_URL: origin,
  THEOREMOS_WEB_STATIC_ROOT: path.join(root, 'out/web'), THEOREMOS_WEB_CONCURRENCY: '8' }), runner);
type MotionStart = { node: Element; kind: string };
type MotionProbe = { starts: MotionStart[]; observer: MutationObserver };
type MotionEntry = { kind: string; target: string; sequence: string | null; message: string | null; panel: boolean; code: boolean; status: boolean; dialog: boolean };
type Harness = { page: Page; context: BrowserContext; requests: RequestRecord[]; runIds: string[] };
type ReadingProbe = { nodes: Record<string, Element | null>; text: Node | null; focus: Element | null; selection: string;
  scrolls: Record<string, { node: Element; top: number; left: number }>; sequences: string[] };
type Check = { name: string; elapsedMs: number; requests: RequestRecord[] };
const checks: Check[] = [];
const samples: Array<{ name: string; entries: MotionEntry[] }> = [];
const screenshots: string[] = [];
let browser: Awaited<ReturnType<typeof chromium.launch>> | undefined;
const suite: ScenarioSuite = { origin, output, checks, failedScenario: '' };

async function nextPaint(page: Page) {
  await page.evaluate(() => new Promise<void>(resolve => {
    requestAnimationFrame(() => requestAnimationFrame(() => resolve()));
  }));
}

async function settled(page: Page) {
  await page.waitForFunction(() => !document.querySelector('[data-motion]'));
  await nextPaint(page);
  assert.equal(await page.locator('[data-motion]').count(), 0, 'motion markers must be removed after completion');
}

async function offset(page: Page) {
  await nextPaint(page);
  return page.evaluate(() => (window as unknown as { __motionProbe: MotionProbe }).__motionProbe.starts.length);
}

async function entries(page: Page, since: number): Promise<MotionEntry[]> {
  await nextPaint(page);
  return page.evaluate(since => (window as unknown as { __motionProbe: MotionProbe }).__motionProbe.starts.slice(since).map(({ node, kind }) => ({
    kind, target: node.id || node.getAttribute('class') || node.tagName,
    sequence: node.closest<HTMLElement>('.timeline-event')?.dataset.sequence ?? null,
    message: node.closest('.chat-message')?.classList.contains('user') ? 'user' : node.closest('.chat-message') ? 'assistant' : null,
    panel: node.id === 'detail-panel',
    code: Boolean(node.closest('.source-code-grid,.draft-source-scroll,.diff-scroll') || node.querySelector('.source-code-grid,.draft-source-scroll,.diff-scroll')),
    status: Boolean(node.closest('.detail-statusline .badge,.chat-result') || node.matches('.detail-statusline .badge,.chat-result')),
    dialog: node instanceof HTMLDialogElement,
  })), since);
}

async function record(page: Page, name: string, since: number) {
  const value = await entries(page, since);
  samples.push({ name, entries: value });
  return value;
}

async function screenshot(page: Page, name: string) {
  await page.screenshot({ path: path.join(output, name), fullPage: true });
  screenshots.push(name);
}

async function rememberReading(page: Page) {
  await page.locator('#conversation [data-chat-action="source"]').focus();
  await page.evaluate(() => {
    const conversation = document.querySelector('#conversation-scroll')!;
    const code = document.querySelector('#detail-panel .code-scroll')!;
    conversation.scrollTop = 120; code.scrollTop = 120; code.scrollLeft = 80;
    const text = document.querySelector('#conversation .chat-message.user .message-body')!.firstChild!;
    const range = document.createRange(); range.setStart(text, 0); range.setEnd(text, 7);
    getSelection()!.removeAllRanges(); getSelection()!.addRange(range);
  });
  await nextPaint(page);
  await page.evaluate(() => {
    const selectors = { user: '#conversation .chat-message.user', attachment: '#conversation [data-chat-action="source"]',
      assistant: '#conversation .chat-message.assistant', timeline: '#conversation .research-timeline',
      code: '#detail-panel .code-scroll code', panel: '#detail-panel' };
    const nodes = Object.fromEntries(Object.entries(selectors).map(([name, selector]) => [name, document.querySelector(selector)]));
    const scrolls = Object.fromEntries(['#conversation-scroll', '#detail-panel .code-scroll'].map(selector => {
      const node = document.querySelector(selector)!; return [selector, { node, top: node.scrollTop, left: node.scrollLeft }];
    }));
    const rows = Array.from(document.querySelectorAll<HTMLElement>('#conversation .timeline-event'));
    for (const row of rows) nodes[`event-${row.dataset.sequence}`] = row;
    (window as unknown as { __readingProbe: ReadingProbe }).__readingProbe = { nodes, text: nodes.code?.firstChild ?? null,
      focus: document.activeElement, selection: getSelection()?.toString() ?? '', scrolls, sequences: rows.map(row => row.dataset.sequence!) };
  });
}

async function readingIntact(page: Page, sameCodeText = true) {
  const result = await page.evaluate(() => {
    const before = (window as unknown as { __readingProbe: ReadingProbe }).__readingProbe;
    return { retained: Object.fromEntries(Object.entries(before.nodes).map(([name, node]) => [name, Boolean(node?.isConnected)])),
      sameText: before.nodes.code?.firstChild === before.text, sameFocus: before.focus === document.activeElement,
      selectionBefore: before.selection, selectionAfter: getSelection()?.toString() ?? '',
      scrolls: Object.fromEntries(Object.entries(before.scrolls).map(([name, value]) => [name,
        { before: { top: value.top, left: value.left }, after: { top: value.node.scrollTop, left: value.node.scrollLeft } }])) };
  });
  for (const [name, retained] of Object.entries(result.retained)) assert.equal(retained, true, `${name} was replaced during motion`);
  if (sameCodeText) assert.equal(result.sameText, true, 'unchanged code text must survive motion');
  assert.equal(result.sameFocus, true, 'motion must preserve focus');
  assert.equal(result.selectionBefore.length, 7);
  assert.equal(result.selectionAfter, result.selectionBefore, 'motion must preserve selected text');
  for (const [name, value] of Object.entries(result.scrolls)) assert.deepEqual(value.after, value.before, `${name} moved during motion`);
}

async function immediate(page: Page, reduced = true) {
  const result = await page.evaluate(() => {
    const starts = (window as unknown as { __motionProbe: MotionProbe }).__motionProbe.starts;
    const nodes = Array.from(new Set([...starts.map(item => item.node), ...Array.from(document.querySelectorAll('.chat-message,.timeline-event,#detail-panel,dialog[open]'))]))
      .filter(node => node.isConnected && node.getClientRects().length);
    return { marked: document.querySelectorAll('[data-motion]').length,
      cssAnimations: document.getAnimations().filter(animation => animation.playState === 'running').length,
      unfinished: nodes.filter(node => {
        const style = getComputedStyle(node);
        return Number(style.opacity) < 0.999 || (style.transform !== 'none' && style.transform !== 'matrix(1, 0, 0, 1, 0, 0)');
      }).map(node => node.id || node.getAttribute('class') || node.tagName) };
  });
  assert.equal(result.marked, 0, 'reduced or inactive pages must have no active marked tweens');
  if (reduced) assert.equal(result.cssAnimations, 0, 'reduced motion must have no running CSS animations');
  assert.deepEqual(result.unfinished, [], 'cancelled motion must leave its content fully visible');
}

async function fits(page: Page, dialog?: string) {
  const result = await page.evaluate(dialog => {
    const bounds = dialog ? document.querySelector<HTMLElement>(dialog)!.getBoundingClientRect() : undefined;
    const element = dialog ? document.querySelector<HTMLElement>(dialog)! : document.documentElement;
    return { width: innerWidth, height: innerHeight, pageOverflow: document.documentElement.scrollWidth > innerWidth,
      localOverflow: element.scrollWidth > element.clientWidth,
      bounds: bounds ? { left: bounds.left, top: bounds.top, right: bounds.right, bottom: bounds.bottom } : undefined };
  }, dialog);
  assert.equal(result.pageOverflow, false, `${result.width}px page overflows during motion`);
  assert.equal(result.localOverflow, false, `${dialog ?? 'page'} overflows during motion`);
  if (result.bounds) assert.ok(result.bounds.left >= -1 && result.bounds.top >= -1 && result.bounds.right <= result.width + 1
    && result.bounds.bottom <= result.height + 1, `${dialog} leaves the ${result.width}x${result.height} viewport during motion`);
}

async function createRun(h: Harness) {
  await withSettings(h.page, async () => {
    await h.page.locator('#environment').selectOption('standard');
    await h.page.locator('#source').fill(source);
    await h.page.locator('#api-key').fill(credential);
  });
  await h.page.locator('#task').fill('Inspect the original motion fixture declaration.');
  const posted = h.page.waitForResponse(response => new URL(response.url()).pathname === '/api/runs' && response.request().method() === 'POST');
  await h.page.locator('#submit-run').click();
  const response = await posted;
  assert.equal(response.status(), 201);
  const { run } = await response.json() as { run: WebRun };
  h.runIds.push(run.id);
  await h.page.locator('#conversation .chat-message.user').waitFor();
  assert.ok(controls.has(run.id));
  await h.page.waitForFunction(() => document.querySelector('#conversation')?.textContent?.includes('Motion fixture solving started'));
  return { run, control: controls.get(run.id)! };
}

async function activity(page: Page, control: Control, message: string) {
  control.progress(message);
  await page.waitForFunction(message => Array.from(document.querySelectorAll('#conversation .timeline-text>span'))
    .some(node => node.textContent === message), message);
  return page.locator('#conversation .timeline-event').filter({ hasText: message });
}

const scenario = (name: string, run: (h: Harness) => Promise<void>, reducedMotion: 'reduce' | 'no-preference' = 'no-preference') =>
  webScenario<Harness>(browser!, suite, name, run, {
    context: { viewport: { width: 1440, height: 900 }, reducedMotion },
    init: context => context.addInitScript(() => {
      const starts: MotionStart[] = [];
      const observer = new MutationObserver(records => {
        for (const [index, mutation] of records.entries()) {
          if (mutation.oldValue !== null || !(mutation.target instanceof Element)) continue;
          // Later oldValue records retain a short-lived marker even if it was removed in the same task.
          const following = records.slice(index + 1).find(record => record.target === mutation.target);
          const kind = following ? following.oldValue : mutation.target.getAttribute('data-motion');
          if (kind) starts.push({ node: mutation.target, kind });
        }
      });
      observer.observe(document, { subtree: true, attributes: true, attributeFilter: ['data-motion'], attributeOldValue: true });
      (window as unknown as { __motionProbe: MotionProbe }).__motionProbe = { starts, observer };
    }),
    harness: (page, context) => ({ page, context, requests: [], runIds: [] }), routes: 'observe',
    open: async ({ page }) => { await page.goto(origin); await page.locator('#submit-run:enabled').waitFor(); await settled(page); },
    timeout: { label: 'Motion', seconds: 40 }, failure: { capture: screenshot },
    cleanup: ({ runIds }) => { for (const id of runIds) controls.get(id)?.finish({ status: 'incomplete', proof: source, report: { reason: 'Local fixture cleanup' } }); },
  });

async function writeReport(status: 'passed' | 'failed', error?: unknown) {
  const report = { status, checkedAt: new Date().toISOString(), bundleSha256: crypto.createHash('sha256').update(bundle).digest('hex'),
    mode: 'Real HTTP service and Chromium with a controlled runner; no Docker, Lean or model provider is called.',
    notes: ['data-motion marks the full lifetime of each application tween.', 'Visibility and page lifecycle checks dispatch controlled browser lifecycle events.',
      'Tests assert motion lifecycle and preserved interaction state, not precise frame timing.'], paidModelCalls: false, checks, samples, screenshots,
    ...(error ? scenarioFailure(suite, error) : {}) };
  assert.equal(JSON.stringify(report).includes(credential), false);
  await fs.writeFile(path.join(output, 'report.json'), JSON.stringify(report, null, 2) + '\n');
}

try {
  browser = await startBrowser(service.server, port);

  await scenario('New conversation messages animate once; ordinary list polling never replays their entrance', async h => {
    const since = await offset(h.page);
    await createRun(h);
    await settled(h.page);
    const entered = await record(h.page, 'conversation-entrance', since);
    for (const role of ['user', 'assistant']) assert.equal(entered.filter(entry => entry.message === role && entry.target.split(' ').includes('chat-message')).length,
      1, `${role} message must enter exactly once`);
    const afterEntrance = await offset(h.page);
    const listed = h.page.waitForResponse(response => new URL(response.url()).pathname === '/api/runs' && response.request().method() === 'GET');
    await listed; await nextPaint(h.page); await settled(h.page);
    assert.deepEqual(await record(h.page, 'unchanged-poll', afterEntrance), [], 'an unchanged poll replayed an entrance or status animation');
    assert.equal(h.requests.filter(request => request.method === 'POST').length, 1);
    await screenshot(h.page, 'desktop-conversation.png');
  });

  await scenario('Following animates only new activity; history reading keeps messages, focus, selection and both reading positions intact', async h => {
    const { control } = await createRun(h);
    for (let index = 0; index < 28; index++) control.progress(`Existing research step ${index + 1}`);
    await h.page.waitForFunction(() => document.querySelectorAll('#conversation .timeline-event').length >= 28);
    await settled(h.page);
    const oldSequences = await h.page.locator('#conversation .timeline-event').evaluateAll(nodes => nodes.map(node => (node as HTMLElement).dataset.sequence!));
    const since = await offset(h.page);
    const row = await activity(h.page, control, 'New isolated motion event');
    const sequence = await row.getAttribute('data-sequence');
    await settled(h.page);
    const entered = await record(h.page, 'appended-event', since);
    assert.equal(entered.filter(entry => entry.sequence === sequence).length, 1, 'the new followed event must enter once');
    assert.equal(entered.some(entry => entry.sequence && oldSequences.includes(entry.sequence)), false, 'an old event replayed');
    assert.equal(entered.some(entry => entry.message && !entry.sequence), false, 'an existing message replayed');
    assert.equal(entered.some(entry => entry.code || entry.panel), false, 'appending activity animated the source');
    await rememberReading(h.page);
    const readingSince = await offset(h.page);
    await activity(h.page, control, 'New activity while reading earlier steps');
    await settled(h.page); await readingIntact(h.page);
    assert.deepEqual(await record(h.page, 'appended-during-history-reading', readingSince), [], 'appending during history reading scheduled motion');
    await screenshot(h.page, 'desktop-reading.png');
  });

  await scenario('Explicit non-source tabs transition; live candidate refresh preserves the source and does not animate code', async h => {
    const { control } = await createRun(h);
    await settled(h.page);
    for (const tab of ['overview', 'report', 'events']) {
      const since = await offset(h.page);
      await h.page.locator(`#detail-tab-${tab}`).click();
      await settled(h.page);
      const entered = await record(h.page, `panel-${tab}`, since);
      assert.ok(entered.some(entry => entry.panel), `${tab} did not receive a panel transition`);
      assert.equal(entered.some(entry => entry.code), false, `${tab} animated source content`);
    }
    await h.page.locator('#detail-tab-source').click(); await settled(h.page);
    await h.page.locator('#detail-panel .code-scroll').evaluate(scroll => { scroll.scrollTop = 120; scroll.scrollLeft = 80; });
    await h.page.locator('#detail-panel .code-scroll').focus();
    const before = await h.page.locator('#detail-panel .code-scroll').evaluate(scroll => {
      (window as unknown as { __sourceNode: Element }).__sourceNode = scroll;
      return { top: scroll.scrollTop, left: scroll.scrollLeft };
    });
    const since = await offset(h.page);
    const candidate = source.replace('  sorry', '  trivial');
    control.artifact(candidate);
    await h.page.waitForFunction(candidate => document.querySelector('#detail-panel .code-scroll code')?.textContent === candidate, candidate);
    await settled(h.page);
    const entered = await record(h.page, 'candidate-refresh', since);
    assert.equal(entered.some(entry => entry.code || entry.panel), false, 'candidate refresh animated the editor');
    const after = await h.page.locator('#detail-panel .code-scroll').evaluate(scroll => ({ top: scroll.scrollTop, left: scroll.scrollLeft,
      retained: scroll === (window as unknown as { __sourceNode: Element }).__sourceNode, focused: scroll === document.activeElement }));
    assert.deepEqual(after, { ...before, retained: true, focused: true });
  });

  await scenario('A real terminal status change receives one status cue without animating or replacing the source', async h => {
    const { control } = await createRun(h);
    await settled(h.page);
    const since = await offset(h.page);
    control.finish({ status: 'incomplete', proof: source, report: { reason: 'Fixture completion without acceptance' } });
    await h.page.waitForFunction(() => document.querySelector('.detail-statusline .badge')?.textContent?.includes('\u8fd0\u884c\u7ed3\u675f'));
    await settled(h.page);
    const entered = await record(h.page, 'terminal-status', since);
    assert.equal(entered.filter(entry => entry.status).length, 1, 'the changed status must receive one cue');
    assert.equal(entered.some(entry => entry.code || entry.panel), false, 'a status change animated the source');
    const next = await offset(h.page);
    await h.page.waitForResponse(response => new URL(response.url()).pathname === '/api/runs' && response.request().method() === 'GET');
    await settled(h.page);
    assert.deepEqual(await record(h.page, 'unchanged-terminal-poll', next), []);
  });

  await scenario('Reduced motion displays messages, events, panels and dialogs immediately with no active tween', async h => {
    const { control } = await createRun(h);
    await activity(h.page, control, 'Reduced motion research update');
    for (const tab of ['overview', 'report', 'events', 'source']) await h.page.locator(`#detail-tab-${tab}`).click();
    await openSettings(h.page); await immediate(h.page); await closeSettings(h.page);
    await openHistory(h.page); await immediate(h.page); await closeHistory(h.page);
    await h.page.setViewportSize({ width: 320, height: 812 });
    await showArtifacts(h.page); await immediate(h.page); await fits(h.page);
    await showChat(h.page); await immediate(h.page); await fits(h.page);
    assert.deepEqual(await record(h.page, 'initial-reduced-motion', 0), [], 'reduced motion scheduled an application tween');
    await screenshot(h.page, 'mobile-reduced.png');
  }, 'reduce');

  await scenario('Changing reduced motion during an entrance clears it and future content remains immediately visible', async h => {
    const { control } = await createRun(h);
    await settled(h.page);
    await activity(h.page, control, 'Entrance interrupted by reduced motion');
    await h.page.waitForFunction(() => Boolean(document.querySelector('#conversation .timeline-event[data-motion]')));
    await h.page.emulateMedia({ reducedMotion: 'reduce' });
    await settled(h.page); await immediate(h.page);
    const since = await offset(h.page);
    await activity(h.page, control, 'New content after reduced motion changed');
    await immediate(h.page);
    assert.deepEqual(await record(h.page, 'dynamic-reduced-motion', since), []);
    await screenshot(h.page, 'desktop-dynamic-reduced.png');
    await h.page.emulateMedia({ reducedMotion: 'no-preference' });
    const restoredSince = await offset(h.page);
    const restored = await activity(h.page, control, 'Only future content animates after motion is restored');
    const restoredSequence = await restored.getAttribute('data-sequence');
    await settled(h.page);
    const resumed = await record(h.page, 'restored-motion', restoredSince);
    assert.equal(resumed.filter(entry => entry.sequence === restoredSequence).length, 1, 'motion must resume for new followed activity');
    assert.equal(resumed.some(entry => entry.sequence && entry.sequence !== restoredSequence), false, 'restoring motion replayed old activity');
    const detachedSince = await offset(h.page);
    await h.page.evaluate(() => {
      const observer = new MutationObserver(records => {
        const target = records.map(record => record.target).find(node => node instanceof HTMLElement && node.matches('.timeline-event[data-motion]')
          && node.textContent?.includes('Detached entrance cleaned by pagehide')) as HTMLElement | undefined;
        if (!target) return;
        const wasMarked = target.hasAttribute('data-motion');
        target.remove();
        window.dispatchEvent(new PageTransitionEvent('pagehide', { persisted: true }));
        (window as unknown as { __detachedCleanup: unknown }).__detachedCleanup = { wasMarked, marked: target.hasAttribute('data-motion'),
          transform: target.style.transform, opacity: target.style.opacity };
        observer.disconnect();
      });
      observer.observe(document.querySelector('#conversation')!, { subtree: true, attributes: true, attributeFilter: ['data-motion'] });
    });
    control.progress('Detached entrance cleaned by pagehide');
    await h.page.waitForFunction(() => Boolean((window as unknown as { __detachedCleanup?: unknown }).__detachedCleanup));
    const detached = await h.page.evaluate(() => (window as unknown as { __detachedCleanup: unknown }).__detachedCleanup);
    assert.deepEqual(detached, { wasMarked: true, marked: false, transform: '', opacity: '' }, 'global motion cleanup must synchronously revert an unexpectedly detached target');
    await record(h.page, 'detached-target-cleanup', detachedSince);
  });

  await scenario('Settings, history and mobile view entrances stay within narrow and desktop viewports', async h => {
    const { control } = await createRun(h); await settled(h.page);
    for (const width of [1440, 375, 320]) {
      await h.page.setViewportSize({ width, height: width > 850 ? 900 : 812 });
      await showChat(h.page); await settled(h.page);
      for (const [open, close, dialog] of [[openSettings, closeSettings, '#run-settings'], [openHistory, closeHistory, '#history-dialog']] as const) {
        const since = await offset(h.page);
        await open(h.page); await fits(h.page, dialog); await settled(h.page); await fits(h.page, dialog);
        const entered = await record(h.page, `${dialog}-${width}`, since);
        assert.ok(entered.some(entry => entry.dialog), `${dialog} did not enter`);
        await close(h.page); await settled(h.page);
      }
      await showArtifacts(h.page); await fits(h.page); await settled(h.page);
      if (width <= 850) {
        const hiddenSince = await offset(h.page);
        await activity(h.page, control, `Activity received in the hidden ${width}px conversation`);
        await settled(h.page);
        const hidden = await record(h.page, `hidden-mobile-activity-${width}`, hiddenSince);
        assert.equal(hidden.some(entry => entry.sequence || entry.message), false, 'hidden mobile content must append without entrance motion');
      }
      const returningSince = await offset(h.page);
      await showChat(h.page); await fits(h.page); await settled(h.page);
      if (width <= 850) assert.equal((await record(h.page, `returning-mobile-conversation-${width}`, returningSince))
        .some(entry => entry.sequence || entry.message), false, 'returning to the conversation must not replay existing messages or events');
      await screenshot(h.page, `views-${width}.png`);
    }
  });

  await scenario('Hiding or leaving a page finishes active entrances and never leaves content transformed', async h => {
    const { control } = await createRun(h); await settled(h.page);
    await activity(h.page, control, 'Entrance interrupted by hidden page');
    await h.page.waitForFunction(() => Boolean(document.querySelector('#conversation .timeline-event[data-motion]')));
    await h.page.evaluate(() => {
      Object.defineProperty(document, 'hidden', { configurable: true, value: true });
      Object.defineProperty(document, 'visibilityState', { configurable: true, value: 'hidden' });
      document.dispatchEvent(new Event('visibilitychange'));
    });
    await settled(h.page); await immediate(h.page, false);
    await h.page.evaluate(() => {
      Object.defineProperty(document, 'hidden', { configurable: true, value: false });
      Object.defineProperty(document, 'visibilityState', { configurable: true, value: 'visible' });
      document.dispatchEvent(new Event('visibilitychange'));
    });
    await activity(h.page, control, 'Entrance interrupted by pagehide');
    await h.page.waitForFunction(() => Boolean(document.querySelector('#conversation .timeline-event[data-motion]')));
    await h.page.evaluate(() => window.dispatchEvent(new PageTransitionEvent('pagehide', { persisted: true })));
    await settled(h.page); await immediate(h.page, false);
    await screenshot(h.page, 'desktop-inactive.png');
  });

  await writeReport('passed');
  console.log(`Motion report: ${path.join(output, 'report.json')}`);
} catch (error) {
  await writeReport('failed', error);
  throw error;
} finally {
  await browser?.close();
  await service.close();
}
