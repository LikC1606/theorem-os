#!/usr/bin/env bun
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { chromium, type BrowserContext, type Page } from 'playwright';
import { readWebConfig } from '../apps/web/config';
import { createWebService } from '../apps/web/server';
import type { WebRunner } from '../apps/web/runner';
import type { WebRun, WebRunInput } from '../apps/web/shared';
import { closeDialog, closeHistory, fitViewport, openHistory } from './web-ui-controls';
import { freePort, postRun, type RequestRecord, type ScenarioSuite, settled, startBrowser, webScenario, writeScenarioReport } from './web-scenario';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const output = path.join(root, 'out/web-history'), reportFile = path.join(output, 'report.json');
const widths = [1440, 375, 320];
const credential = `sk-theoremos-history-fixture-${crypto.randomUUID()}`;
await fs.access(path.join(root, 'out/web/app.js')).catch(() => { throw new Error('Run bun run build:web before the history check.'); });
await fs.mkdir(output, { recursive: true });
await fs.rm(reportFile, { force: true });
const port = await freePort();
const origin = `http://127.0.0.1:${port}`;
const controls = new Map<string, { progress(event: string, message: string): void; finish(): void }>();
let workerStarts = 0, workerAborts = 0, cleanedOwners = 0;
const runner: WebRunner = {
  async readiness() { return { ready: true, message: 'Local history fixture' }; },
  async run(input, send, signal) {
    workerStarts++;
    const result = () => send({ type: 'result', result: { status: 'incomplete', proof: input.input.source, report: { fixture: true } } });
    if (input.input.source.includes('history_auto_finish')) { result(); return; }
    await new Promise<void>((resolve, reject) => {
      const cleanup = () => { controls.delete(input.id); signal.removeEventListener('abort', abort); };
      const abort = () => { workerAborts++; cleanup(); reject(new Error('Cancelled local history fixture')); };
      controls.set(input.id, {
        progress: (event, message) => send({ type: 'progress', event, message }),
        finish: () => { cleanup(); result(); resolve(); },
      });
      signal.addEventListener('abort', abort, { once: true });
      send({ type: 'progress', event: 'solve_started', message: 'Local history fixture started' });
      if (signal.aborted) abort();
    });
  },
};
const service = createWebService(readWebConfig({ THEOREMOS_WEB_PORT: String(port), THEOREMOS_WEB_PUBLIC_URL: origin,
  THEOREMOS_WEB_STATIC_ROOT: path.join(root, 'out/web'), THEOREMOS_WEB_CONCURRENCY: '8', THEOREMOS_WEB_QUEUE_LIMIT: '32' }), runner);
type Harness = { page: Page; context: BrowserContext; requests: RequestRecord[]; creates: number; removals: number; owner: string; owners: Set<string> };
type Anchor = { id: string; offset: number; scrollTop: number; scrollable: boolean };
type HistoryProbe = {
  list: HTMLElement; focus: Element | null;
  rows: Array<{ id: string; row: HTMLElement; button: Element; titleText: ChildNode | null; modelText: ChildNode | null }>;
  selection?: { start: Node; end: Node; startOffset: number; endOffset: number; text: string };
};
type MutationProbe = { root: Element; observer: MutationObserver; changes: number };
const checks: Array<{ name: string; width: number; elapsedMs: number; fixtureCreates: number; fixtureRemovals: number;
  unexpectedWrites: number; requests: RequestRecord[] }> = [];
const screenshots: string[] = [];
const anchorChecks: Array<{ name: string; before: Anchor; after: Anchor }> = [];
const retentionChecks: Array<{ name: string; width: number; rows: number; focus: boolean; selection: boolean }> = [];
let browser: Awaited<ReturnType<typeof chromium.launch>> | undefined;
const suite: ScenarioSuite = { origin, output, checks, failedScenario: '', failureScreenshot: '' };
const row = (id: string) => `[data-history-id="${id}"]`;
const button = (id: string) => `#run-list [data-run-id="${id}"]`;
const orderedAt = (rank: number) => new Date(Date.UTC(2026, 9, 1, 12) + rank * 60_000).toISOString();

async function collectOwner(h: Harness) {
  const owner = (await h.context.cookies(origin)).find(cookie => cookie.name === 'theoremos_session')?.value;
  if (owner) { h.owner = owner; h.owners.add(owner); }
}
async function waitForFixture(predicate: () => boolean, description: string) {
  const deadline = performance.now() + 5000;
  while (!predicate()) {
    if (performance.now() >= deadline) throw new Error(`History fixture did not settle: ${description}`);
    await new Promise(resolve => setTimeout(resolve, 10));
  }
}
const scenario = (name: string, run: (h: Harness) => Promise<void>, width = 1440) => webScenario<Harness>(browser!, suite, name, run, {
  context: { viewport: { width, height: width > 850 ? 900 : 812 }, reducedMotion: 'reduce' },
  harness: (page, context) => ({ page, context, requests: [], creates: 0, removals: 0, owner: '', owners: new Set() }),
  routes: { local: 'history checks must not contact an external site or model provider' }, timeout: { label: 'History', seconds: 50 },
  verify: async (h, elapsedMs) => {
    const writes = h.requests.filter(request => request.method !== 'GET');
    const creates = writes.filter(request => request.method === 'POST' && request.pathname === '/api/runs').length;
    assert.equal(creates, h.creates, 'only explicit fixture setup may submit a run');
    assert.equal(writes.length, h.creates, 'history refresh, filtering, selection and focus recovery must not write to the API');
    const privacy = await h.page.evaluate(() => ({ text: document.body.innerText, session: JSON.stringify(sessionStorage), local: JSON.stringify(localStorage) }));
    assert.equal(JSON.stringify(privacy).includes(credential), false, 'fixture credentials must not be visible or persisted');
    return { name, width, elapsedMs: elapsedMs(), fixtureCreates: h.creates, fixtureRemovals: h.removals, unexpectedWrites: writes.length - h.creates,
      requests: h.requests };
  },
  cleanup: async h => {
    await collectOwner(h);
    for (const owner of h.owners) {
      service.jobs.forget(owner);
      assert.equal(service.jobs.list(owner).length, 0, 'scenario fixtures must be removed');
      cleanedOwners++;
    }
  },
});
async function open(h: Harness) {
  await h.page.goto(origin);
  await h.page.locator('#submit-run:enabled').waitFor();
  await collectOwner(h);
  assert.ok(h.owner, 'the fixture requires a real local session');
}
async function createRun(h: Harness, title: string, rank: number, active = false) {
  const input: WebRunInput = { providerId: 'openai', apiKey: credential, model: 'fixture-history-model', effort: 'low', environment: 'standard',
    source: `${active ? '-- history_controlled_run' : '-- history_auto_finish'}\ntheorem history_fixture : True := by sorry`,
    task: title, maxTurns: 2, maxRunSeconds: 60, workers: 1, coordination: 'independent' };
  const run = await postRun(h, input, 'History fixture');
  h.creates++;
  const saved = service.jobs.get(h.owner, run.id);
  assert.ok(saved, 'fixture run must belong to the current session');
  saved.createdAt = orderedAt(rank);
  await waitForFixture(() => active ? controls.has(run.id) : service.jobs.get(h.owner, run.id)?.status === 'completed', run.id);
  return { ...run, createdAt: saved.createdAt };
}
async function seed(h: Harness, count: number, activeRanks: number[] = []) {
  const runs: WebRun[] = [];
  for (let rank = 1; rank <= count; rank++) runs.push(await createRun(h,
    `History ${rank % 2 ? 'odd' : 'even'} row ${String(rank).padStart(2, '0')} - formal proof`, rank, activeRanks.includes(rank)));
  return runs.toReversed();
}
async function finish(h: Harness, run: WebRun) {
  const control = controls.get(run.id);
  assert.ok(control, 'the active history fixture must be controlled locally');
  control.finish();
  await waitForFixture(() => service.jobs.get(h.owner, run.id)?.status === 'completed', `finish ${run.id}`);
}
function remove(h: Harness, run: WebRun) {
  assert.equal(service.jobs.remove(h.owner, run.id), 'deleted', 'only a completed local fixture may be removed');
  h.removals++;
}
async function poll(h: Harness) {
  const { page } = h;
  await page.locator('#refresh-runs:enabled').waitFor({ state: 'attached' });
  const loaded = page.waitForResponse(response => response.request().method() === 'GET'
    && new URL(response.url()).pathname === '/api/runs' && response.status() === 200);
  // Exercise the existing background-refresh path without moving keyboard focus to a refresh button.
  await page.evaluate(() => document.dispatchEvent(new Event('visibilitychange')));
  await loaded;
  await page.locator('#refresh-runs:enabled').waitFor({ state: 'attached' });
  await settled(page);
}
async function rows(page: Page, expected: WebRun[] | string[]) {
  const ids = expected.map(value => typeof value === 'string' ? value : value.id);
  await page.waitForFunction(ids => {
    const actual = Array.from(document.querySelectorAll<HTMLElement>('#run-list [data-history-id]'), row => row.dataset.historyId);
    return actual.length === ids.length && actual.every((id, index) => id === ids[index]);
  }, ids);
  assert.deepEqual(await page.locator('#run-list [data-run-id]').evaluateAll(nodes => nodes.map(node => (node as HTMLElement).dataset.runId)), ids);
}
async function show(h: Harness, expected: WebRun[]) {
  await openHistory(h.page); await poll(h); await rows(h.page, expected);
}
async function selected(page: Page, id: string) {
  assert.equal(await page.locator('.detail-identifier code').textContent(), id);
  const visible = await page.locator(`${button(id)}.selected`).count();
  assert.equal(await page.locator('#run-list .run-row.selected').count(), visible);
  if (visible) assert.equal(await page.locator(button(id)).getAttribute('aria-pressed'), 'true');
}
async function choose(page: Page, id: string) {
  await closeDialog(page, '#history-dialog', () => page.locator(button(id)).click());
  await selected(page, id);
  await openHistory(page);
}
async function bookmark(page: Page, id: string, selection = false) {
  await page.evaluate(({ id, selection }) => {
    const list = document.querySelector<HTMLElement>('#run-list')!;
    const focused = list.querySelector<HTMLElement>(`[data-run-id="${id}"]`)!;
    focused.focus({ preventScroll: true });
    if (selection) {
      const text = focused.querySelector('.run-row-title')!.firstChild!;
      const range = document.createRange();
      range.setStart(text, 2); range.setEnd(text, Math.min(17, text.textContent!.length));
      getSelection()!.removeAllRanges(); getSelection()!.addRange(range);
    }
    const range = selection ? getSelection()!.getRangeAt(0) : undefined;
    const snapshot: HistoryProbe = { list, focus: document.activeElement,
      rows: Array.from(list.querySelectorAll<HTMLElement>('[data-history-id]'), row => ({ id: row.dataset.historyId!, row,
        button: row.querySelector('[data-run-id]')!, titleText: row.querySelector('.run-row-title')!.firstChild,
        modelText: row.querySelector('.run-row-model')!.firstChild })),
      ...(range ? { selection: { start: range.startContainer, end: range.endContainer,
        startOffset: range.startOffset, endOffset: range.endOffset, text: getSelection()!.toString() } } : {}) };
    (window as unknown as { __historyProbe: HistoryProbe }).__historyProbe = snapshot;
  }, { id, selection });
}
async function retained(page: Page, name: string, options: { focus?: boolean; selection?: boolean; removed?: string[] } = {}) {
  const evidence = await page.evaluate(removed => {
    const p = (window as unknown as { __historyProbe: HistoryProbe }).__historyProbe;
    const rows = p.rows.filter(row => !removed.includes(row.id));
    const selection = getSelection(), range = selection?.rangeCount === 1 ? selection.getRangeAt(0) : undefined;
    return { list: p.list === document.querySelector('#run-list'), rows: rows.length,
      nodes: rows.every(row => row.row === document.querySelector(`[data-history-id="${row.id}"]`)
        && row.button === document.querySelector(`#run-list [data-run-id="${row.id}"]`)
        && row.titleText === row.row.querySelector('.run-row-title')?.firstChild
        && row.modelText === row.row.querySelector('.run-row-model')?.firstChild),
      focus: p.focus === document.activeElement,
      selection: Boolean(p.selection && range && range.startContainer === p.selection.start && range.endContainer === p.selection.end
        && range.startOffset === p.selection.startOffset && range.endOffset === p.selection.endOffset && selection!.toString() === p.selection.text) };
  }, options.removed ?? []);
  assert.equal(evidence.list && evidence.nodes, true, `${name}: surviving history rows, buttons and unchanged title/model text must be reused`);
  if (options.focus !== false) assert.equal(evidence.focus, true, `${name}: keyboard focus must remain on the same node`);
  if (options.selection) assert.equal(evidence.selection, true, `${name}: title selection must retain the same DOM Range endpoints and text`);
  retentionChecks.push({ name, width: page.viewportSize()!.width, rows: evidence.rows, focus: evidence.focus, selection: evidence.selection });
}
async function focused(page: Page, selector: string) {
  assert.equal(await page.locator(selector).evaluate(node => node === document.activeElement), true, `${selector} must receive focus`);
}
async function scroll(page: Page, top = 520) {
  await page.locator('#run-list').evaluate((list, top) => { list.scrollTop = top; }, top);
  await settled(page);
}
async function anchor(page: Page): Promise<Anchor> {
  return page.evaluate(() => {
    const list = document.querySelector<HTMLElement>('#run-list')!;
    const bounds = list.getBoundingClientRect(), top = bounds.top + list.clientTop;
    const first = Array.from(list.querySelectorAll<HTMLElement>('[data-history-id]')).find(row => {
      const rect = row.getBoundingClientRect(); return rect.bottom > top && rect.top < top + list.clientHeight;
    });
    if (!first) throw new Error('History fixture requires a visible row anchor');
    return { id: first.dataset.historyId!, offset: first.getBoundingClientRect().top - top,
      scrollTop: list.scrollTop, scrollable: list.scrollHeight > list.clientHeight };
  });
}
async function anchored(page: Page, before: Anchor, name: string) {
  await settled(page);
  const after = await anchor(page);
  assert.equal(before.scrollable, true, `${name}: fixture must overflow vertically`);
  assert.ok(before.scrollTop > 100, `${name}: fixture must actually be scrolled`);
  assert.equal(after.id, before.id, `${name}: first visible history row must remain the reading anchor`);
  assert.ok(Math.abs(after.offset - before.offset) <= 1, `${name}: anchor offset changed from ${before.offset} to ${after.offset}`);
  anchorChecks.push({ name, before, after });
}
async function atTop(page: Page) {
  assert.ok(await page.locator('#run-list').evaluate(list => Math.abs(list.scrollTop) <= 1), 'history must start at the top');
}
async function observe(page: Page) {
  await settled(page);
  await page.evaluate(() => {
    const root = document.querySelector('#run-list')!;
    const sample: MutationProbe = { root, changes: 0, observer: undefined! };
    sample.observer = new MutationObserver(records => { sample.changes += records.length; });
    sample.observer.observe(root, { childList: true, characterData: true, subtree: true });
    (window as unknown as { __historyMutations: MutationProbe }).__historyMutations = sample;
  });
}
async function unchanged(page: Page, name: string) {
  await settled(page);
  const result = await page.evaluate(() => {
    const sample = (window as unknown as { __historyMutations: MutationProbe }).__historyMutations;
    sample.changes += sample.observer.takeRecords().length; sample.observer.disconnect();
    return { sameRoot: sample.root === document.querySelector('#run-list'), changes: sample.changes };
  });
  assert.equal(result.sameRoot, true); assert.equal(result.changes, 0, `${name}: unchanged polling must not mutate history contents`);
}
const fit = (page: Page, selector: string) => fitViewport(page, selector, 'history must not widen the page');
async function screenshot(page: Page, name: string) {
  await page.screenshot({ path: path.join(output, name) }); screenshots.push(name);
}
const writeReport = (status: 'passed' | 'failed', error?: unknown) => writeScenarioReport(reportFile, suite, status, error,
  'Real temporary-port HTTP service and Chromium with a controlled in-process runner. Only explicit fixture creation posts to the API; timestamps and removals use the local fixture store. No models, Docker, Lean or external requests.',
  { workerStarts, workerAborts, cleanedOwners, widths, checks, anchorChecks, retentionChecks, screenshots,
    unexpectedWrites: checks.reduce((sum, check) => sum + check.unexpectedWrites, 0) }, { credential, failureRequests: true });

try {
  browser = await startBrowser(service.server, port);

  for (const width of widths) await scenario(`Status patches and keyboard selection retain history nodes and title ranges at ${width}px`, async h => {
    const { page } = h; await open(h);
    const runs = await seed(h, 6, [5]); await show(h, runs);
    await bookmark(page, runs[0]!.id, true);
    controls.get(runs[1]!.id)!.progress('proof_check_started', 'History fixture candidate check');
    await poll(h);
    await page.locator(`${row(runs[1]!.id)} .badge`).filter({ hasText: '检查候选证明' }).waitFor();
    await retained(page, 'status patch', { selection: true });
    await page.keyboard.press('ArrowDown'); await selected(page, runs[1]!.id);
    await focused(page, button(runs[1]!.id));
    await retained(page, 'keyboard selection patch', { focus: false, selection: true });
    await page.keyboard.press('Home'); await selected(page, runs[0]!.id);
    await retained(page, 'selection returns to its original button', { selection: true });
    for (const selector of ['#history-dialog', '#run-search', '#run-filter', '#run-list', button(runs[0]!.id)]) await fit(page, selector);
    await screenshot(page, `history-${width}-stable.png`);
  }, width);

  await scenario('A focused middle active row ending moves focus to its old slot without changing the viewed run', async h => {
    const { page } = h; await open(h);
    const runs = await seed(h, 4, [1, 2, 3, 4]); await show(h, runs);
    await page.locator('#run-filter').selectOption('active'); await choose(page, runs[1]!.id);
    await bookmark(page, runs[1]!.id);
    await finish(h, runs[1]!); await poll(h);
    await rows(page, [runs[0]!, runs[2]!, runs[3]!]);
    await focused(page, button(runs[2]!.id)); await selected(page, runs[1]!.id);
    await retained(page, 'active middle-row removal', { focus: false, removed: [runs[1]!.id] });
    assert.equal(await page.locator('#run-filter').inputValue(), 'active');
    await page.keyboard.press('ArrowDown'); await selected(page, runs[3]!.id);
    await focused(page, button(runs[3]!.id));
    await screenshot(page, 'active-middle-focus.png');
  });

  await scenario('Ending the focused last active row falls back to the previous row and then to search when empty', async h => {
    const { page } = h; await open(h);
    const runs = await seed(h, 3, [1, 2, 3]); await show(h, runs);
    await page.locator('#run-filter').selectOption('active'); await choose(page, runs[2]!.id);
    await page.locator(button(runs[2]!.id)).focus();
    await finish(h, runs[2]!); await poll(h); await rows(page, runs.slice(0, 2));
    await focused(page, button(runs[1]!.id)); await selected(page, runs[2]!.id);
    await finish(h, runs[1]!); await poll(h); await rows(page, [runs[0]!]);
    await focused(page, button(runs[0]!.id)); await selected(page, runs[2]!.id);
    await finish(h, runs[0]!); await poll(h); await rows(page, []);
    await focused(page, '#run-search'); await selected(page, runs[2]!.id);
    assert.equal(await page.locator('#run-filter').inputValue(), 'active');
    assert.equal(await page.locator('#run-count').innerText(), '0/3');
    await page.locator('[data-clear-filters]').waitFor();
    await screenshot(page, 'active-empty-search-focus.png');
  });

  await scenario('Top insertions and removal above a scrolled reader preserve the visible history anchor', async h => {
    const { page } = h; await open(h);
    const runs = await seed(h, 16); await show(h, runs); await scroll(page);
    const before = await anchor(page); await bookmark(page, before.id);
    const inserted = await createRun(h, 'History newly completed above the reader', 100);
    await poll(h); await rows(page, [inserted, ...runs]);
    await anchored(page, before, 'visible top insertion'); await retained(page, 'top insertion retains existing nodes');
    assert.notEqual(runs[1]!.id, before.id, 'the deleted fixture must be above the anchor');
    remove(h, runs[1]!); await poll(h); await rows(page, [inserted, ...runs.filter(run => run.id !== runs[1]!.id)]);
    await anchored(page, before, 'visible removal above anchor');
    await retained(page, 'removal above anchor retains surviving nodes', { removed: [runs[1]!.id] });
    await screenshot(page, 'history-visible-anchor.png');
    await scroll(page, 0);
    const newest = await createRun(h, 'History insertion while reading the top', 101);
    await poll(h); await rows(page, [newest, inserted, ...runs.filter(run => run.id !== runs[1]!.id)]); await atTop(page);
  });

  await scenario('Updates while history is closed preserve its reading anchor and the draft input focus and selection', async h => {
    const { page } = h; await open(h);
    const runs = await seed(h, 16); await show(h, runs); await scroll(page, 560);
    const before = await anchor(page); await closeHistory(page);
    await page.locator('#task').fill('Unsent history draft with a backward text selection');
    const inputBefore = await page.locator('#task').evaluate(node => {
      const input = node as HTMLTextAreaElement; input.focus(); input.setSelectionRange(7, 28, 'backward');
      (window as unknown as { __historyDraftInput: Element }).__historyDraftInput = input;
      return { value: input.value, start: input.selectionStart, end: input.selectionEnd, direction: input.selectionDirection };
    });
    const inserted = await createRun(h, 'History inserted while its window is closed', 100);
    remove(h, runs[1]!); await poll(h);
    const inputAfter = await page.locator('#task').evaluate(node => {
      const input = node as HTMLTextAreaElement;
      return { sameNode: input === (window as unknown as { __historyDraftInput: Element }).__historyDraftInput,
        focused: input === document.activeElement, value: input.value, start: input.selectionStart, end: input.selectionEnd, direction: input.selectionDirection };
    });
    assert.equal(inputAfter.sameNode && inputAfter.focused, true, 'a hidden history update must not replace or focus away from the draft input');
    assert.deepEqual({ value: inputAfter.value, start: inputAfter.start, end: inputAfter.end, direction: inputAfter.direction }, inputBefore);
    assert.equal(await page.locator('#history-dialog').evaluate(dialog => (dialog as HTMLDialogElement).open), false);
    await openHistory(page); await rows(page, [inserted, ...runs.filter(run => run.id !== runs[1]!.id)]);
    await anchored(page, before, 'history restored after a hidden update');
    await screenshot(page, 'history-375-reopened-anchor.png');
  }, 375);

  await scenario('User filtering resets reading to the top and keyboard navigation stays inside the filtered rows', async h => {
    const { page } = h; await open(h);
    const runs = await seed(h, 16); await show(h, runs); await scroll(page);
    assert.ok((await anchor(page)).scrollTop > 100);
    await page.locator('#run-filter').selectOption('unproved'); await atTop(page);
    await scroll(page); await page.locator('#run-search').fill('History'); await atTop(page);
    await page.locator('#run-search').fill('even');
    const matching = runs.filter(run => run.title.includes('even')); await rows(page, matching); await atTop(page);
    await bookmark(page, matching[0]!.id);
    await page.keyboard.press('End'); await selected(page, matching.at(-1)!.id); await focused(page, button(matching.at(-1)!.id));
    await retained(page, 'End keeps filtered rows', { focus: false });
    await page.keyboard.press('Home'); await selected(page, matching[0]!.id); await focused(page, button(matching[0]!.id));
    await page.keyboard.press('ArrowUp'); await selected(page, matching.at(-1)!.id);
    await page.keyboard.press('ArrowDown'); await selected(page, matching[0]!.id);
    assert.equal(await page.locator('#run-filter').inputValue(), 'unproved');
    assert.equal(await page.locator('#run-search').inputValue(), 'even');
    assert.equal(await page.locator('#run-count').innerText(), '8/16');
    await retained(page, 'filtered keyboard wrap retains all nodes');
  });

  await scenario('Unchanged polling preserves populated rows and stable empty states including the focused clear button', async h => {
    const { page } = h; await open(h); await openHistory(page);
    const initialEmpty = await page.locator('#run-list > .empty-state').elementHandle();
    await observe(page); await poll(h); await poll(h); await unchanged(page, 'unfiltered empty history');
    assert.equal(await initialEmpty!.evaluate(node => node === document.querySelector('#run-list > .empty-state')), true);
    const runs = await seed(h, 2); await poll(h); await rows(page, runs);
    await bookmark(page, runs[0]!.id, true);
    await observe(page); await poll(h); await poll(h); await unchanged(page, 'populated history');
    await retained(page, 'unchanged populated polling', { selection: true });
    await page.locator('#run-filter').selectOption('passed'); await rows(page, []);
    await page.locator('#run-search').fill('no matching history fixture');
    const empty = await page.locator('#run-list > .empty-state').elementHandle();
    const clear = await page.locator('[data-clear-filters]').elementHandle();
    await page.locator('[data-clear-filters]').focus();
    await observe(page); await poll(h); await poll(h); await unchanged(page, 'filtered empty history');
    assert.equal(await empty!.evaluate(node => node === document.querySelector('#run-list > .empty-state')), true);
    assert.equal(await clear!.evaluate(node => node === document.activeElement && node === document.querySelector('[data-clear-filters]')), true);
    await page.locator('[data-clear-filters]').click(); await rows(page, runs); await atTop(page);
    assert.equal(await page.locator('#run-filter').inputValue(), 'all');
    assert.equal(await page.locator('#run-search').inputValue(), ''); await focused(page, '#run-search');
  });

  await scenario('Reordering an existing focused history row retains its button and restores focus after its DOM move', async h => {
    const { page } = h; await open(h);
    const runs = await seed(h, 6); await show(h, runs);
    const moved = runs.at(-1)!; await bookmark(page, moved.id);
    service.jobs.get(h.owner, moved.id)!.createdAt = orderedAt(100);
    await poll(h); await rows(page, [moved, ...runs.slice(0, -1)]);
    await retained(page, 'focused history row reordered'); await focused(page, button(moved.id));
    await selected(page, runs[0]!.id);
    await screenshot(page, 'history-reordered-focus.png');
  });

  await writeReport('passed');
  console.log(`History checks passed: ${checks.length} scenarios; stable row nodes and selection, active-filter focus recovery, visible and hidden reading anchors, keyboard navigation and no unexpected API writes.`);
  console.log(`Report: ${path.relative(root, reportFile)}`);
} catch (error) { await writeReport('failed', error); throw error; }
finally { try { await browser?.close(); } finally { await service.close(); } }
