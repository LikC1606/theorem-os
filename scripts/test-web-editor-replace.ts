#!/usr/bin/env bun
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { chromium, type BrowserContext, type Page } from 'playwright';
import { readWebConfig, webLimits } from '../apps/web/config';
import { createWebService } from '../apps/web/server';
import type { WebRunner } from '../apps/web/runner';
import { draftRecoveryStorageKey } from '../apps/web/client/draftRecovery';
import { closeDialog, closeSettings, discardSourceEditor, fitViewport, focused, openSettings, selectEditorRange, snapshot, text, value } from './web-ui-controls';
import { freePort, normalize, type RequestRecord, type ScenarioSuite, settled, startBrowser, webScenario, writeScenarioReport } from './web-scenario';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const output = path.join(root, 'out/web-editor-replace'), reportFile = path.join(output, 'report.json');
const widths = [1440, 375, 320];
await fs.access(path.join(root, 'out/web/app.js')).catch(() => { throw new Error('Run bun run build:web before the editor replacement check.'); });
await fs.mkdir(output, { recursive: true }); await fs.rm(reportFile, { force: true });
const port = await freePort();
const origin = `http://127.0.0.1:${port}`;
let workerStarts = 0, cleanedOwners = 0;
const runner: WebRunner = {
  async readiness() { return { ready: true, message: 'Local editor replacement fixture' }; },
  async run() { workerStarts++; throw new Error('Editor replacement must never start a worker'); },
};
const service = createWebService(readWebConfig({ THEOREMOS_WEB_PORT: String(port), THEOREMOS_WEB_PUBLIC_URL: origin,
  THEOREMOS_WEB_STATIC_ROOT: path.join(root, 'out/web') }), runner);
type Harness = { page: Page; context: BrowserContext; requests: RequestRecord[] };
type NativeEvent = { inputType: string; length: number; trusted: boolean };
type NativeCommand = { command: string; length: number };
const checks: Array<{ name: string; width: number; elapsedMs: number; unexpectedWrites: number; requests: RequestRecord[] }> = [];
const screenshots: string[] = [];
const nativeEdits: Array<{ label: string; commands: NativeCommand[]; events: NativeEvent[] }> = [];
const feedback: Array<{ label: string; text: string }> = [];
const overlays: Array<{ label: string; width: number; marks: number; visibleMarks: number }> = [];
const selections: Array<{ label: string; width: number; start: number; end: number; selected: string }> = [];
let browser: Awaited<ReturnType<typeof chromium.launch>> | undefined;
const suite: ScenarioSuite = { origin, output, checks, failedScenario: '', failureScreenshot: '' };

const scenario = (name: string, run: (h: Harness) => Promise<void>, width = 1440) => webScenario<Harness>(browser!, suite, name, run, {
  context: { viewport: { width, height: width > 850 ? 900 : 812 }, reducedMotion: 'reduce' }, harness: (page, context) => ({ page, context, requests: [] }),
  // No scenario needs a write. Block mistakes before they can reach the local service.
  routes: { local: 'replacement must remain local', blockWrites: true }, open: true, timeout: { label: 'Editor replacement', seconds: 45 },
  verify: (h, elapsedMs) => {
    const writes = h.requests.filter(request => request.method !== 'GET');
    assert.deepEqual(writes, [], 'scratch replacement and applying drafts must not create, change, cancel or delete a run');
    assert.equal(workerStarts, 0, 'replacement checks must not start a solver');
    return { name, width, elapsedMs: elapsedMs(), unexpectedWrites: writes.length, requests: h.requests };
  },
  cleanup: async ({ context }) => {
    const owner = (await context.cookies(origin)).find(cookie => cookie.name === 'theoremos_session')?.value;
    if (owner) {
      const remaining = service.jobs.list(owner).length;
      service.jobs.forget(owner); cleanedOwners++;
      assert.equal(remaining, 0, 'replacement must not create hidden fixture jobs');
    }
  },
});
async function editSource(page: Page, source: string) {
  await openSettings(page); await page.locator('#template').selectOption(''); await page.locator('#source').fill(source);
  await page.locator('#expand-source').click(); await page.locator('#source-editor[open]').waitFor();
  await value(page, normalize(source)); await focused(page, '#expanded-source');
}
async function position(page: Page, expected: string) { await text(page, '#editor-find-position', expected); }
async function matchCount(page: Page, count: number) {
  await page.waitForFunction(count => new RegExp(`^\\d+/${count}$`).test(document.querySelector('#editor-find-position')?.textContent ?? ''), count);
}
async function select(page: Page, start: number, end = start, direction: 'forward' | 'backward' | 'none' = 'none') {
  await selectEditorRange(page, start, end, direction); await settled(page);
}
async function selection(page: Page, start: number, end = start, selected = '', label = 'replacement selection') {
  const actual = await snapshot(page);
  assert.equal(actual.start, start, `${label}: expected UTF-16 start offset`);
  assert.equal(actual.end, end, `${label}: expected UTF-16 end offset`);
  assert.equal(actual.value.slice(actual.start, actual.end), selected);
  selections.push({ label, width: page.viewportSize()!.width, start, end, selected });
}
async function openFind(page: Page) {
  if (!await page.locator('#editor-find-controls').isVisible()) await page.locator('#editor-find-toggle').click();
  assert.equal(await page.locator('#editor-find-controls').isVisible(), true);
}
async function openReplace(page: Page, shortcut?: 'Control+h' | 'Meta+h') {
  if (shortcut) await page.keyboard.press(shortcut);
  else {
    await openFind(page);
    if (!await page.locator('#editor-replace-controls').isVisible()) await page.locator('#editor-replace-toggle').click();
  }
  assert.equal(await page.locator('#editor-find-controls').isVisible(), true);
  assert.equal(await page.locator('#editor-replace-controls').isVisible(), true);
  assert.equal(await page.locator('#editor-replace-toggle').getAttribute('aria-expanded'), 'true');
  assert.equal(await page.locator('#editor-replace-toggle').getAttribute('aria-controls'), 'editor-replace-controls');
  assert.equal(await page.locator('#editor-replace-status').getAttribute('role'), 'status');
  await focused(page, '#editor-replace-input');
}
async function setup(page: Page, query: string, replacement: string, count: string) {
  await openFind(page); await page.locator('#editor-find-input').fill(query); await position(page, count);
  await openReplace(page); await page.locator('#editor-replace-input').fill(replacement);
}
async function resultStatus(page: Page, label: string, count?: number) {
  await page.waitForFunction(() => Boolean(document.querySelector('#editor-replace-status')?.textContent?.trim()));
  const content = (await page.locator('#editor-replace-status').innerText()).trim();
  if (count !== undefined) assert.match(content.replaceAll(',', ''), new RegExp(String(count)), `${label}: result must identify the replacement count`);
  feedback.push({ label, text: content });
}
async function recovery(page: Page) { return page.evaluate(key => sessionStorage.getItem(key), draftRecoveryStorageKey); }
async function pristine(page: Page, source: string, backup: string | null) {
  assert.equal(await page.locator('#source').inputValue(), source, 'scratch edits must not change the original draft');
  assert.equal(await recovery(page), backup, 'scratch replacement must not replace a recovery backup');
}
async function inputProbe(page: Page) {
  await page.evaluate(() => {
    const state = window as unknown as { __replaceNativeEvents: NativeEvent[]; __replaceNativeCommands: NativeCommand[]; __replaceProbeInstalled?: boolean };
    state.__replaceNativeEvents = []; state.__replaceNativeCommands = [];
    if (state.__replaceProbeInstalled) return;
    state.__replaceProbeInstalled = true;
    const original = document.execCommand;
    document.execCommand = function(command, showUI, value) {
      state.__replaceNativeCommands.push({ command, length: value?.length ?? 0 });
      return original.call(this, command, showUI, value);
    };
    document.addEventListener('input', event => {
      if (!(event.target instanceof HTMLTextAreaElement) || event.target.id !== 'expanded-source') return;
      state.__replaceNativeEvents.push({ inputType: (event as InputEvent).inputType, length: event.target.value.length, trusted: event.isTrusted });
    }, { capture: true });
  });
}
async function events(page: Page) {
  return page.evaluate(() => (window as unknown as { __replaceNativeEvents: NativeEvent[] }).__replaceNativeEvents);
}
async function commands(page: Page) {
  return page.evaluate(() => (window as unknown as { __replaceNativeCommands: NativeCommand[] }).__replaceNativeCommands);
}
const fit = (page: Page, selector: string) => fitViewport(page, selector, 'replacement must not widen the page', true);
async function screenshot(page: Page, name: string) {
  await page.screenshot({ path: path.join(output, name) }); screenshots.push(name);
}
async function visibleOverlay(page: Page, label: string) {
  await page.locator('#editor-match-overlay .editor-match-mark').first().waitFor({ state: 'visible' }); await settled(page);
  const evidence = await page.evaluate(() => {
    const editor = document.querySelector<HTMLTextAreaElement>('#expanded-source')!;
    const overlay = document.querySelector<HTMLElement>('#editor-match-overlay')!, bounds = editor.getBoundingClientRect();
    const left = bounds.left + editor.clientLeft, top = bounds.top + editor.clientTop;
    const right = left + editor.clientWidth, bottom = top + editor.clientHeight;
    const marks = Array.from(overlay.querySelectorAll<HTMLElement>('.editor-match-mark'));
    return { accessible: overlay.getAttribute('aria-hidden') === 'true', marks: marks.length, visibleMarks: marks.filter(mark => {
      const rect = mark.getBoundingClientRect(), style = getComputedStyle(mark);
      return style.display !== 'none' && style.visibility !== 'hidden' && rect.width > 0 && rect.height > 0
        && rect.left >= left - 1 && rect.right <= right + 1 && rect.top >= top - 1 && rect.bottom <= bottom + 1;
    }).length };
  });
  assert.equal(evidence.accessible, true, 'the visual overlay must remain hidden from assistive technology');
  assert.ok(evidence.visibleMarks >= 1, `${label}: the next match must be visible while replacement input retains focus`);
  overlays.push({ label, width: page.viewportSize()!.width, marks: evidence.marks, visibleMarks: evidence.visibleMarks });
}
const writeReport = (status: 'passed' | 'failed', error?: unknown) => writeScenarioReport(reportFile, suite, status, error,
  'Real local HTTP service and Chromium. Local scratch replacement, native edit transactions and undo/redo. All API writes are blocked; no models, Docker, Lean or external requests.',
  { workerStarts, cleanedOwners, widths, checks, nativeEdits, feedback, selections, overlays, screenshots,
    unexpectedWrites: checks.reduce((sum, check) => sum + check.unexpectedWrites, 0) }, { failureRequests: true });

try {
  browser = await startBrowser(service.server, port);

  for (const width of widths) await scenario(`A single replacement reveals the next Unicode match and keeps controls usable at ${width}px`, async ({ page }) => {
    const source = '-- needle alpha\n-- 🙂x needle beta\n-- needle gamma'; await editSource(page, source);
    const backup = await recovery(page); await setup(page, 'needle', 'proof', '1/3');
    assert.equal((await page.locator('#editor-replace-one').innerText()).trim(), '替换');
    assert.equal((await page.locator('#editor-replace-all').innerText()).trim(), '全部替换');
    await page.locator('#editor-replace-one').click();
    const edited = source.replace('needle', 'proof'), next = edited.indexOf('needle');
    await value(page, edited); await position(page, '1/2'); await selection(page, next, next + 6, 'needle');
    await focused(page, '#editor-replace-input'); await resultStatus(page, 'one literal replacement', 1);
    await visibleOverlay(page, 'next current match after single replacement');
    for (const selector of ['#source-editor', '#editor-navigation', '#editor-find-controls', '#editor-find-input',
      '#editor-replace-toggle', '#editor-replace-controls', '#editor-replace-input', '#editor-replace-one',
      '#editor-replace-all', '#editor-replace-status', '#apply-editor']) await fit(page, selector);
    await screenshot(page, `editor-replace-${width}.png`); await pristine(page, source, backup);
    await discardSourceEditor(page); await closeSettings(page);
  }, width);

  await scenario('Replace one locates an unselected match before making any source edit', async ({ page }) => {
    const source = '-- needle one\n-- needle two\n-- needle three'; await editSource(page, source);
    const backup = await recovery(page); await setup(page, 'needle', 'proof', '1/3'); await inputProbe(page);
    const second = source.indexOf('needle two'); await select(page, second - 1);
    await page.locator('#editor-replace-one').click(); await value(page, source);
    await selection(page, second, second + 6, 'needle', 'first click selects without changing text');
    assert.equal((await events(page)).length, 0, 'a location-only click must not create a native edit transaction');
    await page.locator('#editor-replace-one').click();
    const edited = source.slice(0, second) + 'proof' + source.slice(second + 6), next = edited.indexOf('needle three');
    await value(page, edited); await selection(page, next, next + 6, 'needle', 'second click replaces and advances');
    await focused(page, '#editor-replace-input'); assert.equal((await events(page)).length, 1);
    await pristine(page, source, backup); await discardSourceEditor(page);
  });

  await scenario('Replacement tokens, backslashes, Unicode and an inserted query are literal and processed once', async ({ page }) => {
    const query = '[a+b]*?', replacement = '$& / $1 \\ [a+b]*? 🙂';
    const source = `-- ${query} first\n-- aaab a+b\n-- 🙂 ${query} second`;
    await editSource(page, source); await setup(page, query, replacement, '1/2'); await inputProbe(page);
    await page.locator('#editor-replace-all').click(); await value(page, source.split(query).join(replacement));
    await resultStatus(page, 'literal replacement templates and single-pass growth', 2);
    assert.deepEqual((await commands(page)).map(command => command.command), ['insertText'], 'growing replacement must remain one native edit command');
    await focused(page, '#editor-replace-input'); await matchCount(page, 2);
    await discardSourceEditor(page);
  });

  await scenario('An empty replacement deletes every full and adjacent literal match', async ({ page }) => {
    const source = '-- eraseerase erase\n-- 🙂 erase\n-- safe'; await editSource(page, source);
    const backup = await recovery(page); await setup(page, 'erase', '', '1/4'); await inputProbe(page);
    await page.locator('#editor-replace-all').click(); const edited = source.split('erase').join('');
    await value(page, edited); await position(page, '0/0'); await resultStatus(page, 'empty-string deletion', 4);
    await focused(page, '#editor-replace-input'); assert.equal((await commands(page)).length, 1);
    await page.locator('#expanded-source').focus(); await page.keyboard.press('Control+z'); await value(page, source);
    await text(page, '#editor-change-status', '未修改'); await pristine(page, source, backup);
    await closeDialog(page, '#source-editor', () => page.locator('#cancel-editor').click());
    assert.equal(await page.locator('#editor-discard-dialog').isVisible(), false);
  });

  await scenario('Replace all covers matches beyond the 1000-result cap in one undoable native transaction', async ({ page }) => {
    const count = 1205, source = Array.from({ length: count }, (_, index) => `-- needle ${index + 1}`).join('\n');
    const edited = source.split('needle').join('proof'); await editSource(page, source);
    const backup = await recovery(page); await setup(page, 'needle', 'proof', '1/1000+'); await inputProbe(page);
    await page.locator('#editor-replace-all').click(); await value(page, edited); await position(page, '0/0');
    assert.equal((await page.locator('#expanded-source').inputValue()).includes('needle'), false, 'the undisplayed match tail must also be replaced');
    await resultStatus(page, 'complete-source replacement beyond displayed cap', count); await focused(page, '#editor-replace-input');
    const native = await events(page); assert.ok(native.length > 0, 'replacement must emit native input');
    assert.equal(native.every(event => event.trusted), true, 'replacement must use native browser edits');
    assert.deepEqual((await commands(page)).map(command => command.command), ['insertText'], 'all 1205 replacements must issue one native edit command');
    await page.locator('#expanded-source').focus(); await page.keyboard.press('Control+z'); await value(page, source);
    await text(page, '#editor-change-status', '未修改');
    await page.keyboard.press('Control+Shift+z'); await value(page, edited);
    const history = await events(page);
    assert.ok(history.some(event => event.inputType === 'historyUndo')); assert.ok(history.some(event => event.inputType === 'historyRedo'));
    nativeEdits.push({ label: '1205 replacements with one native undo and redo', commands: await commands(page), events: history });
    await screenshot(page, 'editor-replace-complete-source.png'); await pristine(page, source, backup); await discardSourceEditor(page);
  });

  await scenario('No-op, missing-query and size limits preserve buffers while allowing oversized drafts to shrink', async ({ page }) => {
    const source = '-- same same\n-- unchanged'; await editSource(page, source); const backup = await recovery(page);
    await setup(page, 'same', 'same', '1/2'); await inputProbe(page);
    await page.locator('#editor-replace-one').click(); await page.locator('#editor-replace-all').click();
    await value(page, source); await text(page, '#editor-change-status', '未修改');
    assert.equal((await events(page)).length, 0, 'no-op replacements must not create undo entries');
    await resultStatus(page, 'identical replacement is a no-op');
    for (const query of ['absent', '']) {
      await page.locator('#editor-find-input').fill(query); await position(page, '0/0');
      assert.equal(await page.locator('#editor-replace-one').isDisabled(), true);
      assert.equal(await page.locator('#editor-replace-all').isDisabled(), true);
    }
    await pristine(page, source, backup);
    await closeDialog(page, '#source-editor', () => page.locator('#close-editor').click());
    assert.equal(await page.locator('#editor-discard-dialog').isVisible(), false);
    await closeSettings(page);
    const small = `-- ${'a '.repeat(300)}`, replacement = 'x'.repeat(256);
    assert.ok(Buffer.byteLength(small.split('a').join(replacement)) > webLimits.maxSourceBytes);
    await editSource(page, small); const growthBackup = await recovery(page); await setup(page, 'a', '', '1/300');
    assert.equal(await page.locator('#editor-replace-input').getAttribute('maxlength'), '256');
    await page.locator('#editor-replace-input').press('Control+a'); await page.keyboard.insertText('x'.repeat(257));
    assert.equal(await page.locator('#editor-replace-input').inputValue(), replacement, 'the native replacement input must enforce maxlength 256');
    await inputProbe(page); const before = await snapshot(page); await page.locator('#editor-replace-all').click();
    await value(page, small); await text(page, '#editor-change-status', '未修改');
    const after = await snapshot(page); assert.equal(after.start, before.start); assert.equal(after.end, before.end);
    assert.equal((await events(page)).length, 0, 'expansion beyond the source limit must not make a native edit');
    await resultStatus(page, 'oversized growth is rejected before editing'); await pristine(page, small, growthBackup);
    await closeDialog(page, '#source-editor', () => page.locator('#cancel-editor').click());
    assert.equal(await page.locator('#editor-discard-dialog').isVisible(), false);
    await closeSettings(page);
    const repetitions = Math.ceil(webLimits.maxSourceBytes / 3) + 10;
    const oversized = `-- ${'aaa '.repeat(repetitions)}`, shortened = oversized.split('aaa').join('aa');
    assert.ok(Buffer.byteLength(oversized) > Buffer.byteLength(shortened) && Buffer.byteLength(shortened) > webLimits.maxSourceBytes);
    await editSource(page, oversized); const oversizedBackup = await recovery(page); await setup(page, 'aaa', 'aa', '1/1000+');
    await inputProbe(page); await page.locator('#editor-replace-all').click(); await value(page, shortened);
    assert.deepEqual((await commands(page)).map(command => command.command), ['insertText'], 'an existing oversized draft may shrink in one edit');
    await resultStatus(page, 'shrinking an already oversized draft is allowed', repetitions);
    await page.locator('#apply-editor').click();
    assert.equal(await page.locator('#source-editor').evaluate(node => (node as HTMLDialogElement).open), true);
    assert.equal(await page.locator('#editor-error').isVisible(), true, 'Apply must retain the original source-size validation');
    await pristine(page, oversized, oversizedBackup); await discardSourceEditor(page);
  });

  await scenario('Case sensitivity and previous/next navigation remain usable while replacement is expanded', async ({ page }) => {
    const source = '-- Needle first\n-- needle second\n-- NEEDLE third'; await editSource(page, source);
    await setup(page, 'needle', 'proof', '1/3');
    await page.locator('#editor-find-next').click(); await position(page, '2/3');
    await page.locator('#editor-find-prev').click(); await position(page, '1/3');
    await page.locator('#editor-find-case').click(); await position(page, '1/1');
    const second = source.indexOf('needle'); await selection(page, second, second + 6, 'needle');
    await page.locator('#editor-replace-all').click(); await value(page, source.replace('needle', 'proof'));
    await resultStatus(page, 'case-sensitive replacement excludes other case', 1);
    assert.equal(await page.locator('#editor-replace-controls').isVisible(), true); await focused(page, '#editor-replace-input');
    await page.locator('#editor-find-case').click(); await matchCount(page, 2);
    await page.locator('#editor-replace-all').click(); await value(page, source.replaceAll(/needle/gi, 'proof'));
    await resultStatus(page, 'case-insensitive replacement includes remaining variants', 2); await discardSourceEditor(page); await closeSettings(page);
    const normalizeCase = '-- Needle needle NEEDLE'; await editSource(page, normalizeCase);
    await setup(page, 'needle', 'needle', '1/3'); await inputProbe(page);
    await page.locator('#editor-replace-one').click(); await value(page, '-- needle needle NEEDLE'); await position(page, '2/3');
    assert.equal((await commands(page)).length, 1);
    await page.locator('#editor-replace-one').click(); await value(page, '-- needle needle NEEDLE'); await position(page, '3/3');
    assert.equal((await commands(page)).length, 1, 'a correctly cased match advances without making a no-op undo transaction');
    await focused(page, '#editor-replace-input');
    await page.locator('#editor-replace-one').click(); await value(page, '-- needle needle needle'); await position(page, '1/3');
    assert.equal((await commands(page)).length, 2, 'normalizing three case-insensitive matches changes only the two unequal matches');
    await discardSourceEditor(page);
  });

  await scenario('Unavailable native edits preserve source and selection and show a local error', async ({ page }) => {
    const source = '-- needle one\n-- needle two'; await editSource(page, source); await setup(page, 'needle', 'proof', '1/2');
    const start = source.indexOf('needle');
    await page.evaluate(() => { (window as unknown as { __replaceExecCommand: typeof document.execCommand }).__replaceExecCommand = document.execCommand; });
    for (const mode of ['false', 'throw']) for (const action of ['one', 'all']) {
      await select(page, start, start + 6, 'backward'); const before = await snapshot(page);
      await page.evaluate(mode => { document.execCommand = () => { if (mode === 'throw') throw new Error('Fixture unavailable replacement edit'); return false; }; }, mode);
      await page.locator(`#editor-replace-${action}`).click(); await value(page, source);
      const after = await snapshot(page);
      assert.equal(after.start, before.start); assert.equal(after.end, before.end); assert.equal(after.direction, before.direction);
      assert.ok(Math.abs(after.top - before.top) <= 1 && Math.abs(after.left - before.left) <= 1, 'failed replacement preserves scroll');
      const messages = await page.locator('#editor-error:visible, #editor-replace-status:visible').allTextContents();
      assert.match(messages.join(' '), /未能|无法|失败|不可用|不支持/, 'a failed native edit must show a usable local error');
      await text(page, '#editor-change-status', '未修改');
    }
    await page.evaluate(() => { document.execCommand = (window as unknown as { __replaceExecCommand: typeof document.execCommand }).__replaceExecCommand; });
    await select(page, source.length); await page.keyboard.insertText('\n-- manual edit still works');
    await value(page, source + '\n-- manual edit still works'); await discardSourceEditor(page);
  });

  await scenario('Scratch replacements stay isolated until Apply, create one recovery and reset on editor reopen', async ({ page }) => {
    const source = 'theorem replacement_fixture : True := by\n  sorry\n-- sorry'; await editSource(page, source);
    const backup = await recovery(page); await setup(page, 'sorry', 'trivial', '1/2');
    await page.evaluate(key => {
      const original = Storage.prototype.setItem;
      (window as unknown as { __replaceRecoveryWrites: number }).__replaceRecoveryWrites = 0;
      Storage.prototype.setItem = function(name, value) {
        if (this === sessionStorage && name === key) (window as unknown as { __replaceRecoveryWrites: number }).__replaceRecoveryWrites++;
        return original.call(this, name, value);
      };
    }, draftRecoveryStorageKey);
    await page.locator('#editor-replace-all').click(); const edited = source.split('sorry').join('trivial'); await value(page, edited);
    await pristine(page, source, backup);
    await page.locator('#close-editor').click(); await page.locator('#editor-discard-dialog[open]').waitFor();
    await closeDialog(page, '#editor-discard-dialog', () => page.locator('#keep-editing').click());
    await value(page, edited); await focused(page, '#expanded-source'); await pristine(page, source, backup);
    assert.equal(await page.evaluate(() => (window as unknown as { __replaceRecoveryWrites: number }).__replaceRecoveryWrites), 0);
    await closeDialog(page, '#source-editor', () => page.locator('#apply-editor').click());
    assert.equal(await page.locator('#source').inputValue(), edited);
    const saved = JSON.parse((await recovery(page))!); assert.equal(saved.reason, 'edit'); assert.equal(saved.task.draft.source, source);
    assert.equal(await page.evaluate(() => (window as unknown as { __replaceRecoveryWrites: number }).__replaceRecoveryWrites), 1);
    await page.locator('#expand-source').click(); await page.locator('#source-editor[open]').waitFor(); await value(page, edited);
    assert.equal(await page.locator('#editor-navigation').isVisible(), false);
    assert.equal(await page.locator('#editor-replace-input').inputValue(), '');
    assert.equal((await page.locator('#editor-replace-status').textContent())?.trim(), '');
    await page.keyboard.press('Control+z'); await settled(page);
    assert.equal(await page.locator('#expanded-source').inputValue(), edited, 'a reopened editor must not resurrect the previous multi-line native replacement undo transaction');
    const appliedBackup = await recovery(page), freshSuffix = '\n-- fresh session edit';
    await select(page, edited.length); await page.keyboard.insertText(freshSuffix); await value(page, edited + freshSuffix);
    await page.keyboard.press('Control+z'); await value(page, edited);
    await page.keyboard.press('Control+Shift+z'); await value(page, edited + freshSuffix);
    await page.keyboard.press('Control+z'); await value(page, edited);
    await page.keyboard.press('Control+z'); await settled(page);
    assert.equal(await page.locator('#expanded-source').inputValue(), edited, 'exhausting the fresh buffer undo history cannot restore text from its predecessor');
    await text(page, '#editor-change-status', '未修改'); await pristine(page, edited, appliedBackup);
    await openFind(page); assert.equal(await page.locator('#editor-replace-toggle').getAttribute('aria-expanded'), 'false');
    assert.equal(await page.locator('#editor-find-input').inputValue(), '');
    await closeDialog(page, '#source-editor', () => page.locator('#cancel-editor').click());
  });

  await scenario('Replace shortcuts respect IME and normal typing, and Escape closes tools before dirty confirmation', async ({ page }) => {
    const source = '-- needle one\n-- needle two'; await editSource(page, source);
    for (const modifiers of [
      { ctrlKey: true, metaKey: false, altKey: false, shiftKey: false, isComposing: true },
      { ctrlKey: false, metaKey: true, altKey: false, shiftKey: false, isComposing: true },
      { ctrlKey: true, metaKey: false, altKey: true, shiftKey: false, isComposing: false },
      { ctrlKey: false, metaKey: true, altKey: false, shiftKey: true, isComposing: false },
      { ctrlKey: false, metaKey: false, altKey: false, shiftKey: false, isComposing: false },
    ]) {
      assert.equal(await page.locator('#expanded-source').evaluate((node, modifiers) => node.dispatchEvent(new KeyboardEvent('keydown', {
        key: 'h', bubbles: true, cancelable: true, ...modifiers,
      })), modifiers), true, 'composition, modified and ordinary keys must not be intercepted as replacement shortcuts');
      assert.equal(await page.locator('#editor-navigation').isVisible(), false);
    }
    await openReplace(page, 'Control+h'); await page.locator('#editor-find-input').fill('needle'); await position(page, '1/2');
    await page.locator('#editor-replace-input').fill('proof');
    const beforeComposition = await snapshot(page);
    assert.equal(await page.locator('#editor-replace-input').evaluate(node => node.dispatchEvent(new KeyboardEvent('keydown', {
      key: 'Enter', isComposing: true, bubbles: true, cancelable: true,
    }))), true, 'IME confirmation in the replacement input must not trigger source replacement');
    assert.deepEqual(await snapshot(page), beforeComposition);
    await page.keyboard.press('Escape'); assert.equal(await page.locator('#editor-navigation').isVisible(), false);
    await focused(page, '#expanded-source');
    await openReplace(page, 'Meta+h'); await page.locator('#editor-replace-input').focus();
    await page.locator('#editor-replace-one').click(); const edited = source.replace('needle', 'proof'); await value(page, edited);
    await page.keyboard.press('Escape'); assert.equal(await page.locator('#editor-navigation').isVisible(), false);
    assert.equal(await page.locator('#editor-discard-dialog').isVisible(), false); await focused(page, '#expanded-source');
    await page.keyboard.press('Escape'); await page.locator('#editor-discard-dialog[open]').waitFor();
    await closeDialog(page, '#editor-discard-dialog', () => page.locator('#keep-editing').click()); await value(page, edited);
    await discardSourceEditor(page); await closeSettings(page);
    for (const key of ['h', 'H']) assert.equal(await page.locator('#task').evaluate((node, key) => node.dispatchEvent(new KeyboardEvent('keydown', {
      key, ctrlKey: true, bubbles: true, cancelable: true,
    })), key), true, 'editor replacement shortcuts must not intercept the ordinary task input');
  });

  await scenario('A replacement deep in wrapped Unicode text selects and reveals the next logical match beyond line 160', async ({ page }) => {
    const lines = Array.from({ length: 222 }, (_, index) => `-- context ${index + 1}`);
    lines[0] = `-- ${'lead '.repeat(500)}`;
    lines[174] = `-- ${'prefix '.repeat(60)}🙂x targetNeedle first`;
    lines[203] = `-- ${'following '.repeat(40)}🙂 targetNeedle second`;
    const source = lines.join('\n'); await editSource(page, source); await setup(page, 'targetNeedle', 'proof', '1/2');
    await page.locator('#editor-replace-one').click(); const edited = source.replace('targetNeedle', 'proof'), next = edited.indexOf('targetNeedle');
    await value(page, edited); await selection(page, next, next + 12, 'targetNeedle', 'wrapped next Unicode match');
    await text(page, '#editor-position', `第 204 行 · 第 ${Array.from(edited.slice(edited.lastIndexOf('\n', next - 1) + 1, next + 12)).length + 1} 列`);
    await focused(page, '#editor-replace-input'); await visibleOverlay(page, 'post-160 wrapped next match');
    assert.ok((await snapshot(page)).top > 4000, 'soft wraps before the target must contribute to its scroll offset');
    await screenshot(page, 'editor-replace-wrapped-unicode.png'); await discardSourceEditor(page);
  }, 375);

  await writeReport('passed');
  console.log(`Editor replacement checks passed: ${checks.length} scenarios; literal replacements, complete-source edits, one-step native undo/redo, draft isolation, focus and responsive layouts.`);
  console.log(`Report: ${path.relative(root, reportFile)}`);
} catch (error) { await writeReport('failed', error); throw error; }
finally { try { await browser?.close(); } finally { await service.close(); } }
