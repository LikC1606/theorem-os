#!/usr/bin/env bun
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { chromium, type BrowserContext, type Page, type Route } from 'playwright';
import { readWebConfig, webTemplates } from '../apps/web/config';
import type { TaskDraft } from '../apps/web/client/draft';
import { createWebService } from '../apps/web/server';
import type { WebRunner } from '../apps/web/runner';
import type { WebRunInput } from '../apps/web/shared';
import { closeDialog, closeSettings, discardSourceEditor, fillConfig, fitViewport, openSettings, selectConfig, selectHistoryRun, showChat, withSettings } from './web-ui-controls';
import { freePort, postRun, type RequestRecord, type ScenarioSuite, startBrowser, webScenario, writeScenarioReport } from './web-scenario';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const output = path.join(root, 'out/web-draft-recovery');
const reportFile = path.join(output, 'report.json');
const draftKey = 'theorem-os.web-draft.v1', recoveryKey = 'theorem-os.web-draft-recovery.v1';
const credential = `sk-theoremos-recovery-fixture-${crypto.randomUUID()}`;
const injection = '<img data-recovery-injection src=x onerror="window.__recoveryInjected=true">';
const widths = [1440, 375, 320];
const ids = { providerId: 'provider', model: 'model', effort: 'effort', environment: 'environment', templateId: 'template',
  source: 'source', task: 'task', maxTurns: 'max-turns', maxRunSeconds: 'max-seconds', workers: 'workers' };
const original: TaskDraft = { providerId: 'backup', model: 'fixture-original-model', effort: 'medium', environment: 'standard', templateId: '',
  source: `-- ${injection}\ntheorem unsent_original : True := by sorry\n`, task: `Unsent original task\n${injection}`,
  maxTurns: '4', maxRunSeconds: '120', workers: '2', coordination: 'independent' };
const taskFile = (draft: TaskDraft) => Buffer.from(JSON.stringify({ schema: draftKey, draft }));
await fs.access(path.join(root, 'out/web/app.js')).catch(() => { throw new Error('Run bun run build:web before the draft recovery check.'); });
await fs.mkdir(output, { recursive: true });
await fs.rm(reportFile, { force: true });
const port = await freePort();
const origin = `http://127.0.0.1:${port}`;
let workerStarts = 0;
const runner: WebRunner = {
  async readiness() { return { ready: true, message: 'Local draft recovery fixture' }; },
  async run(input, send) {
    workerStarts++;
    send({ type: 'result', result: { status: 'incomplete', proof: '-- fixture proof is not the original input\ntheorem candidate : True := by trivial',
      report: { fixture: true, source: input.input.source } } });
  },
};
const service = createWebService(readWebConfig({ THEOREMOS_WEB_PORT: String(port), THEOREMOS_WEB_PUBLIC_URL: origin,
  THEOREMOS_WEB_STATIC_ROOT: path.join(root, 'out/web'), THEOREMOS_WEB_PROVIDERS: JSON.stringify([
    { id: 'openai', name: 'OpenAI', baseUrl: 'https://api.openai.com/v1' },
    { id: 'backup', name: 'Fixture backup', baseUrl: 'https://example.invalid/v1' },
  ]) }), runner);
type Harness = { page: Page; context: BrowserContext; requests: RequestRecord[];
  intercept?: (route: Route) => Promise<boolean>; releases: Array<() => void | Promise<void>> };
type Recovery = { schema: string; reason: string; task: { schema: string; draft: TaskDraft } };
const checks: Array<{ name: string; elapsedMs: number; width: number; posts: number; requests: RequestRecord[] }> = [];
const screenshots: string[] = [];
const restored: Array<{ scenario: string; context: string; sourceBytes: number; keyCleared: boolean }> = [];
let browser: Awaited<ReturnType<typeof chromium.launch>> | undefined;
const suite: ScenarioSuite = { origin, output, checks, failedScenario: '', failureScreenshot: '' };

const scenario = (name: string, run: (h: Harness) => Promise<void>, width = 1440, expectedPosts = 0) =>
  webScenario<Harness>(browser!, suite, name, run, {
    context: { viewport: { width, height: width > 850 ? 900 : 812 }, reducedMotion: 'reduce' },
    harness: (page, context) => ({ page, context, requests: [], releases: [] }),
    routes: { local: 'recovery must remain local' }, timeout: { label: 'Draft recovery', seconds: 50 },
    verify: async ({ page, requests }, elapsedMs) => {
      const writes = requests.filter(request => request.method !== 'GET');
      assert.equal(writes.length, expectedPosts, 'only explicit local fixture creation or valid submission may write to the API');
      assert.ok(writes.every(request => request.method === 'POST' && request.pathname === '/api/runs'));
      await privateStorage(page); await noInjection(page);
      return { name, elapsedMs: elapsedMs(), width, posts: writes.length, requests };
    },
    cleanup: async ({ releases }) => { for (const release of releases) await release(); },
  });
async function open(h: Harness) { await h.page.goto(origin); await h.page.locator('#submit-run:enabled').waitFor(); }
async function snapshot(page: Page): Promise<TaskDraft> {
  return page.evaluate(ids => ({ ...Object.fromEntries(Object.entries(ids).map(([key, id]) =>
    [key, (document.getElementById(id) as HTMLInputElement).value])),
    coordination: (document.querySelector('input[name="coordination"]:checked') as HTMLInputElement).value }) as TaskDraft, ids);
}
async function fill(page: Page, value: TaskDraft) {
  await withSettings(page, async () => {
    await page.locator('#provider').selectOption(value.providerId);
    await page.locator('#environment').selectOption(value.environment);
    await page.locator('#template').selectOption(''); await page.locator('#effort').selectOption(value.effort);
    for (const key of ['model', 'source', 'maxTurns', 'maxRunSeconds', 'workers'] as const) await page.locator(`#${ids[key]}`).fill(value[key]);
    await page.locator(`input[name="coordination"][value="${value.coordination}"]`).check();
  });
  await page.locator('#task').fill(value.task);
  if (value.templateId) await selectConfig(page, 'template', value.templateId);
}
async function assertDraft(page: Page, expected: TaskDraft) { assert.deepEqual(await snapshot(page), expected); }
async function recovery(page: Page): Promise<Recovery | null> {
  return page.evaluate(key => { const raw = sessionStorage.getItem(key); return raw ? JSON.parse(raw) : null; }, recoveryKey);
}
async function assertBackup(page: Page, expected: TaskDraft, reason: string) {
  await page.locator('#draft-recovery').waitFor({ state: 'visible' });
  assert.deepEqual(await recovery(page), { schema: recoveryKey, reason, task: { schema: draftKey, draft: expected } });
  assert.equal(await page.locator('#draft-recovery-local').isVisible(), false);
}
async function privateStorage(page: Page) {
  const stored = await page.evaluate(() => {
    let session: string | undefined;
    try { session = JSON.stringify(sessionStorage); } catch { /* Explicit unavailable-storage fixture. */ }
    return { session, local: JSON.stringify(localStorage) };
  });
  assert.equal(stored.session?.includes(credential) ?? false, false, 'neither saved draft may retain the entered API Key');
  assert.equal(stored.local, '{}', 'draft recovery must not write to localStorage');
  if (stored.session) {
    for (const key of [draftKey, recoveryKey]) {
      const item = JSON.parse(stored.session)[key];
      if (!item) continue;
      assert.equal(JSON.stringify(JSON.parse(item)).includes('"apiKey"'), false);
    }
  }
}
async function noInjection(page: Page) {
  assert.equal(await page.locator('[data-recovery-injection]').count(), 0);
  assert.equal(await page.evaluate(() => (window as unknown as { __recoveryInjected?: boolean }).__recoveryInjected), undefined);
}
async function dismiss(page: Page) {
  await showChat(page);
  if (await page.locator('#draft-recovery').isVisible()) await page.locator('#dismiss-draft-recovery').click();
  assert.equal(await page.locator('#draft-recovery').isVisible(), false);
}
async function cleanDraft(page: Page, value = original) { await fill(page, value); await dismiss(page); await assertDraft(page, value); }
async function visibleSettingsSource(page: Page) {
  const geometry = await page.evaluate(() => {
    const source = document.querySelector('#source')!, content = document.querySelector('#run-settings .settings-content')!;
    const box = source.getBoundingClientRect(), frame = content.getBoundingClientRect();
    return { source: { top: box.top, bottom: box.bottom }, frame: { top: frame.top, bottom: frame.bottom },
      visibleHeight: Math.min(box.bottom, frame.bottom, innerHeight) - Math.max(box.top, frame.top, 0) };
  });
  assert.ok(geometry.visibleHeight > 12, `restored source must actually be visible in settings: ${JSON.stringify(geometry)}`);
}
async function restore(page: Page, expected: TaskDraft, fromSettings = false) {
  await page.locator(fromSettings ? '#restore-draft-settings' : '#restore-draft').click();
  await assertDraft(page, expected);
  await page.waitForFunction(id => document.activeElement?.id === id, fromSettings ? 'source' : 'task');
  if (fromSettings) {
    assert.equal(await page.locator('#run-settings').isVisible(), true); await visibleSettingsSource(page);
  } else assert.equal(await page.locator('#run-settings').isVisible(), false);
  assert.equal(await page.locator('#api-key').inputValue(), '');
  assert.equal(await page.locator('#api-key').getAttribute('type'), 'password');
  assert.equal(await page.locator('#toggle-key').getAttribute('aria-pressed'), 'false');
  assert.equal(await page.locator('[aria-invalid="true"]').count(), 0, 'restoring must clear stale validation');
  assert.equal(await page.locator('#draft-recovery').isVisible(), false);
  assert.equal(await page.locator('#restore-draft-settings').isVisible(), false);
  if (page.viewportSize()!.width > 850) assert.equal(await page.locator('#draft-preview').count(), 1, 'restoring must return to the unsent draft');
  restored.push({ scenario: suite.failedScenario, context: fromSettings ? 'settings' : 'composer',
    sourceBytes: Buffer.byteLength(expected.source), keyCleared: true });
}
async function screenshot(page: Page, name: string) { await page.screenshot({ path: path.join(output, name) }); screenshots.push(name); }
const fit = (page: Page, selector: string) => fitViewport(page, selector, 'recovery must not widen the document');
async function importJson(page: Page, draft: TaskDraft, filename = 'recovery.json') {
  await page.locator('#task-file').setInputFiles({ name: filename, mimeType: 'application/json', buffer: taskFile(draft) });
}
async function gateFile(h: Harness, name: string) {
  await h.page.evaluate(name => {
    type Gate = { seen: boolean; complete: boolean; release(): void };
    const exposed = window as unknown as { __recoveryReadGate: Gate };
    let release!: () => void;
    const pending = new Promise<void>(resolve => { release = resolve; }), read = File.prototype.arrayBuffer;
    exposed.__recoveryReadGate = { seen: false, complete: false, release };
    File.prototype.arrayBuffer = async function(this: File) {
      if (this.name !== name) return read.call(this);
      exposed.__recoveryReadGate.seen = true; await pending;
      try { return await read.call(this); } finally { exposed.__recoveryReadGate.complete = true; }
    };
  }, name);
  h.releases.push(async () => { await h.page.evaluate(() => (window as unknown as { __recoveryReadGate?: { release(): void } }).__recoveryReadGate?.release()).catch(() => {}); });
}
async function fileStarted(page: Page) {
  await page.waitForFunction(() => (window as unknown as { __recoveryReadGate: { seen: boolean } }).__recoveryReadGate.seen);
}
async function releaseFile(page: Page) {
  await page.evaluate(() => (window as unknown as { __recoveryReadGate: { release(): void } }).__recoveryReadGate.release());
  await page.waitForFunction(() => (window as unknown as { __recoveryReadGate: { complete: boolean } }).__recoveryReadGate.complete);
  await page.waitForTimeout(100);
}
async function createHistoryFixture(h: Harness) {
  const input: WebRunInput = { providerId: 'openai', apiKey: credential, model: 'fixture-history-model', effort: 'low', environment: 'mathlib',
    source: 'import Mathlib\ntheorem history_original : True := by sorry\n', task: 'Reuse the original history task',
    maxTurns: 2, maxRunSeconds: 60, workers: 1, coordination: 'cooperative' };
  const run = await postRun(h, input, 'History fixture');
  return { run, draft: { providerId: run.providerId, model: run.model, effort: run.effort, environment: run.environment,
    source: run.source, task: run.task, maxTurns: String(run.maxTurns), maxRunSeconds: String(run.maxRunSeconds),
    workers: String(run.workers), coordination: run.coordination, templateId: '' } satisfies TaskDraft };
}
const writeReport = (status: 'passed' | 'failed', error?: unknown) => writeScenarioReport(reportFile, suite, status, error,
  'Real temporary-port HTTP service and Chromium with local files, controlled storage failures and an in-process fixture runner. No models, Docker, Lean or external requests.',
  { workerStarts, widths, checks, restored, screenshots }, { credential });

try {
  browser = await startBrowser(service.server, port);

  await scenario('Select changes recover the previous environment and template before input/change handlers update them', async h => {
    const { page } = h; await open(h);
    assert.equal(await page.locator('#draft-recovery').isVisible(), false, 'initialization must not create a replacement backup');
    const defaults = await snapshot(page);
    await fillConfig(page, 'api-key', credential);
    await selectConfig(page, 'environment', 'standard');
    await assertBackup(page, defaults, 'template');
    await openSettings(page); await restore(page, defaults, true); await closeSettings(page);
    await selectConfig(page, 'environment', 'standard'); await dismiss(page);
    const addition = await snapshot(page);
    assert.equal(addition.templateId, 'addition');
    await selectConfig(page, 'template', 'logic'); await assertBackup(page, addition, 'template');
    await fillConfig(page, 'model', 'edited-after-switch');
    await page.locator('#task').fill('Edited task after replacement');
    await assertBackup(page, addition, 'template');
    await restore(page, addition);
    assert.equal(await recovery(page), null, 'restoring must consume the backup');
  });

  await scenario('Chat suggestions cross environments atomically and repeated suggestions preserve the existing backup', async h => {
    const { page } = h; await open(h); await cleanDraft(page);
    await fillConfig(page, 'api-key', credential);
    await page.locator('[data-chat-template="polynomial"]').click();
    const polynomial = webTemplates.find(template => template.id === 'polynomial')!;
    assert.equal(await page.locator('#environment').inputValue(), 'mathlib');
    assert.equal(await page.locator('#source').inputValue(), polynomial.source);
    await assertBackup(page, original, 'template');
    await page.locator('[data-chat-template="polynomial"]').click(); await assertBackup(page, original, 'template');
    await screenshot(page, 'chat-template-backup.png');
    await restore(page, original); await noInjection(page);
    await page.locator('[data-chat-template="logic"]').click();
    const current = await snapshot(page);
    await page.locator('#dismiss-draft-recovery').click();
    await assertDraft(page, current); assert.equal(await recovery(page), null);
    assert.equal(await page.locator('#task').evaluate(field => field === document.activeElement), true);
  });

  await scenario('New research and settings reset keep one full replacement and restore without redo', async h => {
    const { page } = h; await open(h); await cleanDraft(page); await fillConfig(page, 'api-key', credential);
    await page.locator('#new-research').click(); await assertBackup(page, original, 'reset');
    await page.locator('#task').fill('A newer unsent task');
    const second = await snapshot(page);
    await page.locator('#new-research').click(); await assertBackup(page, second, 'reset');
    await restore(page, second); assert.equal(await recovery(page), null);
    await cleanDraft(page); await fillConfig(page, 'api-key', credential);
    await openSettings(page); await page.locator('#reset-form').click();
    assert.equal(await page.evaluate(key => sessionStorage.getItem(key), draftKey), null, 'reset keeps existing autosave clearing semantics');
    assert.equal((await recovery(page))?.reason, 'reset');
    await screenshot(page, 'settings-reset-backup.png');
    await restore(page, original, true); await closeSettings(page);
  });

  await scenario('Reusing a history task preserves the unsent draft and never substitutes its candidate proof', async h => {
    const { page } = h; await open(h); await cleanDraft(page); await fillConfig(page, 'api-key', credential);
    const fixture = await createHistoryFixture(h);
    await page.reload(); await page.locator('#submit-run:enabled').waitFor();
    await selectHistoryRun(page, fixture.run.id);
    await page.locator('[data-action="reuse-run"]').click();
    await page.locator('#run-settings[open]').waitFor();
    await assertDraft(page, fixture.draft);
    assert.equal(await page.locator('#api-key').evaluate(field => field === document.activeElement), true);
    assert.deepEqual((await recovery(page))?.task.draft, original);
    assert.equal((await recovery(page))?.reason, 'reuse');
    await restore(page, original, true); await closeSettings(page);
    assert.equal(await page.locator('#run-count').innerText(), '1', 'restoring must not add or delete history');
  }, 1440, 1);

  await scenario('JSON cancel, invalid files and unchanged confirmation preserve the previous backup; changed confirmation replaces it', async h => {
    const { page } = h; await open(h); await cleanDraft(page);
    await page.locator('#new-research').click(); const current = await snapshot(page);
    await fillConfig(page, 'api-key', credential);
    const incoming = { ...original, model: 'fixture-json-model', task: 'Incoming JSON task' };
    await importJson(page, incoming); await page.locator('#import-task-dialog[open]').waitFor();
    await closeDialog(page, '#import-task-dialog', () => page.locator('#cancel-import').click());
    await assertDraft(page, current); await assertBackup(page, original, 'reset');
    assert.equal(await page.locator('#api-key').inputValue(), credential);
    await page.locator('#task-file').setInputFiles({ name: 'invalid.json', mimeType: 'application/json', buffer: Buffer.from('{broken') });
    await page.locator('#draft-error').waitFor({ state: 'visible' }); await assertBackup(page, original, 'reset');
    await importJson(page, current); await page.locator('#import-task-dialog[open]').waitFor();
    await closeDialog(page, '#import-task-dialog', () => page.locator('#confirm-import').click());
    await page.locator('#run-settings[open]').waitFor(); await closeSettings(page);
    await assertBackup(page, original, 'reset');
    await importJson(page, incoming); await page.locator('#import-task-dialog[open]').waitFor();
    await closeDialog(page, '#import-task-dialog', () => page.locator('#confirm-import').click());
    await page.locator('#run-settings[open]').waitFor(); await assertDraft(page, incoming);
    assert.equal((await recovery(page))?.reason, 'import'); assert.deepEqual((await recovery(page))?.task.draft, current);
    assert.equal(await page.locator('#api-key').evaluate(field => field === document.activeElement), true);
    await restore(page, current, true); await closeSettings(page);
  });

  await scenario('Lean import and source editing recover atomically while cancellation, invalid input and no-op applications keep the backup', async h => {
    const { page } = h; await open(h); const initial = await snapshot(page);
    await fillConfig(page, 'api-key', credential);
    const source = 'theorem imported_recovery : True := by sorry\n';
    await page.locator('#source-file').setInputFiles({ name: 'recovery.lean', mimeType: 'text/plain', buffer: Buffer.from(source) });
    await page.waitForFunction(source => (document.querySelector('#source') as HTMLTextAreaElement).value === source, source);
    const imported = await snapshot(page);
    assert.equal(imported.task, '保留原题声明，补全 Lean 证明并通过独立验收。');
    assert.equal(imported.environment, initial.environment); await assertBackup(page, initial, 'source');
    await gateFile(h, 'same.lean');
    await page.locator('#source-file').setInputFiles({ name: 'same.lean', mimeType: 'text/plain', buffer: Buffer.from(source) });
    await fileStarted(page); await releaseFile(page); await assertBackup(page, initial, 'source');
    await page.locator('#source-file').setInputFiles({ name: 'wrong.txt', mimeType: 'text/plain', buffer: Buffer.from('wrong') });
    await page.locator('#source-error').waitFor({ state: 'visible' });
    assert.deepEqual((await recovery(page))?.task.draft, initial);
    await closeSettings(page); await restore(page, initial);
    await page.locator('#source-file').setInputFiles({ name: 'again.lean', mimeType: 'text/plain', buffer: Buffer.from(source) });
    await page.waitForFunction(source => (document.querySelector('#source') as HTMLTextAreaElement).value === source, source);
    await openSettings(page);
    for (const action of ['cancel', 'escape', 'unchanged', 'invalid']) {
      await page.locator('#expand-source').click(); await page.locator('#source-editor[open]').waitFor();
      if (action === 'cancel' || action === 'escape') await page.locator('#expanded-source').fill('discarded editor text');
      if (action === 'invalid') {
        await page.locator('#expanded-source').fill(' '); await page.locator('#apply-editor').click();
        await page.locator('#editor-error').waitFor({ state: 'visible' });
      }
      if (action === 'unchanged') await closeDialog(page, '#source-editor', () => page.locator('#apply-editor').click());
      else await discardSourceEditor(page, () => action === 'escape' ? page.keyboard.press('Escape')
        : page.locator('#cancel-editor').click());
      await assertDraft(page, imported); assert.deepEqual((await recovery(page))?.task.draft, initial);
      assert.equal(await page.locator('#expand-source').evaluate(button => button === document.activeElement), true);
    }
    await page.locator('#expand-source').click(); await page.locator('#expanded-source').fill(`${source}\n-- applied recovery edit`);
    await closeDialog(page, '#source-editor', () => page.locator('#apply-editor').click());
    assert.equal((await recovery(page))?.reason, 'edit'); assert.deepEqual((await recovery(page))?.task.draft, imported);
    await restore(page, imported, true); await closeSettings(page);
  });

  await scenario('A persisted backup survives refresh, stays independent of autosave and is not shared with a fresh tab', async h => {
    const { page } = h; await open(h);
    const unfinished = { ...original, maxTurns: '', maxRunSeconds: '', workers: '' };
    await cleanDraft(page, unfinished); await fillConfig(page, 'api-key', credential);
    await page.locator('#new-research').click(); await assertBackup(page, unfinished, 'reset');
    await page.locator('#task').fill('Edited replacement persisted separately');
    const replacement = await snapshot(page);
    await page.waitForFunction(({ key, task }) => JSON.parse(sessionStorage.getItem(key) || 'null')?.draft?.task === task,
      { key: draftKey, task: replacement.task });
    await page.reload(); await page.locator('#submit-run:enabled').waitFor();
    await assertDraft(page, replacement); await assertBackup(page, unfinished, 'reset');
    const other = await h.context.newPage();
    await other.goto(origin); await other.locator('#submit-run:enabled').waitFor();
    assert.equal(await other.locator('#draft-recovery').isVisible(), false);
    assert.equal(await other.evaluate(key => sessionStorage.getItem(key), recoveryKey), null);
    await other.close();
    await restore(page, unfinished); assert.equal(await recovery(page), null);
    await page.reload(); await page.locator('#submit-run:enabled').waitFor();
    await assertDraft(page, unfinished); assert.equal(await page.locator('#draft-recovery').isVisible(), false);
  });

  for (const failure of ['quota', 'unavailable'] as const) await scenario(`Storage ${failure} leaves the latest replacement recoverable in memory`, async h => {
    await h.context.addInitScript(({ key, failure }) => {
      if (failure === 'unavailable') Object.defineProperty(window, 'sessionStorage', { configurable: true,
        get() { throw new DOMException('Fixture storage unavailable', 'SecurityError'); } });
      else {
        const write = Storage.prototype.setItem;
        Storage.prototype.setItem = function(name, value) {
          if (name === key) throw new DOMException('Fixture recovery quota', 'QuotaExceededError');
          return write.call(this, name, value);
        };
      }
    }, { key: recoveryKey, failure });
    const { page } = h; await open(h); await cleanDraft(page); await fillConfig(page, 'api-key', credential);
    await page.locator('#new-research').click();
    await page.locator('#draft-recovery-local').waitFor({ state: 'visible' });
    await screenshot(page, `storage-${failure}-memory.png`);
    await restore(page, original);
    await page.reload(); await page.locator('#submit-run:enabled').waitFor();
    assert.equal(await page.locator('#draft-recovery').isVisible(), false, 'an in-memory backup must not survive refresh');
  });

  await scenario('An oversized unfinished draft remains recoverable without writing an invalid backup', async h => {
    const { page } = h; await open(h);
    const oversized = { ...original, source: `${original.source}${'x'.repeat(32 * 1024)}` };
    await cleanDraft(page, oversized); await fillConfig(page, 'api-key', credential);
    await page.locator('#new-research').click(); await page.locator('#draft-recovery-local').waitFor({ state: 'visible' });
    assert.equal(await recovery(page), null);
    await screenshot(page, 'oversized-memory-backup.png');
    await restore(page, oversized);
    assert.equal(await page.locator('#source-count').evaluate(count => count.classList.contains('over-limit')), true);
  });

  await scenario('Restoration invalidates pending Lean and JSON reads and prevents an old editor from overwriting it', async h => {
    const { page } = h; await open(h); await cleanDraft(page);
    await page.locator('#new-research').click();
    await gateFile(h, 'slow.lean');
    await page.locator('#source-file').setInputFiles({ name: 'slow.lean', mimeType: 'text/plain', buffer: Buffer.from('theorem delayed : True := by sorry') });
    await fileStarted(page); await restore(page, original); await releaseFile(page);
    await page.locator('#toast').filter({ hasText: '草稿已变化，未导入文件' }).waitFor();
    await assertDraft(page, original); assert.equal(await recovery(page), null);
    await page.locator('#new-research').click(); await gateFile(h, 'slow.json');
    await importJson(page, { ...original, task: 'Delayed JSON task' }, 'slow.json'); await fileStarted(page);
    await restore(page, original); await releaseFile(page);
    assert.equal(await page.locator('#import-task-dialog').isVisible(), false); await assertDraft(page, original);
    await page.locator('#new-research').click(); await openSettings(page); await page.locator('#expand-source').click();
    await page.locator('#expanded-source').fill('theorem obsolete_editor : True := by sorry');
    // Trigger restoration while a nested editor holds an older revision, then exercise its real Apply command.
    await page.locator('#restore-draft-settings').evaluate(button => (button as HTMLButtonElement).click());
    await page.locator('#apply-editor').click(); await page.locator('#editor-error').waitFor({ state: 'visible' });
    assert.match(await page.locator('#editor-error').innerText(), /原始草稿已变化/);
    await assertDraft(page, original); assert.equal(await recovery(page), null);
    await discardSourceEditor(page); await closeSettings(page);
  });

  await scenario('Local validation keeps the backup while a real fixture submission consumes it before the response', async h => {
    const { page } = h; await open(h); await cleanDraft(page); await page.locator('#new-research').click();
    await page.locator('#submit-run').click(); await page.locator('#run-settings[open]').waitFor();
    await page.locator('#api-key-validation').waitFor({ state: 'visible' });
    assert.deepEqual((await recovery(page))?.task.draft, original);
    assert.equal(h.requests.filter(request => request.method !== 'GET').length, 0);
    await page.locator('#api-key').fill(credential);
    let release!: () => void, sawRequest!: () => void;
    const pending = new Promise<void>(resolve => { release = resolve; }), sent = new Promise<void>(resolve => { sawRequest = resolve; });
    h.releases.push(release);
    h.intercept = async route => {
      if (route.request().method() !== 'POST' || new URL(route.request().url()).pathname !== '/api/runs') return false;
      sawRequest(); await pending; await route.continue(); return true;
    };
    const response = page.waitForResponse(response => new URL(response.url()).pathname === '/api/runs' && response.request().method() === 'POST');
    void response.catch(() => {});
    await page.locator('#settings-submit').click(); await sent;
    assert.equal(await recovery(page), null); assert.equal(await page.locator('#draft-recovery').isVisible(), false);
    assert.equal(await page.locator('#form-fields').evaluate(fieldset => (fieldset as HTMLFieldSetElement).disabled), true);
    assert.equal(await page.locator('#submit-run').isDisabled(), true);
    release(); assert.equal((await response).status(), 201);
    await page.waitForFunction(() => (document.querySelector('#api-key') as HTMLInputElement).value === '');
    await page.locator('#submit-run:enabled').waitFor();
    assert.equal(await page.locator('#task').inputValue(), ''); assert.equal(await recovery(page), null);
    assert.equal(await page.locator('#draft-recovery').isVisible(), false, 'successful task clearing must not create a new backup');
    await screenshot(page, 'submitted-without-undo.png');
  }, 1440, 1);

  for (const width of widths) await scenario(`Recovery commands remain visible, focus correctly and preserve the draft at ${width}px`, async h => {
    const { page } = h; await open(h); await cleanDraft(page); await fillConfig(page, 'api-key', credential);
    await page.locator('#new-research').click(); await assertBackup(page, original, 'reset');
    for (const selector of ['#draft-recovery', '#restore-draft', '#dismiss-draft-recovery', '#submit-run']) await fit(page, selector);
    await screenshot(page, `recovery-${width}-composer.png`);
    await openSettings(page);
    for (const selector of ['#restore-draft-settings', '#reset-form', '#apply-settings', '#settings-submit']) await fit(page, selector);
    await screenshot(page, `recovery-${width}-settings.png`);
    await restore(page, original, true); await closeSettings(page);
    if (width <= 850) {
      await page.locator('#mobile-runs').click(); await page.locator('#draft-preview').waitFor();
      assert.equal(await page.locator('#draft-preview-code code').textContent(), original.source);
      assert.equal(await page.locator('#draft-preview-task').textContent(), original.task);
      await page.locator('#mobile-compose').click();
    }
    await page.locator('#new-research').click(); await restore(page, original);
    await fit(page, '#task'); await fit(page, '#submit-run'); await noInjection(page);
    await screenshot(page, `recovery-${width}-restored.png`);
  }, width);

  assert.equal(workerStarts, 2, 'only the history fixture and explicit valid submission may run');
  await writeReport('passed');
  console.log(`Draft recovery checks passed: ${checks.length} scenarios, complete replacement and single recovery, privacy, storage fallbacks, revision races, submission boundary and responsive focus.`);
  console.log(`Report: ${path.relative(root, reportFile)}`);
} catch (error) { await writeReport('failed', error); throw error; }
finally { await browser?.close(); await service.close(); }
