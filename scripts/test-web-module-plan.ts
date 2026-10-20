#!/usr/bin/env bun
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { chromium, type BrowserContext, type Page, type Route } from 'playwright';
import { readWebConfig } from '../apps/web/config';
import { createWebService } from '../apps/web/server';
import type { WebRunner } from '../apps/web/runner';
import type { WebEventDetails, WebRun, WebRunInput } from '../apps/web/shared';
import type { CustomResearchModule, ResearchModulePlan } from '../src/solver/modules/policy';
import { modulePlanLibraryStorageKey, type SavedModulePlan } from '../apps/web/client/modulePlanLibrary';
import { closeDialog, closeSettings, openSettings, selectModules, showArtifacts, showChat } from './web-ui-controls';
import { freePort, postRun, readRun, type RequestRecord, type ScenarioSuite, settled, startBrowser, webScenario, writeScenarioReport } from './web-scenario';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const output = path.join(root, 'out/web-module-plan');
const reportFile = path.join(output, 'report.json');
const storageKey = 'theorem-os.web-draft.v1';
const credential = `sk-theoremos-plan-fixture-${crypto.randomUUID()}`;
const markup = '<img data-plan-injection src=x onerror="window.__planInjected=true">';
const rows = '.module-plan-row[data-module-plan-id]';
const widths = [1440, 375, 320];
await fs.access(path.join(root, 'out/web/app.js')).catch(() => { throw new Error('Run bun run build:web before the module plan check.'); });
await fs.mkdir(output, { recursive: true });
await fs.rm(reportFile, { force: true });
const port = await freePort();
const origin = `http://127.0.0.1:${port}`;
type Control = { progress(type: string, message: string, details?: WebEventDetails): void; finish(): void };
const controls = new Map<string, Control>(), received = new Map<string, WebRunInput>();
let workerStarts = 0;
const runner: WebRunner = {
  async readiness() { return { ready: true, message: 'Local custom module plan fixture' }; },
  async run(input, send, signal) {
    workerStarts++; received.set(input.id, structuredClone(input.input));
    await new Promise<void>((resolve, reject) => {
      const cleanup = () => { controls.delete(input.id); signal.removeEventListener('abort', abort); };
      const abort = () => { cleanup(); reject(new Error('Cancelled module plan fixture')); };
      signal.addEventListener('abort', abort, { once: true });
      controls.set(input.id, {
        progress: (event, message, details) => send({ type: 'progress', event, message, ...(details ? { details } : {}) }),
        finish: () => { send({ type: 'result', result: { status: 'incomplete', proof: input.input.source, report: { fixture: true } } }); cleanup(); resolve(); },
      });
      if (signal.aborted) abort();
    });
  },
};
const service = createWebService(readWebConfig({ THEOREMOS_WEB_PORT: String(port), THEOREMOS_WEB_PUBLIC_URL: origin,
  THEOREMOS_WEB_STATIC_ROOT: path.join(root, 'out/web'), THEOREMOS_WEB_CONCURRENCY: '8' }), runner);
type Harness = { page: Page; context: BrowserContext; requests: RequestRecord[]; runIds: string[]; uiCreates: number;
  expectedSource?: string; expectedTask?: string; intercept?: (route: Route) => Promise<boolean> };
type DraftEnvelope = { schema: string; draft: Record<string, unknown> & { modulePlan?: ResearchModulePlan } };
const checks: Array<{ name: string; elapsedMs: number; fixtureCreates: number; uiCreates: number; unexpectedApiWrites: number; requests: RequestRecord[] }> = [];
const screenshots: string[] = [];
const applicationChecks: Array<{ runId: string; retainedEvents: number; applications: Record<string, number> }> = [];
let browser: Awaited<ReturnType<typeof chromium.launch>> | undefined;
const suite: ScenarioSuite = { origin, output, checks, failedScenario: '', failureScreenshot: '' };

async function noStoredKey(page: Page) {
  const stored = await page.evaluate(() => JSON.stringify({ session: sessionStorage, local: localStorage }));
  assert.equal(stored.includes(credential), false, 'credentials must not be saved with module plans');
}
async function noInjection(page: Page) {
  assert.equal(await page.locator('[data-plan-injection]').count(), 0, 'custom names and instructions must remain inert text');
  assert.equal(await page.evaluate(() => (window as unknown as { __planInjected?: boolean }).__planInjected), undefined);
}
let draft = '', task = '';
const scenario = (name: string, run: (h: Harness) => Promise<void>, width = 1440) => webScenario<Harness>(browser!, suite, name, run, {
  context: { viewport: { width, height: width > 850 ? 960 : 812 }, reducedMotion: 'reduce' },
  harness: (page, context) => ({ page, context, requests: [], runIds: [], uiCreates: 0 }),
  routes: { local: 'module configuration must not contact external sites or model providers' }, timeout: { label: 'Module plan', seconds: 50 },
  open: async ({ page }) => {
    await page.goto(origin); await page.locator('#submit-run:enabled').waitFor();
    draft = await page.locator('#source').inputValue(), task = await page.locator('#task').inputValue();
  },
  verify: async (h, elapsedMs) => {
    assert.equal(await h.page.locator('#source').inputValue(), h.expectedSource ?? draft, 'module configuration must preserve the Lean source or explicitly restored run source');
    assert.equal(await h.page.locator('#task').inputValue(), h.expectedTask ?? task, 'module configuration must preserve the research task or explicitly restored run task');
    await noStoredKey(h.page); await noInjection(h.page);
    const writes = h.requests.filter(request => request.method !== 'GET');
    assert.equal(writes.length, h.runIds.length, 'only explicit fixture and UI run creation may write to the API');
    assert.ok(writes.every(request => request.method === 'POST' && request.pathname === '/api/runs'));
    return { name, elapsedMs: elapsedMs(), fixtureCreates: h.runIds.length - h.uiCreates,
      uiCreates: h.uiCreates, unexpectedApiWrites: writes.length - h.runIds.length, requests: h.requests };
  },
  cleanup: ({ runIds }) => { for (const id of runIds) { controls.get(id)?.finish(); received.delete(id); } },
});
function rule(page: Page, id: string) { return page.locator(`${rows}[data-module-plan-id="${id}"]`); }
function graphToggle(page: Page, id: string) { return page.locator(`[data-module-custom-enabled="${id}"]`); }
async function addRule(page: Page, value: Omit<CustomResearchModule, 'id'>) {
  await page.locator('#module-plan-add').click();
  const id = (await page.locator(rows).last().getAttribute('data-module-plan-id'))!, row = rule(page, id);
  await row.locator('[data-module-plan-field="name"]').fill(value.name);
  await row.locator('[data-module-plan-field="slot"]').selectOption(value.slot);
  await row.locator('[data-module-plan-field="mode"]').selectOption(value.mode);
  await row.locator('[data-module-plan-field="instructions"]').fill(value.instructions);
  await row.locator('[data-module-plan-field="enabled"]').setChecked(value.enabled);
  return id;
}
async function editorPlan(page: Page): Promise<ResearchModulePlan> {
  return page.evaluate(rows => ({ scheduler: (document.querySelector('#module-plan-scheduler') as HTMLSelectElement).value,
    context: (document.querySelector('#module-plan-context') as HTMLSelectElement).value,
    custom: Array.from(document.querySelectorAll<HTMLElement>(rows)).map(row => ({ id: row.dataset.modulePlanId!,
      name: row.querySelector<HTMLInputElement>('[data-module-plan-field="name"]')!.value,
      slot: row.querySelector<HTMLSelectElement>('[data-module-plan-field="slot"]')!.value,
      mode: row.querySelector<HTMLSelectElement>('[data-module-plan-field="mode"]')!.value,
      enabled: row.querySelector<HTMLInputElement>('[data-module-plan-field="enabled"]')!.checked,
      instructions: row.querySelector<HTMLTextAreaElement>('[data-module-plan-field="instructions"]')!.value,
    })) }) as ResearchModulePlan, rows);
}
async function configure(page: Page, custom: Array<Omit<CustomResearchModule, 'id'>>, scheduler: ResearchModulePlan['scheduler'] = 'critical-path') {
  await openSettings(page);
  await page.locator('#module-plan-scheduler').selectOption(scheduler);
  await page.locator('#module-plan-context').selectOption('essential');
  for (const value of custom) await addRule(page, value);
  return editorPlan(page);
}
async function saved(page: Page, plan: ResearchModulePlan) {
  await page.waitForFunction(({ key, plan }) => {
    try { return JSON.stringify(JSON.parse(sessionStorage.getItem(key) || 'null')?.draft?.modulePlan) === JSON.stringify(plan); }
    catch { return false; }
  }, { key: storageKey, plan });
}
async function openLibrary(page: Page) {
  await openSettings(page);
  if (await page.locator('#module-plan-library').getAttribute('open') === null)
    await page.locator('#module-plan-library>summary').click();
}
async function libraryPlans(page: Page): Promise<SavedModulePlan[]> {
  return page.evaluate(key => JSON.parse(localStorage.getItem(key) || '{"plans":[]}').plans, modulePlanLibraryStorageKey);
}
async function libraryAction(page: Page, action: 'save' | 'copy' | 'load' | 'delete' | 'undo') {
  await page.locator(`[data-module-library-${action}]`).click();
  await page.locator('#module-plan-library:not([aria-busy="true"])').waitFor();
}
async function saveLibraryPlan(page: Page, name: string) {
  await openLibrary(page); await page.locator('#module-library-name').fill(name);
  await libraryAction(page, 'save');
  assert.match(await page.locator('[data-module-library-notice]').innerText(), /已保存/);
  return (await libraryPlans(page))[0]!;
}
async function exportDraft(page: Page): Promise<DraftEnvelope> {
  await showChat(page);
  const downloading = page.waitForEvent('download'); await page.locator('#export-draft').click();
  const downloaded = await downloading, content = await fs.readFile((await downloaded.path())!, 'utf8');
  assert.equal(content.includes(credential), false, 'exported module plans must not contain the API key');
  return JSON.parse(content) as DraftEnvelope;
}
async function importFile(page: Page, value: unknown, filename: string) {
  await showChat(page);
  const choosing = page.waitForEvent('filechooser'); await page.locator('#import-task').click();
  await (await choosing).setFiles({ name: filename, mimeType: 'application/json', buffer: Buffer.from(JSON.stringify(value)) });
  await page.locator('#import-task-dialog[open]').waitFor();
  await page.locator('#confirm-import').click(); await page.locator('#import-task-dialog').waitFor({ state: 'hidden' });
}
async function submitRun(h: Harness) {
  await closeSettings(h.page); await showChat(h.page);
  const submitted = h.page.waitForResponse(response => new URL(response.url()).pathname === '/api/runs' && response.request().method() === 'POST');
  await h.page.locator('#submit-run').click();
  const response = await submitted; assert.equal(response.status(), 201);
  const run = (await response.json() as { run: WebRun }).run;
  h.runIds.push(run.id); h.uiCreates++;
  assert.ok(controls.has(run.id), 'the controlled worker must start after UI submission');
  return run;
}
async function createRun(h: Harness, plan: ResearchModulePlan, workers = 2) {
  const input: WebRunInput = { providerId: 'openai', apiKey: credential, model: 'fixture-plan-model', effort: 'low', environment: 'standard',
    source: 'theorem plan_fixture : True := by sorry\n', task: 'Inspect configured research modules', maxTurns: 2, maxRunSeconds: 60, workers,
    coordination: workers > 1 ? 'cooperative' : 'independent', modulePlan: plan };
  const run = await postRun(h, input);
  h.runIds.push(run.id); assert.ok(controls.has(run.id)); return run;
}
async function sync(h: Harness, id: string) {
  const run = await readRun(h, id), sequence = run.events.at(-1)!.sequence;
  const observed = h.page.waitForResponse(async response => {
    if (new URL(response.url()).pathname !== '/api/runs' || response.request().method() !== 'GET' || response.status() !== 200) return false;
    const payload = await response.json() as { runs: WebRun[] };
    return payload.runs.some(run => run.id === id && run.events.at(-1)!.sequence >= sequence);
  });
  await h.page.evaluate(() => document.dispatchEvent(new Event('visibilitychange')));
  await observed; await settled(h.page); return run;
}
async function customState(page: Page, id: string, count: number, label: string) {
  const row = page.locator(`[data-module-custom-id="${id}"][data-applied-count="${count}"]`);
  await row.waitFor(); assert.equal(await row.locator('[data-module-custom-state]').innerText(), label);
}
async function policyText(page: Page, id: string) {
  const policy = page.locator(`[data-module-policy-id="${id}"]`);
  if (await policy.getAttribute('open') === null) await policy.locator('summary').click();
  return policy.locator('.module-policy-instructions').innerText();
}
async function selectedPolicy(page: Page, id: string, slot: CustomResearchModule['slot']) {
  await page.locator(`#module-inspector[data-module="${slot}"]`).waitFor();
  const policy = page.locator(`[data-module-policy-id="${id}"]`);
  assert.notEqual(await policy.getAttribute('open'), null, 'selecting a policy must open its exact details');
  assert.equal(await policy.getAttribute('data-selected'), 'true');
  assert.equal(await page.locator(`[data-module-custom-id="${id}"]`).getAttribute('aria-current'), 'true');
  assert.equal(await page.locator('[data-module-custom-id][aria-current="true"]').count(), 1);
  assert.equal(await policy.locator('summary').evaluate(summary => document.activeElement === summary), true,
    'explicit policy navigation must focus the selected summary');
  return policy;
}
async function openPolicyEditor(page: Page, id: string) {
  await page.locator(`[data-module-policy-edit="${id}"]`).click();
  await page.locator('#run-settings[open]').waitFor();
  const target = rule(page, id), instructions = target.locator('[data-module-plan-field="instructions"]');
  assert.equal(await target.getAttribute('data-expanded'), 'true', 'direct editing must reveal a folded policy');
  assert.equal(await instructions.isVisible(), true);
  assert.equal(await instructions.evaluate(control => document.activeElement === control), true,
    'direct editing must focus the selected policy instructions');
  return target;
}
async function horizontalFit(page: Page, selector: string) {
  const boxes = await page.locator(selector).evaluateAll(elements => elements.map(element => {
    const box = element.getBoundingClientRect(); return { x: box.x, right: box.right, width: box.width };
  }));
  assert.ok(boxes.length, `${selector} must exist`);
  for (const box of boxes) assert.ok(box.x >= -1 && box.width > 0 && box.right <= page.viewportSize()!.width + 1,
    `${selector} must fit ${page.viewportSize()!.width}px: ${JSON.stringify(box)}`);
  assert.equal(await page.evaluate(() => document.documentElement.scrollWidth <= innerWidth + 1), true, 'module plans must not widen the document');
}
async function screenshot(page: Page, name: string) {
  await page.screenshot({ path: path.join(output, name) }); screenshots.push(name);
}
const writeReport = (status: 'passed' | 'failed', error?: unknown) => writeScenarioReport(reportFile, suite, status, error,
  'Real local HTTP service and Chromium with a controlled in-process runner. No models, Docker, Lean or external requests.',
  { workerStarts, widths, checks, applicationChecks, screenshots }, { credential });
const enabledRule: Omit<CustomResearchModule, 'id'> = { name: 'Focused construction', slot: 'M1', mode: 'replace', enabled: true,
  instructions: 'Prefer a short direct proof and preserve every original declaration.' };
const disabledRule: Omit<CustomResearchModule, 'id'> = { name: 'Context strategy with a long name', slot: 'M4', mode: 'append', enabled: false, instructions: '' };

try {
  browser = await startBrowser(service.server, port);

  await scenario('Named module plans load and undo independently of the task, credentials and execution settings', async h => {
    const { page } = h;
    const original = await configure(page, [enabledRule, disabledRule]);
    await page.locator('#api-key').fill(credential);
    await page.locator('#max-turns').fill('7'); await page.locator('#max-seconds').fill('90'); await page.locator('#workers').fill('3');
    const savedPlan = await saveLibraryPlan(page, 'My research workflow');
    assert.deepEqual(savedPlan.plan, original);
    await page.locator('#module-plan-scheduler').selectOption('goals-first');
    await rule(page, original.custom[0]!.id).locator('[data-module-plan-field="instructions"]').fill('A task-specific strategy');
    const before = await editorPlan(page);
    const otherFields = async () => page.evaluate(() => Object.fromEntries(['source', 'task', 'api-key', 'max-turns', 'max-seconds', 'workers', 'model', 'environment', 'provider']
      .map(id => [id, (document.getElementById(id) as HTMLInputElement).value])));
    const preserved = await otherFields();
    await libraryAction(page, 'load');
    assert.deepEqual(await editorPlan(page), original); assert.deepEqual(await otherFields(), preserved);
    await saved(page, original);
    await closeSettings(page); await showArtifacts(page); await page.locator('#draft-tab-modules').click();
    assert.ok((await page.locator(`[data-module-custom-id="${original.custom[0]!.id}"]`).innerText()).includes(enabledRule.name));
    await showChat(page); await page.locator('#task').fill('An updated task after loading the module plan');
    h.expectedTask = await page.locator('#task').inputValue();
    await openLibrary(page); assert.equal(await page.locator('[data-module-library-undo]').isVisible(), true);
    await libraryAction(page, 'undo');
    assert.deepEqual(await editorPlan(page), before);
    assert.equal(await page.locator('#task').inputValue(), h.expectedTask);
    assert.equal(await page.locator('#api-key').inputValue(), credential);
    await libraryAction(page, 'load');
    await rule(page, original.custom[0]!.id).locator('[data-module-plan-field="enabled"]').uncheck();
    assert.equal(await page.locator('[data-module-library-undo]').isVisible(), false, 'further module edits must invalidate the load undo');
    assert.deepEqual((await libraryPlans(page))[0]!.plan, original, 'ordinary module edits must not mutate the saved snapshot');
    const stored = await page.evaluate(key => localStorage.getItem(key)!, modulePlanLibraryStorageKey);
    assert.equal(stored.includes(preserved.source!), false); assert.equal(stored.includes(credential), false);
  });

  await scenario('Saved unfinished plans remain editable and real submission still rejects invalid enabled rules', async h => {
    const { page } = h;
    const unfinished = await configure(page, [{ ...enabledRule, name: '', instructions: '' }]);
    const savedPlan = await saveLibraryPlan(page, 'Unfinished experiment');
    assert.deepEqual(savedPlan.plan, unfinished);
    await rule(page, unfinished.custom[0]!.id).locator('[data-module-plan-field="name"]').fill('Now completed');
    await rule(page, unfinished.custom[0]!.id).locator('[data-module-plan-field="instructions"]').fill('Use the installed library.');
    await libraryAction(page, 'load');
    await page.locator('#api-key').fill(credential);
    await page.locator('#settings-submit').click();
    await page.locator('#module-plan-error').waitFor();
    assert.match(await page.locator('#module-plan-error').innerText(), /名称/);
    assert.equal(h.runIds.length, 0); assert.deepEqual(await editorPlan(page), unfinished);
  });

  await scenario('Library updates, renames, copies and reversible deletion never change the current module plan', async h => {
    const { page } = h;
    const configured = await configure(page, [enabledRule]);
    const first = await saveLibraryPlan(page, markup.slice(0, 40));
    await rule(page, configured.custom[0]!.id).locator('[data-module-plan-field="instructions"]').fill('An updated saved strategy.');
    const updatedPlan = await editorPlan(page), updated = await saveLibraryPlan(page, 'Renamed workflow');
    assert.equal(updated.id, first.id); assert.deepEqual(updated.plan, updatedPlan);
    await libraryAction(page, 'copy');
    let entries = await libraryPlans(page);
    assert.equal(entries.length, 2); assert.notEqual(entries[0]!.id, first.id);
    assert.equal(entries[0]!.name, 'Renamed workflow 副本');
    await page.locator('#module-library-name').fill('Renamed workflow'); await libraryAction(page, 'save');
    assert.match(await page.locator('[data-module-library-notice]').innerText(), /同名/);
    assert.deepEqual(await libraryPlans(page), entries, 'a rejected rename must preserve both snapshots');
    await libraryAction(page, 'delete');
    assert.equal((await libraryPlans(page)).length, 1); assert.deepEqual(await editorPlan(page), updatedPlan);
    await libraryAction(page, 'undo');
    assert.deepEqual(await libraryPlans(page), entries); assert.deepEqual(await editorPlan(page), updatedPlan);
    await saved(page, updatedPlan); await page.reload(); await page.locator('#submit-run:enabled').waitFor();
    await openLibrary(page);
    assert.equal(await page.locator('#module-library-select option').count(), 3);
    assert.deepEqual(await editorPlan(page), updatedPlan);
    assert.deepEqual(await libraryPlans(page), entries);
  });

  await scenario('Reset and new research clear the selected library binding while retaining all saved plans', async h => {
    const { page } = h;
    await configure(page, [enabledRule]);
    const first = await saveLibraryPlan(page, 'Original workflow');
    await page.locator('#reset-form').click();
    assert.equal(await page.locator('#module-library-select').inputValue(), '');
    assert.equal(await page.locator('#module-library-name').inputValue(), '');
    const second = await saveLibraryPlan(page, 'New default workflow');
    assert.notEqual(second.id, first.id); assert.equal((await libraryPlans(page)).length, 2);
    assert.deepEqual((await libraryPlans(page)).find(entry => entry.id === first.id), first);
    await closeSettings(page); await page.locator('#new-research').click();
    await openLibrary(page);
    assert.equal(await page.locator('#module-library-select').inputValue(), '');
    const third = await saveLibraryPlan(page, 'Another research workflow');
    assert.equal((await libraryPlans(page)).length, 3); assert.notEqual(third.id, second.id);
  });

  await scenario('Other tabs retain sibling plans and stale selections cannot overwrite concurrent edits', async h => {
    const { page, context } = h;
    await configure(page, [enabledRule]);
    const first = await saveLibraryPlan(page, 'Shared workflow');
    const other = await context.newPage(); await other.goto(origin); await other.locator('#submit-run:enabled').waitFor();
    await openLibrary(other); await other.locator('#module-library-select').selectOption(first.id);
    const second = await saveLibraryPlan(page, 'Updated in first tab');
    await other.locator('#module-library-name').fill('A stale update');
    await libraryAction(other, 'save');
    assert.match(await other.locator('[data-module-library-notice]').innerText(), /其他页面/);
    assert.deepEqual(await libraryPlans(other), [second]);
    await other.locator('#module-library-select').selectOption('');
    await saveLibraryPlan(other, 'Independent workflow');
    await page.locator('#module-library-select option').filter({ hasText: 'Independent workflow' }).waitFor({ state: 'attached' });
    await libraryAction(page, 'delete');
    assert.deepEqual((await libraryPlans(page)).map(entry => entry.name), ['Independent workflow']);
    await other.locator('#module-library-select').selectOption(''); await saveLibraryPlan(other, 'Another independent workflow');
    await libraryAction(page, 'undo');
    assert.equal((await libraryPlans(page)).length, 3);
    assert.deepEqual((await libraryPlans(page)).find(entry => entry.id === second.id), second);
    await other.close();
  });

  await scenario('Storage failures do not report success or erase snapshots, and corrupt libraries remain untouched', async h => {
    const { page } = h;
    await configure(page, [enabledRule]);
    const first = await saveLibraryPlan(page, 'Persistent workflow');
    await page.evaluate(key => {
      const get = Storage.prototype.getItem;
      (window as unknown as { blockLibraryRead: boolean }).blockLibraryRead = true;
      Storage.prototype.getItem = function (name) {
        if (name === key && (window as unknown as { blockLibraryRead: boolean }).blockLibraryRead) throw new DOMException('Denied', 'SecurityError');
        return get.call(this, name);
      };
    }, modulePlanLibraryStorageKey);
    await page.locator('#module-library-select').selectOption('');
    assert.match(await page.locator('[data-module-library-notice]').innerText(), /无法读取/);
    assert.equal(await page.locator('#module-library-select').inputValue(), first.id, 'a failed selection must retain the visible binding');
    assert.equal(await page.locator('#module-library-name').inputValue(), first.name);
    await page.evaluate(() => { (window as unknown as { blockLibraryRead: boolean }).blockLibraryRead = false; });
    await page.evaluate(key => {
      const set = Storage.prototype.setItem;
      Storage.prototype.setItem = function (name, value) { if (name === key) throw new DOMException('Quota', 'QuotaExceededError'); return set.call(this, name, value); };
    }, modulePlanLibraryStorageKey);
    await page.locator('#module-library-name').fill('Not written'); await libraryAction(page, 'save');
    assert.match(await page.locator('[data-module-library-notice]').innerText(), /写入失败/);
    assert.deepEqual(await libraryPlans(page), [first]);
    await libraryAction(page, 'delete');
    assert.match(await page.locator('[data-module-library-notice]').innerText(), /写入失败/);
    assert.equal(await page.locator('#module-library-select').inputValue(), first.id);
    await page.reload(); await page.locator('#submit-run:enabled').waitFor();
    await page.evaluate(key => localStorage.setItem(key, 'corrupt-library-fixture'), modulePlanLibraryStorageKey);
    await openLibrary(page);
    assert.match(await page.locator('[data-module-library-notice]').innerText(), /格式无效/);
    await page.locator('#module-library-name').fill('Do not overwrite'); await libraryAction(page, 'save');
    assert.match(await page.locator('[data-module-library-notice]').innerText(), /格式无效/);
    assert.equal(await page.evaluate(key => localStorage.getItem(key), modulePlanLibraryStorageKey), 'corrupt-library-fixture');
  });

  await scenario('Simultaneous tab saves hold an origin lock and pending work cannot rebind a reset research draft', async h => {
    const { page, context } = h;
    const plan = await configure(page, [enabledRule]); await openLibrary(page);
    const other = await context.newPage(); await other.goto(origin); await other.locator('#submit-run:enabled').waitFor();
    await openLibrary(other);
    await Promise.all([page.locator('#module-library-name').fill('First simultaneous save'), other.locator('#module-library-name').fill('Second simultaneous save')]);
    await Promise.all([libraryAction(page, 'save'), libraryAction(other, 'save')]);
    assert.equal((await libraryPlans(page)).length, 2);
    await page.locator('#module-library-select').selectOption('');
    await page.locator('#module-library-name').fill('Save queued before reset');
    await other.evaluate(async key => {
      await new Promise<void>(acquired => {
        void navigator.locks.request(key, async () => {
          acquired(); await new Promise<void>(resolve => { (window as unknown as { releaseLibraryLock: () => void }).releaseLibraryLock = resolve; });
        });
      });
    }, modulePlanLibraryStorageKey);
    await page.locator('[data-module-library-save]').click();
    await page.locator('#module-plan-library[aria-busy="true"]').waitFor();
    await page.locator('#reset-form').click();
    await other.evaluate(() => (window as unknown as { releaseLibraryLock: () => void }).releaseLibraryLock());
    await page.locator('#module-plan-library[aria-busy="false"]').waitFor();
    assert.equal(await page.locator('#module-library-select').inputValue(), '');
    assert.equal(await page.locator('#module-library-name').inputValue(), '');
    assert.equal((await libraryPlans(page)).length, 3);
    assert.deepEqual((await libraryPlans(page)).find(entry => entry.name === 'Save queued before reset')!.plan, plan);
    await other.close();
  });

  await scenario('Missing browser locking support reports the prerequisite without writing an uncoordinated library', async h => {
    const { page } = h;
    await openLibrary(page);
    await page.evaluate(() => Object.defineProperty(navigator, 'locks', { configurable: true, value: undefined }));
    await page.locator('#module-library-name').fill('Unsupported write'); await libraryAction(page, 'save');
    assert.match(await page.locator('[data-module-library-notice]').innerText(), /HTTPS.*localhost/);
    assert.equal(await page.evaluate(key => localStorage.getItem(key), modulePlanLibraryStorageKey), null);
  });

  await scenario('Editing and conflicting replacement policies stay local and block invalid submission', async h => {
    const { page } = h;
    let plan = await configure(page, [enabledRule, disabledRule], 'goals-first');
    const first = plan.custom[0]!, second = plan.custom[1]!;
    await rule(page, first.id).locator('[data-module-plan-field="name"]').fill('Edited construction policy');
    await rule(page, first.id).locator('[data-module-plan-field="enabled"]').uncheck();
    assert.equal((await editorPlan(page)).custom[0]!.enabled, false);
    await rule(page, first.id).locator('[data-module-plan-field="enabled"]').check();
    const deleted = await addRule(page, { ...disabledRule, name: 'Disposable rule' });
    await rule(page, deleted).locator('[data-module-plan-delete]').click(); assert.equal(await page.locator(rows).count(), 2);
    await rule(page, second.id).locator('[data-module-plan-field="slot"]').selectOption('M1');
    await rule(page, second.id).locator('[data-module-plan-field="mode"]').selectOption('replace');
    await rule(page, second.id).locator('[data-module-plan-field="instructions"]').fill('An overlapping replacement must be rejected.');
    await rule(page, second.id).locator('[data-module-plan-field="enabled"]').check();
    await page.locator('#api-key').fill(credential);
    await closeSettings(page);
    if (await page.locator('#submit-run').isEnabled()) await page.locator('#submit-run').click();
    await openSettings(page); await page.locator('#module-plan-error').waitFor();
    assert.match(await page.locator('#module-plan-error').innerText(), /替换/);
    const conflictMode = rule(page, second.id).locator('[data-module-plan-field="mode"]');
    assert.equal(await conflictMode.getAttribute('aria-invalid'), 'true');
    const refreshed = page.waitForResponse(response => new URL(response.url()).pathname === '/api/runs' && response.request().method() === 'GET');
    await page.evaluate(() => document.dispatchEvent(new Event('visibilitychange')));
    await refreshed; await settled(page);
    assert.equal(await conflictMode.getAttribute('aria-invalid'), 'true', 'polling must preserve the conflicting replacement field marker');
    assert.equal(await page.locator('#module-plan-error').isVisible(), true);
    assert.equal(h.requests.filter(request => request.method === 'POST').length, 0, 'conflicting policies must be rejected before API creation');
    await screenshot(page, 'replacement-conflict.png');
    await rule(page, second.id).locator('[data-module-plan-field="enabled"]').uncheck();
    await rule(page, second.id).locator('[data-module-plan-field="instructions"]').fill('');
    plan = await editorPlan(page); await saved(page, plan);
    const exported = await exportDraft(page); assert.deepEqual(exported.draft.modulePlan, plan);
    assert.equal(plan.scheduler, 'goals-first'); assert.equal(plan.context, 'essential');
    assert.equal(plan.custom[0]!.name, 'Edited construction policy'); assert.equal(plan.custom[1]!.enabled, false);
    assert.equal(plan.custom[1]!.instructions, '', 'an unfinished disabled rule must remain editable and exportable');
  });

  await scenario('Duplicated policies are independent disabled drafts with unique names and a recoverable limit', async h => {
    const { page } = h;
    const originalPlan = await configure(page, [{ ...enabledRule, name: `${'A'.repeat(36)}\u{1D6C2}AB` }, disabledRule]);
    const original = originalPlan.custom[0]!;
    const duplicate = rule(page, original.id).locator('[data-module-plan-duplicate]');
    assert.match(await duplicate.getAttribute('title') ?? '', /默认停用/);
    await duplicate.locator('svg').click();
    let plan = await editorPlan(page);
    assert.equal(plan.custom.length, 3);
    const copy = plan.custom[1]!;
    assert.notEqual(copy.id, original.id);
    assert.notEqual(copy.name, original.name);
    assert.match(copy.name, / 副本$/);
    assert.ok(copy.name.length <= 40);
    assert.doesNotMatch(copy.name, /[\uD800-\uDFFF]/u, 'truncation must preserve complete Unicode characters');
    assert.deepEqual(copy, { ...original, id: copy.id, name: copy.name, enabled: false });
    assert.deepEqual(plan.custom[0], original);
    assert.deepEqual(plan.custom[2], originalPlan.custom[1]);
    const name = rule(page, copy.id).locator('[data-module-plan-field="name"]');
    assert.equal(await name.evaluate(control => control === document.activeElement), true);
    assert.deepEqual(await name.evaluate(control => [(control as HTMLInputElement).selectionStart, (control as HTMLInputElement).selectionEnd]), [0, copy.name.length]);
    await duplicate.click();
    plan = await editorPlan(page);
    assert.equal(plan.custom.length, 4);
    assert.notEqual(plan.custom[1]!.name, copy.name);
    assert.match(plan.custom[1]!.name, / 副本 2$/);
    await name.fill('Independent construction variant');
    await rule(page, copy.id).locator('[data-module-plan-field="instructions"]').fill('Try a different library lemma.');
    assert.deepEqual((await editorPlan(page)).custom[0], original, 'editing a copy must preserve its source policy');
    for (let count = 4; count < 8; count++) await duplicate.click();
    plan = await editorPlan(page);
    assert.equal(plan.custom.length, 8);
    assert.equal(new Set(plan.custom.map(module => module.id)).size, 8);
    assert.equal(new Set(plan.custom.map(module => module.name)).size, 8);
    assert.equal(plan.custom.filter(module => module.enabled).length, 1, 'copying a replacement must not introduce an enabled conflict');
    assert.ok(plan.custom.every(module => module.name.length <= 40));
    assert.equal(await page.locator('#module-plan-add').isDisabled(), true);
    assert.equal(await page.locator('[data-module-plan-duplicate]:disabled').count(), 8);
    assert.match(await duplicate.getAttribute('title') ?? '', /8/);
    await page.locator(rows).last().locator('[data-module-plan-delete]').click();
    assert.equal(await page.locator(rows).count(), 7);
    assert.equal(await page.locator('#module-plan-add').isEnabled(), true);
    assert.equal(await page.locator('[data-module-plan-duplicate]:enabled').count(), 7);
    await duplicate.click();
    plan = await editorPlan(page); await saved(page, plan);
    assert.equal(plan.custom.length, 8);
    assert.equal(new Set(plan.custom.map(module => module.id)).size, 8);
    assert.deepEqual((await exportDraft(page)).draft.modulePlan, plan);
    await page.reload(); await page.locator('#submit-run:enabled').waitFor(); await openSettings(page);
    assert.deepEqual(await editorPlan(page), plan);
    assert.equal(h.requests.filter(request => request.method === 'POST').length, 0, 'duplicating policies must stay local');
  });

  await scenario('Undo deletion restores the exact policy without overwriting later edits, ordering or reading state', async h => {
    const { page } = h;
    const initial = await configure(page, [enabledRule,
      { ...disabledRule, name: '<img data-plan-injection src=x>', slot: 'M3', instructions: markup },
      { ...disabledRule, name: 'Context policy', instructions: 'Keep the active interfaces and recent Lean feedback.' }]);
    const [first, removed, last] = initial.custom as [CustomResearchModule, CustomResearchModule, CustomResearchModule];
    await page.locator('#api-key').fill(credential);
    await rule(page, removed.id).locator('[data-module-plan-disclosure]').click();
    const originalRow = await rule(page, removed.id).elementHandle();
    await rule(page, removed.id).locator('[data-module-plan-delete]').click();
    assert.equal(await rule(page, removed.id).count(), 0);
    assert.equal(await page.locator('[data-module-plan-deleted-name]').innerText(), `已删除 ${removed.name}`);
    await rule(page, first.id).locator('[data-module-plan-field="name"]').fill('Edited after deletion');
    await rule(page, first.id).locator('[data-module-plan-field="instructions"]').fill('Preserve this later instruction.');
    await rule(page, last.id).locator('[data-module-plan-field="enabled"]').check();
    await rule(page, last.id).locator('[data-module-plan-move="up"]').click();
    const later = await editorPlan(page);
    await closeSettings(page); await showArtifacts(page); await page.locator('#draft-tab-modules').click();
    assert.equal(await page.locator(`[data-module-custom-id="${removed.id}"]`).count(), 0);
    await openSettings(page);
    const undo = page.locator('[data-module-plan-undo]');
    assert.equal(await undo.isEnabled(), true, 'closing settings must retain the undo record');
    await undo.focus(); await undo.press('Enter');
    const plan = { ...later, custom: [later.custom[0]!, removed, later.custom[1]!] };
    assert.deepEqual(await editorPlan(page), plan);
    assert.equal(await originalRow!.evaluate(row => row.isConnected), true, 'undo must retain the original editor controls');
    assert.equal(await rule(page, removed.id).getAttribute('data-expanded'), 'false');
    assert.equal(await rule(page, removed.id).locator('[data-module-plan-disclosure]').evaluate(button => button === document.activeElement), true);
    assert.equal(await page.locator('[data-module-plan-deletion]').isVisible(), false);
    await undo.dispatchEvent('click'); assert.deepEqual(await editorPlan(page), plan, 'repeated undo must not duplicate the policy');
    assert.equal(await page.locator('#api-key').inputValue(), credential);
    await saved(page, plan); await noInjection(page);
    await closeSettings(page); await showArtifacts(page); await page.locator('#draft-tab-modules').click();
    assert.deepEqual(await page.locator('[data-module-custom-id]').evaluateAll(items => items.map(item => (item as HTMLElement).dataset.moduleCustomId)), plan.custom.map(module => module.id));
    await page.reload(); await page.locator('#submit-run:enabled').waitFor();
    assert.deepEqual(await editorPlan(page), plan);
    assert.equal(await page.locator('#api-key').inputValue(), '');
    await openSettings(page);
    assert.equal(await page.locator('[data-module-plan-deletion]').isVisible(), false);
  });

  await scenario('Undo respects the policy limit and restores only the most recent deletion, including an empty list', async h => {
    const { page } = h;
    const initial = await configure(page, Array.from({ length: 8 }, (_, index) => ({ ...disabledRule, name: `Policy ${index + 1}` })));
    const removed = initial.custom[3]!;
    await rule(page, removed.id).locator('[data-module-plan-delete]').click();
    const extra = await addRule(page, { ...disabledRule, name: 'Added later' });
    const full = await editorPlan(page), undo = page.locator('[data-module-plan-undo]');
    assert.equal(full.custom.length, 8); assert.equal(await undo.isDisabled(), true);
    assert.match(await undo.getAttribute('title') ?? '', /8/);
    await undo.dispatchEvent('click'); assert.deepEqual(await editorPlan(page), full, 'undo must not exceed eight policies');
    await rule(page, extra).locator('[data-module-plan-delete]').click(); await undo.click();
    assert.deepEqual(await editorPlan(page), full, 'the latest deletion must replace the earlier undo record');
    assert.equal(await rule(page, removed.id).count(), 0);
    for (const module of full.custom) await rule(page, module.id).locator('[data-module-plan-delete]').click();
    assert.equal(await page.locator(rows).count(), 0);
    assert.equal(await undo.isEnabled(), true);
    const last = full.custom.at(-1)!;
    await undo.click();
    assert.deepEqual((await editorPlan(page)).custom, [last]);
    assert.equal(await rule(page, last.id).locator('[data-module-plan-field="name"]').evaluate(control => control === document.activeElement), true);
    await saved(page, await editorPlan(page));
  });

  await scenario('Restoring an enabled replacement preserves both rules and blocks conflicting submission', async h => {
    const { page } = h;
    const initial = await configure(page, [enabledRule]);
    await page.locator('#api-key').fill(credential);
    await rule(page, initial.custom[0]!.id).locator('[data-module-plan-delete]').click();
    const replacement = await addRule(page, { ...enabledRule, name: 'New replacement' });
    await page.locator('[data-module-plan-undo]').click();
    let plan = await editorPlan(page);
    assert.equal(plan.custom.length, 2); assert.ok(plan.custom.every(module => module.enabled));
    assert.deepEqual(plan.custom[0], initial.custom[0]);
    await page.locator('#settings-submit').click();
    assert.match(await page.locator('#module-plan-error').innerText(), /只能启用一个/);
    assert.equal(await rule(page, replacement).locator('[data-module-plan-field="mode"]').getAttribute('aria-invalid'), 'true');
    assert.equal(h.requests.filter(request => request.method === 'POST').length, 0);
    await rule(page, replacement).locator('[data-module-plan-field="enabled"]').uncheck();
    assert.equal(await page.locator('#module-plan-error').isVisible(), false);
    plan = await editorPlan(page); await saved(page, plan);
  });

  await scenario('Replacing a task or resetting its configuration clears the old deletion record', async h => {
    const { page } = h;
    const initial = await configure(page, [enabledRule]);
    await closeSettings(page);
    const exported = await exportDraft(page);
    await openSettings(page);
    await rule(page, initial.custom[0]!.id).locator('[data-module-plan-delete]').click();
    assert.equal(await page.locator('[data-module-plan-undo]').isEnabled(), true);
    await importFile(page, exported, 'unchanged-plan.json'); await openSettings(page);
    assert.deepEqual(await editorPlan(page), initial);
    assert.equal(await page.locator('[data-module-plan-deletion]').isVisible(), false);
    await page.locator('[data-module-plan-undo]').dispatchEvent('click'); assert.deepEqual(await editorPlan(page), initial);
    await rule(page, initial.custom[0]!.id).locator('[data-module-plan-delete]').click();
    assert.equal(await page.locator('[data-module-plan-undo]').isEnabled(), true);
    await page.locator('#reset-form').click();
    assert.deepEqual(await editorPlan(page), { scheduler: 'plan', context: 'full', custom: [] });
    assert.equal(await page.locator('[data-module-plan-deletion]').isVisible(), false);
    await page.locator('[data-module-plan-undo]').dispatchEvent('click');
    assert.equal(await page.locator(rows).count(), 0);
  }, 375);

  await scenario('Policy folding and ordering preserve content, keyboard focus and hidden error recovery', async h => {
    const { page } = h;
    const initial = await configure(page, [enabledRule, disabledRule,
      { ...enabledRule, name: 'Alternate construction advice', mode: 'append', instructions: 'Try a library lemma before splitting cases.' }]);
    const [first, second, third] = initial.custom as [CustomResearchModule, CustomResearchModule, CustomResearchModule];
    const move = (id: string, direction: string) => rule(page, id).locator(`[data-module-plan-move="${direction}"]`);
    assert.equal(await move(first.id, 'up').isDisabled(), true);
    assert.equal(await move(third.id, 'down').isDisabled(), true);
    await page.locator('[data-module-plan-collapse-all]').click();
    assert.equal(await page.locator(`${rows}[data-expanded="false"]`).count(), 3);
    assert.equal(await rule(page, first.id).locator('.module-plan-summary-name').innerText(), first.name);
    assert.match(await rule(page, first.id).locator('.module-plan-summary-meta').innerText(), /M1.*替换/);
    assert.deepEqual(await editorPlan(page), initial, 'folding must only change the reading state');
    const disclosure = rule(page, first.id).locator('[data-module-plan-disclosure]');
    await disclosure.focus(); await disclosure.press('Enter');
    assert.equal(await disclosure.getAttribute('aria-expanded'), 'true');
    assert.equal(await rule(page, first.id).locator('[data-module-plan-field="instructions"]').isVisible(), true);
    await disclosure.press('Space');
    assert.equal(await disclosure.getAttribute('aria-expanded'), 'false');
    await move(third.id, 'up').click();
    let plan = await editorPlan(page);
    assert.deepEqual(plan.custom, [first, third, second]);
    assert.equal(await page.locator(`${rows}[data-expanded="false"]`).count(), 3, 'moving must preserve folded rows');
    assert.equal(await move(third.id, 'up').evaluate(button => button === document.activeElement), true);
    await move(third.id, 'up').press('Enter');
    assert.deepEqual((await editorPlan(page)).custom, [third, first, second]);
    assert.equal(await move(third.id, 'up').isDisabled(), true);
    assert.equal(await move(third.id, 'down').evaluate(button => button === document.activeElement), true, 'boundary moves must retain focus on an available action');
    await move(third.id, 'down').press('Enter'); await move(third.id, 'down').press('Enter');
    assert.deepEqual(await editorPlan(page), initial, 'moving back must preserve every field and identity');
    assert.equal(await move(third.id, 'down').isDisabled(), true);
    assert.equal(await move(third.id, 'up').evaluate(button => button === document.activeElement), true);
    await move(third.id, 'up').press('Enter');
    assert.deepEqual((await editorPlan(page)).custom, [first, third, second]);
    await rule(page, second.id).locator('[data-module-plan-field="enabled"]').check();
    assert.equal(await rule(page, second.id).getAttribute('data-expanded'), 'false');
    await page.locator('#api-key').fill(credential); await closeSettings(page);
    if (await page.locator('#submit-run').isEnabled()) await page.locator('#submit-run').click();
    await openSettings(page); await page.locator('#module-plan-error').waitFor();
    const missingRule = rule(page, second.id).locator('[data-module-plan-field="instructions"]');
    assert.equal(await missingRule.isVisible(), true, 'validation must reveal a folded invalid field');
    assert.equal(await missingRule.getAttribute('aria-invalid'), 'true');
    assert.equal(await missingRule.evaluate(control => control === document.activeElement), true);
    assert.equal(await rule(page, first.id).getAttribute('data-expanded'), 'false', 'validation must preserve unrelated reading state');
    await rule(page, second.id).locator('[data-module-plan-field="enabled"]').uncheck();
    assert.equal(await page.locator('#module-plan-error').isVisible(), false);
    await page.locator('[data-module-plan-expand-all]').click();
    assert.equal(await page.locator(`${rows}[data-expanded="true"]`).count(), 3);
    plan = await editorPlan(page); await saved(page, plan);
    const exported = await exportDraft(page); assert.deepEqual(exported.draft.modulePlan, plan);
    await showArtifacts(page); await page.locator('#draft-tab-modules').click();
    assert.deepEqual(await page.locator('[data-module-custom-id]').evaluateAll(items => items.map(item => (item as HTMLElement).dataset.moduleCustomId)), plan.custom.map(item => item.id));
    await page.locator('[data-module-id="M1"]').click();
    assert.deepEqual(await page.locator('[data-module-policy-id]').evaluateAll(items => items.map(item => (item as HTMLElement).dataset.modulePolicyId)), [first.id, third.id]);
    await page.reload(); await page.locator('#submit-run:enabled').waitFor(); await openSettings(page);
    assert.deepEqual(await editorPlan(page), plan, 'refresh must preserve the edited policy order');
    assert.equal(h.requests.filter(request => request.method === 'POST').length, 0, 'folding, ordering and validation must stay local');
  });

  await scenario('Policy navigation edits the exact draft and restores focus after moving or deleting it', async h => {
    const { page } = h;
    const initial = await configure(page, [enabledRule,
      { ...enabledRule, name: 'Second construction policy', mode: 'append' },
      { ...enabledRule, name: 'Third construction policy', mode: 'append', instructions: 'Inspect the current goal before searching.' }]);
    const [first, second, third] = initial.custom as [CustomResearchModule, CustomResearchModule, CustomResearchModule];
    await page.locator('#api-key').fill(credential);
    await page.locator('[data-module-plan-collapse-all]').click();
    await closeSettings(page); await showArtifacts(page); await page.locator('#draft-tab-modules').click();
    await page.locator(`[data-module-custom-id="${third.id}"]`).click();
    await selectedPolicy(page, third.id, 'M1');
    assert.equal(await page.locator('[data-module-policy-id][open]').count(), 1,
      'selecting the third rule must not open another rule in the same module');
    assert.equal(await page.locator(`[data-module-policy-id="${first.id}"]`).getAttribute('open'), null);
    assert.equal(await page.locator(`[data-module-policy-id="${second.id}"]`).getAttribute('open'), null);
    const beforeScroll = await page.locator('#draft-preview').evaluate(panel => panel.scrollTop);
    const refreshed = page.waitForResponse(response => new URL(response.url()).pathname === '/api/runs' && response.request().method() === 'GET');
    await page.evaluate(() => document.dispatchEvent(new Event('visibilitychange')));
    await refreshed; await settled(page);
    await selectedPolicy(page, third.id, 'M1');
    assert.ok(Math.abs(await page.locator('#draft-preview').evaluate(panel => panel.scrollTop) - beforeScroll) <= 1.5,
      'polling must retain the selected policy reading position');
    const target = await openPolicyEditor(page, third.id);
    assert.equal(await rule(page, first.id).getAttribute('data-expanded'), 'false', 'direct editing must preserve unrelated folds');
    await target.locator('[data-module-plan-field="name"]').fill('Edited context policy');
    await target.locator('[data-module-plan-field="instructions"]').fill('Retain the exact interfaces needed for the next proof step.');
    await target.locator('[data-module-plan-field="slot"]').selectOption('M4');
    let plan = await editorPlan(page);
    assert.deepEqual(plan.custom.slice(0, 2), initial.custom.slice(0, 2), 'direct editing must preserve other policies');
    assert.deepEqual(plan.custom[2], { ...third, name: 'Edited context policy', slot: 'M4',
      instructions: 'Retain the exact interfaces needed for the next proof step.' });
    await closeSettings(page);
    const policy = await selectedPolicy(page, third.id, 'M4');
    assert.equal(await policy.locator('.module-policy-name').innerText(), plan.custom[2]!.name);
    assert.equal(await policy.locator('.module-policy-instructions').innerText(), plan.custom[2]!.instructions);
    assert.equal(await page.locator('[data-module-id="M4"]').getAttribute('aria-pressed'), 'true');
    await saved(page, plan); await noStoredKey(page);
    await openPolicyEditor(page, third.id);
    await rule(page, third.id).locator('[data-module-plan-delete]').click();
    plan = await editorPlan(page); assert.deepEqual(plan.custom, initial.custom.slice(0, 2));
    await closeSettings(page);
    assert.equal(await page.locator(`[data-module-policy-id="${third.id}"]`).count(), 0);
    assert.equal(await page.locator('[data-module-custom-id][aria-current="true"]').count(), 0);
    assert.equal(await page.locator('[data-module-id="M4"]').getAttribute('aria-pressed'), 'true');
    assert.equal(await page.locator('[data-module-id="M4"]').evaluate(node => document.activeElement === node), true,
      'deleting the edited policy must return focus to its selected module');
    await saved(page, plan);
    assert.equal(h.requests.filter(request => request.method === 'POST').length, 0, 'policy navigation and direct edits must remain local');
  });

  await scenario('Draft module actions create scoped disabled policies and keep submitted plans read-only', async h => {
    const { page } = h;
    await showArtifacts(page); await page.locator('#draft-tab-modules').click();
    const slots = ['M1', 'M3', 'M4', 'M5'] as const;
    for (const id of ['M2', 'S3']) {
      await page.locator(`[data-module-id="${id}"]`).click();
      assert.equal(await page.locator('[data-module-policy-add]').isVisible(), false, `${id} must not offer configurable rules`);
    }
    let plan = await editorPlan(page);
    for (const slot of [...slots, ...slots]) {
      await page.locator(`[data-module-id="${slot}"]`).click();
      const add = page.locator(`[data-module-policy-add="${slot}"]`);
      assert.equal(await add.isVisible(), true); assert.equal(await add.isEnabled(), true);
      const before = plan.custom.length;
      await add.click(); await page.locator('#run-settings[open]').waitFor();
      plan = await editorPlan(page); assert.equal(plan.custom.length, before + 1);
      const created = plan.custom.at(-1)!;
      assert.deepEqual(created, { id: created.id, name: `自定义策略 ${before + 1}`, slot, mode: 'append', enabled: false, instructions: '' });
      const name = rule(page, created.id).locator('[data-module-plan-field="name"]');
      assert.equal(await name.evaluate(control => document.activeElement === control), true, 'scoped creation must focus the new name');
      assert.deepEqual(await name.evaluate(control => [(control as HTMLInputElement).selectionStart, (control as HTMLInputElement).selectionEnd]), [0, created.name.length]);
      await closeSettings(page); await selectedPolicy(page, created.id, slot);
    }
    for (const slot of slots) {
      await page.locator(`[data-module-id="${slot}"]`).click();
      const add = page.locator(`[data-module-policy-add="${slot}"]`);
      assert.equal(await add.isVisible(), true); assert.equal(await add.isDisabled(), true);
      assert.match(await add.getAttribute('title') ?? '', /8/);
      await add.dispatchEvent('click');
      assert.equal(await page.locator('#run-settings[open]').count(), 0, 'the full plan must not create another policy');
    }
    assert.deepEqual(await editorPlan(page), plan); await saved(page, plan);
    assert.equal(h.requests.filter(request => request.method === 'POST').length, 0, 'scoped creation must not submit a run');
    const run = await createRun(h, plan); await selectModules(h, run.id);
    assert.equal(await page.locator('[data-module-configure]').isVisible(), false);
    for (const slot of slots) {
      await page.locator(`[data-module-id="${slot}"]`).click();
      assert.equal(await page.locator('[data-module-policy-add]').isVisible(), false);
      const configured = plan.custom.find(module => module.slot === slot)!;
      await page.locator(`[data-module-custom-id="${configured.id}"]`).click();
      await selectedPolicy(page, configured.id, slot);
      const edit = page.locator(`[data-module-policy-edit="${configured.id}"]`);
      assert.equal(await edit.isVisible(), false, 'submitted rule details must be read-only');
      await edit.dispatchEvent('click'); await page.locator('[data-module-policy-add]').dispatchEvent('click');
      assert.equal(await page.locator('#run-settings[open]').count(), 0, 'submitted plans must reject draft editing actions');
    }
    assert.deepEqual((await readRun(h, run.id)).modulePlan, plan);
    assert.deepEqual(received.get(run.id)!.modulePlan, plan, 'viewing submitted policies must preserve the worker configuration');
    assert.deepEqual(await editorPlan(page), plan);
  });

  await scenario('Graph switches preserve reading state, synchronize the draft and reject edits during or after submission', async h => {
    const { page } = h;
    const initial = await configure(page, [enabledRule,
      { ...disabledRule, name: 'Search policy', slot: 'M3', instructions: 'Revisit the remaining goal before retrying.' },
      { ...disabledRule, name: 'Review policy', slot: 'M5', instructions: 'Review the proposed interface before integration.' }]);
    const [first, second] = initial.custom as [CustomResearchModule, CustomResearchModule, CustomResearchModule];
    await page.locator('#api-key').fill(credential); await page.locator('[data-module-plan-collapse-all]').click();
    await closeSettings(page); await showArtifacts(page); await page.locator('#draft-tab-modules').click();
    await page.locator('[data-module-id="M4"]').click();
    const toggle = graphToggle(page, first.id), originalToggle = await toggle.elementHandle();
    await toggle.focus(); await settled(page);
    const top = await page.locator('#draft-preview').evaluate(panel => panel.scrollTop);
    await toggle.press('Space');
    let plan = await editorPlan(page);
    assert.deepEqual(plan.custom, [{ ...first, enabled: false }, ...initial.custom.slice(1)]);
    assert.equal(await toggle.isChecked(), false);
    assert.equal(await rule(page, first.id).locator('[data-module-plan-field="enabled"]').isChecked(), false);
    assert.equal(await rule(page, first.id).getAttribute('data-expanded'), 'false');
    assert.equal(await originalToggle!.evaluate(control => document.activeElement === control), true);
    assert.equal(await page.locator('#module-inspector').getAttribute('data-module'), 'M4');
    assert.ok(Math.abs(await page.locator('#draft-preview').evaluate(panel => panel.scrollTop) - top) <= 1.5);
    assert.equal(await page.locator('#run-settings[open]').count(), 0, 'a valid graph switch must stay in the workspace');
    await toggle.press('Space');
    await graphToggle(page, second.id).focus(); await graphToggle(page, second.id).press('Space');
    plan = await editorPlan(page);
    assert.deepEqual(plan, { ...initial, custom: initial.custom.map(module => module.id === second.id ? { ...module, enabled: true } : module) });
    assert.equal(await page.locator('[data-module-custom-count]').innerText(), '2 / 3 已启用');
    assert.equal(await page.locator('[data-module-id="M3"] .module-node-subject').innerText(), '1 个自定义策略');
    assert.equal(await page.locator('#module-inspector').getAttribute('data-module'), 'M4');
    assert.equal(await page.locator('button input[data-module-custom-enabled]').count(), 0, 'switches must not nest inside navigation buttons');
    await saved(page, plan);
    assert.equal(h.requests.filter(request => request.method === 'POST').length, 0);

    let release!: () => void, observed!: () => void, submittedRun: WebRun | undefined;
    const held = new Promise<void>(resolve => { release = resolve; });
    const created = new Promise<void>(resolve => { observed = resolve; });
    h.intercept = async route => {
      if (route.request().method() !== 'POST' || new URL(route.request().url()).pathname !== '/api/runs') return false;
      const response = await route.fetch(); assert.equal(response.status(), 201);
      submittedRun = (await response.json() as { run: WebRun }).run;
      h.runIds.push(submittedRun.id); h.uiCreates++; observed();
      await held; await route.fulfill({ response }); return true;
    };
    try {
      await page.locator('#submit-run').click(); await created;
      assert.equal(await graphToggle(page, second.id).isDisabled(), true, 'submitting must disable graph switches');
      await graphToggle(page, second.id).evaluate(control => {
        (control as HTMLInputElement).checked = false; control.dispatchEvent(new Event('change', { bubbles: true }));
      });
      assert.equal(await graphToggle(page, second.id).isChecked(), true, 'a queued submission must reject forced changes');
      assert.deepEqual(await editorPlan(page), plan);
      assert.deepEqual(submittedRun!.modulePlan, plan); assert.deepEqual(received.get(submittedRun!.id)!.modulePlan, plan);
    } finally { release(); }
    await page.locator('#return-to-draft').waitFor(); h.expectedTask = ''; h.intercept = undefined;
    await selectModules(h, submittedRun!.id);
    for (const module of plan.custom) {
      const frozen = graphToggle(page, module.id);
      assert.equal(await frozen.isVisible(), false); assert.equal(await frozen.isDisabled(), true);
      await frozen.evaluate(control => {
        const input = control as HTMLInputElement;
        input.checked = !input.checked; input.dispatchEvent(new Event('change', { bubbles: true }));
      });
      assert.equal(await frozen.isChecked(), module.enabled, 'submitted plans must restore their frozen switch state');
    }
    assert.deepEqual(await editorPlan(page), plan);
    assert.deepEqual((await readRun(h, submittedRun!.id)).modulePlan, plan);
  });

  await scenario('Enabling unfinished or conflicting graph policies reveals the exact field without creating a run', async h => {
    const { page } = h;
    const initial = await configure(page, [enabledRule, { ...disabledRule, name: 'Alternative construction', slot: 'M1', mode: 'replace' }]);
    const pending = initial.custom[1]!;
    await page.locator('[data-module-plan-collapse-all]').click(); await closeSettings(page);
    await showArtifacts(page); await page.locator('#draft-tab-modules').click();
    await graphToggle(page, pending.id).focus(); await graphToggle(page, pending.id).press('Space');
    await page.locator('#run-settings[open]').waitFor();
    const instructions = rule(page, pending.id).locator('[data-module-plan-field="instructions"]');
    assert.equal(await instructions.isVisible(), true); assert.equal(await instructions.getAttribute('aria-invalid'), 'true');
    assert.equal(await instructions.evaluate(control => document.activeElement === control), true);
    assert.match(await page.locator('#module-plan-error').innerText(), /填写规则/);
    await instructions.fill('Inspect an alternative proof before committing to a construction.');
    await rule(page, pending.id).locator('[data-module-plan-field="enabled"]').uncheck();
    assert.equal(await page.locator('#module-plan-error').isVisible(), false);
    await closeSettings(page); await selectedPolicy(page, pending.id, 'M1');
    await graphToggle(page, pending.id).focus(); await graphToggle(page, pending.id).press('Space');
    await page.locator('#run-settings[open]').waitFor();
    const mode = rule(page, pending.id).locator('[data-module-plan-field="mode"]');
    assert.equal(await mode.getAttribute('aria-invalid'), 'true');
    assert.equal(await mode.evaluate(control => document.activeElement === control), true);
    assert.match(await page.locator('#module-plan-error').innerText(), /只能启用一个/);
    assert.equal((await editorPlan(page)).custom[0]!.enabled, true, 'enabling a replacement must not silently disable another rule');
    await screenshot(page, 'graph-switch-conflict.png');
    await mode.selectOption('append'); assert.equal(await page.locator('#module-plan-error').isVisible(), false);
    await closeSettings(page); await selectedPolicy(page, pending.id, 'M1');
    assert.equal(await graphToggle(page, pending.id).isChecked(), true);
    await saved(page, await editorPlan(page));
    assert.equal(h.requests.filter(request => request.method === 'POST').length, 0);
  }, 320);

  await scenario('Module plans survive refresh and draft or archive roundtrips without saving a credential', async h => {
    const { page } = h;
    const plan = await configure(page, [enabledRule, { ...disabledRule, name: '<img data-plan-injection src=x>', instructions: markup }], 'continuation');
    await page.locator('#api-key').fill(credential); await saved(page, plan); await noStoredKey(page);
    const exported = await exportDraft(page); assert.deepEqual(exported.draft.modulePlan, plan);
    await page.reload(); await page.locator('#submit-run:enabled').waitFor(); await openSettings(page);
    assert.deepEqual(await editorPlan(page), plan); assert.equal(await page.locator('#api-key').inputValue(), '');
    await page.locator('#module-plan-scheduler').selectOption('primary-led'); await page.locator('#api-key').fill(credential);
    await importFile(page, exported, 'module-plan-draft.json'); await openSettings(page);
    assert.deepEqual(await editorPlan(page), plan); assert.equal(await page.locator('#api-key').inputValue(), '');
    const draft = exported.draft, now = new Date().toISOString();
    const archived = { schema: 'theorem-os.web-export.v1', run: { ...draft, id: crypto.randomUUID(), title: 'Archived plan fixture',
      status: 'completed', phase: 'finished', createdAt: now, updatedAt: now, events: [],
      maxTurns: Number(draft.maxTurns), maxRunSeconds: Number(draft.maxRunSeconds), workers: Number(draft.workers) } };
    await page.locator('#module-plan-context').selectOption('full'); await page.locator('#api-key').fill(credential);
    await importFile(page, archived, 'module-plan-archive.json'); await openSettings(page);
    assert.deepEqual(await editorPlan(page), plan); assert.equal(await page.locator('#api-key').inputValue(), ''); await saved(page, plan);
    await closeSettings(page); await showArtifacts(page); await page.locator('#draft-tab-modules').click();
    await page.locator(`[data-module-custom-id="${plan.custom[1]!.id}"]`).click();
    assert.equal(await policyText(page, plan.custom[1]!.id), markup); await noInjection(page);
    assert.equal(await page.locator('.module-node[data-tone="active"],.module-node[data-tone="passed"]').count(), 0, 'configuration alone must not fabricate model activity or acceptance');
  });

  await scenario('UI submission freezes its module plan and task reuse restores that snapshot with an empty key', async h => {
    const { page } = h;
    const draftSource = await page.locator('#source').inputValue();
    let plan = await configure(page, [enabledRule, { name: 'Review coordination', slot: 'M5', mode: 'append', enabled: true, instructions: 'Review before integration.' }]);
    await rule(page, plan.custom[1]!.id).locator('[data-module-plan-move="up"]').click(); plan = await editorPlan(page);
    await page.locator('#api-key').fill(credential);
    const run = await submitRun(h); assert.deepEqual(run.modulePlan, plan); assert.deepEqual(received.get(run.id)!.modulePlan, plan);
    await showChat(page); await page.locator('#return-to-draft').click(); await openSettings(page);
    await rule(page, plan.custom[0]!.id).locator('[data-module-plan-field="name"]').fill('Changed later draft');
    await rule(page, plan.custom[0]!.id).locator('[data-module-plan-field="enabled"]').uncheck();
    await page.locator('#module-plan-scheduler').selectOption('primary-led'); await page.locator('#api-key').fill(credential);
    assert.notDeepEqual(await editorPlan(page), plan);
    assert.equal(await page.locator('#source').inputValue(), draftSource, 'module edits must preserve the existing source before explicit task reuse');
    assert.deepEqual((await readRun(h, run.id)).modulePlan, plan, 'later draft edits must not mutate a running plan');
    assert.deepEqual(received.get(run.id)!.modulePlan, plan, 'the controlled worker must retain its submitted plan');
    await closeSettings(page); await selectModules(h, run.id);
    assert.ok((await page.locator(`[data-module-custom-id="${plan.custom[0]!.id}"]`).innerText()).includes(plan.custom[0]!.name));
    await page.locator('[data-action="reuse-run"]').click(); await page.locator('#run-settings[open]').waitFor();
    h.expectedSource = run.source; h.expectedTask = run.task;
    assert.deepEqual(await editorPlan(page), plan); assert.equal(await page.locator('#api-key').inputValue(), '');
    assert.equal(h.requests.filter(request => request.method === 'POST').length, 1, 'reuse must not submit another run');
    await saved(page, plan);
  });

  await scenario('Submitting from a mobile policy editor opens the conversation without a delayed workspace return', async h => {
    const { page } = h;
    const plan = await configure(page, [enabledRule]), policy = plan.custom[0]!;
    const disposable = await addRule(page, { ...disabledRule, name: 'Deleted before submission' });
    await rule(page, disposable).locator('[data-module-plan-delete]').click();
    assert.equal(await page.locator('[data-module-plan-undo]').isEnabled(), true);
    await closeSettings(page); await showArtifacts(page); await page.locator('#draft-tab-modules').click();
    await page.locator(`[data-module-custom-id="${policy.id}"]`).click();
    await openPolicyEditor(page, policy.id);
    await page.locator('#api-key').fill(credential);
    const submitted = page.waitForResponse(response => new URL(response.url()).pathname === '/api/runs' && response.request().method() === 'POST');
    await closeDialog(page, '#run-settings', () => page.locator('#settings-submit').click());
    const response = await submitted; assert.equal(response.status(), 201);
    const run = (await response.json() as { run: WebRun }).run;
    h.runIds.push(run.id); h.uiCreates++; h.expectedTask = '';
    await page.locator('#return-to-draft').waitFor();
    assert.equal(await page.locator('body').getAttribute('data-mobile-view'), 'compose');
    assert.equal(await page.locator('#compose-panel').isVisible(), true);
    assert.equal(await page.locator('#runs-panel').isVisible(), false);
    assert.deepEqual(run.modulePlan, plan); assert.deepEqual(received.get(run.id)!.modulePlan, plan);
    assert.equal(await page.locator('#api-key').inputValue(), '');
    await openSettings(page);
    assert.equal(await page.locator('[data-module-plan-deletion]').isVisible(), false, 'submission must clear the previous draft deletion');
    await page.locator('[data-module-plan-undo]').dispatchEvent('click');
    assert.deepEqual(await editorPlan(page), plan);
  }, 320);

  await scenario('Only actual custom application events update counts, and retained summaries survive rotation and reload', async h => {
    const { page } = h;
    const plan: ResearchModulePlan = { scheduler: 'critical-path', context: 'essential', custom: [
      { ...enabledRule, id: 'custom_construct' }, { ...disabledRule, id: 'custom_disabled' },
      { id: 'custom_review', name: 'Review coordination', slot: 'M5', mode: 'append', enabled: true, instructions: 'Review before integration.' },
    ] };
    const run = await createRun(h, plan), control = controls.get(run.id)!;
    await selectModules(h, run.id);
    await customState(page, 'custom_construct', 0, '待应用'); await customState(page, 'custom_disabled', 0, '已停用');
    control.progress('custom_module_applied', 'Construction policy applied', { moduleId: 'custom_construct', slot: 'M1', mode: 'replace' });
    control.progress('custom_module_applied', 'Construction policy applied again', { moduleId: 'custom_construct', slot: 'M1', mode: 'replace' });
    control.progress('custom_module_applied', 'Coordination policy applied', { moduleId: 'custom_review', slot: 'M5', mode: 'append' });
    await sync(h, run.id); await customState(page, 'custom_construct', 2, '已应用 2 次'); await customState(page, 'custom_review', 1, '已应用 1 次');
    await customState(page, 'custom_disabled', 0, '已停用');
    assert.equal(await page.locator('.module-node[data-tone="active"],.module-node[data-tone="passed"]').count(), 0, 'policy application must not invent a model turn or successful proof');
    for (let index = 0; index < 210; index++) control.progress('diagnostic', `Unrelated retained log ${index + 1}`);
    const snapshot = await sync(h, run.id);
    assert.equal(snapshot.events.length, 200); assert.equal(snapshot.events.some(event => event.type === 'custom_module_applied'), false);
    assert.equal(snapshot.moduleApplications!.custom_construct!.eventCount, 2); assert.equal(snapshot.moduleApplications!.custom_review!.eventCount, 1);
    assert.equal(snapshot.moduleApplications?.custom_disabled, undefined);
    await page.reload(); await page.locator('#submit-run:enabled').waitFor(); await selectModules(h, run.id);
    await customState(page, 'custom_construct', 2, '已应用 2 次'); await customState(page, 'custom_review', 1, '已应用 1 次');
    await page.locator('[data-module-custom-id="custom_construct"]').click();
    await page.locator('#module-inspector[data-module="M1"]').waitFor();
    assert.equal(await policyText(page, 'custom_construct'), enabledRule.instructions);
    applicationChecks.push({ runId: run.id, retainedEvents: snapshot.events.length, applications: { custom_construct: 2, custom_review: 1 } });
    await screenshot(page, 'retained-custom-applications.png');
    const independent = await createRun(h, plan, 1); await selectModules(h, independent.id);
    await customState(page, 'custom_review', 0, '当前模式不参与');
  });

  for (const width of widths) await scenario(`Custom module configuration and graph fit at ${width}px`, async h => {
    const { page } = h;
    let plan = await configure(page, [enabledRule, disabledRule]);
    await rule(page, plan.custom[0]!.id).locator('[data-module-plan-duplicate]').click();
    plan = await editorPlan(page);
    assert.equal(plan.custom.length, 3); assert.equal(plan.custom[1]!.enabled, false);
    await page.locator('#module-plan').scrollIntoViewIfNeeded();
    for (const selector of ['#run-settings', '#module-plan', rows, '[data-module-plan-field]', '.module-plan-view-actions', '[data-module-plan-disclosure]', '[data-module-plan-move]', '[data-module-plan-duplicate]', '[data-module-plan-delete]', '#module-plan-add']) await horizontalFit(page, selector);
    assert.equal(await page.locator('.module-plan-row-heading,.module-plan-row-actions').evaluateAll(headings => headings.every(heading => {
      const parent = heading.getBoundingClientRect(), boxes = Array.from(heading.children, child => child.getBoundingClientRect());
      return boxes.every((box, index) => box.width > 0 && box.left >= parent.left - 1 && box.right <= parent.right + 1
        && boxes.slice(0, index).every(previous => box.left >= previous.right - 1 || box.right <= previous.left + 1
          || box.top >= previous.bottom - 1 || box.bottom <= previous.top + 1));
    })), true, 'policy labels, toggle and actions must fit without overlapping');
    await screenshot(page, `module-plan-${width}-settings.png`);
    await page.locator('#module-plan').evaluate(section => section.scrollIntoView({ block: 'start', behavior: 'instant' }));
    await settled(page); await screenshot(page, `module-plan-${width}-settings-top.png`);
    await saveLibraryPlan(page, '研究方案'.repeat(10));
    for (const selector of ['#module-plan-library', '#module-plan-library>summary', '.module-library-selection', '#module-library-select', '#module-library-name', '.module-library-actions', '.module-library-notice'])
      await horizontalFit(page, selector);
    assert.equal(await page.locator('.module-library-selection,.module-library-actions').evaluateAll(groups => groups.every(group => {
      const boxes = Array.from(group.children, child => child.getBoundingClientRect()).filter(box => box.width > 0);
      return boxes.every((box, index) => boxes.slice(0, index).every(previous => box.left >= previous.right - 1 || box.right <= previous.left + 1));
    })), true, 'library controls must not overlap');
    await page.locator('#module-plan').evaluate(section => section.scrollIntoView({ block: 'start', behavior: 'instant' }));
    await screenshot(page, `module-library-${width}.png`);
    await page.locator('#module-plan-library>summary').click();
    await page.locator('[data-module-plan-collapse-all]').click();
    assert.equal(await page.locator(`${rows}[data-expanded="false"]`).count(), 3);
    for (const selector of ['.module-plan-disclosure', '.module-plan-summary-name', '.module-plan-summary-meta', '.module-plan-row-actions']) await horizontalFit(page, selector);
    const deletedPolicy = plan.custom[1]!;
    await rule(page, deletedPolicy.id).locator('[data-module-plan-delete]').click();
    for (const selector of ['[data-module-plan-deletion]', '[data-module-plan-deleted-name]', '[data-module-plan-undo]']) await horizontalFit(page, selector);
    const geometry = await page.locator('[data-module-plan-deletion]').evaluate(notice => {
      const box = notice.getBoundingClientRect(), scroller = notice.closest('.settings-content')!.getBoundingClientRect();
      const action = notice.querySelector('button')!.getBoundingClientRect(), copy = notice.querySelector('p')!.getBoundingClientRect();
      return { visible: box.top >= scroller.top && box.bottom <= scroller.bottom + 1, separate: copy.right < action.left };
    });
    assert.equal(geometry.visible, true, 'the undo notice must remain visible inside the settings scroller');
    assert.equal(geometry.separate, true, 'the deleted policy name must not overlap its undo action');
    await screenshot(page, `module-plan-${width}-deleted.png`);
    await page.locator('[data-module-plan-undo]').click();
    assert.deepEqual(await editorPlan(page), plan);
    assert.equal(await rule(page, deletedPolicy.id).getAttribute('data-expanded'), 'false');
    await page.locator('#module-plan').evaluate(section => section.scrollIntoView({ block: 'start', behavior: 'instant' }));
    await settled(page); await screenshot(page, `module-plan-${width}-collapsed.png`);
    await rule(page, plan.custom[1]!.id).locator('[data-module-plan-move="up"]').click();
    plan = await editorPlan(page); assert.equal(plan.custom[0]!.enabled, false);
    await closeSettings(page);
    await showArtifacts(page); await page.locator('#draft-tab-modules').click();
    const draftPolicy = plan.custom.find(module => module.enabled)!;
    await graphToggle(page, draftPolicy.id).uncheck();
    assert.equal((await editorPlan(page)).custom.find(module => module.id === draftPolicy.id)!.enabled, false);
    await graphToggle(page, draftPolicy.id).check();
    assert.deepEqual(await editorPlan(page), plan, 'responsive graph switches must preserve all other policy fields');
    assert.equal(await page.locator('#run-settings[open]').count(), 0);
    for (const selector of ['.module-customization-row', '.module-custom-toggle', '[data-module-custom-enabled]']) await horizontalFit(page, selector);
    assert.equal(await page.locator('.module-customization-row').evaluateAll(items => items.every(row => {
      const toggle = row.querySelector('.module-custom-toggle')!.getBoundingClientRect();
      const button = row.querySelector('button')!.getBoundingClientRect();
      return toggle.right <= button.left && toggle.width >= 28 && toggle.height >= 36;
    })), true, 'graph switches must have a stable touch target beside the policy button');
    await page.locator('.module-customizations').scrollIntoViewIfNeeded(); await settled(page);
    await screenshot(page, `module-plan-${width}-draft-switches.png`);
    await page.locator(`[data-module-custom-id="${draftPolicy.id}"]`).click();
    await selectedPolicy(page, draftPolicy.id, draftPolicy.slot);
    for (const selector of ['.module-inspector>header', `[data-module-policy-id="${draftPolicy.id}"]`,
      `[data-module-policy-id="${draftPolicy.id}"] .module-policy-tools`, `[data-module-policy-edit="${draftPolicy.id}"]`]) await horizontalFit(page, selector);
    await screenshot(page, `module-plan-${width}-draft-policy.png`);
    const readingTop = await page.locator('#draft-preview').evaluate(panel => panel.scrollTop);
    await openPolicyEditor(page, draftPolicy.id);
    await closeDialog(page, '#run-settings', () => page.keyboard.press('Escape'));
    await selectedPolicy(page, draftPolicy.id, draftPolicy.slot);
    assert.deepEqual(await editorPlan(page), plan, 'opening and dismissing a policy must preserve its values');
    assert.ok(Math.abs(await page.locator('#draft-preview').evaluate(panel => panel.scrollTop) - readingTop) <= 1.5,
      'dismissing an unchanged policy must retain the reading position');
    await page.locator('#open-settings').click();
    await page.locator('#run-settings[open]').waitFor();
    assert.equal(await page.locator('#run-settings').isVisible(), true, 'the global configuration must be visible from the workspace');
    await closeSettings(page);
    if (width <= 850) assert.equal(await page.locator('body').getAttribute('data-mobile-view'), 'runs',
      'closing the global configuration must restore the mobile workspace');
    assert.equal(await page.locator('#open-settings').evaluate(button => document.activeElement === button), true);
    assert.equal(await page.locator(`[data-module-policy-id="${draftPolicy.id}"]`).getAttribute('open'), '',
      'closing the global configuration must preserve the open policy');
    const editing = await openPolicyEditor(page, draftPolicy.id);
    await editing.locator('[data-module-plan-field="name"]').fill('Inspected construction policy');
    await editing.locator('[data-module-plan-field="instructions"]').fill(`${draftPolicy.instructions}\nCheck the current Lean goal before extending the proof.`);
    plan = await editorPlan(page);
    await horizontalFit(page, `[data-module-plan-id="${draftPolicy.id}"]`);
    await horizontalFit(page, `[data-module-plan-id="${draftPolicy.id}"] [data-module-plan-field="instructions"]`);
    await screenshot(page, `module-plan-${width}-draft-edit.png`);
    await closeSettings(page);
    const selected = await selectedPolicy(page, draftPolicy.id, draftPolicy.slot);
    assert.equal(await selected.locator('.module-policy-name').innerText(), plan.custom.find(module => module.id === draftPolicy.id)!.name);
    assert.equal(await selected.locator('.module-policy-instructions').innerText(), plan.custom.find(module => module.id === draftPolicy.id)!.instructions);
    await screenshot(page, `module-plan-${width}-draft-return.png`);
    await saved(page, plan); await noStoredKey(page);
    assert.equal(h.requests.filter(request => request.method === 'POST').length, 0, 'responsive direct editing must not start a run');
    const run = await createRun(h, plan); await selectModules(h, run.id);
    for (const selector of ['.module-workspace', '.module-graph', '.module-customizations', '[data-module-custom-id]']) await horizontalFit(page, selector);
    await page.locator('.module-customizations').scrollIntoViewIfNeeded(); await screenshot(page, `module-plan-${width}-graph.png`);
    const enabled = plan.custom.find(module => module.enabled)!, disabled = plan.custom.find(module => !module.enabled)!;
    await customState(page, enabled.id, 0, '待应用'); await customState(page, disabled.id, 0, '已停用');
    await page.locator(`[data-module-custom-id="${enabled.id}"]`).click();
    await page.locator('#module-inspector[data-module="M1"]').waitFor();
    assert.equal(await policyText(page, enabled.id), enabled.instructions);
    await horizontalFit(page, '.module-policies'); await horizontalFit(page, '[data-module-policy-id]');
    await page.locator('.module-policies').scrollIntoViewIfNeeded(); await screenshot(page, `module-plan-${width}-policy.png`);
    assert.equal(await page.locator('.module-node[data-tone="passed"]').count(), 0);
  }, width);

  await writeReport('passed');
  console.log(`Module plan checks passed: ${checks.length} scenarios; local editing, validation, draft transfer, immutable run plans, real application evidence and responsive layouts.`);
  console.log(`Report: ${path.relative(root, reportFile)}`);
} catch (error) {
  await writeReport('failed', error); throw error;
} finally {
  await browser?.close(); await service.close();
}
