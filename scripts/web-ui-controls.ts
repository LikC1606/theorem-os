import assert from 'node:assert/strict';
import type { Page } from 'playwright';

export async function closeDialog(page: Page, selector: string, action: () => Promise<unknown>) {
  await page.locator(`${selector}[open]`).waitFor();
  await page.evaluate(selector => {
    const dialog = document.querySelector<HTMLDialogElement>(selector)!;
    dialog.dataset.controlCloseCompleted = 'false';
    dialog.addEventListener('close', () => { dialog.dataset.controlCloseCompleted = 'true'; }, { once: true });
  }, selector);
  await action();
  await page.waitForFunction(selector => {
    const dialog = document.querySelector<HTMLDialogElement>(selector)!;
    return !dialog.open && dialog.dataset.controlCloseCompleted === 'true';
  }, selector);
  await page.locator(selector).evaluate(dialog => { delete (dialog as HTMLElement).dataset.controlCloseCompleted; });
}

export async function discardSourceEditor(page: Page, action: () => Promise<unknown> = () => page.locator('#cancel-editor').click()) {
  await closeDialog(page, '#source-editor', async () => {
    await action();
    await page.locator('#editor-discard-dialog[open]').waitFor();
    await closeDialog(page, '#editor-discard-dialog', () => page.locator('#discard-editor-changes').click());
  });
}

export async function closeSettings(page: Page) {
  if (await page.locator('#run-settings[open]').count()) {
    await closeDialog(page, '#run-settings', () => page.locator('#close-settings').click());
  }
}

export async function closeHistory(page: Page) {
  if (await page.locator('#history-dialog[open]').count()) {
    await closeDialog(page, '#history-dialog', () => page.locator('#close-history').click());
  }
}

export async function showChat(page: Page) {
  await closeSettings(page);
  await closeHistory(page);
  if ((page.viewportSize()?.width ?? 1440) <= 850) await page.locator('#mobile-compose').click();
}

export async function showArtifacts(page: Page) {
  await closeSettings(page);
  await closeHistory(page);
  if ((page.viewportSize()?.width ?? 1440) <= 850) await page.locator('#mobile-runs').click();
}

export async function openSettings(page: Page) {
  if (await page.locator('#run-settings[open]').count()) return;
  await showChat(page);
  if (await page.locator('#run-settings[open]').count()) return;
  await page.locator('#open-settings').click();
  await page.locator('#run-settings[open]').waitFor();
}

export async function withSettings<T>(page: Page, action: () => Promise<T>): Promise<T> {
  await openSettings(page);
  try { return await action(); }
  finally { await closeSettings(page); }
}

export async function fillConfig(page: Page, id: string, value: string) {
  await withSettings(page, () => page.locator(`#${id}`).fill(value));
}

export async function selectConfig(page: Page, id: string, value: string) {
  await withSettings(page, () => page.locator(`#${id}`).selectOption(value));
}

export async function openHistory(page: Page) {
  if (await page.locator('#history-dialog[open]').count()) return;
  await closeSettings(page);
  await page.locator('#open-history').click();
  await page.locator('#history-dialog[open]').waitFor();
}

export async function refreshHistory(page: Page) {
  await openHistory(page);
  await page.locator('#refresh-runs').click();
  await closeHistory(page);
}

export async function selectHistoryRun(page: Page, id: string) {
  await openHistory(page);
  await closeDialog(page, '#history-dialog', () => page.locator(`[data-run-id="${id}"]`).click());
  await showArtifacts(page);
}

export type EditorSnapshot = { value: string; start: number; end: number; direction: string; top: number; left: number };
export async function snapshot(page: Page): Promise<EditorSnapshot> {
  return page.locator('#expanded-source').evaluate(node => {
    const editor = node as HTMLTextAreaElement;
    return { value: editor.value, start: editor.selectionStart, end: editor.selectionEnd, direction: editor.selectionDirection,
      top: editor.scrollTop, left: editor.scrollLeft };
  });
}
export async function value(page: Page, expected: string) {
  await page.waitForFunction(expected => (document.querySelector('#expanded-source') as HTMLTextAreaElement).value === expected, expected);
}
export async function text(page: Page, selector: string, expected: string) {
  await page.waitForFunction(({ selector, expected }) => document.querySelector(selector)?.textContent === expected, { selector, expected });
}
export async function focused(page: Page, selector: string) {
  assert.equal(await page.locator(selector).evaluate(node => node === document.activeElement), true, `${selector} must have focus`);
}
/** Assert `selector` lies inside the viewport (1px tolerance) and the document is no wider; `widen` is that overflow's message. */
export async function fitViewport(page: Page, selector: string, widen: string, nonEmpty = false) {
  const box = await page.locator(selector).boundingBox(), viewport = page.viewportSize()!;
  assert.ok(box && (!nonEmpty || box.width > 0 && box.height > 0) && box.x >= -1 && box.y >= -1
    && box.x + box.width <= viewport.width + 1 && box.y + box.height <= viewport.height + 1,
    `${selector} must fit ${viewport.width}px: ${JSON.stringify(box)}`);
  assert.equal(await page.evaluate(() => document.documentElement.scrollWidth <= innerWidth + 1), true, widen);
}
export async function selectEditorRange(page: Page, start: number, end = start, direction: 'forward' | 'backward' | 'none' = 'none') {
  await page.locator('#expanded-source').evaluate((node, selection) => {
    const editor = node as HTMLTextAreaElement; editor.focus({ preventScroll: true });
    editor.setSelectionRange(selection.start, selection.end, selection.direction);
  }, { start, end, direction });
}
/** Like `refreshHistory`, but waits for and requires a successful `/api/runs` response before closing history. */
export async function refresh(h: { page: Page }) {
  await openHistory(h.page);
  await h.page.locator('#refresh-runs:enabled').waitFor();
  const response = h.page.waitForResponse(response => new URL(response.url()).pathname === '/api/runs' && response.request().method() === 'GET');
  await h.page.locator('#refresh-runs').click();
  assert.equal((await response).status(), 200);
  await h.page.locator('#refresh-runs:enabled').waitFor();
  await closeHistory(h.page);
}
export async function selectModules(h: { page: Page }, id: string) {
  await openHistory(h.page); await h.page.locator('#refresh-runs:enabled').waitFor();
  const refreshed = h.page.waitForResponse(response => new URL(response.url()).pathname === '/api/runs' && response.request().method() === 'GET');
  await h.page.locator('#refresh-runs').click(); await refreshed;
  await h.page.locator('#refresh-runs:enabled').waitFor(); await closeHistory(h.page);
  await selectHistoryRun(h.page, id); await showArtifacts(h.page);
  await h.page.locator('#detail-tab-modules').click(); await h.page.locator('.module-workspace').waitFor();
}
