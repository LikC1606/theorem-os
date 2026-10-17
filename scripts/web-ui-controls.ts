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
