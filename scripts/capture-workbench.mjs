import assert from 'node:assert/strict';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { chromium } from 'playwright';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const origin = process.argv[2] ?? 'http://127.0.0.1:8787';
const browser = await chromium.launch();
try {
  const page = await browser.newPage({ viewport: { width: 1440, height: 500 }, reducedMotion: 'reduce' });
  let submissions = 0;
  const guardSubmissions = async route => {
    if (route.request().method() === 'POST') {
      submissions++;
      await route.abort();
    } else await route.continue();
  };
  await page.route('**/api/runs', guardSubmissions);
  await page.goto(origin);
  await page.locator('#draft-preview').waitFor();
  await page.locator('#submit-run:enabled').waitFor();
  await page.evaluate(() => document.fonts.ready);
  assert.equal(await page.locator('#environment').inputValue(), 'mathlib');
  assert.equal(await page.locator('#api-key').inputValue(), '');
  assert.equal(await page.locator('#draft-preview .preview-status').innerText(), '未提交');
  await page.screenshot({ path: path.join(root, 'docs/assets/workbench-desktop.png') });

  await page.setViewportSize({ width: 390, height: 440 });
  await page.locator('#mobile-compose').click();
  await page.locator('label[for="source"]').evaluate(node => window.scrollTo(0, node.getBoundingClientRect().top + window.scrollY - 62));
  const source = await page.locator('#source').evaluate(node => {
    const bounds = node.getBoundingClientRect();
    return { top: bounds.top, bottom: bounds.bottom, viewport: innerHeight,
      value: node.value, scrollHeight: node.scrollHeight, clientHeight: node.clientHeight };
  });
  assert.match(source.value, /theorem square_add/);
  assert.ok(source.top >= 47 && source.bottom <= source.viewport && source.scrollHeight <= source.clientHeight + 2,
    'The mobile screenshot must show the entire original Lean source');
  await page.screenshot({ path: path.join(root, 'docs/assets/workbench-mobile.png') });

  const detail = await browser.newPage({ viewport: { width: 1440, height: 900 }, deviceScaleFactor: 2, reducedMotion: 'reduce' });
  await detail.route('**/api/runs', guardSubmissions);
  await detail.goto(origin);
  await detail.locator('#draft-preview').waitFor();
  await detail.locator('#submit-run:enabled').waitFor();
  await detail.evaluate(() => document.fonts.ready);
  assert.equal(await detail.locator('#api-key').inputValue(), '');
  assert.equal(await detail.locator('#draft-preview .preview-status').innerText(), '未提交');
  assert.equal(await detail.locator('#source').inputValue(), source.value);
  await detail.screenshot({ path: path.join(root, 'docs/assets/workbench-full-desktop.png') });
  await detail.setViewportSize({ width: 390, height: 844 });
  await detail.locator('#mobile-compose').click();
  await detail.locator('label[for="source"]').evaluate(node => window.scrollTo(0, node.getBoundingClientRect().top + window.scrollY - 62));
  await detail.screenshot({ path: path.join(root, 'docs/assets/workbench-full-mobile.png') });
  assert.equal(submissions, 0, 'A website screenshot must never submit a research task');
  console.log('Captured the real workbench draft, responsive homepage images and full-height 2x previews, without submitting a task.');
} finally {
  await browser.close();
}
