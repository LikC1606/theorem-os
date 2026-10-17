import assert from 'node:assert/strict';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { chromium } from 'playwright';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const origin = process.argv[2] ?? 'http://127.0.0.1:8787';
const draftSource = 'import Mathlib\ntheorem square_add (x y : ℝ) :\n  (x+y)^2 = x^2+2*x*y+y^2 := by\n  sorry';
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
  await page.locator('#edit-draft-source').click();
  await page.locator('#expanded-source').fill(draftSource);
  await page.locator('#apply-editor').click();
  await page.locator('#source-editor').waitFor({ state: 'hidden' });
  await page.locator('#draft-status').filter({ hasText: '草稿已保存' }).waitFor();
  await page.locator('#conversation-scroll').evaluate(node => { node.scrollTop = 0; });
  await page.screenshot({ path: path.join(root, 'docs/assets/workbench-desktop.png') });

  await page.setViewportSize({ width: 390, height: 440 });
  await page.locator('#mobile-runs').click();
  await page.locator('.preview-heading').evaluate(node => { node.parentElement.scrollTop = node.offsetHeight; });
  const source = await page.locator('.draft-source-scroll').evaluate(node => {
    const bounds = node.getBoundingClientRect();
    return { top: bounds.top, bottom: bounds.bottom, viewport: innerHeight,
      value: node.querySelector('code').textContent, scrollHeight: node.scrollHeight, clientHeight: node.clientHeight,
      scrollWidth: node.scrollWidth, clientWidth: node.clientWidth };
  });
  assert.equal(source.value, draftSource);
  assert.ok(source.top >= 98 && source.bottom <= source.viewport && source.scrollHeight <= source.clientHeight + 2
    && source.scrollWidth <= source.clientWidth + 2,
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
  await detail.locator('#edit-draft-source').click();
  await detail.locator('#expanded-source').fill(draftSource);
  await detail.locator('#apply-editor').click();
  await detail.locator('#source-editor').waitFor({ state: 'hidden' });
  await detail.locator('#draft-status').filter({ hasText: '草稿已保存' }).waitFor();
  assert.equal(await detail.locator('#source').inputValue(), draftSource);
  await detail.screenshot({ path: path.join(root, 'docs/assets/workbench-full-desktop.png') });
  await detail.setViewportSize({ width: 390, height: 844 });
  await detail.locator('#mobile-runs').click();
  await detail.screenshot({ path: path.join(root, 'docs/assets/workbench-full-mobile.png') });
  assert.equal(submissions, 0, 'A website screenshot must never submit a research task');
  console.log('Captured the real workbench draft, responsive homepage images and full-height 2x previews, without submitting a task.');
} finally {
  await browser.close();
}
