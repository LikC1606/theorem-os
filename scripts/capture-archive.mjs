import assert from 'node:assert/strict';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { chromium } from 'playwright';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const browser = await chromium.launch();
try {
  const page = await browser.newPage({ viewport: { width: 1440, height: 900 }, deviceScaleFactor: 2, reducedMotion: 'reduce' });
  await page.goto(pathToFileURL(path.join(root, 'out/site/archive.html')).href);
  await page.locator('.proof-row').first().waitFor();
  await page.evaluate(() => document.fonts.ready);
  assert.equal(await page.locator('#inspector .detail-title').innerText(), 'Equiangular lines');
  await page.screenshot({ path: path.join(root, 'docs/assets/archive-preview.png') });
  await page.setViewportSize({ width: 390, height: 844 });
  const inspector = page.locator('#inspector');
  await inspector.scrollIntoViewIfNeeded();
  assert.equal(await page.evaluate(() => document.documentElement.scrollWidth <= innerWidth), true);
  const bounds = await inspector.boundingBox();
  assert.ok(bounds && bounds.width > 300 && bounds.height > 500);
  await inspector.screenshot({ path: path.join(root, 'docs/assets/archive-preview-mobile.png') });
  console.log(JSON.stringify({ source: 'local proof archive', desktop: { width: 1440, height: 900 },
    mobile: { width: bounds.width, height: bounds.height }, deviceScaleFactor: 2, modelInvoked: false }));
} finally {
  await browser.close();
}
