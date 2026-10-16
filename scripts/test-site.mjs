import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { chromium } from 'playwright';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const url = pathToFileURL(path.join(root, 'out/site/archive.html')).href;
const output = path.join(root, 'out/site-checks');
fs.mkdirSync(output, { recursive: true });
const catalog = JSON.parse(fs.readFileSync(path.join(root, 'out/site/data/catalog.json'), 'utf8'));
const official = catalog.records.filter(record => record.status === 'official_accepted');
const ongoing = catalog.records.filter(record => record.status !== 'official_accepted');
const errors = [];
const browser = await chromium.launch();
try {
  const page = await browser.newPage({ viewport: { width: 1440, height: 1000 }, reducedMotion: 'reduce' });
  page.on('pageerror', error => errors.push(error.message));
  page.on('console', message => { if (['error', 'warning'].includes(message.type())) errors.push(message.text()); });
  await page.addInitScript(() => {
    Object.defineProperty(navigator, 'clipboard', { value: { writeText: async value => { window.testClipboard = value; } }, configurable: true });
  });
  await page.goto(url);
  await page.waitForSelector('.proof-row');
  assert.equal(await page.locator('.proof-row').count(), catalog.records.length);
  assert.equal(await page.locator('.proof-row.is-selected').count(), 1);
  assert.equal(await page.locator('#inspector .detail-title').textContent(), official[0].title);
  await page.screenshot({ path: path.join(output, 'desktop.png'), fullPage: true });

  await page.getByRole('radio', { name: /已验收/ }).check();
  assert.equal(await page.locator('.proof-row').count(), official.length);
  await page.getByRole('radio', { name: /研究中/ }).check();
  assert.equal(await page.locator('.proof-row').count(), ongoing.length);
  assert.match(await page.locator('#inspector').innerText(), /尚未官方验收/);
  await page.getByRole('tab', { name: '验证证据' }).click();
  assert.equal(await page.locator('.official-result-link').count(), 0);

  await page.getByRole('radio', { name: /全部/ }).check();
  await page.getByRole('searchbox').fill('不存在的题目');
  assert.equal(await page.locator('.proof-row').count(), 0);
  assert.equal(await page.locator('#empty-state').isVisible(), true);
  await page.getByRole('button', { name: '清除筛选' }).click();
  await page.getByRole('searchbox').fill('群环');
  assert.equal(await page.locator('.proof-row').count(), 1);
  assert.equal(await page.locator('#inspector .detail-title').textContent(), 'Unit conjecture');
  await page.getByRole('tab', { name: '概览' }).click();
  assert.equal(await page.locator('#inspector').innerText().then(text => text.includes('DeepScientist + GPT-5.6')), true);
  await page.getByRole('tab', { name: '验证证据' }).click();
  assert.equal(await page.locator('.official-result-link').getAttribute('href'), official.find(record => record.id === 'annals_unit_conjecture').official.resultUrl);
  assert.equal(await page.locator('#inspector').innerText().then(text => text.includes('comparator:')), false);

  await page.getByRole('searchbox').fill('');
  await page.selectOption('#sort', 'title');
  const titles = await page.locator('.row-title').allTextContents();
  assert.deepEqual(titles, [...titles].sort((a, b) => a.localeCompare(b, 'en')));
  await page.locator('[data-proof-id="annals_rademacher_enflo_type"]').click();
  await page.keyboard.press('Enter');
  await page.keyboard.press('ArrowDown');
  assert.notEqual(await page.locator('.proof-row.is-selected').getAttribute('data-proof-id'), 'annals_rademacher_enflo_type');
  await page.locator('[data-proof-id="annals_rademacher_enflo_type"]').click();
  await page.getByRole('tab', { name: 'Lean 源码' }).click();
  assert.match(await page.locator('.is-declaration').innerText(), /theorem theorem_1_1/);
  await page.locator('[data-proof-id="annals_equiangular_lines_fixed_angle"]').click();
  await page.getByRole('tab', { name: '验证证据' }).click();
  assert.match(await page.locator('.binding-note').innerText(), /源码哈希与当前归档不同/);
  await page.getByRole('tab', { name: 'Lean 源码' }).click();
  assert.match(await page.locator('.source-code').innerText(), /theorem theorem_1_2/);
  assert.ok(await page.locator('.source-code').evaluate(element => element.scrollTop > 0));
  await page.getByRole('button', { name: '复制 Lean 源码' }).click();
  assert.equal(await page.evaluate(() => window.testClipboard), official.find(record => record.id === 'annals_equiangular_lines_fixed_angle').sources.find(source => source.name === 'Submission.lean').code);
  await page.selectOption('#source-file', 'Submission/Helpers.lean');
  assert.equal(await page.locator('.source-code .code-line').count(), official.find(record => record.id === 'annals_equiangular_lines_fixed_angle').sources.find(source => source.name === 'Submission/Helpers.lean').lines);
  const downloadPromise = page.waitForEvent('download');
  await page.getByRole('button', { name: '下载此题档案 JSON' }).click();
  const download = await downloadPromise;
  assert.equal(download.suggestedFilename(), 'annals_equiangular_lines_fixed_angle.json');
  const record = JSON.parse(fs.readFileSync(await download.path(), 'utf8'));
  assert.equal(record.status, 'official_accepted');
  assert.ok(record.official.resultUrl.includes('/issues/2135'));
  const deepLink = page.url();
  await page.reload();
  assert.equal(page.url(), deepLink);
  assert.equal(await page.getByRole('tab', { name: 'Lean 源码' }).getAttribute('aria-selected'), 'true');
  await page.getByRole('tab', { name: 'Lean 源码' }).focus();
  await page.keyboard.press('ArrowRight');
  assert.equal(await page.getByRole('tab', { name: '验证证据' }).getAttribute('aria-selected'), 'true');

  await page.locator('[data-view-link="quickstart"]').click();
  assert.equal(await page.locator('#quickstart-view').isVisible(), true);
  assert.match(await page.locator('#replay-command').innerText(), /elan toolchain install leanprover\/lean4:v4.33.0/);
  await page.getByRole('button', { name: '复制回放命令' }).click();
  assert.match(await page.evaluate(() => window.testClipboard), /example replay/);
  assert.ok(await page.locator('.replay-evidence img').evaluate(image => image.complete && image.naturalWidth > 0));
  await page.screenshot({ path: path.join(output, 'quickstart.png'), fullPage: true });
  await page.goBack();
  assert.equal(await page.locator('#archive-view').isVisible(), true);

  for (const viewport of [{ width: 1920, height: 1080 }, { width: 390, height: 844 }, { width: 320, height: 740 }]) {
    await page.setViewportSize(viewport);
    await page.goto(url);
    await page.waitForSelector('.proof-row');
    assert.ok(await page.evaluate(() => document.documentElement.scrollWidth <= innerWidth), `Horizontal overflow at ${viewport.width}px`);
    assert.ok(await page.locator('.brand-mark').evaluate(image => image.complete && image.naturalWidth > 0));
    await page.screenshot({ path: path.join(output, `archive-${viewport.width}.png`), fullPage: true });
    await page.getByRole('searchbox').fill('long-query-'.repeat(30));
    assert.ok(await page.evaluate(() => document.documentElement.scrollWidth <= innerWidth), `Search overflow at ${viewport.width}px`);
    await page.getByRole('searchbox').fill('');
    await page.locator('[data-proof-id="hopf_rinow"]').click();
    await page.getByRole('tab', { name: 'Lean 源码' }).click();
    assert.ok(await page.evaluate(() => document.documentElement.scrollWidth <= innerWidth), `Source overflow at ${viewport.width}px`);
    await page.screenshot({ path: path.join(output, `source-${viewport.width}.png`), fullPage: true });
  }
  assert.deepEqual(errors, []);
  console.log('Site checks passed: filters, search, provenance, evidence, source files, clipboard, JSON download, links, navigation, and 4 viewport sizes.');
  console.log(`Screenshots: ${path.relative(root, output)}`);
} finally {
  await browser.close();
}
