import assert from 'node:assert/strict';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { chromium } from 'playwright';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const origin = process.argv[2] ?? 'http://127.0.0.1:8787';
const draftSource = 'import Mathlib\ntheorem square_add (x y : ℝ) :\n  (x+y)^2 = x^2+2*x*y+y^2 := by sorry';
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
  await page.route('**/api/**', guardSubmissions);
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
  await page.locator('#dismiss-draft-recovery').click();
  await page.evaluate(() => document.activeElement?.blur());
  await page.locator('#conversation-scroll').evaluate(node => { node.scrollTop = 0; });
  await page.screenshot({ path: path.join(root, 'docs/assets/workbench-desktop.png') });

  await page.setViewportSize({ width: 390, height: 440 });
  await page.locator('#mobile-runs').click();
  await page.locator('.preview-view-tabs').evaluate(node => node.scrollIntoView({ block: 'start', behavior: 'instant' }));
  const source = await page.locator('.draft-source-scroll').evaluate(node => {
    const bounds = node.getBoundingClientRect();
    return { top: bounds.top, bottom: bounds.bottom, viewport: innerHeight,
      value: node.querySelector('code').textContent, scrollHeight: node.scrollHeight, clientHeight: node.clientHeight,
      scrollWidth: node.scrollWidth, clientWidth: node.clientWidth };
  });
  assert.equal(source.value, draftSource);
  assert.ok(source.top >= 98 && source.bottom <= source.viewport + 1 && source.scrollHeight <= source.clientHeight + 2
    && source.scrollWidth <= source.clientWidth + 2,
    `The mobile screenshot must show the entire original Lean source: ${JSON.stringify(source)}`);
  await page.screenshot({ path: path.join(root, 'docs/assets/workbench-mobile.png') });

  const detail = await browser.newPage({ viewport: { width: 1440, height: 900 }, deviceScaleFactor: 2, reducedMotion: 'reduce' });
  await detail.route('**/api/**', guardSubmissions);
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
  await detail.locator('#dismiss-draft-recovery').click();
  await detail.evaluate(() => document.activeElement?.blur());
  assert.equal(await detail.locator('#source').inputValue(), draftSource);
  await detail.screenshot({ path: path.join(root, 'docs/assets/workbench-full-desktop.png') });
  await detail.setViewportSize({ width: 390, height: 844 });
  await detail.locator('#mobile-runs').click();
  await detail.screenshot({ path: path.join(root, 'docs/assets/workbench-full-mobile.png') });

  await detail.setViewportSize({ width: 1600, height: 600 });
  await detail.locator('#draft-preview').evaluate(node => { node.scrollTop = 0; });
  assert.equal(await detail.locator('#environment').inputValue(), 'mathlib');
  assert.equal(await detail.locator('#api-key').inputValue(), '');
  assert.equal(await detail.locator('#draft-preview .preview-status').innerText(), '未提交');
  const sourceDetail = await detail.locator('.draft-source-scroll').evaluate(node => ({
    value: node.querySelector('code').textContent,
    scrollHeight: node.scrollHeight, clientHeight: node.clientHeight,
    scrollWidth: node.scrollWidth, clientWidth: node.clientWidth,
  }));
  assert.equal(sourceDetail.value, draftSource);
  assert.ok(sourceDetail.scrollHeight <= sourceDetail.clientHeight + 2
    && sourceDetail.scrollWidth <= sourceDetail.clientWidth + 2,
    'The source detail must show the complete original Lean draft without scrolling');
  const sourceBounds = await detail.locator('#draft-preview').boundingBox();
  await detail.locator('#draft-preview').screenshot({ path: path.join(root, 'docs/assets/workbench-source-detail.png') });

  await detail.setViewportSize({ width: 1440, height: 900 });
  await detail.locator('#open-settings').click();
  await detail.locator('#run-settings').waitFor({ state: 'visible' });
  await detail.setViewportSize({ width: 390, height: 844 });
  await detail.locator('[data-settings-section="settings-connection"]').click();
  assert.equal(await detail.locator('#api-key').inputValue(), '');
  assert.equal(await detail.locator('#api-key').getAttribute('type'), 'password');
  const settingsDetail = await detail.locator('.settings-content').evaluate(node => {
    const bounds = node.getBoundingClientRect();
    return ['#provider', '#provider-address', '#model', '#effort', '#api-key'].map(selector => {
      const field = node.querySelector(selector);
      const rect = field.getBoundingClientRect();
      const label = field.labels?.[0]?.getBoundingClientRect();
      return { selector, visible: rect.top >= bounds.top && rect.bottom <= bounds.bottom
        && rect.left >= bounds.left && rect.right <= bounds.right
        && (!label || label.top >= bounds.top && label.bottom <= bounds.bottom) };
    });
  });
  assert.ok(settingsDetail.every(field => field.visible),
    `The real settings screenshot must show provider, model and empty API Key: ${JSON.stringify(settingsDetail)}`);
  const settingsBounds = await detail.locator('#run-settings').boundingBox();
  await detail.locator('#run-settings').screenshot({ path: path.join(root, 'docs/assets/workbench-settings-detail.png') });

  await detail.setViewportSize({ width: 1440, height: 900 });
  await detail.locator('[data-settings-section="module-plan"]').click();
  await detail.locator('#module-plan-scheduler').selectOption('critical-path');
  await detail.locator('#module-plan-context').selectOption('essential');
  for (const [name, slot, instructions] of [
    ['优先代数化简', 'M1', '先检查 ring、linarith 等代数策略，保留原题声明。'],
    ['检索相关引理', 'M4', '优先选取与当前目标类型匹配的 Mathlib 引理。'],
  ]) {
    await detail.locator('#module-plan-add').click();
    const rule = detail.locator('[data-module-plan-id]').last();
    await rule.locator('[data-module-plan-field="name"]').fill(name);
    await rule.locator('[data-module-plan-field="slot"]').selectOption(slot);
    await rule.locator('[data-module-plan-field="instructions"]').fill(instructions);
    await rule.locator('[data-module-plan-field="enabled"]').check();
    await rule.locator('[data-module-plan-disclosure]').click();
  }
  await detail.locator('#module-plan-library>summary').click();
  await detail.locator('#module-library-name').fill('Mathlib 代数研究');
  await detail.locator('[data-module-library-save]').click();
  await detail.locator('[data-module-library-notice]').filter({ hasText: '已保存' }).waitFor();
  assert.equal(await detail.locator('[data-module-library-count]').innerText(), '1 / 12');
  assert.equal(await detail.locator('[data-module-library-summary]').innerText(), '2 / 2 项策略启用 · 与当前配置一致');
  for (const [width, height, device] of [[1440, 900, 'desktop'], [390, 844, 'mobile']]) {
    await detail.setViewportSize({ width, height });
    await detail.locator('[data-settings-section="module-plan"]').click();
    await detail.screenshot({ path: path.join(root, `docs/assets/workbench-library-${device}.png`) });
  }
  await detail.locator('#close-settings').click();
  await detail.locator('#draft-tab-modules').click();
  for (const [width, height, device] of [[1440, 900, 'desktop'], [390, 844, 'mobile']]) {
    await detail.setViewportSize({ width, height });
    await detail.locator('#draft-module-panel').evaluate(node => { node.scrollTop = 0; });
    if (device === 'mobile') {
      const acceptance = detail.locator('[data-module-id="S3"]');
      await detail.locator('.module-view-heading').evaluate(node => node.scrollIntoView({ block: 'start', behavior: 'instant' }));
      const coordinator = await detail.locator('[data-module-id="M5"]').boundingBox();
      const receipt = await acceptance.boundingBox();
      assert.ok(coordinator.y >= 100 && receipt.y + receipt.height <= height + 1,
        'The mobile module screenshot must show the complete research graph and independent acceptance');
    }
    assert.equal(await detail.locator('#draft-preview .preview-status').innerText(), '未提交');
    await detail.screenshot({ path: path.join(root, `docs/assets/workbench-modules-${device}.png`) });
  }
  assert.equal(await detail.locator('#api-key').inputValue(), '');
  assert.equal(submissions, 0, 'A website screenshot must never submit a research task');
  console.log(JSON.stringify({
    sourceDetail: { width: sourceBounds.width, height: sourceBounds.height, scale: 2 },
    settingsDetail: { width: settingsBounds.width, height: settingsBounds.height, scale: 2 },
    submissions, apiKeyEmpty: true,
  }, null, 2));
  console.log('Captured real drafts, source, connection settings, module maps and a saved plan, without submitting a task.');
} finally {
  await browser.close();
}
