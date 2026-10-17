import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { chromium } from 'playwright';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const url = pathToFileURL(path.join(root, 'out/site/index.html')).href;
const output = path.join(root, 'out/site-motion-checks');
await fs.mkdir(output, { recursive: true });
await fs.access(path.join(root, 'out/site/landing.js'));
const browser = await chromium.launch();
const errors = [];
const checks = [];
const screenshots = [];
const viewports = [{ width: 1440, height: 900 }, { width: 390, height: 844 }, { width: 320, height: 812 }];
let currentPage;
let currentCheck = '';
let apiRequests = 0;

function track(page) {
  page.on('pageerror', error => errors.push(error.message));
  page.on('console', message => {
    if (['warning', 'error'].includes(message.type())) errors.push(message.text());
  });
  page.on('requestfailed', request => errors.push(`${request.url()}: ${request.failure()?.errorText}`));
  page.on('request', request => {
    if (/\/api\//.test(new URL(request.url()).pathname)) apiRequests++;
  });
}

async function state(page) {
  return page.locator('.replay-window').evaluate(node => ({
    current: node.dataset.replayCurrent, playing: node.dataset.replayPlaying, state: node.dataset.replayState,
  }));
}

async function assertStage(page, current, playing = false) {
  const actual = await state(page);
  assert.equal(actual.current, current, `${currentCheck}: current replay step`);
  assert.equal(actual.playing, String(playing), `${currentCheck}: playback state`);
  assert.equal(await page.locator(`#demo-${current}`).getAttribute('aria-selected'), 'true');
  assert.equal(await page.locator(`#stage-${current}`).isVisible(), true);
  assert.equal(await page.locator('.replay-panel:visible').count(), 1);
  assert.equal(await page.locator('#replay-play').getAttribute('aria-pressed'), String(playing));
}

async function visualState(page, selector) {
  return page.locator(selector).evaluate(node => {
    const style = getComputedStyle(node);
    return { opacity: Number(style.opacity), transform: style.transform };
  });
}

async function progress(page) {
  return page.locator('.replay-progress-fill').evaluate(node =>
    new DOMMatrixReadOnly(getComputedStyle(node).transform).a);
}

async function tick(page, milliseconds = 800) {
  await page.clock.runFor(milliseconds);
}

async function showReplay(page) {
  await page.locator('.replay-toolbar').evaluate(node => node.scrollIntoView({ behavior: 'instant', block: 'center' }));
  await tick(page);
}

async function screenshot(page, name, selector) {
  const target = selector ? page.locator(selector) : page;
  await target.screenshot({ path: path.join(output, name) });
  screenshots.push(name);
}

async function assertWidth(page) {
  assert.ok(await page.evaluate(() => document.documentElement.scrollWidth <= innerWidth), `${currentCheck}: page overflows horizontally`);
  const controlsFit = await page.locator('.replay-playback button').evaluateAll(nodes => nodes.every(node => {
    const bounds = node.getBoundingClientRect();
    return bounds.width >= 30 && bounds.height >= 30 && bounds.left >= 0 && bounds.right <= innerWidth;
  }));
  assert.ok(controlsFit, `${currentCheck}: transport buttons must fit the viewport`);
}

try {
  for (const viewport of viewports) for (const reducedMotion of ['no-preference', 'reduce']) {
    currentCheck = `${viewport.width}px ${reducedMotion}`;
    const context = await browser.newContext({ viewport, reducedMotion });
    const page = await context.newPage();
    currentPage = page;
    page.setDefaultTimeout(6000);
    track(page);
    // Advance every animation frame on a controlled clock, including paused replay timers.
    const start = new Date('2026-10-17T04:00:00Z');
    await page.clock.install({ time: start });
    await page.clock.pauseAt(start);
    await page.goto(url);
    await page.waitForSelector('.release-pill svg.lucide');
    const initialHero = await visualState(page, '.workbench-preview');
    if (reducedMotion === 'reduce') assert.deepEqual(initialHero, { opacity: 1, transform: 'none' });
    else assert.ok(initialHero.opacity < 1 || initialHero.transform !== 'none', 'Normal motion must have a product entrance');
    await tick(page, 1300);
    assert.deepEqual(await visualState(page, '.workbench-preview'), { opacity: 1, transform: 'none' });
    await page.locator('.workbench-picture img').evaluate(image => image.decode());
    await screenshot(page, `hero-${viewport.width}-${reducedMotion}.png`);

    await assertStage(page, 'verified');
    await showReplay(page);
    await tick(page, 20000);
    await assertStage(page, 'verified');
    assert.equal(await page.locator('#replay-next').isDisabled(), true);
    assert.match(await page.locator('.replay-badge').innerText(), /预设回放 · 不调用模型/);
    assert.match(await page.locator('.receipt-status').innerText(), /evaluated_passed/);
    assert.equal(await page.locator('.receipt-evidence').getAttribute('href'), 'assets/replay.json');
    await assertWidth(page);

    await page.locator('#replay-play').click();
    await assertStage(page, 'candidate', true);
    assert.equal(await page.locator('#replay-play').evaluate(node => node === document.activeElement), true);
    await tick(page, 1200);
    await page.locator('#replay-play').click();
    await assertStage(page, 'candidate');
    const pausedProgress = await progress(page);
    await tick(page, 7000);
    await assertStage(page, 'candidate');
    assert.ok(Math.abs((await progress(page)) - pausedProgress) < .001, 'Pause must retain the progress position');
    await page.locator('#replay-play').click();
    await tick(page, 2200);
    await assertStage(page, 'feedback', true);

    await page.locator('#demo-repair').click();
    await assertStage(page, 'repair');
    await tick(page, 20000);
    await assertStage(page, 'repair');
    assert.equal(await page.locator('#replay-progress').getAttribute('aria-valuenow'), '3');
    assert.match(await page.locator('#stage-repair').innerText(), /exact Nat.zero_add n/);
    const switching = await page.evaluate(() => {
      for (const id of ['verified', 'feedback', 'repair', 'candidate']) document.querySelector(`#demo-${id}`).click();
      const style = getComputedStyle(document.querySelector('#stage-candidate'));
      return { opacity: Number(style.opacity), transform: style.transform };
    });
    if (reducedMotion === 'reduce') assert.deepEqual(switching, { opacity: 1, transform: 'none' });
    else assert.ok(switching.opacity < 1 || switching.transform !== 'none', 'Normal step changes must animate');
    await tick(page, 500);
    await assertStage(page, 'candidate');
    assert.deepEqual(await visualState(page, '#stage-candidate'), { opacity: 1, transform: 'none' });
    assert.equal(await page.locator('#replay-prev').isDisabled(), true);
    await page.locator('#replay-next').click();
    await assertStage(page, 'feedback');
    await page.locator('#replay-prev').click();
    await assertStage(page, 'candidate');

    await page.locator('#demo-verified').focus();
    for (const [key, id] of [['ArrowRight', 'candidate'], ['End', 'verified'], ['Home', 'candidate']]) {
      await page.keyboard.press(key);
      await assertStage(page, id);
      assert.equal(await page.locator(`#demo-${id}`).evaluate(node => node === document.activeElement), true);
    }
    await tick(page, 500);
    await screenshot(page, `replay-${viewport.width}-${reducedMotion}.png`, '.replay-window');

    await page.locator('#replay-restart').click();
    await assertStage(page, 'candidate', true);
    await tick(page, 900);
    await page.evaluate(() => window.scrollTo({ top: 0, behavior: 'instant' }));
    await tick(page, 500);
    const offscreen = await state(page);
    assert.equal(offscreen.playing, 'false', 'Leaving the viewport must pause playback');
    await tick(page, 10000);
    assert.deepEqual(await state(page), offscreen);
    await showReplay(page);
    assert.deepEqual(await state(page), offscreen, 'Returning to the viewport must not restart playback');

    await page.locator('#replay-play').click();
    await tick(page, 300);
    // Headless tabs stay visible; exercise the visibility event with explicit document state.
    await page.evaluate(() => {
      Object.defineProperty(document, 'hidden', { configurable: true, value: true });
      Object.defineProperty(document, 'visibilityState', { configurable: true, value: 'hidden' });
      document.dispatchEvent(new Event('visibilitychange'));
    });
    const hidden = await state(page);
    assert.equal(hidden.playing, 'false', 'A hidden document must pause playback');
    await tick(page, 10000);
    assert.deepEqual(await state(page), hidden);
    await page.evaluate(() => {
      delete document.hidden;
      delete document.visibilityState;
      document.dispatchEvent(new Event('visibilitychange'));
    });
    await tick(page, 300);
    assert.deepEqual(await state(page), hidden, 'A visible document must remain paused');

    await page.locator('#replay-play').click();
    await page.evaluate(() => window.dispatchEvent(new PageTransitionEvent('pagehide', { persisted: true })));
    assert.equal((await state(page)).playing, 'false');
    await tick(page, 6000);
    const pageHidden = await state(page);
    await page.evaluate(() => window.dispatchEvent(new PageTransitionEvent('pageshow', { persisted: true })));
    assert.deepEqual(await state(page), pageHidden);

    await page.locator('#tab-m3').evaluate(node => node.scrollIntoView({ behavior: 'instant', block: 'center' }));
    await tick(page);
    await page.locator('#tab-m3').focus();
    await page.keyboard.press('End');
    assert.equal(await page.locator('#component-panel').getAttribute('aria-labelledby'), 'tab-m5');
    assert.equal(await page.locator('#tab-m5').evaluate(node => node === document.activeElement), true);
    if (reducedMotion === 'reduce') assert.deepEqual(await visualState(page, '.module-details'), { opacity: 1, transform: 'none' });
    await page.keyboard.press('Home');
    assert.equal(await page.locator('#component-panel').getAttribute('aria-labelledby'), 'tab-m1');
    await tick(page, 500);
    assert.deepEqual(await visualState(page, '.module-details'), { opacity: 1, transform: 'none' });
    await assertWidth(page);

    if (viewport.width === 1440 && reducedMotion === 'no-preference') {
      await showReplay(page);
      await page.locator('#replay-restart').click();
      await assertStage(page, 'candidate', true);
      for (const [duration, stage] of [[3300, 'feedback'], [4500, 'repair'], [3700, 'verified']]) {
        await tick(page, duration);
        await assertStage(page, stage, true);
      }
      await tick(page, 4100);
      await assertStage(page, 'verified');
      assert.equal((await state(page)).state, 'complete');
      assert.equal(await progress(page), 1);
      await page.locator('#replay-restart').click();
      await tick(page, 400);
      await page.emulateMedia({ reducedMotion: 'reduce' });
      await tick(page, 100);
      await assertStage(page, 'candidate');
      await tick(page, 10000);
      await assertStage(page, 'candidate');
      assert.deepEqual(await visualState(page, '#stage-candidate'), { opacity: 1, transform: 'none' });
    }
    checks.push(currentCheck);
    console.log(`Passed ${currentCheck}: paused default, playback controls, manual/keyboard interruption, viewport and document lifecycle, responsive layout.`);
    await context.close();
    currentPage = undefined;
  }

  for (const viewport of viewports) {
    currentCheck = `${viewport.width}px JavaScript disabled`;
    const context = await browser.newContext({ viewport, javaScriptEnabled: false });
    const page = await context.newPage();
    currentPage = page;
    track(page);
    await page.goto(url);
    assert.equal(await page.locator('.replay-playback').isVisible(), false);
    assert.equal(await page.locator('#stage-verified').isVisible(), true);
    assert.match(await page.locator('.receipt-status').innerText(), /evaluated_passed/);
    assert.equal(await page.locator('.receipt-evidence').getAttribute('href'), 'assets/replay.json');
    assert.ok(await page.locator('.workbench-picture img').evaluate(image => image.complete && image.naturalWidth > 0));
    checks.push(currentCheck);
    await context.close();
    currentPage = undefined;
  }
  assert.equal(apiRequests, 0, 'The static replay must never invoke an API');
  assert.deepEqual(errors, [], 'The website must not log warnings or errors');
  await fs.writeFile(path.join(output, 'report.json'), JSON.stringify({ checks, screenshots, apiRequests, errors }, null, 2) + '\n');
  console.log(`Landing motion checks passed: ${checks.length} viewport/preference cases; complete four-step playback, live preference changes, static evidence, and no API calls.`);
} catch (error) {
  if (currentPage && !currentPage.isClosed()) {
    await currentPage.screenshot({ path: path.join(output, 'failure.png'), fullPage: true }).catch(() => {});
  }
  console.error(`Failed ${currentCheck}`);
  throw error;
} finally {
  await browser.close();
}
