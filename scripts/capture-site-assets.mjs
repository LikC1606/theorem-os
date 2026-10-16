import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import { execFileSync } from 'node:child_process';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { chromium } from 'playwright';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const resultFile = process.argv[2];
if (!resultFile) throw new Error('Usage: node scripts/capture-site-assets.mjs /path/to/preset-replay/result.json');
const result = JSON.parse(fs.readFileSync(resultFile, 'utf8'));
assert.equal(result.example?.source, 'preset-replay');
assert.equal(result.example?.modelInvoked, false);
assert.equal(result.status, 'evaluated_passed');
assert.equal(result.evaluator?.official, false);
const batch = result.evaluator.verification.verification;
assert.equal(batch.status, 'kernel_verified');
assert.ok(batch.results.length > 0);
assert.ok(batch.results.every(item => item.status === 'kernel_verified' && item.sorryCount === 0));
const evidence = {
  schema: 'theoremos.site-replay-evidence.v1', runId: result.runId, status: result.status,
  source: result.example.source, modelInvoked: result.example.modelInvoked,
  method: result.evaluator.method, official: result.evaluator.official,
  checkedAt: new Date(batch.checkedAt).toISOString(),
  targets: batch.results.map(item => ({
    theorem: item.theoremName, declaration: item.elaboratedDeclarationType,
    status: item.status, receiptId: item.receiptId, sorryCount: item.sorryCount,
  })),
};
const assets = path.join(root, 'docs/assets');
fs.mkdirSync(assets, { recursive: true });
fs.writeFileSync(path.join(assets, 'replay.json'), JSON.stringify(evidence, null, 2) + '\n');
const browser = await chromium.launch();
try {
  const page = await browser.newPage({ viewport: { width: 1100, height: 640 }, deviceScaleFactor: 1, reducedMotion: 'reduce' });
  const mark = fs.readFileSync(path.join(assets, 'mark.svg')).toString('base64');
  await page.setContent(`<img src="data:image/svg+xml;base64,${mark}" width="128" height="128" alt="">`);
  await page.locator('img').screenshot({ path: path.join(assets, 'mark.png'), omitBackground: true });
  await page.setContent(`<!doctype html><html><head><meta charset="utf-8"><style>
    *{box-sizing:border-box;margin:0;letter-spacing:0}body{background:#202b26;color:#dae6de;font-family:Consolas,"Liberation Mono",monospace}
    .receipt{width:1100px;height:640px;padding:58px 64px}header{display:flex;align-items:center;justify-content:space-between;color:#849e8e;font-size:17px;border-bottom:1px solid #3c5143;padding-bottom:23px}
    h1{color:#a8daba;font-size:35px;margin:31px 0 11px;font-weight:500}.context{font-size:17px;color:#92aa9a;margin-bottom:31px}.row{display:flex;align-items:center;justify-content:space-between;border-top:1px solid #344a3b;padding:20px 0;font-size:19px;gap:20px}
    .row span:last-child{color:#a8daba;font-size:17px}.declaration{color:#819c89;font-size:15px;margin-top:6px}.evaluation{margin-top:20px;display:grid;grid-template-columns:180px auto;gap:11px;font-size:16px;color:#9fb6a5}.evaluation dt{color:#728f7b}.evaluation dd{margin:0}.evaluation .false{color:#dfc08b}
    footer{display:flex;justify-content:space-between;margin-top:31px;padding-top:22px;border-top:1px solid #3c5143;color:#748e7c;font-size:13px}
  </style></head><body><div class="receipt"><header><span>THEOREMOS / LOCAL REPLAY</span><span>LEAN KERNEL</span></header><h1 id="outcome"></h1><p class="context">preset-replay · modelInvoked: false</p><div id="targets"></div><dl class="evaluation"><dt>method</dt><dd id="method"></dd><dt>official</dt><dd class="false">false</dd><dt>sorryCount</dt><dd>0</dd></dl><footer><span id="checked"></span><span>RECORDED LOCAL EVIDENCE</span></footer></div></body></html>`);
  await page.evaluate(evidence => {
    document.querySelector('#outcome').textContent = evidence.status;
    document.querySelector('#method').textContent = evidence.method;
    document.querySelector('#checked').textContent = evidence.checkedAt.slice(0, 10);
    for (const target of evidence.targets) {
      const row = document.createElement('div');
      row.className = 'row';
      const description = document.createElement('div');
      description.textContent = target.theorem;
      const type = document.createElement('p');
      type.className = 'declaration';
      type.textContent = target.declaration;
      description.append(type);
      const status = document.createElement('span');
      status.textContent = target.status;
      row.append(description, status);
      document.querySelector('#targets').append(row);
    }
  }, evidence);
  await page.screenshot({ path: path.join(assets, 'replay.png') });
  execFileSync('bun', ['run', 'build:site'], { cwd: root, stdio: 'inherit' });
  await page.setViewportSize({ width: 1440, height: 960 });
  await page.goto(pathToFileURL(path.join(root, 'out/site/archive.html')).href);
  await page.waitForSelector('.proof-row');
  await page.screenshot({ path: path.join(assets, 'archive-preview.png'), clip: { x: 0, y: 0, width: 1440, height: 900 } });
  console.log('Generated mark.png, replay.png, archive-preview.png, and replay.json from recorded local evidence.');
} finally {
  await browser.close();
}
