import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { chromium } from 'playwright';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const browser = await chromium.launch();
try {
  const page = await browser.newPage({ viewport: { width: 1200, height: 630 }, reducedMotion: 'reduce' });
  await page.goto(pathToFileURL(path.join(root, 'out/site/index.html')).href);
  const replay = await page.locator('.replay-window').evaluate(node => node.outerHTML);
  const css = fs.readFileSync(path.join(root, 'out/site/landing.css'), 'utf8');
  const mark = fs.readFileSync(path.join(root, 'docs/assets/mark.svg')).toString('base64');
  await page.setContent(`<!doctype html><html lang="zh-CN"><meta charset="utf-8"><style>${css}
    body{width:1200px;height:630px;overflow:hidden;background:#09090c;color:#eeeef4}
    .social{position:relative;height:630px;padding:35px 53px}
    .social-top{display:flex;align-items:center;justify-content:space-between}
    .social .brand{font-size:26px;gap:10px}.social .brand img{width:32px;height:32px}
    .preview{font:10px var(--mono);color:#9494a3;border:1px solid #3c3c46;border-radius:5px;padding:7px 10px}
    .social h1{font-size:39px;font-weight:550;line-height:1.4;margin:26px 0 9px}
    .social-description{font-size:13px;color:#9393a3}
    .social-product{position:absolute;left:53px;right:53px;top:219px}
    .social .replay-window{box-shadow:none}.social .replay-chrome{height:34px;font-size:10px}
    .social .replay-tabs>button{min-height:39px;font-size:11px}.social .replay-tabs .mono{font-size:9px}
    .social .replay-panel{min-height:246px}.social .editor-heading{height:35px;font-size:9px}
    .social .demo-code{padding-block:14px;font-size:11px;line-height:2}.social .code-line{min-height:22px}
    .social .replay-receipt{padding:14px 21px}.social .receipt-status{margin:13px 0}
    .social .receipt-status strong{font-size:16px}.social .receipt-status code{font-size:9px}
    .social .receipt-targets{padding-block:11px;gap:11px}.social .receipt-targets strong{font-size:10px}
    .social .receipt-targets code{font-size:9px}.social .receipt-facts{display:none}
    .social .receipt-link{font-size:9px;margin-top:12px}.social .receipt-title{font-size:9px}
    .social .replay-caption{padding-block:6px;font-size:8px}.social .motion-toggle{display:none}
    .social-bottom{position:absolute;left:53px;right:53px;bottom:20px;display:flex;justify-content:space-between;font:9px var(--mono);color:#6e6e80}
  </style><body><div class="social"><div class="social-top"><div class="brand"><img src="data:image/svg+xml;base64,${mark}" alt=""><span>Theorem<span class="brand-os">OS</span></span></div><span class="preview">v0.1.0 / RESEARCH PREVIEW</span></div><h1>数学 Agent 的研究运行时。</h1><p class="social-description">组合研究策略，保存每次尝试，由 Lean 独立验收完整原题。</p><div class="social-product">${replay}</div><div class="social-bottom"><span>OPEN SOURCE · COMPOSABLE RESEARCH · LEAN VERIFIED</span><span>likc1606.github.io/theorem-os</span></div></div></body></html>`);
  await page.evaluate(() => document.fonts.ready);
  await page.screenshot({ path: path.join(root, 'docs/assets/social-preview.png') });
  console.log('Generated docs/assets/social-preview.png from the product replay and bundled typography.');
} finally {
  await browser.close();
}
