import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { chromium } from 'playwright';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const browser = await chromium.launch();
try {
  const page = await browser.newPage({ viewport: { width: 1200, height: 630 }, reducedMotion: 'reduce' });
  await page.goto(pathToFileURL(path.join(root, 'out/site/index.html')).href);
  const title = await page.locator('#hero-title').innerHTML();
  const category = await page.locator('.hero-category').innerText();
  const description = await page.locator('.hero-description').innerText();
  const css = fs.readFileSync(path.join(root, 'out/site/landing.css'), 'utf8');
  const mark = fs.readFileSync(path.join(root, 'docs/assets/mark.svg')).toString('base64');
  const workbench = fs.readFileSync(path.join(root, 'docs/assets/workbench-desktop.png')).toString('base64');
  await page.setContent(`<!doctype html><html lang="zh-CN"><meta charset="utf-8"><style>${css}
    body{width:1200px;height:630px;overflow:hidden;background:#f7f9fc;color:#20232a}
    .social{position:relative;height:630px;padding:28px 70px}
    .social-top{display:flex;align-items:center;justify-content:space-between}
    .social .brand{font-size:11px;gap:12px;color:#68778f}.social .brand img{width:28px;height:28px}
    .preview{font:10px var(--mono);color:#59657c;border:1px solid #d8e0ed;border-radius:4px;padding:7px 10px;background:#fff}
    .social h1{font-size:60px;line-height:1.1;margin:18px 0 7px}
    .social-category{font-size:22px;line-height:1.5;color:#303a4b}
    .social-description{font-size:13px;color:#6c7585;margin-top:5px}
    .social-product{position:absolute;left:70px;right:70px;top:226px;border-block:1px solid #dce2eb}
    .social-product img{width:100%;height:auto}
    .social-bottom{position:absolute;left:70px;right:70px;bottom:13px;display:flex;justify-content:space-between;font:9px var(--mono);color:#68778f}
  </style><body><div class="social"><div class="social-top"><div class="brand"><img src="data:image/svg+xml;base64,${mark}" alt=""><span>OPEN MATHEMATICAL RESEARCH</span></div><span class="preview">v0.1.0 / RESEARCH PREVIEW</span></div><h1>${title}</h1><p class="social-category">${category}</p><p class="social-description">${description}</p><div class="social-product"><img src="data:image/png;base64,${workbench}" alt="本地工作台草稿预览"></div><div class="social-bottom"><span>LOCAL WORKBENCH · LEAN 4 + MATHLIB · BRING YOUR OWN KEY</span><span>likc1606.github.io/theorem-os</span></div></div></body></html>`);
  await page.evaluate(() => document.fonts.ready);
  await page.locator('.social-product img').evaluate(image => image.decode());
  await page.screenshot({ path: path.join(root, 'docs/assets/social-preview.png') });
  console.log('Generated docs/assets/social-preview.png from the real workbench screenshot and homepage typography.');
} finally {
  await browser.close();
}
