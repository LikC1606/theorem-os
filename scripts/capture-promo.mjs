import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { chromium } from 'playwright';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const browser = await chromium.launch();
try {
  const page = await browser.newPage({ viewport: { width: 1200, height: 630 }, reducedMotion: 'reduce' });
  await page.goto(pathToFileURL(path.join(root, 'out/site/index.html')).href);
  const illustration = await page.locator('.manifold').evaluate(svg => svg.outerHTML);
  const css = fs.readFileSync(path.join(root, 'out/site/landing.css'), 'utf8');
  const mark = fs.readFileSync(path.join(root, 'docs/assets/mark.svg')).toString('base64');
  await page.setContent(`<!doctype html><html lang="zh-CN"><meta charset="utf-8"><style>${css}
    body{width:1200px;height:630px;overflow:hidden;background:#0a1122;color:#f4f7ff}
    .social{padding:44px 58px;position:relative;height:630px;background:radial-gradient(ellipse at 80% 45%,#1c396b88,transparent 65%)}
    .social-top{display:flex;align-items:center;justify-content:space-between;padding-bottom:28px;border-bottom:1px solid #293750}
    .social .brand{font-size:27px;gap:12px}.social .brand img{width:36px;height:36px}
    .preview{font:11px var(--mono);color:#9ab4dd;letter-spacing:.5px;border:1px solid #3b5277;border-radius:6px;padding:9px 12px}
    .social .eyebrow{font-size:10px;letter-spacing:1.5px;margin:39px 0 21px;color:#8da9d9;position:relative;z-index:1}
    .social h1{font-size:66px;line-height:1.28;letter-spacing:-2.8px;position:relative;z-index:1;font-weight:680}
    .social h1 em{color:#76a3ff}.social p{font-size:16px;line-height:1.9;color:#a8bad9;margin-top:23px;position:relative;z-index:1}
    .social .manifold{position:absolute;right:-8px;top:77px;width:630px;height:541px}
    .social .social-check{position:absolute;right:83px;bottom:111px;display:flex;align-items:center;gap:10px;padding:12px 17px;border:1px solid #496b9c;border-radius:9px;background:#1b3153e8;color:#d4e6ff;font-size:12px}
    .social-check .checkmark{color:#a2caff;font-size:16px}.social-check small{color:#8da6cd;margin-left:6px;font-size:10px}
    .social-bottom{position:absolute;left:58px;right:58px;bottom:29px;padding-top:20px;border-top:1px solid #293750;display:flex;justify-content:space-between;font:10px var(--mono);letter-spacing:.6px;color:#8ba1c5}
  </style><body><div class="social"><div class="social-top"><div class="brand"><img src="data:image/svg+xml;base64,${mark}" alt=""><span>Theorem<span class="brand-os">OS</span></span></div><span class="preview">v0.1.0 / RESEARCH PREVIEW</span></div><div class="eyebrow">A RUNTIME FOR MATHEMATICAL AGENTS</div><h1>从自由探索，<br><em>到严谨证明。</em></h1><p>为数学 Agent 打造的开源研究运行时。<br>自由组合研究策略，让每次探索有迹可循。</p>${illustration}<div class="social-check"><span class="checkmark">✓</span>完整原题 · 独立 Lean 验收<small>概念视图</small></div><div class="social-bottom"><span>COMPOSABLE · VERIFIABLE · REPRODUCIBLE</span><span>likc1606.github.io/theorem-os</span></div></div></body></html>`);
  await page.evaluate(() => document.fonts.ready);
  await page.screenshot({ path: path.join(root, 'docs/assets/social-preview.png') });
  console.log('Generated docs/assets/social-preview.png from the website illustration and typography.');
} finally {
  await browser.close();
}
