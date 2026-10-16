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
  const css = fs.readFileSync(path.join(root, 'docs/landing.css'), 'utf8');
  const mark = fs.readFileSync(path.join(root, 'docs/assets/mark.png')).toString('base64');
  await page.setContent(`<!doctype html><html lang="zh-CN"><meta charset="utf-8"><style>${css}
    body{width:1200px;height:630px;overflow:hidden}.social{padding:51px 64px;position:relative;height:630px}
    .social:before{content:'';position:absolute;left:64px;right:64px;top:107px;height:1px;background:#d7dacf}
    .brand{font-size:26px;gap:11px}.brand img{width:33px;height:33px}.preview{position:absolute;right:65px;top:56px;font:10px var(--mono);color:#77876a;letter-spacing:.7px}
    .social .eyebrow{font-size:9px;letter-spacing:1.4px;margin:49px 0 19px;color:#51754a}
    .social h1{font-size:68px;line-height:1.35;letter-spacing:-4px;position:relative;z-index:1}.social h1 em{letter-spacing:-4px}
    .social p{font-size:15px;line-height:1.9;color:#6c7b62;margin-top:25px}.social .manifold{position:absolute;right:0px;top:56px;width:610px;height:524px}
    .social .social-bottom{position:absolute;left:64px;right:64px;bottom:32px;padding-top:17px;border-top:1px solid #d7dacf;display:flex;justify-content:space-between;font:10px var(--mono);letter-spacing:.6px;color:#77876a}
  </style><body><div class="social"><div class="brand"><img src="data:image/png;base64,${mark}" alt=""><span>Theorem<span class="brand-os">OS</span></span></div><span class="preview">v0.1.0 / RESEARCH PREVIEW</span><div class="eyebrow">A RUNTIME FOR MATHEMATICAL AGENTS</div><h1>从自由探索，<br><em>到严谨证明。</em></h1><p>可组合的数学 Agent 研究运行时<br>研究策略可替换，证明结果可核查。</p>${illustration}<div class="social-bottom"><span>COMPOSABLE · VERIFIABLE · REPRODUCIBLE</span><span>THEOREMOS / OPEN RESEARCH</span></div></div></body></html>`);
  await page.screenshot({ path: path.join(root, 'docs/assets/social-preview.png') });
  console.log('Generated docs/assets/social-preview.png from the website illustration and typography.');
} finally {
  await browser.close();
}
