#!/usr/bin/env bun
import fs from 'node:fs';
import path from 'node:path';
import { execFileSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import { build } from 'esbuild';
import { buildSiteCatalog } from '../docs/web/catalog';
import { acceptedProofCards, researchManifold } from '../docs/web/presentation';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const revision = execFileSync('git', ['rev-parse', 'HEAD'], { cwd: root, encoding: 'utf8' }).trim();
const catalog = buildSiteCatalog(root, revision);
const output = path.join(root, 'out/site');
fs.mkdirSync(output, { recursive: true });
await build({
  entryPoints: [path.join(root, 'docs/web/app.ts')], outfile: path.join(output, 'site.js'),
  bundle: true, platform: 'browser', format: 'iife', target: ['es2022'], minify: true,
  legalComments: 'eof',
  plugins: [{ name: 'public-archive', setup(builder) {
    builder.onResolve({ filter: /^virtual:archive$/ }, () => ({ path: 'archive', namespace: 'public-archive' }));
    builder.onLoad({ filter: /.*/, namespace: 'public-archive' }, () => ({ contents: JSON.stringify(catalog), loader: 'json' }));
  } }],
});
await build({
  entryPoints: [path.join(root, 'docs/web/landing.ts')], outfile: path.join(output, 'landing.js'),
  bundle: true, platform: 'browser', format: 'iife', target: ['es2022'], minify: true,
  legalComments: 'eof',
});
const homepage = fs.readFileSync(path.join(root, 'docs/index.html'), 'utf8')
  .replace('<!-- research-manifold -->', researchManifold())
  .replace('<!-- accepted-count -->', String(catalog.records.filter(record => record.status === 'official_accepted').length).padStart(2, '0'))
  .replace('<!-- accepted-proofs -->', acceptedProofCards(catalog));
fs.writeFileSync(path.join(output, 'index.html'), homepage);
for (const file of ['archive.html', 'site.css', 'landing.css']) fs.copyFileSync(path.join(root, 'docs', file), path.join(output, file));
fs.copyFileSync(path.join(root, 'node_modules/lucide/LICENSE'), path.join(output, 'lucide-LICENSE.txt'));
fs.copyFileSync(path.join(root, 'LICENSE'), path.join(output, 'LICENSE.txt'));
if (fs.existsSync(path.join(root, 'docs/assets'))) {
  fs.cpSync(path.join(root, 'docs/assets'), path.join(output, 'assets'), { recursive: true });
}
fs.mkdirSync(path.join(output, 'data'), { recursive: true });
fs.writeFileSync(path.join(output, 'data/catalog.json'), JSON.stringify(catalog, null, 2) + '\n');
fs.writeFileSync(path.join(output, '.nojekyll'), '');
console.log(`Built ${catalog.records.length} archive records in ${path.relative(root, output)} (${revision.slice(0, 7)})`);
