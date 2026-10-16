#!/usr/bin/env bun
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { build } from 'esbuild';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const output = path.join(root, 'out/web');
fs.mkdirSync(output, { recursive: true });
await build({ entryPoints: [path.join(root, 'apps/web/client/app.ts')], outfile: path.join(output, 'app.js'),
  bundle: true, minify: true, target: 'es2023', platform: 'browser', logLevel: 'silent' });
for (const [source, destination] of [['index.html', 'index.html'], ['app.css', 'app.css']])
  fs.copyFileSync(path.join(root, 'apps/web/client', source), path.join(output, destination));
fs.mkdirSync(path.join(output, 'assets/fonts'), { recursive: true });
for (const file of ['mark.svg', 'fonts/InterVariable.woff2', 'fonts/Inter-LICENSE.txt'])
  fs.copyFileSync(path.join(root, 'docs/assets', file), path.join(output, 'assets', file));
fs.mkdirSync(path.join(output, 'assets/licenses'), { recursive: true });
fs.copyFileSync(path.join(root, 'node_modules/diff/LICENSE'), path.join(output, 'assets/licenses/diff-LICENSE.txt'));
fs.copyFileSync(path.join(root, 'LICENSE'), path.join(output, 'LICENSE.txt'));
console.log('Built research workbench in out/web');
