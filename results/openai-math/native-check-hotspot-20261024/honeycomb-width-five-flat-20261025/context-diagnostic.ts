import fs from 'node:fs';
import path from 'node:path';
import { inspectLeanDeclarationRegions } from '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/honeycomb-new-build-continuation-20261024/runtime/src/math/leanSource';

const stage = import.meta.dir;
const frozen = JSON.parse(fs.readFileSync(path.join(stage, 'fixed-source-constraints.json'), 'utf8')).constraints;
const originalNames = new Set(frozen.declarations['Submission.lean'].map((d: {name: string}) => d.name));
for (const variant of ['baseline', 'namespaced', 'flat-anonymous', 'flat-named-simp', 'project']) {
  const source = fs.readFileSync(path.join(stage, variant, 'Submission.lean'), 'utf8');
  const regions = inspectLeanDeclarationRegions(source);
  let context = '';
  let cursor = 0;
  for (const region of regions) {
    const preceding = source.slice(cursor, region.startOffset);
    context += originalNames.has(region.name) ? preceding : preceding.replace(/\bnoncomputable[ \t]+$/u, '');
    if (originalNames.has(region.name)) context += `${region.declarationType}\n`;
    cursor = region.endOffset;
  }
  context += source.slice(cursor);
  const normalized = context.split('\n').map(l => l.trim()).filter(Boolean).join('\n');
  fs.writeFileSync(path.join(stage, `${variant}-context-diagnostic.txt`), normalized + '\n', {flag: 'wx'});
  console.log(JSON.stringify({variant, regions: regions.length, contextLines: normalized.split('\n').length}));
}
fs.copyFileSync(path.join(stage, 'project/Submission.lean'), path.join(stage, 'project-guard-01-source.lean'), fs.constants.COPYFILE_EXCL);
