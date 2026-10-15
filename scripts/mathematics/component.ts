#!/usr/bin/env bun
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { parseArgs } from 'node:util';
import { componentPaths, createSearchComponent, checkReadyOrdering } from '../../src/solver/componentTemplate';

async function main(): Promise<number> {
  const { values, positionals } = parseArgs({ allowPositionals: true, options: {
    name: { type: 'string' }, help: { type: 'boolean' },
  } });
  if (values.help) {
    console.log('Usage: theorem-os component init|check --name my-search\ninit creates src/components/my-search.ts and scripts/components/my-search.ts without overwriting files.\ncheck checks ordering, dependency and route gates with a small local fixture; no model or Lean calls.\nEdit the ready function, update its version, then build and use a new problem case.');
    return 0;
  }
  if (positionals.length !== 1 || !['init', 'check'].includes(positionals[0]) || !values.name)
    throw new Error('Use component init|check --name my-search.');
  const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '../..');
  if (positionals[0] === 'init') {
    const files = createSearchComponent(root, values.name);
    console.log(`Created ${path.relative(root, files.source)}\nCreated ${path.relative(root, files.entry)}\n\nEdit the ready function, then run:\nbun run math component check --name ${values.name}`);
  } else {
    const loaded = await import(pathToFileURL(componentPaths(root, values.name).source).href);
    if (typeof loaded.modules?.M3?.ready !== 'function') throw new Error('The component must export modules with an M3.ready function.');
    console.log(JSON.stringify({ status: 'passed', component: loaded.modules.id,
      ...checkReadyOrdering(loaded.modules.M3.ready), note: 'Local ordering contract only; measure effectiveness with real experiments.' }, null, 2));
  }
  return 0;
}
main().then(code => { process.exitCode = code; }, error => {
  console.error(error instanceof Error ? error.message : 'Component command failed.'); process.exitCode = 1;
});
