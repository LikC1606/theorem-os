#!/usr/bin/env bun
import fs from 'node:fs';
import path from 'node:path';
import { parseArgs } from 'node:util';
import { fileURLToPath } from 'node:url';
import { createMathRetrievalCorpus } from "../../src/math/mathRetrievalCorpus";
import {
  canonicalMathJson,
  mathDigest,
  syncMathDirectory,
} from "../../src/math/mathRuntimeIo";

export async function freezeMathRetrievalCorpus(args: readonly string[]) {
  const { values } = parseArgs({
    args: [...args],
    options: {
      workspace: { type: 'string' },
      scope: { type: 'string', multiple: true },
      output: { type: 'string' },
    },
  });
  if (!values.workspace || !values.output || !values.scope?.length) {
    throw new Error(
      'Usage: bun scripts/mathematics/freezeMathRetrievalCorpus.ts --workspace DIR --scope PACKAGE --output NEW_FILE'
    );
  }
  const root = fs.realpathSync(values.workspace);
  const output = path.resolve(values.output);
  const corpus = await createMathRetrievalCorpus(root, values.scope);
  const content = canonicalMathJson(corpus);
  // An explicit new path prevents accidental replacement of an experiment's frozen identity.
  const fd = fs.openSync(
    output,
    fs.constants.O_CREAT | fs.constants.O_EXCL | fs.constants.O_WRONLY | fs.constants.O_NOFOLLOW,
    0o600
  );
  try {
    fs.writeFileSync(fd, content, 'utf8');
    fs.fchmodSync(fd, 0o400);
    fs.fsyncSync(fd);
  } finally {
    fs.closeSync(fd);
  }
  syncMathDirectory(path.dirname(output));
  return { path: output, sha256: mathDigest(content), sourceFiles: corpus.sources.length, solverInvoked: false };
}

if (process.argv[1] && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  freezeMathRetrievalCorpus(process.argv.slice(2)).then(
    (result) => console.log(JSON.stringify(result)),
    (error: unknown) => {
      console.error(error instanceof Error ? error.message : String(error));
      process.exitCode = 1;
    }
  );
}
