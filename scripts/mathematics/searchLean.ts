#!/usr/bin/env bun
import fs from 'node:fs';
import path from 'node:path';
import { parseArgs } from 'node:util';
import { searchMathRetrievalCorpus, searchMathRetrievalCorpusBatch } from '../../src/math/mathRetrievalCorpus';
import { mathDigest, readMathText } from '../../src/math/mathRuntimeIo';
import { resolveMathematicsRuntimeEnvironment } from '../../src/math/mathRuntimeEnvironment';
import { readMathematicsReceiptSecret } from '../../src/math/receiptAttestation';

try {
  const args = process.argv.slice(2);
  if (args[0] === 'search-lean') args.shift();
  const { values } = parseArgs({ args, options: {
    workspace: { type: 'string' }, corpus: { type: 'string' }, query: { type: 'string', multiple: true },
    sha256: { type: 'string' }, limit: { type: 'string', default: '15' }, goal: { type: 'string' }, help: { type: 'boolean' },
  } });
  if (values.help) {
    console.log('Usage: deepscientist-math search-lean --workspace DIR --corpus FILE --query TEXT [--query TEXT ...] [--goal TEXT --limit 1..64 --sha256 HASH]\nReturns source names, line numbers, headers and source variable/open context from verified installed packages. Use short library keywords in --query; optional --goal supplies the Lean goal/context (up to 16000 bytes) to rank candidates. Ranking does not establish applicability; use #check and test the application in Lean. Up to 8 queries share one library scan. Corpus and hash default to the pinned mathematics environment.');
  } else {
    const env = resolveMathematicsRuntimeEnvironment();
    const corpus = values.corpus || env.DEEPSCIENTIST_MATH_RETRIEVAL_CORPUS;
    const digest = values.sha256 || env.DEEPSCIENTIST_MATH_RETRIEVAL_CORPUS_SHA256;
    if (!values.workspace || !corpus || !values.query?.length) throw new Error('--workspace, --corpus and --query are required');
    const text = readMathText(corpus);
    if (digest && mathDigest(text) !== digest) throw new Error('math_corpus_identity_changed');
    const library = JSON.parse(text);
    const secret = path.extname(process.argv[1] ?? '') === '.js' ? readMathematicsReceiptSecret() : undefined;
    const cache = secret ? { directory: path.join(path.dirname(corpus), 'retrieval-index'),
      implementation: mathDigest(fs.readFileSync(process.argv[1])), secret } : undefined;
    console.log(JSON.stringify(values.query.length === 1
      ? searchMathRetrievalCorpus(values.workspace, library, values.query[0]!, Number(values.limit), values.goal, cache)
      : searchMathRetrievalCorpusBatch(values.workspace, library, values.query, Number(values.limit), values.goal, cache)));
  }
} catch (error) {
  console.error(error instanceof Error ? error.message : 'math_search_failed');
  process.exitCode = 1;
}
