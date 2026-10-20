#!/usr/bin/env bun
import fs from 'node:fs';
import path from 'node:path';
import { parseArgs } from 'node:util';
import { importKnowledgeRuns } from '../../src/solver/theoremKnowledgeRuns';
import { importAcceptedKnowledge } from '../../src/solver/theoremKnowledgeAccepted';
import { buildTheoremKnowledge, getKnowledgeTheorem, searchTheoremKnowledgeBatch,
  theoremKnowledgeStats, writeTheoremKnowledge } from '../../src/solver/theoremKnowledge';
import { readKnowledgeCatalog, writePackedKnowledge } from '../../src/solver/theoremKnowledgeStore';
import { getKnowledgeDependencies } from '../../src/solver/theoremKnowledgeDependencies';
import { getKnowledgeConsumers } from '../../src/solver/theoremKnowledgeConsumers';
import { enrichAcceptedKnowledge, writeKnowledgeEnrichment } from '../../src/solver/theoremKnowledgeEnrichment';
import { getKnowledgeSource } from '../../src/solver/theoremKnowledgeSource';
import { getKnowledgeMetadata, type KnowledgeMetadataField } from '../../src/solver/theoremKnowledgeMetadata';
import { searchKnowledgeRouteFindings, getKnowledgeRouteFindingPage } from '../../src/solver/theoremKnowledgeFindings';
import { assertMathCanonicalPath } from '../../src/math/paths';

const help = `Usage: theorem-os knowledge <build|enrich|pack|search|get|finding|source|dependencies|consumers|stats> [arguments]
  build  [--state STATE_JSON ...] [--accepted-manifest accepted.json] [--submitted-manifest submitted.json]
         [--accepted-enrichment FILE] [--submitted-enrichment FILE]
         --output NEW_CATALOG [--merge EXISTING_CATALOG] [--report NEW_REPORT] [--format v1|v2] [--include-findings]
  enrich --accepted-manifest accepted.json --problem ID --output NEW_SIDECAR
         (or --submitted-manifest submitted.json) [--retry-enrichment PREVIOUS_SIDECAR]
  pack   --catalog FILE --output NEW_CATALOG [--sha256 HASH]
  search --catalog FILE [--query KEYWORDS ...] [--goal LEAN_CONTEXT]
         [--limit 1..32] [--problem ID] [--environment DIGEST] [--problem-receipt DIGEST] [--sha256 HASH] [--include-findings]
  get    --catalog FILE --id THEOREM_ID [--source ARCHIVED_FILE] [--sha256 HASH]
         [--metadata [--field FIELD --offset N] [--max-bytes 1024..65536]]
  finding --catalog FILE --id FINDING_ID [--sha256 HASH] [--offset N] [--max-bytes 1024..65536]
  source --catalog FILE --id THEOREM_ID [--file ARCHIVED_FILE]
         [--name QUALIFIED_DECLARATION | --start-line N | --offset N]
         [--lines 1..200] [--max-bytes 1024..65536] [--sha256 HASH]
  dependencies --catalog FILE --id THEOREM_ID [--depth 0..8] [--sha256 HASH]
  consumers --catalog FILE --id THEOREM_ID [--offset N] [--limit 1..32] [--max-bytes 1024..65536] [--sha256 HASH]
  stats  --catalog FILE [--sha256 HASH]

Catalogs contain historical sources and recorded evidence. Reuse requires fresh Lean
checking in the target problem. Search previews are bounded; get returns exact types
and declarations. --source returns a complete archived file, including its context.
Use get --metadata for a bounded JSON packet without proof bodies. Deferred fields
have read handles; --field and --offset return exact text pages with nextOffset.
Text fields concatenate directly; concatenate JSON fields before parsing them.
The source command returns bounded exact excerpts; --offset uses UTF-16 code units
and resumes at nextOffset. An excerpt does not establish complete Lean context.
Build reads only explicit sources and never starts a solver or calls a model.
Only enrich runs Lean, in a disposable full-proof copy with the already installed
pinned toolchain. It has no time limit. Unavailable environments remain unknown.
Sidecars bind the exact manifest, record, source, configuration, tool and collector.
--retry-enrichment collects only failed, unavailable or missing roots from the
validated previous sidecar. Its new sidecar records the selected roots separately.
Build never compiles an archive implicitly. Consumers are same-context local
reference closures, not instantiated applications; missing coverage stays unknown.
--include-findings explicitly imports or searches advisory research separately from
checked theorems. Group-private findings and findings depending on private tasks are
excluded. A recorded refutation never refutes an original theorem or parks a task.
finding returns exact JSON text pages; concatenate them using nextOffset before
parsing. Recorded assumptions, local-check claims and reopening conditions require
review in the current problem; old evidence never grants new acceptance.
Use --merge with a new output path to add proofs without overwriting old catalogs.`;

try {
  const [command, ...args] = process.argv.slice(2);
  if (!command || ['--help', '-h', 'help'].includes(command) || args.includes('--help')) {
    console.log(help);
  } else {
    const { values } = parseArgs({ args, options: {
      state: { type: 'string', multiple: true }, 'accepted-manifest': { type: 'string' }, 'submitted-manifest': { type: 'string' },
      'accepted-enrichment': { type: 'string' }, 'submitted-enrichment': { type: 'string' },
      'retry-enrichment': { type: 'string' },
      output: { type: 'string' }, merge: { type: 'string' }, report: { type: 'string' },
      format: { type: 'string', default: 'v2' },
      catalog: { type: 'string' }, sha256: { type: 'string' }, query: { type: 'string', multiple: true },
      goal: { type: 'string' }, limit: { type: 'string', default: '10' }, problem: { type: 'string' },
      environment: { type: 'string' }, 'problem-receipt': { type: 'string' },
      id: { type: 'string' }, source: { type: 'string' }, depth: { type: 'string', default: '2' },
      metadata: { type: 'boolean' }, field: { type: 'string' },
      'include-findings': { type: 'boolean' },
      file: { type: 'string' }, name: { type: 'string' }, 'start-line': { type: 'string' }, offset: { type: 'string' },
      lines: { type: 'string' }, 'max-bytes': { type: 'string' },
    } });
    const required = (name: string) => {
      const value = values[name];
      if (typeof value !== 'string' || !value.trim()) throw new Error(`--${name} is required`);
      return value;
    };
    if (values['retry-enrichment'] !== undefined && command !== 'enrich')
      throw new Error('--retry-enrichment requires enrich');
    if (command === 'build') {
      if (values['accepted-enrichment'] && !values['accepted-manifest'] || values['submitted-enrichment'] && !values['submitted-manifest'])
        throw new Error('enrichment requires its corresponding explicit manifest');
      if (values['include-findings'] && !values.state?.length) throw new Error('--include-findings requires explicit --state inputs');
      if (!values.state?.length && !values['accepted-manifest'] && !values['submitted-manifest'])
        throw new Error('--state, --accepted-manifest or --submitted-manifest is required');
      const output = path.resolve(required('output'));
      assertMathCanonicalPath(output);
      if (fs.existsSync(output)) throw new Error('math_knowledge_output_exists');
      const report = values.report ? path.resolve(values.report) : undefined;
      if (report) {
        assertMathCanonicalPath(report);
        if (report === output || fs.existsSync(report)) throw new Error('math_knowledge_report_exists_or_conflicts');
      }
      if (!['v1', 'v2'].includes(values.format)) throw new Error('--format must be v1 or v2');
      const previous = values.merge ? readKnowledgeCatalog(values.merge).base : undefined;
      const imports = [
        ...(values.state?.length ? [importKnowledgeRuns(values.state, { includeFindings: values['include-findings'] })] : []),
        ...(values['accepted-manifest'] ? [importAcceptedKnowledge(values['accepted-manifest'],
          { enrichmentFile: values['accepted-enrichment'] })] : []),
        ...(values['submitted-manifest'] ? [importAcceptedKnowledge(values['submitted-manifest'],
          { enrichmentFile: values['submitted-enrichment'] })] : []),
      ];
      const candidates = imports.flatMap(item => item.candidates), skipped = imports.flatMap(item => item.skipped);
      const findings = imports.flatMap(item => item.findings ?? []);
      const base = buildTheoremKnowledge(candidates, previous, findings);
      const result = values.format === 'v1' ? writeTheoremKnowledge(output, base) : writePackedKnowledge(output, base);
      const summary = { ...result, inputCandidates: candidates.length, inputFindings: findings.length, skippedRecords: skipped.length };
      if (report) {
        fs.mkdirSync(path.dirname(report), { recursive: true, mode: 0o700 });
        const fd = fs.openSync(report, 'wx', 0o400);
        try { fs.writeFileSync(fd, JSON.stringify({ ...summary, skipped }, null, 2) + '\n'); fs.fsyncSync(fd); }
        finally { fs.closeSync(fd); }
      }
      console.log(JSON.stringify({ ...summary, ...(report ? { report } : {}) }));
    } else if (command === 'enrich') {
      if (Boolean(values['accepted-manifest']) === Boolean(values['submitted-manifest']))
        throw new Error('enrich requires exactly one --accepted-manifest or --submitted-manifest');
      const output = path.resolve(required('output'));
      assertMathCanonicalPath(output);
      if (fs.existsSync(output)) throw new Error('math_knowledge_output_exists');
      const controller = new AbortController();
      const stop = () => controller.abort();
      process.once('SIGINT', stop); process.once('SIGTERM', stop);
      try {
        const result = await enrichAcceptedKnowledge(values['accepted-manifest'] ?? values['submitted-manifest']!, required('problem'),
          { signal: controller.signal, timeoutMs: Infinity, retryFile: values['retry-enrichment'] });
        console.log(JSON.stringify(writeKnowledgeEnrichment(output, result)));
      } finally { process.removeListener('SIGINT', stop); process.removeListener('SIGTERM', stop); }
    } else if (['pack', 'search', 'get', 'finding', 'source', 'dependencies', 'consumers', 'stats'].includes(command)) {
      const { base, digest, format } = readKnowledgeCatalog(required('catalog'), values.sha256);
      if (command === 'pack') console.log(JSON.stringify(writePackedKnowledge(required('output'), base, digest)));
      else if (command === 'stats') console.log(JSON.stringify({ sha256: digest, format, ...theoremKnowledgeStats(base) }));
      else if (command === 'finding') console.log(JSON.stringify(getKnowledgeRouteFindingPage(base, required('id'), {
        startOffset: values.offset === undefined ? undefined : Number(values.offset),
        maxBytes: values['max-bytes'] === undefined ? undefined : Number(values['max-bytes']),
      })));
      else if (command === 'get') {
        if (values.metadata) {
          if (values.source !== undefined) throw new Error('--metadata cannot be combined with --source');
          console.log(JSON.stringify(getKnowledgeMetadata(base, required('id'), {
            field: values.field as KnowledgeMetadataField | undefined,
            startOffset: values.offset === undefined ? undefined : Number(values.offset),
            maxBytes: values['max-bytes'] === undefined ? undefined : Number(values['max-bytes']),
          })));
        } else {
          if (values.field !== undefined || values.offset !== undefined || values['max-bytes'] !== undefined)
            throw new Error('get --field, --offset and --max-bytes require --metadata');
          console.log(JSON.stringify(getKnowledgeTheorem(base, required('id'), values.source)));
        }
      }
      else if (command === 'source') console.log(JSON.stringify(getKnowledgeSource(base, required('id'), {
        file: values.file, name: values.name,
        startLine: values['start-line'] === undefined ? undefined : Number(values['start-line']),
        startOffset: values.offset === undefined ? undefined : Number(values.offset),
        lines: values.lines === undefined ? undefined : Number(values.lines),
        maxBytes: values['max-bytes'] === undefined ? undefined : Number(values['max-bytes']),
      })));
      else if (command === 'dependencies')
        console.log(JSON.stringify(getKnowledgeDependencies(base, required('id'), { depth: Number(values.depth) })));
      else if (command === 'consumers') console.log(JSON.stringify(getKnowledgeConsumers(base, required('id'), {
        offset: values.offset === undefined ? undefined : Number(values.offset), limit: Number(values.limit),
        maxBytes: values['max-bytes'] === undefined ? undefined : Number(values['max-bytes']),
      })));
      else {
        const queries = values.query?.length ? values.query : values.goal?.trim() ? [''] : [];
        if (!queries.length || queries.length > 8) throw new Error('supply 1..8 --query arguments or a nonempty --goal');
        const results = searchTheoremKnowledgeBatch(base, queries, {
          goal: values.goal, limit: Number(values.limit), problemId: values.problem,
          environmentDigest: values.environment, problemReceiptDigest: values['problem-receipt'],
        });
        if (values['include-findings']) for (let index = 0; index < results.length; index++) {
          Object.assign(results[index], { routeFindings: searchKnowledgeRouteFindings(base, queries[index], {
            goal: values.goal, limit: Number(values.limit), problemId: values.problem,
            environmentDigest: values.environment, problemReceiptDigest: values['problem-receipt'],
          }) });
        }
        console.log(JSON.stringify(results.length === 1 ? results[0] : { queries: queries.map((query, index) => ({ query, ...results[index] })) }));
      }
    } else throw new Error(`Unknown knowledge command: ${command}`);
  }
} catch (error) {
  console.error(error instanceof Error ? error.message : 'math_knowledge_failed');
  process.exitCode = 1;
}
