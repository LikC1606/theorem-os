import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import { afterEach, beforeEach, describe, expect, it } from 'vitest';
import { mathDigest } from '../src/math/mathRuntimeIo';

const cli = path.resolve('bin/math.ts');
let directory: string;
beforeEach(() => { directory = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'knowledge-cli-'))); });
afterEach(() => fs.rmSync(directory, { recursive: true, force: true }));

function fixture() {
  const files = { 'Submission.lean': 'theorem saved : True := by trivial\n',
    'lean-toolchain': 'leanprover/lean4:v0.0.0\n', 'lakefile.toml': 'name = "offline-knowledge"\n' };
  const project = path.join(directory, 'fixture'); fs.mkdirSync(project);
  for (const [file, text] of Object.entries(files)) fs.writeFileSync(path.join(project, file), text);
  const manifest = path.join(directory, 'accepted.json');
  fs.writeFileSync(manifest, JSON.stringify([{ problem_id: 'fixture', directory: 'fixture', status: 'official_accepted',
    original_source_commit: 'a'.repeat(40), result_url: 'https://example.org/result',
    source_sha256: Object.fromEntries(Object.entries(files).map(([file, text]) => [file, mathDigest(text)])) }]));
  return { manifest, project };
}
function run(...args: string[]) {
  return spawnSync('bun', [cli, 'knowledge', ...args], { cwd: directory, encoding: 'utf8',
    env: { ...process.env, ELAN_HOME: path.join(directory, 'uninstalled-toolchains') }, timeout: 30000 });
}
function json(...args: string[]) {
  const result = run(...args);
  expect(result.status, result.stderr).toBe(0);
  return JSON.parse(result.stdout);
}

describe('explicit knowledge enrichment CLI', () => {
  it('records an unavailable pin without compiling implicitly and round trips it through build and metadata', () => {
    const { manifest, project } = fixture(), sidecar = path.join(directory, 'enrichment.json');
    const catalog = path.join(directory, 'catalog.json');
    const enriched = json('enrich', '--accepted-manifest', manifest, '--problem', 'fixture', '--output', sidecar);
    expect(enriched).toMatchObject({ collected: 0, failed: 0, unavailable: 1 });
    expect(fs.existsSync(path.join(project, '.lake', 'build'))).toBe(false);
    const build = json('build', '--accepted-manifest', manifest, '--accepted-enrichment', sidecar, '--output', catalog);
    expect(build.entries).toBe(1);
    const searched = json('search', '--catalog', catalog, '--query', 'saved');
    const id = searched.hits[0].id;
    expect(searched.hits[0].consumers).toEqual({ command: 'knowledge consumers', id });
    expect(json('get', '--catalog', catalog, '--id', id, '--metadata', '--field', 'elaboration'))
      .toMatchObject({ text: 'null', truncated: false, requiresFreshCheck: true });
    expect(json('consumers', '--catalog', catalog, '--id', id, '--max-bytes', '16000'))
      .toMatchObject({ environmentMatch: 'unknown', coverage: { status: 'unknown' }, total: 0, consumers: [] });
    expect(fs.existsSync(path.join(project, '.lake', 'build'))).toBe(false);
  });

  it('rejects an unmatched enrichment option before creating a catalog', () => {
    fixture();
    const output = path.join(directory, 'unwritten.json');
    const result = run('build', '--accepted-enrichment', path.join(directory, 'missing.json'), '--output', output);
    expect(result.status).toBe(1); expect(result.stderr).toContain('corresponding explicit manifest');
    expect(fs.existsSync(output)).toBe(false);
  });

  it('retries unavailable roots through a separately bound sidecar', () => {
    const { manifest, project } = fixture();
    const initial = path.join(directory, 'initial.json'), retry = path.join(directory, 'retry.json');
    json('enrich', '--accepted-manifest', manifest, '--problem', 'fixture', '--output', initial);
    const original = fs.readFileSync(initial);
    expect(json('enrich', '--accepted-manifest', manifest, '--problem', 'fixture',
      '--retry-enrichment', initial, '--output', retry)).toMatchObject({ reportedRoots: 1, unavailable: 1 });
    expect(fs.readFileSync(initial)).toEqual(original);
    const catalog = path.join(directory, 'retry-catalog.json');
    expect(json('build', '--accepted-manifest', manifest, '--accepted-enrichment', retry, '--output', catalog).entries).toBe(1);
    expect(fs.existsSync(path.join(project, '.lake', 'build'))).toBe(false);
  });

  it('rejects an unmatched retry manifest before creating an output', () => {
    const { manifest } = fixture(), initial = path.join(directory, 'initial.json');
    json('enrich', '--accepted-manifest', manifest, '--problem', 'fixture', '--output', initial);
    fs.appendFileSync(manifest, '\n');
    const output = path.join(directory, 'unwritten.json');
    const result = run('enrich', '--accepted-manifest', manifest, '--problem', 'fixture',
      '--retry-enrichment', initial, '--output', output);
    expect(result.status).toBe(1);
    expect(result.stderr).toContain('math_knowledge_enrichment_mismatch');
    expect(fs.existsSync(output)).toBe(false);
  });

  it('rejects the retry option outside explicit enrichment', () => {
    const output = path.join(directory, 'unwritten.json');
    const result = run('build', '--retry-enrichment', path.join(directory, 'missing.json'), '--output', output);
    expect(result.status).toBe(1); expect(result.stderr).toContain('--retry-enrichment requires enrich');
    expect(fs.existsSync(output)).toBe(false);
  });

  it('rejects an existing enrichment output before tool discovery', () => {
    const { manifest } = fixture(), output = path.join(directory, 'existing.json');
    fs.writeFileSync(output, 'keep-this-file\n');
    const result = run('enrich', '--accepted-manifest', manifest, '--problem', 'fixture', '--output', output);
    expect(result.status).toBe(1); expect(result.stderr).toContain('math_knowledge_output_exists');
    expect(fs.readFileSync(output, 'utf8')).toBe('keep-this-file\n');
  });

  it('rejects source changes and invalid consumer pages without publishing output', () => {
    const { manifest, project } = fixture(), sidecar = path.join(directory, 'enrichment.json');
    const catalog = path.join(directory, 'catalog.json');
    json('enrich', '--accepted-manifest', manifest, '--problem', 'fixture', '--output', sidecar);
    json('build', '--accepted-manifest', manifest, '--accepted-enrichment', sidecar, '--output', catalog);
    const id = json('search', '--catalog', catalog, '--query', 'saved').hits[0].id;
    expect(run('consumers', '--catalog', catalog, '--id', id, '--offset=-1').stderr)
      .toContain('math_knowledge_consumers_options_invalid');
    fs.appendFileSync(path.join(project, 'Submission.lean'), '-- changed\n');
    const output = path.join(directory, 'changed.json');
    const result = run('build', '--accepted-manifest', manifest, '--accepted-enrichment', sidecar, '--output', output);
    expect(result.status).toBe(1); expect(result.stderr).toContain('math_knowledge_accepted_source_changed');
    expect(fs.existsSync(output)).toBe(false);
  });
});
