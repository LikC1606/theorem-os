import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import { afterEach, describe, expect, it } from 'vitest';
import { writeSolverRunState, type SolverRunState } from '../src/solver/archive';
import { inspectStoredRun } from '../src/solver/storedRunInspection';
import { canonicalMathJson, mathDigest } from '../src/math/mathRuntimeIo';
import { freezeContinuationInput, type ContinuationManifest } from '../src/solver/continuationInput';

const roots: string[] = [];
function fixture() {
  const root = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'math-stored-inspection-'))); roots.push(root);
  const run = path.join(root, 'result.json'), stateFile = `${run}.runtime/state.json`;
  fs.mkdirSync(path.dirname(stateFile), { mode: 0o700 });
  const task = { id: 'goal', kind: 'goal' as const, objective: 'Prove the original goal', dependsOn: [], revision: 0,
    theoremName: 'Original.goal', proofPath: 'Submission.lean' };
  const state: SolverRunState = {
    schema: 'deepscientist.math.solver.v1', runId: 'saved-run', taskDigest: 'task', buildDigest: 'build',
    environmentDigest: 'environment', evaluatorDigest: 'evaluation', model: 'fixture', effort: 'max',
    worktree: path.join(root, 'worktree'), phase: 'running', turns: 0,
    problem: { kind: 'imo2026', workspace: root, projectRelative: 'generated/example', baseCommit: 'a'.repeat(40),
      receiptDigest: 'problem', activeProblemPath: path.join(root, 'active-problem.json'),
      contract: { problemId: 'example', informalStatement: 'Prove the original goal.', formalStatement: 'theorem goal : True := by sorry',
        assumptions: [], knownTraps: [], acceptanceCriteria: [], statementHash: 's', leanStatementHash: 'l', officialVerificationCommand: 'lean' },
      targets: [{ proofPath: 'Submission.lean', theoremName: 'Original.goal', declarationHash: 'declaration' }],
      ownedFiles: ['Submission.lean'], trustedFiles: {}, declarations: {}, sourceStructure: {} },
    cooperation: { planVersion: 'version-1', canonicalCommit: 'b'.repeat(40),
      tasks: [{ task, status: 'pending', attempts: 0 }], groups: [{ group: {
        id: 'main', objective: 'Original proof', status: 'active', revision: 0 }, turns: 0 }] },
  };
  writeSolverRunState(stateFile, state);
  const result = { schema: 'deepscientist.math.run.v2', runId: state.runId, status: 'prepared', stateFile };
  fs.writeFileSync(run, JSON.stringify(result));
  const log = path.join(root, 'solver.log');
  const writeLog = (...events: Record<string, unknown>[]) => fs.writeFileSync(log, events.map(event => JSON.stringify(event) + '\n').join(''));
  const batchFile = path.join(root, 'batch.json');
  const writeBatch = (jobs: unknown[]) => fs.writeFileSync(batchFile, JSON.stringify({ jobs }));
  return { root, run, stateFile, state, result, log, writeLog, batchFile, writeBatch };
}
const invoke = (args: string[]) => spawnSync('bun', ['bin/math.ts', 'inspect', ...args],
  { encoding: 'utf8', timeout: 10_000, maxBuffer: 256_000 });

function frozenHistory(f: ReturnType<typeof fixture>, options: { id?: string; history?: unknown } = {}) {
  f.state.taskDigest = mathDigest('unchanged-task');
  f.state.problem.receiptDigest = mathDigest('unchanged-problem');
  const sourceFile = path.join(f.root, 'old-run', 'result.json.runtime', 'state.json');
  fs.mkdirSync(path.dirname(sourceFile), { recursive: true });
  fs.writeFileSync(sourceFile, 'This live source must never be read by inspection.');
  const source = { runId: 'previous-run', stateFile: sourceFile, stateDigest: mathDigest('saved-old-state'),
    buildDigest: mathDigest('previous-build'), methodDigest: mathDigest('previous-method'),
    canonicalCommit: 'c'.repeat(40), planVersion: 'previous-plan' };
  const history = options.history ?? { source, capturedAt: 1234,
    capture: 'canonical-commit-and-individually-stable-advisory-worker-files',
    history: { tasks: [{ taskId: 'goal', status: 'integrated', attempts: 9 }] } };
  const text = canonicalMathJson(history), sha256 = mathDigest(text);
  const manifest: ContinuationManifest = { schema: 'theorem-os.continuation-snapshot.v1',
    taskDigest: f.state.taskDigest, problemReceiptDigest: f.state.problem.receiptDigest,
    attachments: [{ id: options.id ?? 'seed-history', kind: 'diagnostics', path: 'history.json',
      bytes: Buffer.byteLength(text), sha256, contentPath: `continuation/${sha256}.txt`,
      provenance: { evidence: 'recorded-not-replayed', runId: source.runId, source: sourceFile } }] };
  const snapshot = freezeContinuationInput({ manifest, digest: mathDigest(canonicalMathJson(manifest)),
    contents: new Map([[sha256, text]]) }, path.dirname(f.stateFile));
  f.state.continuationDigest = snapshot.digest;
  writeSolverRunState(f.stateFile, f.state);
  return { snapshot, source, blob: path.join(path.dirname(snapshot.file), manifest.attachments[0].contentPath) };
}

afterEach(() => { for (const root of roots.splice(0)) fs.rmSync(root, { recursive: true, force: true }); });

describe('stored run inspection artifacts', () => {
  it('reads the default report without inventing a journal or changing checkpoint/result bytes', async () => {
    const f = fixture(), stateBefore = fs.readFileSync(f.stateFile), resultBefore = fs.readFileSync(f.run);
    // A plausible filename is deliberately ignored unless it is explicitly supplied.
    fs.writeFileSync(path.join(path.dirname(f.stateFile), 'events.jsonl'), '{"event":"ready","runId":"other"}\n');
    const report = await inspectStoredRun(f.run);
    expect(report.runId).toBe(f.state.runId);
    expect(report.evidence).toBe('recorded-not-replayed');
    expect(report.artifacts).toMatchObject({ stateFile: f.stateFile, resultFile: f.run,
      journal: { source: 'none', status: 'absent', runBinding: 'unknown', coverage: 'unknown', bytesRead: 0 },
      continuation: { status: 'absent' } });
    expect(report.progress.checkedProofTasks).toBe(0);
    expect(fs.readFileSync(f.stateFile)).toEqual(stateBefore);
    expect(fs.readFileSync(f.run)).toEqual(resultBefore);
  });

  it('keeps result/state validation and a missing result follows existing checkpoint semantics', async () => {
    const f = fixture();
    fs.writeFileSync(f.run, JSON.stringify({ ...f.result, runId: 'other-run' }));
    await expect(inspectStoredRun(f.run)).rejects.toThrow('math_inspect_result_identity_mismatch');
    expect((await inspectStoredRun(f.stateFile)).snapshot.resultDigest).toBeNull();
    fs.unlinkSync(f.run);
    expect((await inspectStoredRun(f.run)).runId).toBe(f.state.runId);
    fs.writeFileSync(f.stateFile, '{}');
    await expect(inspectStoredRun(f.run)).rejects.toThrow('math_resume_state_invalid');
  });

  it('binds complete event lines while preserving mixed output and an incomplete tail as partial evidence', async () => {
    const f = fixture();
    const bytes = Buffer.from('host diagnostic\n' + JSON.stringify({ event: 'ready', runId: f.state.runId, at: 1 }) + '\n' +
      '{"event":"task_assigned","taskId":"goal","at":2}\n' + '{"event":"task_integrated","at":');
    fs.writeFileSync(f.log, bytes);
    const report = await inspectStoredRun(f.run, { journal: { logFile: f.log } });
    expect(report.artifacts.journal).toMatchObject({ source: 'log', status: 'read', file: f.log,
      runBinding: 'matched', coverage: 'partial', bytesRead: bytes.length, digest: mathDigest(bytes), ignoredLines: 1,
      truncated: false, incompleteTailBytes: Buffer.byteLength('{"event":"task_integrated","at":') });
    expect(report.artifacts.journal.diagnostics).toContain('math_inspect_log_incomplete_tail');
    expect(report.progress.checkedProofTasks).toBe(0);
  });

  it.each(['no-run-id', 'foreign-run', 'mixed-runs'] as const)('does not infer current-run binding from %s', async mode => {
    const f = fixture();
    f.writeLog({ event: 'task_assigned', taskId: 'goal', workerId: 'engineer', at: 2 },
      ...(mode === 'no-run-id' ? [] : [{ event: 'ready', runId: 'foreign-run', at: 1 }]),
      ...(mode === 'mixed-runs' ? [{ event: 'ready', runId: f.state.runId, at: 3 }] : []));
    const report = await inspectStoredRun(f.run, { journal: { logFile: f.log } });
    expect(report.artifacts.journal).toMatchObject({ status: 'read', coverage: 'unknown',
      runBinding: mode === 'no-run-id' ? 'unknown' : 'mismatched' });
    expect(report.progress.checkedProofTasks).toBe(0);
  });

  it.each(['result', 'state'] as const)('selects a batch log by its exact output mapping for %s input', async input => {
    const f = fixture(), otherLog = path.join(f.root, 'other.log');
    f.writeLog({ event: 'ready', runId: f.state.runId, at: 1 });
    fs.writeFileSync(otherLog, '{"event":"ready","runId":"other"}\n');
    f.writeBatch([{ output: path.join(f.root, 'other-result.json'), log: otherLog }, { output: f.run, log: f.log }]);
    const report = await inspectStoredRun(input === 'state' ? f.stateFile : f.run, { journal: { batchFile: f.batchFile } });
    expect(report.artifacts.journal).toMatchObject({ source: 'batch', status: 'read', batchFile: f.batchFile,
      file: f.log, outputFile: f.run, runBinding: 'matched', coverage: 'unknown' });
    if (input === 'state') expect(report.snapshot.resultDigest).toBeNull();
  });

  it.each(['missing', 'duplicate', 'anonymous-log'] as const)('does not guess batch identity for %s', async mode => {
    const f = fixture();
    f.writeLog({ event: 'task_assigned', taskId: 'goal', at: 1 });
    f.writeBatch(mode === 'missing' ? [{ output: path.join(f.root, 'unrelated.json'), log: f.log }]
      : Array.from({ length: mode === 'duplicate' ? 2 : 1 }, () => ({ output: f.run, log: f.log })));
    const report = await inspectStoredRun(f.run, { journal: { batchFile: f.batchFile } });
    expect(report.artifacts.journal).toMatchObject({ source: 'batch', runBinding: 'unknown',
      status: mode === 'missing' ? 'unmapped' : mode === 'duplicate' ? 'ambiguous' : 'read' });
  });

  it('does not derive an output from a state outside the documented runtime layout', async () => {
    const f = fixture(), stateFile = path.join(f.root, 'state.json');
    fs.copyFileSync(f.stateFile, stateFile);
    f.writeBatch([{ output: f.run, log: f.log }]);
    const report = await inspectStoredRun(stateFile, { journal: { batchFile: f.batchFile } });
    expect(report.artifacts.journal).toMatchObject({ status: 'unmapped', runBinding: 'unknown' });
    expect(report.artifacts.journal.diagnostics).toContain('math_inspect_batch_output_unknown');
  });

  it.each(['missing-log', 'missing-batch', 'malformed-batch', 'invalid-jobs'] as const)
  ('reports optional artifact failure %s without losing the saved report', async mode => {
    const f = fixture();
    if (mode === 'malformed-batch') fs.writeFileSync(f.batchFile, '{');
    if (mode === 'invalid-jobs') fs.writeFileSync(f.batchFile, JSON.stringify({ jobs: {} }));
    const report = await inspectStoredRun(f.run, { journal: mode === 'missing-log'
      ? { logFile: f.log } : { batchFile: f.batchFile } });
    expect(report.runId).toBe(f.state.runId);
    expect(report.artifacts.journal).toMatchObject({ status: mode.startsWith('missing') ? 'unreadable' : 'invalid',
      runBinding: 'unknown', bytesRead: 0 });
    expect(report.artifacts.journal.diagnostics.length).toBeGreaterThan(0);
  });

  it('bounds a large journal to the captured prefix and reports discarded tail coverage', async () => {
    const f = fixture();
    f.writeLog({ event: 'ready', runId: f.state.runId, at: 1 });
    fs.truncateSync(f.log, 16 * 1024 * 1024 + 100);
    const report = await inspectStoredRun(f.run, { journal: { logFile: f.log } });
    expect(report.artifacts.journal).toMatchObject({ status: 'read', runBinding: 'matched', coverage: 'partial',
      bytesRead: 16 * 1024 * 1024, truncated: true });
    expect(report.artifacts.journal.diagnostics).toContain('math_inspect_log_prefix_limit');
  });
});

describe('stored continuation provenance', () => {
  it('reports only the frozen seed source and leaves current-run task history unchanged', async () => {
    const f = fixture(), frozen = frozenHistory(f), before = fs.readFileSync(f.stateFile);
    const report = await inspectStoredRun(f.run);
    expect(report.artifacts.continuation).toMatchObject({ status: 'recorded', evidence: 'recorded-not-replayed',
      file: frozen.snapshot.file, snapshotDigest: frozen.snapshot.digest, source: frozen.source, capturedAt: 1234,
      capture: 'canonical-commit-and-individually-stable-advisory-worker-files',
      attachment: { id: 'seed-history', sha256: mathDigest(fs.readFileSync(frozen.blob)) } });
    expect(report.tasks).toHaveLength(1);
    expect(report.tasks[0]).toMatchObject({ id: 'goal', status: 'pending', attempts: 0 });
    expect(report.progress.checkedProofTasks).toBe(0);
    expect(report.contributionFlow.continuation).toMatchObject({ executionHistory: 'not-inferred' });
    expect(fs.readFileSync(f.stateFile)).toEqual(before);
  });

  it('reads frozen provenance even after the source run path has disappeared', async () => {
    const f = fixture(), frozen = frozenHistory(f);
    fs.rmSync(path.join(f.root, 'old-run'), { recursive: true });
    expect(fs.existsSync(frozen.source.stateFile)).toBe(false);
    const report = await inspectStoredRun(f.stateFile);
    expect(report.artifacts.continuation).toMatchObject({ status: 'recorded', source: frozen.source });
  });

  it.each(['manifest', 'blob'] as const)('reports corrupt frozen %s as unknown', async target => {
    const f = fixture(), frozen = frozenHistory(f);
    const file = target === 'manifest' ? frozen.snapshot.file : frozen.blob;
    const bytes = fs.readFileSync(file);
    bytes[0] = bytes[0] === 120 ? 121 : 120;
    fs.unlinkSync(file); fs.writeFileSync(file, bytes, { mode: 0o400 });
    const report = await inspectStoredRun(f.run);
    expect(report.artifacts.continuation).toMatchObject({ status: 'unknown', snapshotDigest: frozen.snapshot.digest,
      reason: target === 'manifest' ? 'math_continuation_identity_changed' : 'math_continuation_content_changed' });
    expect(report.runId).toBe(f.state.runId);
  });

  it.each(['task', 'problem'] as const)('rejects provenance bound to a different %s identity', async target => {
    const f = fixture(); frozenHistory(f);
    if (target === 'task') f.state.taskDigest = mathDigest('different-task');
    else f.state.problem.receiptDigest = mathDigest('different-problem');
    writeSolverRunState(f.stateFile, f.state);
    const report = await inspectStoredRun(f.run);
    expect(report.artifacts.continuation).toMatchObject({ status: 'unknown', reason: 'math_continuation_identity_changed' });
  });

  it.each(['non-seed', 'missing-source', 'missing-snapshot'] as const)
  ('keeps %s continuation provenance unknown', async mode => {
    const f = fixture();
    const frozen = frozenHistory(f, mode === 'non-seed' ? { id: 'ordinary-notes' }
      : mode === 'missing-source' ? { history: { capturedAt: 1234, capture: 'saved-notes' } } : {});
    if (mode === 'missing-snapshot') fs.unlinkSync(frozen.snapshot.file);
    const report = await inspectStoredRun(f.run);
    expect(report.artifacts.continuation).toMatchObject({ status: 'unknown', snapshotDigest: frozen.snapshot.digest });
    if (report.artifacts.continuation.status === 'unknown') expect(report.artifacts.continuation.reason).toBeTruthy();
  });
});

describe('stored inspection CLI', () => {
  it('emits JSON with explicit journal provenance through the ordinary inspect command', () => {
    const f = fixture();
    f.writeLog({ event: 'ready', runId: f.state.runId, at: 1 });
    f.writeBatch([{ output: f.run, log: f.log }]);
    const result = invoke(['--run', f.run, '--format', 'json', '--batch', f.batchFile]);
    expect(result.status, result.stderr).toBe(0);
    const report = JSON.parse(result.stdout);
    expect(report.artifacts.journal).toMatchObject({ source: 'batch', status: 'read', runBinding: 'matched' });
    expect(report.contributionFlow).toBeDefined();
  });

  it('rejects competing journal inputs while plan exports skip journal reads', () => {
    const f = fixture();
    const conflict = invoke(['--run', f.run, '--batch', f.batchFile, '--log', f.log]);
    expect(conflict.status).toBe(1);
    expect(conflict.stderr).toContain('--batch and --log are mutually exclusive');
    const plan = invoke(['--run', f.run, '--format', 'plan', '--batch', f.batchFile]);
    expect(plan.status, plan.stderr).toBe(0);
    expect(JSON.parse(plan.stdout)).toMatchObject({ baseVersion: 'version-1' });
    expect(fs.existsSync(f.batchFile)).toBe(false);
    expect(fs.existsSync(f.log)).toBe(false);
  });
});
