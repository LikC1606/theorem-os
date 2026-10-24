import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { CooperativeResearch } from '../src/solver/cooperation';
import { MAX_DELIVERY_LINE_BYTES, readDeliveryLines, type DeliveryRecord } from '../src/solver/deliveries';
import { git } from '../src/solver/problem';
import { assignmentDeliveryFile, taskVersion, type CooperativeAction, type CooperativeTask } from '../src/solver/tasks';

describe('worker delivery log recovery', () => {
  let directory: string, commit: string, cooperative: any, controller: AbortController;
  let action: Extract<CooperativeAction, { kind: 'task' }>;
  let cursors: Record<string, number>, records: DeliveryRecord[], events: { event: string; reason?: string }[];
  let snapshots: Record<string, number>[];
  const worker = () => ({ id: 'peer', role: 'researcher' as const, worktree: directory, ownedFiles: [] });
  const log = () => assignmentDeliveryFile(action.assignment);
  const key = () => `peer/${log()}`;
  const append = (value: unknown, legacy = false) => fs.appendFileSync(path.join(directory, legacy ? 'DELIVERIES.jsonl' : log()),
    JSON.stringify(legacy && value && typeof value === 'object' ? {
      taskId: action.task.id, taskDigest: action.assignment.taskDigest, ...value,
    } : value) + '\n');
  const poll = () => cooperative.readWorkerDeliveries(worker(), action, cursors) as Promise<void>;
  const create = () => {
    const instance = Object.create(CooperativeResearch.prototype);
    const node = { task: action.task, status: 'running', attempts: 1, assignment: action.assignment };
    Object.assign(instance, {
      archive: { tasks: [node], deliveries: records },
      input: { signal: controller.signal, state: { problem: { baseCommit: commit } },
        save: () => snapshots.push({ ...cursors }),
        emit: (event: string, details: { reason?: string }) => events.push({ event, ...details }) },
      current: () => true, dependencies: () => [], reportBlockers: vi.fn(),
      record: (_worker: unknown, _task: unknown, kind: DeliveryRecord['kind'], status: DeliveryRecord['status'],
        summary: string, options: Partial<DeliveryRecord>) => records.push({ producer: 'peer', taskId: action.task.id,
          taskDigest: action.assignment.taskDigest, kind, status, summary, ...options } as DeliveryRecord),
    });
    instance.publishTaskProof = vi.fn(async (_worker: unknown, _action: unknown, _commit: string, summary: string,
      options: Partial<DeliveryRecord>) => instance.record(worker(), action.task, 'proof', 'verified', summary, options));
    return instance;
  };

  beforeEach(() => {
    directory = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'worker-delivery-recovery-')));
    git(directory, ['init', '--quiet']);
    git(directory, ['-c', 'user.name=Fixture', '-c', 'user.email=fixture@localhost', 'commit', '--quiet', '--allow-empty', '-m', 'Fixture']);
    commit = git(directory, ['rev-parse', 'HEAD']);
    const task: CooperativeTask = { id: 'a', kind: 'lemma', objective: 'Prove a.', dependsOn: [], revision: 0,
      theoremName: 'a', proofPath: 'Submission.lean', type: 'True' };
    action = { kind: 'task', task, assignment: { taskId: task.id, taskDigest: taskVersion(task), workerId: 'peer',
      seedCommit: commit, assignmentId: 'dispatch' } };
    controller = new AbortController(); cursors = {}; records = []; events = []; snapshots = [];
    cooperative = create();
  });
  afterEach(() => { vi.restoreAllMocks(); fs.rmSync(directory, { recursive: true, force: true }); });

  it.each(['storage', 'verifier'] as const)('retries a %s failure without consuming its proof or replaying the accepted prefix', async failure => {
    append({ summary: 'Useful prefix.' });
    const prefixEnd = fs.statSync(path.join(directory, log())).size;
    append({ id: 'proof', kind: 'proof', commit, summary: 'Checked proof.' });
    append({ summary: 'Useful suffix.' });
    const error = failure === 'storage' ? Object.assign(new Error('Transient storage failure'), { code: 'EIO' }) :
      new Error('math_verifier_unavailable');
    cooperative.publishTaskProof.mockRejectedValueOnce(error);
    await expect(poll()).rejects.toBe(error);
    expect(cursors[key()]).toBe(prefixEnd);
    expect(snapshots.at(-1)?.[key()]).toBe(prefixEnd);
    expect(records.map(record => record.summary)).toEqual(['Useful prefix.']);
    expect(events).toEqual([]);
    await poll();
    expect(records.map(record => record.summary)).toEqual(['Useful prefix.', 'Checked proof.', 'Useful suffix.']);
    expect(cooperative.publishTaskProof).toHaveBeenCalledTimes(2);
    expect(cursors[key()]).toBe(fs.statSync(path.join(directory, log())).size);
  });

  it('preserves an aborted proof for a resumed reader', async () => {
    append({ summary: 'Useful prefix.' });
    const prefixEnd = fs.statSync(path.join(directory, log())).size;
    append({ kind: 'proof', commit, summary: 'Resume this proof.' });
    cooperative.publishTaskProof.mockImplementationOnce(async () => {
      controller.abort(); controller.signal.throwIfAborted();
    });
    await expect(poll()).rejects.toMatchObject({ name: 'AbortError' });
    expect(cursors[key()]).toBe(prefixEnd);
    expect(snapshots.at(-1)?.[key()]).toBe(prefixEnd);
    expect(events).toEqual([]);
    controller = new AbortController(); cooperative = create();
    await poll();
    expect(records.map(record => record.summary)).toEqual(['Useful prefix.', 'Resume this proof.']);
  });

  it('does not consume any line when the run was already stopped', async () => {
    append({ kind: 'proof', commit }); controller.abort();
    await expect(poll()).rejects.toMatchObject({ name: 'AbortError' });
    expect(cursors[key()] ?? 0).toBe(0);
    expect(cooperative.publishTaskProof).not.toHaveBeenCalled();
    expect(events).toEqual([]);
  });

  it('rejects malformed JSON, schema and nonexistent commits once, then accepts later lines', async () => {
    fs.appendFileSync(path.join(directory, log()), '{broken\n');
    append({ summary: 123 });
    append({ kind: 'proof', commit: 'not a commit' });
    append({ kind: 'proof', commit: '0'.repeat(40) });
    append({ summary: 'Still useful.' });
    await poll(); await poll();
    expect(events.map(event => event.reason)).toEqual(['math_delivery_invalid_json', 'math_delivery_invalid',
      'math_delivery_requires_fixed_proof', 'math_delivery_invalid_commit']);
    expect(records.map(record => record.summary)).toEqual(['Still useful.']);
    expect(cooperative.publishTaskProof).not.toHaveBeenCalled();
  });

  it('saves actionable rejection receipts with the cursor and retries notification after restore', async () => {
    fs.appendFileSync(path.join(directory, log()), '{broken\n');
    const notify = vi.fn().mockRejectedValueOnce(new Error('transport unavailable'));
    cooperative.active = new Map([['peer', { action, notify }]]);
    await poll();
    const receipt = cooperative.archive.deliveryReceipts[0];
    expect(receipt).toMatchObject({ workerId: 'peer', assignmentKey: log(), taskId: action.task.id,
      taskDigest: action.assignment.taskDigest, status: 'needs-correction', code: 'math_delivery_invalid_json',
      issues: [{ path: '$', message: 'math_delivery_invalid_json' }] });
    expect(snapshots.at(-1)?.[key()]).toBe(fs.statSync(path.join(directory, log())).size);
    const saved = JSON.parse(JSON.stringify(cooperative.archive.deliveryReceipts));
    cursors = JSON.parse(JSON.stringify(cursors)); cooperative = create();
    cooperative.archive.deliveryReceipts = saved;
    const resumedNotify = vi.fn().mockResolvedValue(undefined);
    cooperative.active = new Map([['peer', { action, notify: resumedNotify }]]);
    await poll(); await poll();
    expect(resumedNotify).toHaveBeenCalledOnce();
    expect(resumedNotify.mock.calls[0][0]).toContain(receipt.id);
    expect(cooperative.archive.deliveryReceipts).toEqual(saved);
    expect(events.filter(event => event.event === 'delivery_rejected')).toHaveLength(1);
  });

  it('rejects a commit outside the frozen problem history once without blocking following progress', async () => {
    const tree = git(directory, ['rev-parse', `${commit}^{tree}`]);
    const unrelated = git(directory, ['-c', 'user.name=Fixture', '-c', 'user.email=fixture@localhost',
      'commit-tree', tree, '-m', 'Unrelated root']);
    append({ kind: 'proof', commit: unrelated }); append({ summary: 'Valid progress after the rejected root.' });
    await poll(); await poll();
    expect(events.map(event => event.reason)).toEqual(['math_delivery_invalid_commit']);
    expect(cooperative.publishTaskProof).not.toHaveBeenCalled();
    expect(records.map(record => record.summary)).toEqual(['Valid progress after the rejected root.']);
  });

  it.each(['math_task_existing_declaration_changed', 'math_original_context_changed', 'math_trusted_source_changed'])(
    'consumes a deterministic source rejection once: %s', async reason => {
      append({ kind: 'proof', commit }); append({ summary: 'The following progress.' });
      cooperative.publishTaskProof.mockRejectedValueOnce(new Error(reason + '\nRestore the frozen source.'));
      await poll(); await poll();
      expect(cooperative.publishTaskProof).toHaveBeenCalledOnce();
      expect(events).toEqual([{ event: 'delivery_rejected', workerId: 'peer', reason: reason + '\nRestore the frozen source.' }]);
      expect(records.map(record => record.summary)).toEqual(['The following progress.']);
    });

  it.each([null, false, 42, 'plain string', []])('rejects a scoped non-object response %j', async value => {
    append(value); append({ summary: 'Valid object.' });
    await poll(); await poll();
    expect(events.map(event => event.reason)).toEqual(['math_delivery_invalid']);
    expect(records.map(record => record.summary)).toEqual(['Valid object.']);
  });

  it('discards a complete oversized line in bounded chunks and keeps both log streams usable', async () => {
    fs.appendFileSync(path.join(directory, log()), JSON.stringify({ summary: 'x'.repeat(MAX_DELIVERY_LINE_BYTES * 2 + 100) }) + '\n');
    append({ summary: 'Scoped progress after the oversized line.' });
    append({ id: 'legacy', kind: 'progress', summary: 'Legacy progress.' }, true);
    const read = vi.spyOn(fs, 'readSync');
    await poll();
    expect(records.map(record => record.summary)).toEqual(['Legacy progress.']);
    expect(cursors[`${key()}/discardingOversized`]).toBe(1);
    expect(snapshots.at(-1)?.[`${key()}/discardingOversized`]).toBe(1);
    cursors = JSON.parse(JSON.stringify(cursors)); cooperative = create();
    await poll(); await poll(); await poll();
    expect(events.map(event => event.reason)).toEqual(['math_delivery_line_too_large']);
    expect(records.map(record => record.summary)).toEqual(['Legacy progress.', 'Scoped progress after the oversized line.']);
    expect(cursors[`${key()}/discardingOversized`]).toBe(0);
    expect(read.mock.calls.every(call => call[3] <= MAX_DELIVERY_LINE_BYTES + 1)).toBe(true);
  });

  it('remembers an oversized partial write across resume and never parses its trailing fragment', async () => {
    fs.appendFileSync(path.join(directory, log()), 'x'.repeat(MAX_DELIVERY_LINE_BYTES + 1));
    await poll(); await poll();
    expect(events.map(event => event.reason)).toEqual(['math_delivery_line_too_large']);
    cursors = JSON.parse(JSON.stringify(cursors)); cooperative = create();
    fs.appendFileSync(path.join(directory, log()), '{"summary":"Tail fragment must stay rejected."}\n');
    append({ summary: 'A complete new line.' });
    await poll();
    expect(records.map(record => record.summary)).toEqual(['A complete new line.']);
    expect(events.map(event => event.reason)).toEqual(['math_delivery_line_too_large']);
  });

  it('keeps the existing strict line reader behavior for callers without recovery state', () => {
    const file = path.join(directory, log()); fs.writeFileSync(file, 'x'.repeat(MAX_DELIVERY_LINE_BYTES + 1));
    expect(() => readDeliveryLines(file, 0)).toThrow('math_delivery_line_too_large');
  });
});
