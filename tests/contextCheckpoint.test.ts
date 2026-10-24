import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { mathDigest } from '../src/math/mathRuntimeIo';
import { readSolverRunState, writeSolverRunState, type SolverRunState } from '../src/solver/archive';
import { CooperativeResearch } from '../src/solver/cooperation';
import { acceptContextCheckpoint, readCheckpointNotesDigest, savedContextCheckpoint } from '../src/solver/contextCheckpoint';
import { MAX_RESEARCH_NOTES_BYTES } from '../src/solver/deliveries';
import { git } from '../src/solver/problem';
import { assignmentDeliveryFile, taskVersion, type CooperativeAction, type CooperativeTask } from '../src/solver/tasks';
import { deferred } from './helpers/async';
import { localExample, solverState } from './helpers/solver';

type Research = Pick<SolverRunState, 'threadId' | 'contextCheckpoint'>;
let directory: string, notes: string, research: Research;
const text = 'The exact current argument and unresolved inference remain saved.\n';
const digest = mathDigest(text);
const event = { kind: 'checkpoint', requestId: 'current-request', notesDigest: digest };

beforeEach(() => {
  directory = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'context-checkpoint-')));
  notes = path.join(directory, 'RESEARCH.md');
  fs.writeFileSync(notes, text);
  research = { threadId: 'current-thread', contextCheckpoint: {
    threadId: 'current-thread', requestedAt: 1, requestId: event.requestId, notesDigest: digest,
  } };
});
afterEach(() => { vi.restoreAllMocks(); fs.rmSync(directory, { recursive: true, force: true }); });

describe('explicit context checkpoint publication', () => {
  it('waits for publication even after notes change, then accepts unchanged accurate notes for the current request', () => {
    expect(readCheckpointNotesDigest(directory)).toBe(digest);
    expect(savedContextCheckpoint(research, directory)).toBeUndefined();
    fs.appendFileSync(notes, 'A newer argument alone does not hand back writing.\n');
    expect(savedContextCheckpoint(research, directory)).toBeUndefined();
    fs.writeFileSync(notes, text);
    acceptContextCheckpoint(research, directory, event);
    expect(savedContextCheckpoint(research, directory)).toBe(digest);
    expect(research.contextCheckpoint).toMatchObject({ publishedNotesDigest: digest, publishedAt: expect.any(Number) });
    fs.appendFileSync(notes, 'Further edits invalidate the saved publication.\n');
    expect(savedContextCheckpoint(research, directory)).toBeUndefined();
  });

  it.each([null, [], {}, { ...event, kind: 'research' }, { ...event, requestId: 'old-request' },
    { ...event, notesDigest: 'not-a-digest' }, { ...event, notesDigest: '0'.repeat(64) }])(
    'rejects an invalid or stale publication without acknowledging it: %j', value => {
      const previous = structuredClone(research);
      expect(() => acceptContextCheckpoint(research, directory, value)).toThrow('math_delivery_invalid');
      expect(research).toEqual(previous);
    });

  it.each(['missing-request', 'legacy-request', 'previous-thread'] as const)('does not acknowledge %s', state => {
    if (state === 'missing-request') research.contextCheckpoint = undefined;
    if (state === 'legacy-request') delete research.contextCheckpoint!.requestId;
    if (state === 'previous-thread') research.threadId = 'new-thread';
    expect(() => acceptContextCheckpoint(research, directory, event)).toThrow('math_delivery_invalid');
    expect(savedContextCheckpoint(research, directory)).toBeUndefined();
  });

  it('reads only ordinary nonempty notes within the existing size and link boundaries', () => {
    fs.unlinkSync(notes);
    expect(readCheckpointNotesDigest(directory)).toBeUndefined();
    fs.writeFileSync(notes, ' \n');
    expect(readCheckpointNotesDigest(directory)).toBeUndefined();
    fs.writeFileSync(notes, Buffer.alloc(MAX_RESEARCH_NOTES_BYTES + 1, 65));
    expect(readCheckpointNotesDigest(directory)).toBeUndefined();
    const target = path.join(directory, 'saved.md');
    fs.renameSync(notes, target);
    fs.writeFileSync(target, text);
    fs.symlinkSync(target, notes);
    expect(readCheckpointNotesDigest(directory)).toBeUndefined();
    fs.unlinkSync(notes);
    fs.linkSync(target, notes);
    expect(readCheckpointNotesDigest(directory)).toBeUndefined();
  });

  it('retains new publication fields and legacy checkpoint requests through state recovery', () => {
    const example = localExample('context-checkpoint-state-');
    try {
      acceptContextCheckpoint(research, directory, event);
      const state = solverState(example.problem, example.workspace, { runId: 'checkpoint-state', phase: 'running',
        ...research, workers: [{ id: 'peer', role: 'prover', worktree: directory, phase: 'running', turns: 1, ...research }] });
      const file = path.join(directory, 'state.json');
      writeSolverRunState(file, state);
      const restored = readSolverRunState(file);
      expect(restored.contextCheckpoint).toEqual(research.contextCheckpoint);
      expect(restored.workers![0].contextCheckpoint).toEqual(research.contextCheckpoint);
      state.contextCheckpoint = { threadId: 'legacy-thread', requestedAt: 1, notesDigest: digest };
      writeSolverRunState(file, state);
      expect(readSolverRunState(file).contextCheckpoint).toEqual(state.contextCheckpoint);
    } finally { fs.rmSync(example.directory, { recursive: true, force: true }); }
  });
});

describe('task checkpoint event intake', () => {
  const reader = (commit = 'a'.repeat(40)) => {
    const task: CooperativeTask = { id: 'a', kind: 'lemma', objective: 'Prove a.', dependsOn: [], revision: 0,
      theoremName: 'a', proofPath: 'Submission.lean', type: 'True' };
    const action: Extract<CooperativeAction, { kind: 'task' }> = { kind: 'task', task, assignment: {
      taskId: task.id, taskDigest: taskVersion(task), workerId: 'peer', seedCommit: commit, assignmentId: 'dispatch',
    } };
    const worker = { id: 'peer', role: 'prover' as const, worktree: directory, ownedFiles: [] };
    const session = { id: worker.id, ...research };
    const main = { threadId: 'other-thread', workers: [session], problem: { baseCommit: commit }, environmentDigest: 'environment' };
    const sequence: string[] = [], save = vi.fn();
    const cooperative = Object.create(CooperativeResearch.prototype);
    Object.assign(cooperative, {
      archive: { tasks: [{ task, status: 'running', attempts: 1, assignment: action.assignment }], deliveries: [] },
      input: { state: main, signal: new AbortController().signal, save,
        emit: (name: string) => { sequence.push(name); } },
      current: () => true, record: vi.fn(),
    });
    return { cooperative, action, worker, session, main, sequence, save };
  };

  it('publishes the checkpoint only after the preceding research event finishes intake', async () => {
    git(directory, ['init', '--quiet']);
    git(directory, ['-c', 'user.name=Fixture', '-c', 'user.email=fixture@localhost', 'commit', '--quiet', '--allow-empty', '-m', 'Fixture']);
    const commit = git(directory, ['rev-parse', 'HEAD']);
    const { cooperative, action, worker, session, main, sequence, save } = reader(commit);
    const entered = deferred(), release = deferred();
    cooperative.publishResearchFinding = vi.fn(async () => {
      entered.resolve(); await release.promise; sequence.push('research-recorded');
    });
    const file = path.join(directory, assignmentDeliveryFile(action.assignment));
    fs.writeFileSync(file, JSON.stringify({ kind: 'research', finding: { summary: 'The exact unresolved gap.' } }) + '\n' +
      JSON.stringify(event) + '\n');
    const cursors = {};
    const pending = cooperative.readWorkerDeliveries(worker, action, cursors);
    await entered.promise;
    expect(savedContextCheckpoint(session, directory)).toBeUndefined();
    expect(sequence).toEqual([]);
    release.resolve(); await pending;
    expect(sequence).toEqual(['research-recorded', 'context_checkpoint_published']);
    expect(savedContextCheckpoint(session, directory)).toBe(digest);
    expect(main).not.toHaveProperty('contextCheckpoint');
    expect(cooperative.record).not.toHaveBeenCalled();
    expect(cooperative.archive.deliveries).toEqual([]);
    expect(cooperative.archive.tasks[0].status).toBe('running');
    expect(cursors).toHaveProperty(`peer/${assignmentDeliveryFile(action.assignment)}`, fs.statSync(file).size);
    expect(save).toHaveBeenCalled();
  });

  it.each(['legacy-log', 'wrong-task', 'wrong-digest', 'superseded', 'wrong-worker'] as const)(
    'rejects checkpoint intake from %s', async scope => {
      const { cooperative, action, worker, session } = reader();
      const value = { ...event, id: 'checkpoint', taskId: action.task.id, taskDigest: action.assignment.taskDigest };
      if (scope === 'wrong-task') value.taskId = 'other';
      if (scope === 'wrong-digest') value.taskDigest = 'other';
      if (scope === 'superseded') cooperative.current = () => false;
      if (scope === 'wrong-worker') action.assignment.workerId = 'other';
      await expect(cooperative.receive(worker, action, value, scope !== 'legacy-log')).rejects.toThrow('math_delivery_invalid');
      expect(savedContextCheckpoint(session, directory)).toBeUndefined();
      expect(cooperative.record).not.toHaveBeenCalled();
    });
});
