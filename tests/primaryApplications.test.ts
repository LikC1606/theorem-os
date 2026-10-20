import { expect, it } from 'vitest';
import { primaryApplicationConsumer, primaryHelpApplications, taskConsumerInterfaces } from '../src/solver/taskConsumers';
import { originalGoalTaskFocus, readyResearchTasks } from '../src/solver/modules/search';
import { buildProofContinuation } from '../src/solver/progress';
import { taskVersion, type TaskRecord } from '../src/solver/tasks';

function fixture() {
  const root: TaskRecord = { task: { id: 'original', kind: 'goal', objective: 'Original', revision: 0,
    dependsOn: [], status: 'paused', theoremName: 'Original.target', proofPath: 'Submission.lean' },
    primaryOwned: true, status: 'pending', attempts: 0 };
  const helper: TaskRecord = { task: { id: 'helper', kind: 'lemma', objective: 'Estimate', revision: 0,
    dependsOn: [], type: 'True', theoremName: 'Saved.helper', proofPath: 'Submission.lean' }, status: 'pending', attempts: 0 };
  helper.application = primaryHelpApplications([{ id: 'helper' }], [root, helper])[0]!.application;
  return { root, helper, tasks: [root, helper] };
}

it('keeps primary application purpose visible without creating a dependency or dispatching the original', () => {
  const { root, helper, tasks } = fixture();
  const focus = originalGoalTaskFocus(tasks);
  expect([...focus.frontier]).toEqual(['original']);
  expect(focus.support.has('helper')).toBe(true);
  expect(focus.proofPath.has('helper')).toBe(false);
  expect(readyResearchTasks(tasks).map(node => node.task.id)).toEqual(['helper']);
  expect(taskConsumerInterfaces(helper.task, tasks)[0]).toMatchObject({ taskDigest: taskVersion(root.task),
    uses: [{ kind: 'primary-application' }] });
  const report = buildProofContinuation(tasks);
  expect(report.goals[0]).toMatchObject({ executionOwner: 'primary', checkedDependencies: [],
    advisoryApplications: [{ taskId: 'helper', consumerTaskId: 'original' }] });
  expect(report.unconnectedTasks).toEqual([]);
  expect(root.task.dependsOn).toEqual([]);
  expect(report.continuationCandidates).toEqual([]);
});

it('requires explicit selection for multiple originals and never associates a helper with both', () => {
  const { root, helper, tasks } = fixture();
  const other: TaskRecord = { ...root, task: { ...root.task, id: 'other', theoremName: 'Original.other' } };
  tasks.push(other);
  expect(primaryHelpApplications([{ id: 'helper' }], tasks)).toEqual([]);
  expect(() => primaryHelpApplications([{ id: 'helper', consumer: { theoremName: 'Unknown.target' } }], tasks))
    .toThrow('math_help_select_original_consumer');
  helper.application = primaryHelpApplications([{ id: 'helper', consumer: { theoremName: 'Original.other',
    residualGoal: 'n > 0' } }], tasks)[0]!.application;
  expect(taskConsumerInterfaces(helper.task, tasks).map(row => row.task.id)).toEqual(['other']);
  expect(primaryApplicationConsumer(helper, tasks)).toBe(other);
});

it.each(['helper-revision', 'consumer-revision', 'explicit-pause', 'stop', 'private-group'])(
  'expires advisory use on %s and leaves the execution graph untouched', change => {
    const { root, helper, tasks } = fixture();
    if (change === 'helper-revision') helper.task = { ...helper.task, revision: 1 };
    if (change === 'consumer-revision') root.task = { ...root.task, revision: 1 };
    if (change === 'explicit-pause') root.primaryOwned = false;
    if (change === 'stop') root.task = { ...root.task, status: 'stopped' };
    if (change === 'private-group') root.task = { ...root.task, groupId: 'private', sharing: 'group' };
    expect(taskConsumerInterfaces(helper.task, tasks)).toEqual([]);
    expect(buildProofContinuation(tasks).primaryApplications).toEqual([]);
    expect(originalGoalTaskFocus(tasks).support.has('helper')).toBe(false);
  });

it('rejects an explicit private target before recording any application', () => {
  const { root, helper } = fixture();
  root.task = { ...root.task, groupId: 'private', sharing: 'group' };
  expect(() => primaryHelpApplications([{ id: 'helper' }], [root, helper])).toThrow('math_help_consumer_not_shared');
});
