import { describe, expect, it } from 'vitest';
import { assignResearchTask, assignSharedResearchTask, independentFeasibilityWorker,
  type ResearchWorker } from '../src/solver/modules/organization';
import { continuationResearchTasks, criticalPathResearchTasks, goalsFirstResearchTasks,
  readyResearchTasks, taskCanStart } from '../src/solver/modules/search';
import { isFeasibilityReview, taskVersion, type RouteRecord, type TaskRecord } from '../src/solver/tasks';

const node = (id: string, kind: TaskRecord['task']['kind'] = 'lemma', dependsOn: string[] = []): TaskRecord => ({
  task: { id, kind, objective: `Investigate or prove ${id}.`, dependsOn, revision: 0,
    ...(['lemma', 'goal'].includes(kind) ? { proofPath: 'Submission.lean', theoremName: `Original.${id}` } : {}),
    ...(kind === 'lemma' ? { type: 'forall (n : Nat), n = n' } : {}) },
  status: 'pending', attempts: 0,
});
const feasibility = (id: string, dependsOn: string[]) => {
  const review = node(id, 'research', dependsOn);
  review.task = { ...review.task, reviewScope: 'feasibility' };
  return review;
};
const conditional = (id: string, kind: 'goal' | 'lemma', dependsOn: string[]) => {
  const consumer = node(id, kind, dependsOn);
  consumer.task = { ...consumer.task, conditional: true };
  return consumer;
};
const group = (id = 'main'): RouteRecord => ({
  group: { id, objective: `Investigate ${id}.`, status: 'active', revision: 0 }, turns: 0,
});
const worker = (id: string, role: ResearchWorker['role'] = 'researcher'): ResearchWorker => ({
  id, role, worktree: `/fixture/${id}`, ownedFiles: ['Submission.lean'],
});
const assignTo = (record: TaskRecord, workerId: string) => {
  record.assignment = { taskId: record.task.id, taskDigest: taskVersion(record.task), workerId, seedCommit: 'fixture-seed' };
};
const schedulers = [
  ['plan', readyResearchTasks], ['goals-first', goalsFirstResearchTasks],
  ['critical-path', criticalPathResearchTasks], ['continuation', continuationResearchTasks],
] as const;
const assignments = [['role-based', assignResearchTask], ['shared', assignSharedResearchTask]] as const;

it('recognizes only advisory feasibility tasks and preserves the reserved final-candidate review identity', () => {
  for (const kind of ['research', 'sketch'] as const) {
    const review = node('route_check', kind);
    review.task = { ...review.task, reviewScope: 'feasibility' };
    expect(isFeasibilityReview(review.task)).toBe(true);
    expect(isFeasibilityReview({ ...review.task, reviewScope: 'final-candidate' })).toBe(false);
    expect(isFeasibilityReview({ ...review.task, id: 'independent_candidate_review' })).toBe(false);
  }
  expect(isFeasibilityReview({ ...node('proof').task, reviewScope: 'feasibility' })).toBe(false);
  expect(isFeasibilityReview(node('ordinary_investigation', 'research').task)).toBe(false);
});

describe.each(schedulers)('%s early route selection', (_name, schedule) => {
  it.each(['feasibility', 'conditional'] as const)('preserves a first %s check when only one proof slot remains', kind => {
    const busy = worker('busy'), available = worker('available'), running = node('running');
    running.status = 'running'; assignTo(running, busy.id);
    const premise = node('premise'), bridge = conditional('bridge', 'lemma', ['premise']);
    const original = node('original', 'goal', ['running', 'bridge']);
    const check = kind === 'feasibility' ? feasibility('route_check', ['original']) : bridge;
    const tasks = [running, premise, bridge, original, ...(check === bridge ? [] : [check]), node('independent', 'research')];
    const ready = schedule(tasks), before = structuredClone(tasks);
    expect(ready[0]).toBe(check);
    expect(assignSharedResearchTask(ready, available, [busy, available], undefined, tasks)).toBe(check);
    expect(tasks).toEqual(before);
  });

  it.each(['pending', 'blocked'] as const)('investigates a consumer before its %s premise has a proof', status => {
    const premise = node('premise'); premise.status = status;
    const consumer = node('consumer', 'goal', ['premise']);
    const review = feasibility('consumer_feasibility', ['consumer']);
    const tasks = [premise, consumer, review], before = structuredClone(tasks);
    const ready = schedule(tasks);
    expect(ready[0]).toBe(review);
    expect(ready).not.toContain(consumer);
    expect(taskCanStart(review.task, tasks)).toBe(true);
    expect(taskCanStart(consumer.task, tasks)).toBe(false);
    expect(tasks).toEqual(before);
    expect(review.integratedCheck).toBeUndefined();
    expect(consumer.integratedCheck).toBeUndefined();
  });

  it('tests an original conditional consumer once before investing in its unproved helper', () => {
    const premise = node('premise'), consumer = conditional('consumer', 'goal', ['premise']);
    const tasks = [premise, consumer];
    expect(schedule(tasks)[0]).toBe(consumer);
    expect(premise.status).toBe('pending');
    expect(consumer.proof).toBeUndefined();
    expect(consumer.integratedCheck).toBeUndefined();
  });

  it('checks an OR closing lemma conditionally without dispatching the original goal before its route is proved', () => {
    const premise = node('premise'), closing = conditional('closing', 'lemma', ['premise']);
    const original = conditional('original', 'goal', []);
    original.alternativeRoutes = [{ id: 'candidate_route', targetTaskId: 'original',
      prerequisiteTaskIds: ['premise'], closingTaskId: 'closing' }];
    const tasks = [premise, original, closing], ready = schedule(tasks);
    expect(ready[0]).toBe(closing);
    expect(ready).not.toContain(original);
    expect(taskCanStart(original.task, tasks)).toBe(false);
    expect(premise.integratedCheck).toBeUndefined();
    expect(closing.integratedCheck).toBeUndefined();
  });

  it('checks a conditional lemma before its premise when an original goal explicitly consumes it', () => {
    const premise = node('premise'), bridge = conditional('bridge', 'lemma', ['premise']);
    const original = node('original', 'goal', ['bridge']);
    const ready = schedule([premise, original, bridge]);
    expect(ready[0]).toBe(bridge);
    expect(ready).not.toContain(original);
    expect(premise.integratedCheck).toBeUndefined();
    expect(bridge.integratedCheck).toBeUndefined();
  });

  it('does not promote a conditional lemma that has no proof consumer', () => {
    const original = node('original', 'goal'), premise = node('premise');
    const unused = conditional('unused', 'lemma', ['premise']);
    const ready = schedule([original, premise, unused]);
    expect(ready[0]).toBe(original);
    expect(ready).toContain(unused);
  });

  it('offers a fresh independent feasibility check before a conditional consumer', () => {
    const premise = node('premise'), consumer = conditional('consumer', 'goal', ['premise']);
    const review = feasibility('route_check', ['consumer']);
    expect(schedule([premise, consumer, review])[0]).toBe(review);
  });

  it('does not give already attempted route checks another early priority', () => {
    const original = node('ordinary_original', 'goal'), premise = node('premise');
    const consumer = conditional('consumer', 'goal', ['premise']); consumer.attempts = 1;
    const review = feasibility('route_check', ['consumer']); review.attempts = 1;
    const ready = schedule([original, premise, consumer, review]);
    expect(ready[0]).not.toBe(consumer);
    expect(ready[0]).not.toBe(review);
    expect(ready).toContain(consumer);
    expect(ready).toContain(review);
  });

  it('promotes only one fresh feasibility check ahead of ordinary proof work', () => {
    const helper = node('ordinary_helper');
    const first = feasibility('first_check', ['ordinary_helper']);
    const second = feasibility('second_check', ['ordinary_helper']);
    expect(schedule([helper, first, second])).toEqual([first, helper, second]);
  });

  it.each(['feasibility', 'conditional'] as const)('leaves ordinary scheduling in place while a %s check is running', kind => {
    const original = node('ordinary_original', 'goal');
    const running = kind === 'feasibility' ? feasibility('running_check', ['ordinary_original']) :
      conditional('running_check', 'lemma', []);
    running.status = 'running';
    const queued = feasibility('queued_check', ['ordinary_original']);
    const ready = schedule([original, running, queued]);
    expect(ready[0]).toBe(original);
    expect(ready).toContain(queued);
    expect(ready).not.toContain(running);
  });

  it('preserves pause, stop, parking, concurrency and group budget gates for early checks', () => {
    for (const control of ['paused-task', 'stopped-task', 'parked', 'paused-group', 'spent-group', 'busy-group'] as const) {
      const ordinary = node('ordinary', 'goal'); ordinary.task = { ...ordinary.task, groupId: 'safe' };
      const premise = node('premise'); premise.status = 'blocked';
      const review = feasibility('route_check', ['premise']), main = group();
      if (control === 'paused-task') review.task = { ...review.task, status: 'paused' };
      if (control === 'stopped-task') review.task = { ...review.task, status: 'stopped' };
      if (control === 'parked') review.routeParking = ['recorded-obstruction'];
      if (control === 'paused-group') main.group = { ...main.group, status: 'paused' };
      if (control === 'spent-group') { main.group = { ...main.group, maxTurns: 1 }; main.turns = 1; }
      if (control === 'busy-group') { main.group = { ...main.group, maxConcurrent: 1 }; main.busy = 1; }
      const ready = schedule([ordinary, premise, review], [main, group('safe')]);
      expect(ready, control).toEqual([ordinary]);
    }
  });

  it('keeps both explicit and reserved final-candidate reviews behind original proof acceptance', () => {
    const premise = node('premise'); premise.status = 'blocked';
    const original = node('original', 'goal', ['premise']);
    const final = node('final_review', 'research', ['original']);
    final.task = { ...final.task, reviewScope: 'final-candidate' };
    const reserved = feasibility('independent_candidate_review', ['original']);
    const early = feasibility('early_review', ['original']);
    const tasks = [premise, original, final, reserved, early], ready = schedule(tasks);
    expect(ready).toEqual([early]);
    expect(taskCanStart(final.task, tasks)).toBe(false);
    expect(taskCanStart(reserved.task, tasks)).toBe(false);
  });
});

describe.each(assignments)('%s independent feasibility assignment', (_name, assign) => {
  it.each(['assignment', 'owner', 'engineer'] as const)('excludes an author recorded through %s even outside the ready list', origin => {
    const author = worker('author'), checker = worker('checker', 'engineer'), lead = worker('lead', 'lead');
    const source = node('source', origin === 'engineer' ? 'goal' : 'lemma'); source.status = 'running';
    const main = group();
    if (origin === 'assignment') assignTo(source, author.id);
    if (origin === 'owner') source.task = { ...source.task, ownerId: author.id };
    if (origin === 'engineer') main.group = { ...main.group, engineerId: author.id };
    const review = feasibility('route_check', ['source']), tasks = [source, review];
    expect(independentFeasibilityWorker(review, author, tasks, [main])).toBe(false);
    expect(independentFeasibilityWorker(review, checker, tasks, [main])).toBe(true);
    expect(independentFeasibilityWorker(review, lead, tasks, [main])).toBe(false);
    expect(assign([review], author, [lead, author, checker], [main], tasks)).toBeUndefined();
    expect(assign([review], checker, [lead, author, checker], [main], tasks)).toBe(review);
    expect(assign([review], lead, [lead, author, checker], [main], tasks)).toBeUndefined();
  });

  it('excludes authors of every directly reviewed input without banning unrelated proof authors', () => {
    const firstAuthor = worker('first_author'), secondAuthor = worker('second_author');
    const checker = worker('checker'), first = node('first'), second = node('second'), unrelated = node('unrelated');
    assignTo(first, firstAuthor.id); second.task = { ...second.task, ownerId: secondAuthor.id };
    assignTo(unrelated, checker.id);
    const review = feasibility('route_check', ['first', 'second']), tasks = [first, second, unrelated, review];
    const live = [firstAuthor, secondAuthor, checker];
    expect(assign([review], firstAuthor, live, undefined, tasks)).toBeUndefined();
    expect(assign([review], secondAuthor, live, undefined, tasks)).toBeUndefined();
    expect(assign([review], checker, live, undefined, tasks)).toBe(review);
  });

  it.each(['owner', 'assignment'] as const)('preserves the feasibility task\'s own %s pin while enforcing independence', pin => {
    const author = worker('author'), checker = worker('checker'), other = worker('other');
    const source = node('source'); assignTo(source, author.id);
    const review = feasibility('route_check', ['source']);
    if (pin === 'owner') review.task = { ...review.task, ownerId: checker.id };
    else assignTo(review, checker.id);
    const tasks = [source, review], live = [author, checker, other];
    expect(assign([review], author, live, undefined, tasks)).toBeUndefined();
    expect(assign([review], other, live, undefined, tasks)).toBeUndefined();
    expect(assign([review], checker, live, undefined, tasks)).toBe(review);
    if (pin === 'owner') review.task = { ...review.task, ownerId: author.id };
    else assignTo(review, author.id);
    expect(assign([review], author, live, undefined, tasks)).toBeUndefined();
    expect(assign([review], checker, live, undefined, tasks)).toBeUndefined();
  });

  it('leaves an unassignable review pending while its only author continues ordinary proof work', () => {
    const author = worker('author'), lead = worker('lead', 'lead'), source = node('source');
    assignTo(source, author.id);
    const review = feasibility('route_check', ['source']), proof = node('ordinary_proof');
    const tasks = [source, review, proof], live = [lead, author];
    expect(assign([review], author, live, undefined, tasks)).toBeUndefined();
    expect(assign([review], lead, live, undefined, tasks)).toBeUndefined();
    expect(assign([review, proof], author, live, undefined, tasks)).toBe(proof);
    expect(review.status).toBe('pending');
    expect(review.assignment).toBeUndefined();
  });

  it('keeps the optional full-graph argument backward compatible for ordinary task assignment', () => {
    const researcher = worker('researcher'), proof = node('proof');
    expect(assign([proof], researcher, [researcher])).toBe(proof);
  });
});
