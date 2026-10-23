import { omitTaskHelpers } from './cooperativeProof';
import { plannedTaskDependencyIds } from './modules/search';
import type { SolverProblem } from './problem';
import type { ResearchTaskView } from './researchRecords';
import { taskGroup, taskReferenceDependencies, type CooperativeTask, type TaskRecord } from './tasks';

/** Source visibility metadata is advisory; it cannot restore a checked proof. */
export type ResearchSourceTask = ResearchTaskView & {
  visibleDependencies: readonly string[];
  sourceDependencies: readonly string[];
  sourceHelpers: readonly string[];
};

export function researchSourceTasks(tasks: readonly TaskRecord[]): ResearchSourceTask[] {
  const nodes = new Map(tasks.map(node => [node.task.id, node]));
  const dependencies = (node: TaskRecord): string[] => {
    const found = new Set<string>();
    const visit = (id: string) => {
      if (found.has(id)) return;
      found.add(id);
      const input = nodes.get(id);
      if (input) (taskReferenceDependencies(input)?.map(ref => ref.taskId) ?? plannedTaskDependencyIds(input, tasks)).forEach(visit);
    };
    (taskReferenceDependencies(node)?.map(ref => ref.taskId) ?? plannedTaskDependencyIds(node, tasks)).forEach(visit);
    return [...found];
  };
  return tasks.map(node => ({ task: node.task, status: node.status, finding: node.finding,
    proof: node.proof && { passed: node.proof.passed, taskDigest: node.proof.taskDigest, conditions: node.proof.conditions },
    integratedCheck: node.integratedCheck && { passed: node.integratedCheck.passed,
      taskDigest: node.integratedCheck.taskDigest, conditions: node.integratedCheck.conditions },
    visibleDependencies: [...plannedTaskDependencyIds(node, tasks)], sourceDependencies: dependencies(node),
    sourceHelpers: [...(node.task.kind === 'lemma' ? [node.task.theoremName!] : []),
      ...(node.proof?.changes?.filter(change => !change.before).map(change => change.name) ?? [])] }));
}

/** The same projection supplies dispatch seeds and later compares their canonical source bytes. */
export function scopedResearchSources(problem: SolverProblem, task: CooperativeTask | undefined,
  sources: Readonly<Record<string, string>>, tasks: readonly ResearchSourceTask[]): Record<string, string> {
  if (!task) return { ...sources };
  const nodes = new Map(tasks.map(node => [node.task.id, node]));
  const visible = new Set(tasks.filter(node => taskGroup(node.task) === taskGroup(task) ||
    node.task.sharing !== 'group' && ['integrated', 'completed'].includes(node.status)).map(node => node.task.id));
  const seen = new Set<string>();
  const visit = (id: string) => {
    if (seen.has(id)) return;
    seen.add(id);
    for (const inputId of nodes.get(id)?.visibleDependencies ?? []) {
      const input = nodes.get(inputId);
      if (!input || taskGroup(input.task) !== taskGroup(task) && input.task.sharing === 'group') continue;
      visible.add(inputId); visit(inputId);
    }
  };
  visit(task.id);
  // A visible shared wrapper retains its private implementation prerequisites.
  for (const id of [...visible]) for (const input of nodes.get(id)?.sourceDependencies ?? []) visible.add(input);
  const hidden = tasks.filter(node => !visible.has(node.task.id)).flatMap(node => node.sourceHelpers);
  return Object.fromEntries(Object.entries(sources).map(([file, source]) => [file,
    file.endsWith('.lean') ? omitTaskHelpers(problem, file, source, hidden) : source]));
}
