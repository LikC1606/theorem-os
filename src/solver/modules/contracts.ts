import { isAdvisoryTask, taskVersion, type CooperativeAction, type TaskRecord } from '../tasks';

/** One work product per dispatch; worker slots and mathematical responsibilities are separate. */
export function cooperativeWorkContract(action: CooperativeAction, tasks: readonly TaskRecord[]) {
  const stage = action.kind === 'task' ? isAdvisoryTask(action.task) ? 'investigation' : 'formal-proof' :
    action.kind === 'lead' ? 'route-planning' : action.kind === 'review' ? 'candidate-review' :
      action.kind === 'solve' ? 'primary-proof' : action.kind === 'assemble' ? 'integration' : action.kind;
  const products = {
    'route-planning': { owner: 'lead', output: 'validated-task-graph-and-handoff-decisions',
      consumer: 'M3-ready-selection-and-M5-assignment', acceptance: 'host-plan-validation', sourcePolicy: 'host-checks-any-source-repair' },
    investigation: { owner: 'researcher', output: 'advisory-finding-retained-code-and-exact-lemma-proposals',
      consumer: 'lead-handoff-decision', acceptance: 'advisory-only', sourcePolicy: 'read-only' },
    'formal-proof': { owner: 'proof-worker', output: 'saved-exact-typed-declaration',
      consumer: 'M2-then-canonical-integration', acceptance: 'independent-exact-source-check', sourcePolicy: 'owned-proof-sources' },
    'primary-proof': { owner: 'primary-solver', output: 'saved-original-targets',
      consumer: 'M2-then-independent-review-and-S3', acceptance: 'S3-final-evaluation', sourcePolicy: 'owned-proof-sources' },
    integration: { owner: 'lead', output: 'saved-complete-original-proof',
      consumer: 'M2-then-independent-review-and-S3', acceptance: 'S3-final-evaluation', sourcePolicy: 'owned-proof-sources' },
    'candidate-review': { owner: 'reviewer', output: 'fixed-candidate-verdict',
      consumer: 'S3-final-evaluation', acceptance: 'advisory-review-not-kernel-acceptance', sourcePolicy: 'read-only' },
    backtranslate: { owner: 'reviewer', output: 'blind-fixed-statement-translation',
      consumer: 'statement-review', acceptance: 'advisory-only', sourcePolicy: 'read-only' },
    'statement-review': { owner: 'reviewer', output: 'fixed-statement-comparison',
      consumer: 'lead', acceptance: 'advisory-only', sourcePolicy: 'read-only' },
  } as const;
  return { schema: 'theorem-os.work-contract.v1' as const, stage, ...products[stage],
    input: action.kind === 'task' ? { taskId: action.task.id, taskDigest: taskVersion(action.task),
      seedCommit: action.assignment.seedCommit, dependencies: action.assignment.dependencies ?? [] } : { seedCommit: action.seedCommit },
    ...(action.kind === 'lead' || action.kind === 'solve' ? { handoffIds: action.handoffIds ?? [] } : {}),
    ...(action.kind === 'task' ? { plannedConsumers: tasks.filter(node => node.task.dependsOn.includes(action.task.id) ||
      node.alternativeRoutes?.some(route => route.prerequisiteTaskIds.includes(action.task.id) || route.closingTaskId === action.task.id))
      .map(node => node.task.id) } : {}),
  };
}
