import { isAdvisoryTask, isFeasibilityReview, taskVersion, type CooperativeAction, type TaskRecord } from '../tasks';
import { contextTaskConsumers, type TaskConsumerContext } from '../taskConsumers';

/** One work product per dispatch; worker slots and mathematical responsibilities are separate. */
export function cooperativeWorkContract(action: CooperativeAction, tasks: readonly TaskRecord[], context: TaskConsumerContext = {}) {
  const stage = action.kind === 'task' ? isFeasibilityReview(action.task) ? 'feasibility-review' :
    isAdvisoryTask(action.task) ? 'investigation' : 'formal-proof' :
    action.kind === 'lead' ? 'route-planning' : action.kind === 'review' ? 'candidate-review' :
      action.kind === 'solve' ? 'primary-proof' : action.kind === 'assemble' ? 'integration' : action.kind;
  const products = {
    'route-planning': { owner: 'lead', output: 'validated-task-graph-and-handoff-decisions',
      consumer: 'M3-ready-selection-and-M5-assignment', acceptance: 'host-plan-validation', sourcePolicy: 'host-checks-any-source-repair' },
    investigation: { owner: 'researcher', output: 'advisory-finding-retained-code-and-exact-lemma-proposals',
      consumer: 'lead-handoff-decision', acceptance: 'advisory-only', sourcePolicy: 'read-only' },
    'feasibility-review': { owner: 'independent-researcher', output: 'core-inference-risk-and-discriminating-evidence',
      consumer: 'lead-route-decision', acceptance: 'advisory-only', sourcePolicy: 'read-only' },
    'formal-proof': { owner: 'proof-worker', output: 'saved-exact-typed-declaration',
      consumer: 'M2-then-canonical-integration', acceptance: 'independent-exact-source-check', sourcePolicy: 'owned-proof-sources' },
    'primary-proof': { owner: 'primary-solver', output: 'saved-original-targets',
      consumer: 'M2-then-independent-review-and-S3', acceptance: 'S3-final-evaluation', sourcePolicy: 'owned-proof-sources' },
    integration: { owner: 'host', output: 'fixed-original-proof-check',
      consumer: 'independent-review-then-S3', acceptance: 'independent-exact-source-check', sourcePolicy: 'read-only' },
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
    ...(action.kind === 'lead' || action.kind === 'solve' ? { handoffIds: action.handoffIds ?? [],
      handoffActivations: action.handoffActivations ?? {} } : {}),
    ...(action.kind === 'task' ? { plannedConsumers: contextTaskConsumers(action.task, tasks, context)
      .map(consumer => consumer.task.id) } : {}),
  };
}
