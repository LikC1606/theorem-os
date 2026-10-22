import { isAdvisoryTask, isFeasibilityReview, taskVersion, type CooperativeAction, type TaskRecord } from '../tasks';
import { contextTaskConsumers, type TaskConsumerContext } from '../taskConsumers';

/** One work product per dispatch; worker slots and mathematical responsibilities are separate. */
export function cooperativeWorkContract(action: CooperativeAction, tasks: readonly TaskRecord[], context: TaskConsumerContext = {}) {
  const exploration = action.kind === 'task' ? tasks.find(node => node.task.id === action.task.id)?.capacityExploration : undefined;
  const stage = action.kind === 'task' ? isFeasibilityReview(action.task) ? 'feasibility-review' :
    exploration ? 'capacity-exploration' : isAdvisoryTask(action.task) ? 'investigation' : action.assignment.connectionCheck ? 'consumer-connection' : 'formal-proof' :
    action.kind === 'lead' ? 'route-planning' : action.kind === 'review' ? 'candidate-review' :
      action.kind === 'assemble' ? 'integration' : action.kind;
  const products = {
    'route-planning': { owner: 'lead', output: 'validated-task-graph-and-handoff-decisions',
      consumer: 'M3-ready-selection-and-M5-assignment', acceptance: 'host-plan-validation', sourcePolicy: 'host-checks-any-source-repair' },
    investigation: { owner: 'researcher', output: 'advisory-finding-retained-code-and-exact-lemma-proposals',
      consumer: 'lead-handoff-decision', acceptance: 'advisory-only', sourcePolicy: 'read-only' },
    'capacity-exploration': { owner: 'idle-proof-or-research-worker', output: 'distinct-frontier-finding-retained-lean-probe-and-exact-interface',
      consumer: 'target-owner-and-lead-handoff-decision', acceptance: 'advisory-only', sourcePolicy: 'read-only' },
    'feasibility-review': { owner: 'independent-researcher', output: 'core-inference-risk-and-discriminating-evidence',
      consumer: 'lead-route-decision', acceptance: 'advisory-only', sourcePolicy: 'read-only' },
    'formal-proof': { owner: 'proof-worker', output: 'saved-exact-typed-declaration',
      consumer: 'M2-then-canonical-integration', acceptance: 'independent-exact-source-check', sourcePolicy: 'owned-proof-sources' },
    'consumer-connection': { owner: 'proof-worker', output: 'consumer-proof-from-fixed-typed-inputs',
      consumer: 'M2-then-input-proofs-and-unconditional-integration', acceptance: 'conditional-check-only', sourcePolicy: 'owned-proof-sources' },
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
      seedCommit: action.assignment.seedCommit, dependencies: action.assignment.dependencies ?? [],
      ...(action.assignment.connectionCheck ? { connectionCheck: action.assignment.connectionCheck,
        purpose: 'check-consumer-sufficiency-with-fixed-inputs', acceptance: 'conditional-only-until-inputs-checked' } : {}) } : { seedCommit: action.seedCommit },
    ...(action.kind === 'lead' ? { handoffIds: action.handoffIds ?? [],
      handoffActivations: action.handoffActivations ?? {}, challengeIds: action.challengeIds ?? [],
      challengeActivations: action.challengeActivations ?? {},
      ...(action.capacityRefill ? { capacityRefill: action.capacityRefill } : {}) } : {}),
    ...(action.kind === 'task' ? { plannedConsumers: contextTaskConsumers(action.task, tasks, context)
      .map(consumer => consumer.task.id) } : {}),
    ...(exploration ? { capacityExploration: exploration } : {}),
  };
}
