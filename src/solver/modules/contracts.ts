import { isAdvisoryTask, isFeasibilityReview, taskVersion, type CooperativeAction, type TaskRecord } from '../tasks';
import { contextTaskConsumers, type TaskConsumerContext } from '../taskConsumers';

const finiteWorkGuidance = 'A finite range of target values is not an enumerable proof task while it still quantifies over an infinite family of objects. ' +
  'State the finite reduction or a uniform argument before proposing enumeration.';
const planningDeliveryGuidance = 'For each new parallel task, use objective to state its distinct scope relative to in-flight work, ' +
  'a concrete first construction, proof step or discriminating check, and the intended consumer with its application. ' +
  'Use the existing type and dependsOn fields for exact proof interfaces and actual inputs. ' +
  'Changing the bound or restating an unresolved theorem does not supply a new method. ' +
  'When a helper or glue step is implementable from available inputs, publish a typed lemma or original-goal proof task promptly; ' +
  'give the Engineer executable proof work instead of repeatedly assigning the same research. ' +
  'Keep unresolved mathematical questions as scoped research; no task is required merely to occupy an idle worker. ' + finiteWorkGuidance;
const researchDeliveryGuidance = 'As soon as a useful helper or glue step has an exact interface and a concrete implementation method, ' +
  'publish it promptly in lemmaRequests with a full closed Lean type and actual typed input dependencies. ' +
  'In its objective, state the distinct scope, first construction or Lean step, and intended consumer with the application back to it. ' +
  'Retain reusable Lean probe code in RESEARCH.md and request a Lead decision; do not keep researching an already implementable step. ' +
  'If the method is still unknown, report the precise missing inference instead of presenting another form of the same gap as ready proof work. ' +
  finiteWorkGuidance + ' Proposals remain advisory and require a separate proof assignment and independent checking.';

/** One work product per dispatch; worker slots and mathematical responsibilities are separate. */
export function cooperativeWorkContract(action: CooperativeAction, tasks: readonly TaskRecord[], context: TaskConsumerContext = {}) {
  const exploration = action.kind === 'task' ? tasks.find(node => node.task.id === action.task.id)?.capacityExploration : undefined;
  const stage = action.kind === 'task' ? isFeasibilityReview(action.task) ? 'feasibility-review' :
    exploration ? 'capacity-exploration' : isAdvisoryTask(action.task) ? 'investigation' : action.assignment.connectionCheck ? 'consumer-connection' : 'formal-proof' :
    action.kind === 'lead' ? action.coordination ? 'coordination-decision' : 'route-planning' : action.kind === 'review' ? 'candidate-review' :
      action.kind === 'assemble' ? 'integration' : action.kind;
  const products = {
    'route-planning': { owner: 'lead', output: 'validated-task-graph-and-handoff-decisions',
      consumer: 'M3-ready-selection-and-M5-assignment', acceptance: 'host-plan-validation', sourcePolicy: 'host-checks-any-source-repair',
      deliveryGuidance: planningDeliveryGuidance },
    'coordination-decision': { owner: 'lead', output: 'version-bound-inbox-or-capacity-decision',
      consumer: 'M3-ready-selection-and-M5-assignment', acceptance: 'host-coordination-validation', sourcePolicy: 'read-only',
      deliveryGuidance: 'Decide the shown handoff/challenge activations or capacity/stagnation request using the current planVersion and dispatchNonce. ' +
        'Prefer the offered short decision event; a decision does not require rewriting the complete task graph. ' +
        'Use a complete plan when the work needs a graph change. ' + planningDeliveryGuidance },
    investigation: { owner: 'researcher', output: 'advisory-finding-retained-code-and-exact-lemma-proposals',
      consumer: 'lead-handoff-decision', acceptance: 'advisory-only', sourcePolicy: 'read-only', deliveryGuidance: researchDeliveryGuidance },
    'capacity-exploration': { owner: 'idle-proof-or-research-worker', output: 'distinct-frontier-finding-retained-lean-probe-and-exact-interface',
      consumer: 'target-owner-and-lead-handoff-decision', acceptance: 'advisory-only', sourcePolicy: 'read-only', deliveryGuidance: researchDeliveryGuidance },
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
