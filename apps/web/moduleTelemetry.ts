import type { WebEvent, WebEventDetails, WebModuleId, WebModuleSnapshot, WebRun } from './shared';

const ids = /^[A-Za-z0-9_-]{1,64}$/u;
const statuses = /^[a-z][a-z0-9_-]{0,63}$/u;
const operations = ['direct', 'decompose', 'bridge', 'prove-lemma', 'integrate-lemma'] as const;
const roles = ['lead', 'researcher', 'engineer', 'reviewer'] as const;
const object = (value: unknown): value is Record<string, unknown> =>
  value !== null && typeof value === 'object' && !Array.isArray(value);
const count = (value: unknown): value is number => Number.isSafeInteger(value) && Number(value) >= 0;

export function sanitizeWebEventDetails(value: unknown): WebEventDetails | undefined {
  if (!object(value)) return;
  const details: WebEventDetails = {};
  for (const key of ['workerId', 'taskId', 'moduleId'] as const)
    if (Object.hasOwn(value, key) && typeof value[key] === 'string' && ids.test(value[key])) details[key] = value[key];
  if (details.moduleId && ['__proto__', 'prototype', 'constructor'].includes(details.moduleId)) delete details.moduleId;
  for (const key of ['turn', 'usedBytes', 'maxBytes'] as const)
    if (Object.hasOwn(value, key) && count(value[key])) details[key] = value[key];
  for (const key of ['passed', 'conditional', 'reused'] as const)
    if (Object.hasOwn(value, key) && typeof value[key] === 'boolean') details[key] = value[key];
  if (Object.hasOwn(value, 'operation') && operations.includes(value.operation as typeof operations[number]))
    details.operation = value.operation as WebEventDetails['operation'];
  if (Object.hasOwn(value, 'role') && roles.includes(value.role as typeof roles[number]))
    details.role = value.role as WebEventDetails['role'];
  if (Object.hasOwn(value, 'status') && typeof value.status === 'string' && statuses.test(value.status)) details.status = value.status;
  if (Object.hasOwn(value, 'slot') && ['M1', 'M3', 'M4', 'M5'].includes(value.slot as string))
    details.slot = value.slot as WebEventDetails['slot'];
  if (Object.hasOwn(value, 'mode') && ['append', 'replace'].includes(value.mode as string))
    details.mode = value.mode as WebEventDetails['mode'];
  return Object.keys(details).length ? details : undefined;
}

export function isWebEventDetails(value: unknown): value is WebEventDetails {
  if (!object(value)) return false;
  const details = sanitizeWebEventDetails(value) ?? {};
  const keys = Object.keys(value);
  return keys.length === Object.keys(details).length && keys.every(key => Object.hasOwn(details, key));
}

const moduleEvents: Record<WebModuleId, readonly string[]> = {
  M1: ['turn_started', 'worker_activity', 'turn_checkpoint', 'turn_failed', 'worker_failed',
    'worker_recovering', 'worker_recovered', 'assignment_superseded'],
  M2: ['proof_check_started', 'proof_checked', 'candidate_selected', 'lemma_checked', 'source_rejected',
    'task_checked', 'task_check_reused', 'task_failure_check_reused', 'task_recheck_started', 'task_recheck_finished'],
  M3: ['research_action', 'turn_retry', 'model_budget_stopped', 'route_parked', 'route_reopened', 'routes_idle', 'plan_stalled'],
  M4: ['context_compiled', 'context_restarted'],
  M5: ['task_assigned', 'plan_updated', 'plan_rejected', 'initial_plan_fallback', 'assembly_started',
    'review_requested', 'review_assigned', 'review_completed', 'statement_review_requested',
    'statement_review_assigned', 'statement_review_completed', 'task_integrated', 'delivery_published', 'research_delivered'],
  S3: ['evaluation_started', 'evaluation_finished'],
};
const eventModules = new Map<string, WebModuleId>(Object.entries(moduleEvents)
  .flatMap(([module, events]) => events.map(event => [event, module as WebModuleId] as const)));
export const webEventModule = (type: string): WebModuleId | undefined => eventModules.get(type);

type Snapshots = Partial<Record<WebModuleId, WebModuleSnapshot>>;
const clearActive = (modules: Snapshots, only?: readonly WebModuleId[]) => {
  for (const module of only ?? Object.keys(modules) as WebModuleId[]) {
    if (modules[module]) modules[module]!.activeWorkers = [];
  }
};
const endWorker = (modules: Snapshots, module: WebModuleId, workerId: string | undefined) => {
  if (workerId && modules[module]) modules[module]!.activeWorkers = modules[module]!.activeWorkers.filter(id => id !== workerId);
};
const m1Ends = new Set(['proof_check_started', 'turn_checkpoint', 'turn_failed', 'worker_failed', 'turn_retry',
  'source_rejected', 'context_restarted', 'context_compiled', 'research_action', 'review_completed',
  'statement_review_completed', 'assembly_started', 'assignment_superseded', 'candidate_selected', 'task_checked']);
const m2Ends = new Set(['proof_checked', 'source_rejected', 'worker_failed', 'candidate_selected', 'task_checked']);

function record(modules: Snapshots, value: WebEvent, workerLimit: number) {
  const details = sanitizeWebEventDetails(value.details);
  const event: WebEvent = { sequence: value.sequence, at: value.at, type: value.type, message: value.message,
    ...(details ? { details } : {}) };
  const workerId = details?.workerId;
  if (['finished', 'cancelled', 'error'].includes(event.type)) clearActive(modules);
  if (event.type === 'evaluation_started') clearActive(modules, ['M1', 'M2']);
  if (m1Ends.has(event.type)) endWorker(modules, 'M1', workerId);
  if (m2Ends.has(event.type)) endWorker(modules, 'M2', workerId);
  if (event.type === 'evaluation_finished') clearActive(modules, ['S3']);
  const module = webEventModule(event.type);
  if (!module) return;
  const snapshot = modules[module] ??= { eventCount: 0, firstAt: event.at, lastEvent: event, activeWorkers: [] };
  snapshot.eventCount = Math.min(Number.MAX_SAFE_INTEGER, snapshot.eventCount + 1);
  snapshot.lastEvent = event;
  const starts = module === 'M1' && ['turn_started', 'worker_activity'].includes(event.type)
    || module === 'M2' && event.type === 'proof_check_started'
    || module === 'S3' && event.type === 'evaluation_started';
  if (starts && workerId && !snapshot.activeWorkers.includes(workerId) && snapshot.activeWorkers.length < workerLimit)
    snapshot.activeWorkers.push(workerId);
}

const workerLimit = (run: WebRun) => Number.isSafeInteger(run.workers) ? Math.min(4, Math.max(1, run.workers)) : 1;
const terminal = (run: WebRun) => ['completed', 'cancelled', 'error'].includes(run.status);

export function webModuleSnapshots(run: WebRun): Snapshots {
  if (run.modules) return run.modules;
  const modules: Snapshots = {};
  for (const event of run.events) record(modules, event, workerLimit(run));
  if (terminal(run)) clearActive(modules);
  return modules;
}

export function recordWebModuleEvent(run: WebRun, event: WebEvent): void {
  const modules = run.modules ??= webModuleSnapshots(run);
  record(modules, event, workerLimit(run));
  if (event.type === 'custom_module_applied') recordCustomModule(run, run.moduleApplications ??= {}, event);
  if (terminal(run)) clearActive(modules);
}

function recordCustomModule(run: WebRun, snapshots: Record<string, WebModuleSnapshot>, value: WebEvent) {
  if (value.type !== 'custom_module_applied') return;
  const details = sanitizeWebEventDetails(value.details);
  const rule = run.modulePlan?.custom.find(rule => rule.enabled && rule.id === details?.moduleId
    && rule.slot === details.slot && rule.mode === details.mode);
  if (!rule || (rule.slot === 'M5' && (run.coordination !== 'cooperative' || run.workers <= 1))) return;
  const event: WebEvent = { sequence: value.sequence, at: value.at, type: value.type, message: value.message, details };
  const snapshot = snapshots[rule.id] ??= { eventCount: 0, firstAt: event.at, lastEvent: event, activeWorkers: [] };
  snapshot.eventCount = Math.min(Number.MAX_SAFE_INTEGER, snapshot.eventCount + 1);
  snapshot.lastEvent = event;
}

export function webCustomModuleSnapshots(run: WebRun): Record<string, WebModuleSnapshot> {
  if (run.moduleApplications) return run.moduleApplications;
  const snapshots: Record<string, WebModuleSnapshot> = {};
  for (const event of run.events) recordCustomModule(run, snapshots, event);
  return snapshots;
}
