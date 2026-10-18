import { sanitizeWebEventDetails } from './moduleTelemetry';
import type { WebEventDetails, WorkerMessage } from './shared';

const descriptions: Record<string, string> = {
  ready: '原题与运行环境已固定', dependency_check: '正在检查 Lean 依赖',
  proof_environment: '正在准备只读数学依赖', library_index: '正在准备数学库检索',
  preparation_finished: '题目准备完成', solve_started: '开始研究', turn_started: 'Agent 正在构造候选',
  worker_activity: 'Agent 正在运行', turn_checkpoint: '当前尝试已记录检查点', turn_failed: '当前尝试未完成',
  turn_retry: '准备继续尝试', proof_check_started: '正在检查候选证明',
  proof_checked: '候选检查完成', candidate_selected: '已选出候选，准备最终验收',
  evaluation_started: '正在独立验收完整原题', evaluation_finished: '完整原题验收结束',
  lemma_checked: '辅助引理检查完成', assembly_started: '正在集成候选证明',
  source_rejected: '候选更改了原题约束，已拒绝', preparation_failed: '运行环境预检未通过',
  worker_failed: 'Agent 会话已停止', finished: '求解流程结束',
  worker_recovering: 'Agent 正在恢复会话', worker_recovered: 'Agent 已恢复，保留已检查成果',
  assignment_superseded: '当前分配已被更新', research_action: '已选择下一步研究操作',
  model_budget_stopped: '模型预算已停止后续调用', context_compiled: '本轮上下文已整理',
  context_restarted: '研究上下文已重新建立', task_assigned: '研究任务已分配',
  task_checked: '局部任务检查完成', task_check_reused: '已复用当前任务检查',
  task_failure_check_reused: '已复用当前任务的失败检查', task_recheck_started: '正在重新检查任务',
  task_recheck_finished: '任务重新检查结束', task_integrated: '任务成果已集成',
  plan_updated: '研究计划已更新', plan_rejected: '研究计划未通过约束检查',
  initial_plan_fallback: '已建立初始研究任务', review_requested: '候选已提交审阅',
  review_assigned: '候选审阅已分配', review_completed: '候选审阅结束',
  statement_review_requested: '声明已提交审阅', statement_review_assigned: '声明审阅已分配',
  statement_review_completed: '声明审阅结束', delivery_published: '研究交付已记录',
  research_delivered: '研究结论已交付', route_parked: '当前路线已暂缓',
  route_reopened: '研究路线已重新开放', routes_idle: '当前没有可继续的路线', plan_stalled: '研究计划需要调整',
  custom_module_applied: '已将自定义策略加入本轮上下文',
};
const failureDescriptions: Record<string, string> = {
  math_model_authentication_failed: 'API Key 认证失败，请检查密钥和服务商',
  math_model_concurrency_limit: '服务商限制了当前请求，请检查配额或并发',
  math_model_request_failed: '模型服务连接失败',
  math_model_request_timeout: '模型服务请求超时',
  math_codex_transport_closed: '模型会话连接已中断',
};
const fields: Record<string, readonly (keyof WebEventDetails)[]> = {
  turn_started: ['turn'], turn_checkpoint: ['turn'], proof_check_started: ['turn'],
  proof_checked: ['passed', 'reused'], research_action: ['operation'],
  context_compiled: ['usedBytes', 'maxBytes'], evaluation_finished: ['status'],
  task_assigned: ['taskId'], task_checked: ['taskId', 'passed', 'conditional'],
  task_check_reused: ['taskId'], task_failure_check_reused: ['taskId'],
  task_recheck_started: ['taskId'], task_recheck_finished: ['taskId', 'passed'], task_integrated: ['taskId'],
  review_assigned: ['role'], statement_review_requested: ['taskId'],
  statement_review_assigned: ['taskId', 'role'], statement_review_completed: ['taskId', 'status'],
  delivery_published: ['taskId', 'status'], research_delivered: ['taskId'],
  route_parked: ['taskId'], route_reopened: ['taskId'],
  custom_module_applied: ['moduleId', 'slot', 'mode'],
};

export function translateWebProgress(value: unknown): Extract<WorkerMessage, { type: 'progress' }> | undefined {
  if (!value || typeof value !== 'object' || Array.isArray(value)) return;
  const event = value as Record<string, unknown>;
  if (typeof event.event !== 'string' || !Object.hasOwn(descriptions, event.event)) return;
  const keys: readonly (keyof WebEventDetails)[] = ['workerId', ...(fields[event.event] ?? [])];
  const details = sanitizeWebEventDetails(Object.fromEntries(keys.filter(key => Object.hasOwn(event, key)).map(key => [key, event[key]])));
  const failure = typeof event.reason === 'string' && Object.hasOwn(failureDescriptions, event.reason)
    ? failureDescriptions[event.reason] : undefined;
  return { type: 'progress', event: event.event,
    message: (failure ?? descriptions[event.event]) + (details?.workerId ? ` · ${details.workerId}` : ''),
    ...(details ? { details } : {}) };
}
