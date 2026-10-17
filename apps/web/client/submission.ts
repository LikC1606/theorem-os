import type { WebSession } from '../shared';
import type { TaskDraft } from './draft';

export const submissionFields = ['provider', 'environment', 'source', 'task', 'model', 'api-key', 'max-turns', 'max-seconds', 'workers'] as const;
export type SubmissionField = typeof submissionFields[number];
export type SubmissionIssue = { field: SubmissionField; message: string };

// This checks input only. Provider authentication happens when a run is submitted.
export function submissionIssues(draft: TaskDraft, apiKey: string, session: WebSession): SubmissionIssue[] {
  const issues: SubmissionIssue[] = [];
  const add = (field: SubmissionField, message: string) => issues.push({ field, message });
  if (!session.providers.some(provider => provider.id === draft.providerId)) add('provider', '请选择可用的服务商');
  if (!session.environments.some(environment => environment.id === draft.environment)) add('environment', '请选择可用的证明环境');
  for (const [field, value, label, limit] of [
    ['source', draft.source, 'Lean 源码', session.limits.maxSourceBytes],
    ['task', draft.task, '研究任务', session.limits.maxTaskBytes],
  ] as const) {
    if (!value.trim()) add(field, `请填写${label}`);
    else if (value.includes('\0')) add(field, `${label}包含无效字符`);
    else if (new TextEncoder().encode(value).length > limit) add(field, `${label}超出允许大小（最多 ${limit.toLocaleString('zh-CN')} 字节）`);
  }
  const model = draft.model.trim();
  if (!model) add('model', '请填写模型名称');
  else if (model.length > 128) add('model', '模型名称最多 128 个字符');
  else if (!/^[a-zA-Z0-9][a-zA-Z0-9._:/-]*$/.test(model)) add('model', '模型名称须以字母或数字开头，只能包含字母、数字及 . _ : / -');
  const key = apiKey.trim();
  if (!key) add('api-key', '请填写 API Key');
  else if (key.length < 8 || key.length > 4096) add('api-key', 'API Key 长度须为 8–4096 个字符');
  else if (!/^[\x21-\x7e]+$/.test(key)) add('api-key', 'API Key 只能包含英文可见字符，不能包含空格或换行');
  for (const [field, raw, label, min, max] of [
    ['max-turns', draft.maxTurns, '轮次上限', 1, session.limits.maxTurns],
    ['max-seconds', draft.maxRunSeconds, '解题预算', 30, session.limits.maxRunSeconds],
    ['workers', draft.workers, 'Agent 数量', 1, session.limits.maxWorkers],
  ] as const) {
    const value = Number(raw);
    if (!raw.trim() || !Number.isSafeInteger(value) || value < min || value > max) add(field, `${label}须为 ${min}–${max} 的整数`);
  }
  return issues;
}
