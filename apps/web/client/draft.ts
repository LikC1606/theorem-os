import type { WebCoordination, WebEffort, WebEnvironment } from '../shared';

export const taskDraftSchema = 'theorem-os.web-draft.v1';
export const taskDraftStorageKey = 'theorem-os.web-draft.v1';

export type TaskDraft = {
  providerId: string;
  model: string;
  source: string;
  task: string;
  maxTurns: string;
  maxRunSeconds: string;
  workers: string;
  effort: WebEffort;
  environment: WebEnvironment;
  coordination: WebCoordination;
  templateId: string;
};

const archiveSchema = 'theorem-os.web-export.v1';
const maximumFileBytes = 16 * 1024 * 1024;
const encoder = new TextEncoder();
const editableNumber = /^[+-]?(?:(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][+-]?\d*)?|\.)?$/;

function invalid(): never { throw new Error('任务草稿格式无效'); }

function object(value: unknown): Record<string, unknown> {
  if (value === null || typeof value !== 'object' || Array.isArray(value)) invalid();
  return value as Record<string, unknown>;
}

function own(record: Record<string, unknown>, key: string): unknown {
  if (!Object.hasOwn(record, key)) invalid();
  return record[key];
}

function text(record: Record<string, unknown>, key: string, maximum: number): string {
  const value = own(record, key);
  if (typeof value !== 'string' || value.length > maximum || value.includes('\0')) invalid();
  return value;
}

function utf8Text(record: Record<string, unknown>, key: string, maximum: number): string {
  const value = text(record, key, maximum);
  if (encoder.encode(value).byteLength > maximum) invalid();
  return value;
}

function budget(record: Record<string, unknown>, key: string): string {
  const value = text(record, key, 24);
  if (!editableNumber.test(value)) invalid();
  return value;
}

function enumeration<T extends string>(record: Record<string, unknown>, key: string, choices: readonly T[]): T {
  const value = own(record, key);
  if (typeof value !== 'string' || !choices.includes(value as T)) invalid();
  return value as T;
}

function validatedDraft(value: unknown): TaskDraft {
  const draft = object(value);
  return {
    providerId: text(draft, 'providerId', 64), model: text(draft, 'model', 128),
    source: utf8Text(draft, 'source', 32 * 1024), task: utf8Text(draft, 'task', 8_000),
    maxTurns: budget(draft, 'maxTurns'), maxRunSeconds: budget(draft, 'maxRunSeconds'), workers: budget(draft, 'workers'),
    effort: enumeration(draft, 'effort', ['low', 'medium', 'high', 'xhigh']),
    environment: enumeration(draft, 'environment', ['standard', 'mathlib']),
    coordination: enumeration(draft, 'coordination', ['cooperative', 'independent']),
    templateId: text(draft, 'templateId', 64),
  };
}

function archiveBudget(run: Record<string, unknown>, key: string): string {
  const value = own(run, key);
  if (typeof value !== 'number' || !Number.isFinite(value)) invalid();
  return String(value);
}

export function encodeTaskDraft(draft: TaskDraft): string {
  try { return JSON.stringify({ schema: taskDraftSchema, draft: validatedDraft(draft) }); }
  catch { return invalid(); }
}

export function decodeTaskDraft(value: unknown): TaskDraft {
  try {
    const envelope = object(value), schema = own(envelope, 'schema');
    if (schema === taskDraftSchema) return validatedDraft(own(envelope, 'draft'));
    if (schema !== archiveSchema) return invalid();
    const run = object(own(envelope, 'run'));
    return validatedDraft({
      providerId: own(run, 'providerId'), model: own(run, 'model'), source: own(run, 'source'), task: own(run, 'task'),
      maxTurns: archiveBudget(run, 'maxTurns'), maxRunSeconds: archiveBudget(run, 'maxRunSeconds'), workers: archiveBudget(run, 'workers'),
      effort: own(run, 'effort'), environment: own(run, 'environment'), coordination: own(run, 'coordination'), templateId: '',
    });
  } catch { return invalid(); }
}

export async function readTaskDraftFile(file: Pick<File, 'name' | 'size' | 'arrayBuffer'>): Promise<TaskDraft> {
  let name: string, size: number;
  try { name = file.name; size = file.size; }
  catch { throw new Error('无法读取任务文件'); }
  if (typeof name !== 'string' || !/\.json$/i.test(name)) throw new Error('请选择 .json 任务文件');
  if (!Number.isSafeInteger(size) || size < 0 || size > maximumFileBytes) throw new Error('任务文件超过 16 MiB 上限或大小无效');
  let buffer: ArrayBuffer;
  try { buffer = await file.arrayBuffer(); }
  catch { throw new Error('无法读取任务文件'); }
  if (!(buffer instanceof ArrayBuffer)) throw new Error('无法读取任务文件');
  if (buffer.byteLength > maximumFileBytes) throw new Error('任务文件超过 16 MiB 上限');
  let content: string;
  try { content = new TextDecoder('utf-8', { fatal: true }).decode(buffer); }
  catch { throw new Error('任务文件需使用 UTF-8 编码'); }
  if (content.includes('\0')) throw new Error('任务文件包含无效字符');
  let value: unknown;
  try { value = JSON.parse(content); }
  catch { throw new Error('任务文件不是有效 JSON'); }
  return decodeTaskDraft(value);
}
