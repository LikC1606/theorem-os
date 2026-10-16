import { describe, expect, it, vi } from 'vitest';
import { decodeTaskDraft, encodeTaskDraft, readTaskDraftFile, taskDraftSchema, taskDraftStorageKey, type TaskDraft } from '../apps/web/client/draft';

const encoder = new TextEncoder();
const maximumFileBytes = 16 * 1024 * 1024;
const draft = (changes: Partial<TaskDraft> = {}): TaskDraft => ({
  providerId: 'openai', model: 'fixture-model', source: 'theorem sample : True := by sorry',
  task: 'Prove every original target', maxTurns: '4', maxRunSeconds: '180', workers: '2',
  effort: 'xhigh', environment: 'mathlib', coordination: 'cooperative', templateId: 'mathlib-square', ...changes,
});
const envelope = (value: unknown) => ({ schema: taskDraftSchema, draft: value });
const archive = () => ({ schema: 'theorem-os.web-export.v1', run: {
  ...draft(), maxTurns: 4, maxRunSeconds: 180, workers: 2,
  id: 'archived-run', status: 'completed', result: { status: 'evaluated_passed', proof: 'by trivial' },
} });
const file = (content: string | Uint8Array, name = 'task.json', declaredSize?: number): Pick<File, 'name' | 'size' | 'arrayBuffer'> => {
  const bytes = typeof content === 'string' ? encoder.encode(content) : Uint8Array.from(content);
  return { name, size: declaredSize ?? bytes.byteLength, arrayBuffer: vi.fn(async () => bytes.buffer as ArrayBuffer) };
};

describe('task draft codecs without credentials or run-result state', () => {
  it('round trips a complete draft in the versioned envelope', () => {
    const original = draft();
    expect(taskDraftSchema).toBe('theorem-os.web-draft.v1');
    expect(taskDraftStorageKey).toBe(taskDraftSchema);
    expect(JSON.parse(encodeTaskDraft(original))).toEqual(envelope(original));
    expect(decodeTaskDraft(JSON.parse(encodeTaskDraft(original)))).toEqual(original);
  });

  it('converts only archived execution configuration into an editable draft', () => {
    expect(decodeTaskDraft(archive())).toEqual(draft({ templateId: '' }));
    expect(decodeTaskDraft(archive())).not.toHaveProperty('status');
    expect(decodeTaskDraft(archive())).not.toHaveProperty('result');
  });

  it('preserves unfinished empty text and configuration', () => {
    const original = draft({ providerId: '', model: '', source: '', task: '', maxTurns: '', maxRunSeconds: '', workers: '', templateId: '' });
    expect(decodeTaskDraft(JSON.parse(encodeTaskDraft(original)))).toEqual(original);
  });

  it.each(['', '-', '+', '.', '-.', '1.', '1e', '1e-', '-2.5e+', '0', '-1', '999999999999999999999999'])('preserves an editable numeric prefix without execution-range checks: %j', value => {
    const original = draft({ maxTurns: value, maxRunSeconds: value, workers: value });
    expect(decodeTaskDraft(JSON.parse(encodeTaskDraft(original)))).toEqual(original);
  });

  it.each(['abc', 'NaN', 'Infinity', ' 2', '2 ', '1,000', '0x10', '2..5', 'e1', '.e1', '1e--', '1'.repeat(25)])('rejects malformed or overlong numeric strings: %j', value => {
    const original = draft({ maxTurns: value });
    expect(() => encodeTaskDraft(original)).toThrow('任务草稿格式无效');
    expect(() => decodeTaskDraft(envelope(original))).toThrow('任务草稿格式无效');
  });

  it('copies an explicit whitelist without reading extra credentials, results or serialization hooks', () => {
    const original = draft();
    const read = vi.fn(() => { throw new Error('unread-sensitive-value'); });
    for (const key of ['apiKey', 'result', 'status', 'toJSON']) Object.defineProperty(original, key, { enumerable: true, get: read });
    const encoded = encodeTaskDraft(original);
    expect(JSON.parse(encoded)).toEqual(envelope(draft()));
    expect(decodeTaskDraft(envelope(original))).toEqual(draft());
    expect(read).not.toHaveBeenCalled();
    expect(encoded).not.toMatch(/apiKey|result|status|unread-sensitive-value/);
  });

  it('strips extra values from both draft and archive imports', () => {
    const extra = { apiKey: 'sensitive-extra-key', result: { proof: 'extra-proof' }, status: 'accepted', events: ['extra-event'] };
    expect(decodeTaskDraft({ ...envelope({ ...draft(), ...extra }), ...extra })).toEqual(draft());
    const archived = archive();
    Object.assign(archived.run, extra);
    const decoded = decodeTaskDraft(archived);
    expect(decoded).toEqual(draft({ templateId: '' }));
    expect(encodeTaskDraft(decoded)).not.toMatch(/sensitive-extra-key|extra-proof|extra-event|accepted/);
  });

  it('does not read archived results, credentials or a nonstandard template ID', () => {
    const archived = archive();
    const read = vi.fn(() => { throw new Error('unread-sensitive-value'); });
    for (const key of ['apiKey', 'result', 'status', 'templateId']) Object.defineProperty(archived.run, key, { get: read });
    expect(decodeTaskDraft(archived)).toEqual(draft({ templateId: '' }));
    expect(read).not.toHaveBeenCalled();
  });

  it.each([undefined, null, [], true, 1, 'draft', {}, { schema: 'unknown' },
    { schema: taskDraftSchema }, { schema: taskDraftSchema, draft: null },
    { schema: 'theorem-os.web-export.v1', run: [] }].map(value => [value]))('rejects malformed envelopes or schemas: %j', value => {
    expect(() => decodeTaskDraft(value)).toThrow('任务草稿格式无效');
  });

  it('requires own fields rather than inheriting schema or draft data', () => {
    expect(() => decodeTaskDraft(Object.create(envelope(draft())))).toThrow('任务草稿格式无效');
    expect(() => decodeTaskDraft(envelope(Object.create(draft())))).toThrow('任务草稿格式无效');
  });

  it.each([
    ['providerId', 1], ['model', null], ['source', {}], ['task', []], ['maxTurns', 1],
    ['maxRunSeconds', false], ['workers', 2], ['templateId', undefined],
    ['effort', 'maximum'], ['effort', ''], ['environment', 'custom'], ['coordination', 'parallel'],
  ])('rejects an invalid required field: %s', (key, value) => {
    const invalid = { ...draft(), [key]: value };
    expect(() => decodeTaskDraft(envelope(invalid))).toThrow('任务草稿格式无效');
    expect(() => encodeTaskDraft(invalid as TaskDraft)).toThrow('任务草稿格式无效');
  });

  it.each(['providerId', 'model', 'source', 'task', 'maxTurns', 'maxRunSeconds', 'workers', 'effort', 'environment', 'coordination', 'templateId'])('rejects a missing required draft field: %s', key => {
    const invalid: Record<string, unknown> = draft();
    delete invalid[key];
    expect(() => decodeTaskDraft(envelope(invalid))).toThrow('任务草稿格式无效');
  });

  it.each([['providerId', 64], ['model', 128], ['templateId', 64]] as const)('enforces the character boundary for %s', (key, maximum) => {
    const valid = draft({ [key]: 'a'.repeat(maximum) });
    expect(decodeTaskDraft(envelope(valid))).toEqual(valid);
    expect(() => encodeTaskDraft(draft({ [key]: 'a'.repeat(maximum + 1) }))).toThrow('任务草稿格式无效');
  });

  it.each([['source', 32 * 1024], ['task', 8_000]] as const)('enforces the UTF-8 byte boundary for %s', (key, maximum) => {
    const atBoundary = '题'.repeat(Math.floor(maximum / 3)) + 'a'.repeat(maximum % 3);
    expect(encoder.encode(atBoundary).byteLength).toBe(maximum);
    const valid = draft({ [key]: atBoundary });
    expect(decodeTaskDraft(JSON.parse(encodeTaskDraft(valid)))).toEqual(valid);
    expect(() => encodeTaskDraft(draft({ [key]: atBoundary + 'a' }))).toThrow('任务草稿格式无效');
    expect(() => decodeTaskDraft(envelope(draft({ [key]: '题'.repeat(maximum) })))).toThrow('任务草稿格式无效');
  });

  it('rejects NUL in retained fields', () => {
    expect(() => encodeTaskDraft(draft({ source: 'proof\0text' }))).toThrow('任务草稿格式无效');
    expect(() => decodeTaskDraft(envelope(draft({ model: 'model\0name' })))).toThrow('任务草稿格式无效');
  });

  it.each([NaN, Infinity, -Infinity, '4', null, true, {}, []].map(value => [value]))('requires finite numeric budgets in archives: %j', value => {
    const archived = archive();
    Object.assign(archived.run, { maxTurns: value });
    expect(() => decodeTaskDraft(archived)).toThrow('任务草稿格式无效');
  });

  it('converts finite archived budgets without applying execution limits', () => {
    const archived = archive();
    Object.assign(archived.run, { maxTurns: 0, maxRunSeconds: -0.5, workers: Number.MAX_VALUE });
    expect(decodeTaskDraft(archived)).toEqual(draft({ templateId: '', maxTurns: '0', maxRunSeconds: '-0.5', workers: String(Number.MAX_VALUE) }));
  });

  it('uses fixed errors even when a known field getter throws sensitive input', () => {
    const invalid = draft();
    Object.defineProperty(invalid, 'source', { get() { throw new Error('sensitive-input'); } });
    expect(() => encodeTaskDraft(invalid)).toThrow('任务草稿格式无效');
    expect(() => decodeTaskDraft(envelope(invalid))).toThrow('任务草稿格式无效');
  });

  it('does not mutate the imported envelope or draft', () => {
    const original = envelope(draft()), before = structuredClone(original);
    encodeTaskDraft(original.draft);
    decodeTaskDraft(original);
    expect(original).toEqual(before);
  });
});

describe('UTF-8 task draft file import', () => {
  it('reads draft JSON, uppercase extensions, UTF-8 BOM and run archives', async () => {
    const encoded = encodeTaskDraft(draft());
    await expect(readTaskDraftFile(file(encoded))).resolves.toEqual(draft());
    await expect(readTaskDraftFile(file('\uFEFF' + encoded, 'TASK.JSON'))).resolves.toEqual(draft());
    await expect(readTaskDraftFile(file(JSON.stringify(archive())))).resolves.toEqual(draft({ templateId: '' }));
  });

  it('imports a realistic large run archive while discarding result data and extra sensitive fields', async () => {
    const diagnostic = ('诊断 "\\\n').repeat(400).slice(0, 2_000);
    const results = Array.from({ length: 64 }, (_, index) => ({
      theoremName: `Sample.target${index}`, status: 'failed', sorryCount: 0, admitCount: 0,
      error: diagnostic, stdoutPreview: diagnostic, stderrPreview: diagnostic,
    }));
    const archived = { schema: 'theorem-os.web-export.v1', run: {
      ...archive().run, apiKey: 'archive-secret-key',
      events: Array.from({ length: 200 }, (_, index) => ({ sequence: index + 1,
        at: '2026-10-16T00:00:00.000Z', type: 'worker_activity',
        message: ('archive-event-marker 运行消息\n').repeat(100).slice(0, 2_000) })),
      result: { status: 'evaluated_failed', proof: 'p'.repeat(128 * 1024),
        report: { reason: 'archive-result-marker', usage: { totalTokens: 'invalid ignored value' },
          candidateCheck: { passed: false, status: 'failed', results },
          evaluator: { method: 'host-lean-kernel-all-targets', status: 'failed',
            verification: { passed: false, verification: { status: 'failed', results } } } } },
    } };
    const input = file(JSON.stringify(archived), 'large-run-export.json');
    expect(input.size).toBeGreaterThan(256 * 1024);
    expect(input.size).toBeLessThan(maximumFileBytes);
    const decoded = await readTaskDraftFile(input);
    expect(decoded).toEqual(draft({ templateId: '' }));
    expect(encodeTaskDraft(decoded)).not.toMatch(/archive-secret-key|archive-result-marker|archive-event-marker|candidateCheck|evaluator|stdoutPreview|apiKey|status|events|result/);
  });

  it.each([['source', 32 * 1024 + 1], ['task', 8_001]] as const)('still rejects an oversized projected %s in a valid-size archive', async (key, size) => {
    const archived = archive();
    archived.run[key] = 'a'.repeat(size);
    const input = file(JSON.stringify(archived));
    expect(input.size).toBeLessThan(maximumFileBytes);
    await expect(readTaskDraftFile(input)).rejects.toThrow('任务草稿格式无效');
  });

  it('accepts exactly 16 MiB including JSON whitespace', async () => {
    const content = new Uint8Array(maximumFileBytes).fill(0x20);
    content.set(encoder.encode(encodeTaskDraft(draft())));
    await expect(readTaskDraftFile(file(content))).resolves.toEqual(draft());
  });

  it.each(['task.txt', 'task.json.exe', 'json'])('rejects a non-JSON extension before reading: %s', name => {
    const input = file(encodeTaskDraft(draft()), name);
    return expect(readTaskDraftFile(input)).rejects.toThrow('请选择 .json 任务文件').then(() => {
      expect(input.arrayBuffer).not.toHaveBeenCalled();
    });
  });

  it.each([maximumFileBytes + 1, -1, NaN, Infinity, 0.5])('rejects invalid declared file size before reading: %s', declaredSize => {
    const input = file(encodeTaskDraft(draft()), 'task.json', declaredSize);
    return expect(readTaskDraftFile(input)).rejects.toThrow('任务文件超过 16 MiB 上限或大小无效').then(() => {
      expect(input.arrayBuffer).not.toHaveBeenCalled();
    });
  });

  it('also enforces actual buffer size when the declared size is smaller', async () => {
    await expect(readTaskDraftFile(file(new Uint8Array(maximumFileBytes + 1), 'task.json', 1)))
      .rejects.toThrow('任务文件超过 16 MiB 上限');
  });

  it.each([[0xff], [0xc3, 0x28], [0xe4, 0xb8], [0xff, 0xfe, 0x7b, 0x00]].map(bytes => ({ bytes })))('rejects invalid UTF-8 bytes: %j', ({ bytes }) => {
    return expect(readTaskDraftFile(file(Uint8Array.from(bytes)))).rejects.toThrow('任务文件需使用 UTF-8 编码');
  });

  it('rejects raw NUL and escaped NUL retained in draft fields', async () => {
    await expect(readTaskDraftFile(file(encodeTaskDraft(draft()) + '\0'))).rejects.toThrow('任务文件包含无效字符');
    await expect(readTaskDraftFile(file(JSON.stringify(envelope(draft({ source: 'proof\0text' }))))))
      .rejects.toThrow('任务草稿格式无效');
  });

  it.each(['', '{"private":"sensitive-input",', 'not-json', 'null'])('rejects malformed file content without echoing it: %j', content => {
    return expect(readTaskDraftFile(file(content))).rejects.toThrow(/任务文件不是有效 JSON|任务草稿格式无效/);
  });

  it('sanitizes read errors and rejects malformed buffer results', async () => {
    const unreadable = { name: 'sensitive-input.json', size: 10,
      arrayBuffer: async () => { throw new Error('sensitive-input'); } };
    await expect(readTaskDraftFile(unreadable)).rejects.toThrow('无法读取任务文件');
    const malformed = { name: 'task.json', size: 10, arrayBuffer: async () => 'sensitive-input' as unknown as ArrayBuffer };
    await expect(readTaskDraftFile(malformed)).rejects.toThrow('无法读取任务文件');
  });

  it.each(['name', 'size'])('sanitizes a throwing file metadata getter: %s', key => {
    const input = file(encodeTaskDraft(draft()));
    Object.defineProperty(input, key, { get() { throw new Error('sensitive-input'); } });
    return expect(readTaskDraftFile(input)).rejects.toThrow('无法读取任务文件').then(() => {
      expect(input.arrayBuffer).not.toHaveBeenCalled();
    });
  });
});
