import crypto from 'node:crypto';
import type { WebConfig } from './config';
import type { WebRunner } from './runner';
import type { WebProvider, WebRun, WebRunInput, WorkerMessage } from './shared';

type Job = { owner: string; run: WebRun; input: WebRunInput; provider: WebProvider; controller: AbortController };
const terminal = (run: WebRun) => ['completed', 'cancelled', 'error'].includes(run.status);
const clean = <T>(value: T, key: string): T => JSON.parse(JSON.stringify(value).replaceAll(
  JSON.stringify(key).slice(1, -1), '[REDACTED]'));

export class WebJobs {
  private jobs = new Map<string, Job>();
  private running = 0;
  private closing = false;
  constructor(private readonly runner: WebRunner, private readonly config: Pick<WebConfig, 'concurrency' | 'queueLimit'>) {}

  list(owner: string): WebRun[] {
    return [...this.jobs.values()].filter(job => job.owner === owner).map(job => job.run).reverse();
  }
  get(owner: string, id: string): WebRun | undefined {
    const job = this.jobs.get(id);
    return job?.owner === owner ? job.run : undefined;
  }
  create(owner: string, input: WebRunInput, provider: WebProvider): WebRun {
    if (this.closing) throw new Error('服务正在停止，请稍后重试。');
    if ([...this.jobs.values()].filter(job => !terminal(job.run)).length >= this.config.queueLimit)
      throw new Error('运行队列已满，请稍后重试。');
    if (this.list(owner).length >= 20) throw new Error('当前会话已达到 20 条运行记录，请删除已结束的记录后重试。');
    const now = new Date().toISOString();
    const { apiKey, ...visible } = input;
    const environment = input.environment ?? 'standard';
    const run: WebRun = { ...clean(visible, apiKey), environment, id: crypto.randomUUID(),
      title: '', status: 'queued',
      phase: 'queued', createdAt: now, updatedAt: now, timings: {}, events: [] };
    run.title = run.task.split('\n')[0].slice(0, 60) || 'Lean 研究';
    this.jobs.set(run.id, { owner, input: { ...input, environment }, provider, run, controller: new AbortController() });
    this.event(run, 'queued', '任务已进入队列');
    queueMicrotask(() => this.pump());
    return run;
  }
  cancel(owner: string, id: string): WebRun | undefined {
    const job = this.jobs.get(id);
    if (!job || job.owner !== owner) return undefined;
    if (!terminal(job.run)) {
      const queued = job.run.status === 'queued';
      job.run.status = 'cancelled'; job.run.phase = 'cancelled'; job.run.finishedAt = new Date().toISOString();
      this.event(job.run, 'cancelled', '运行已取消');
      job.controller.abort();
      if (queued) job.input.apiKey = '';
    }
    return job.run;
  }
  remove(owner: string, id: string): 'deleted' | 'active' | 'missing' {
    const job = this.jobs.get(id);
    if (!job || job.owner !== owner) return 'missing';
    if (!terminal(job.run)) return 'active';
    this.jobs.delete(id);
    return 'deleted';
  }
  forget(owner: string) {
    for (const [id, job] of this.jobs) if (job.owner === owner) {
      this.cancel(owner, id); this.jobs.delete(id);
    }
  }
  async close() {
    this.closing = true;
    for (const job of this.jobs.values()) this.cancel(job.owner, job.run.id);
    while (this.running) await new Promise(resolve => setTimeout(resolve, 25));
    this.jobs.clear();
  }
  private event(run: WebRun, type: string, message: string) {
    const sequence = (run.events.at(-1)?.sequence ?? 0) + 1;
    run.updatedAt = new Date().toISOString();
    const timing = type === 'preparing' ? 'preparing' : type === 'solve_started' ? 'solving'
      : type === 'evaluation_started' ? 'evaluating' : undefined;
    // Keep phase boundaries even after the bounded activity log has rotated.
    if (timing) (run.timings ??= {})[timing] ??= run.updatedAt;
    run.events.push({ sequence, at: run.updatedAt, type, message: message.slice(0, 2_000) });
    if (run.events.length > 200) run.events.shift();
  }
  private pump() {
    if (this.closing || this.running >= this.config.concurrency) return;
    const job = [...this.jobs.values()].find(item => item.run.status === 'queued');
    if (!job) return;
    this.running++; job.run.status = 'running'; job.run.phase = 'preparing';
    this.event(job.run, 'preparing', '正在准备独立运行环境');
    void this.execute(job).finally(() => { this.running--; this.pump(); });
    this.pump();
  }
  private async execute(job: Job) {
    const key = job.input.apiKey;
    const handle = (raw: WorkerMessage) => {
      if (terminal(job.run)) return;
      const message = clean(raw, key);
      if (message.type === 'progress') {
        job.run.phase = message.event;
        this.event(job.run, message.event, message.message);
      } else if (message.type === 'result') {
        job.run.result = message.result;
        job.run.phase = message.result.status;
      } else if (message.type === 'error') {
        job.run.error = message.message;
      }
    };
    try {
      await this.runner.run({ id: job.run.id, input: job.input, provider: job.provider }, handle, job.controller.signal);
      if (!terminal(job.run)) {
        if (!job.run.result) throw new Error(job.run.error || '没有收到运行结果。');
        job.run.status = job.run.result.status === 'runtime_error' ? 'error' : 'completed';
        this.event(job.run, 'finished', job.run.result.status === 'evaluated_passed' ? '完整原题通过独立 Lean 验收' : '运行结束，请查看验收状态');
      }
    } catch (error) {
      if (!terminal(job.run)) {
        job.run.status = 'error'; job.run.phase = 'error';
        job.run.error = clean(error instanceof Error ? error.message : '运行失败。', key);
        this.event(job.run, 'error', job.run.error);
      }
    } finally {
      job.input.apiKey = '';
      job.run.finishedAt ??= new Date().toISOString();
    }
  }
}
