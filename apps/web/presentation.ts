import type { WebRun } from './shared';

export const isAcceptedRun = (run: WebRun) => run.status === 'completed' && run.result?.status === 'evaluated_passed';

export const runStages = [
  { id: 'queued', label: '排队', events: ['queued'] },
  { id: 'preparing', label: '准备环境', events: ['preparing', 'dependency_check', 'proof_environment', 'library_index', 'ready', 'preparation_finished', 'preparation_failed'] },
  { id: 'solving', label: '构造证明', events: ['solve_started', 'turn_started', 'worker_activity', 'turn_checkpoint', 'turn_failed', 'turn_retry', 'proof_check_started', 'proof_checked', 'candidate_selected', 'lemma_checked', 'assembly_started', 'source_rejected', 'worker_failed'] },
  { id: 'evaluating', label: '独立验收', events: ['evaluation_started', 'evaluation_finished'] },
] as const;

type StepState = 'done' | 'active' | 'stopped' | 'error' | 'pending' | 'skipped';
const milliseconds = (from: string | undefined, to: number) => {
  const start = Date.parse(from ?? '');
  return Number.isFinite(start) && Number.isFinite(to) ? Math.max(0, to - start) : null;
};

export function formatDuration(value: number | null): string {
  if (value === null || !Number.isFinite(value)) return '--:--';
  const seconds = Math.floor(Math.max(0, value) / 1000);
  const parts = [Math.floor(seconds / 60) % 60, seconds % 60];
  if (seconds >= 3600) parts.unshift(Math.floor(seconds / 3600));
  return parts.map(part => String(part).padStart(2, '0')).join(':');
}

export function runProgress(run: WebRun, now = Date.now()) {
  const terminal = run.status !== 'queued' && run.status !== 'running';
  const end = terminal ? Date.parse(run.finishedAt ?? run.updatedAt) : now;
  const starts = runStages.map(stage => stage.id === 'queued' ? run.createdAt
    : run.timings?.[stage.id] ?? run.events.find(event => (stage.events as readonly string[]).includes(event.type))?.at);
  let index = run.status === 'queued' ? 0 : run.status === 'running' ? 1 : 0;
  if (run.status !== 'queued') {
    for (let position = 1; position < runStages.length; position++) {
      if (starts[position] || (runStages[position].events as readonly string[]).includes(run.phase)) index = position;
    }
    if (run.result?.status.startsWith('evaluated_')) index = 3;
  }
  const accepted = isAcceptedRun(run);
  const failed = run.status === 'error' || ['evaluated_failed', 'evaluated_rejected'].includes(run.result?.status ?? '');
  const steps = runStages.map((stage, position) => {
    const next = starts.slice(position + 1).find(Boolean);
    const state: StepState = position < index ? 'done' : position > index ? terminal ? 'skipped' : 'pending'
      : terminal ? accepted ? 'done' : failed ? 'error' : 'stopped' : 'active';
    const elapsed = position > index ? null : milliseconds(starts[position], next ? Date.parse(next) : end);
    return { ...stage, state, elapsed };
  });
  const phaseLabel = run.status === 'queued' ? '等待运行'
    : run.status === 'cancelled' ? '已取消'
      : run.status === 'error' ? '运行错误'
        : terminal ? accepted ? '验收通过' : failed ? '验收未通过' : '研究已结束'
          : run.phase === 'proof_check_started' ? '检查候选证明' : runStages[index].label;
  return { index, steps, phaseLabel, terminal, elapsed: milliseconds(run.createdAt, end), solvingElapsed: steps[2].elapsed };
}

export function resultDescription(run: WebRun): string {
  if (run.error) return run.error;
  if (run.status === 'cancelled') return '任务已停止。';
  if (run.status === 'queued') return '等待可用的运行环境。';
  if (run.status === 'running') {
    const stage = runProgress(run).index;
    if (stage === 1) return `${run.environment === 'mathlib' ? 'Mathlib 依赖' : 'Lean 环境'}准备中，解题尚未开始。`;
    if (stage === 3) return '正在独立验证完整原题。';
    return '正在构造与检查候选证明。';
  }
  if (isAcceptedRun(run)) return '完整原题通过独立 Lean 验收。';
  if (run.result?.status === 'evaluated_failed') return '候选证明未通过独立 Lean 验收。';
  if (run.result?.status === 'evaluated_rejected') return '候选未满足验收约束，详情见报告。';
  if (run.status === 'error') return '运行环境或模型会话发生错误。';
  return '本次研究尚未得到通过完整原题验收的证明。';
}
