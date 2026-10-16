import type { WebRun } from '../shared';
import { isAcceptedRun } from '../presentation';

export type RunFilter = 'all' | 'active' | 'passed' | 'unproved' | 'cancelled' | 'error';

export function filterRuns(runs: readonly WebRun[], query: string, filter: RunFilter): WebRun[] {
  const terms = query.normalize('NFKC').toLowerCase().trim().split(/\s+/).filter(Boolean);
  return runs.filter(run => {
    const accepted = isAcceptedRun(run);
    const matchesStatus = filter === 'all'
      || filter === 'active' && (run.status === 'queued' || run.status === 'running')
      || filter === 'passed' && run.status === 'completed' && accepted
      || filter === 'unproved' && run.status === 'completed' && !accepted
      || filter === 'cancelled' && run.status === 'cancelled'
      || filter === 'error' && run.status === 'error';
    if (!matchesStatus) return false;
    const searchable = [run.title, run.task, run.model, run.id, run.source,
      run.environment === 'mathlib' ? 'Mathlib 数学库' : 'Lean 标准库'].join('\n').normalize('NFKC').toLowerCase();
    return terms.every(term => searchable.includes(term));
  });
}
