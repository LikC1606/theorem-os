import { CooperativeResearch } from '../../src/solver/cooperation';
import { directSolverModules } from '../../src/solver/modules';
import type { ResearchWorker } from '../../src/solver/modules/organization';
import type { WorkerAccess } from '../../src/solver/research';

type Input = ConstructorParameters<typeof CooperativeResearch>[0];

/** Access for every worker with an empty environment and a shared retrieval root. */
export function workerAccess(workers: readonly ResearchWorker[], retrievalRoot: string): Map<string, WorkerAccess> {
  return new Map(workers.map(worker => [worker.id, { environment: {}, retrievalRoot }]));
}

/**
 * CooperativeResearch with fixture defaults: shared-root access, a fresh signal, no-op save and emit,
 * the direct modules and an inline exclusive check. Any field in `input` replaces its default.
 */
export function cooperativeResearch(input: Pick<Input, 'state' | 'workers'> & Partial<Input> & { retrievalRoot: string }): CooperativeResearch {
  const { retrievalRoot, ...rest } = input;
  return new CooperativeResearch({ access: workerAccess(input.workers, retrievalRoot),
    signal: new AbortController().signal, save: () => {}, emit: () => {}, modules: directSolverModules,
    exclusiveCheck: async check => check(), ...rest });
}
