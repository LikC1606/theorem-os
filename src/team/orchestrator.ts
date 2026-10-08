/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

import { isTeamRunAckPersisted, type ITeamRunAck } from "../common/types/team/teamTypes";
import {
  canonicalResearchTeamIdempotencyKey,
  normalizeResearchTeamOpaqueId,
} from "../common/types/team/researchTeamIdentity";
import type { ResearchCoreRunState, ResearchCoreTeamClient } from "./coreTeamClient";
import { TEAM_WAIT_MAX_SECONDS, normalizeTeamWaitSeconds } from "../common/types/team/teamWaitPolicy";
export { ResearchTeamEventStream } from "./coreTeamEvents";
export type { ResearchTeamStreamInvalidation, ResearchTeamCoreEvent } from "./coreTeamEvents";

export type ResearchTeamDispatchRequest<TAssignment> = Readonly<{
  targetSlotId: string;
  assignment: TAssignment;
  idempotencyKey: string;
}>;

export type ResearchTeamStatusRequest = Readonly<{
  waitSeconds?: number;
  targetSlotIds?: readonly string[];
}>;

export type ResearchTeamPreparedDispatch<TDetail = unknown> = Readonly<{
  message: string;
  detail: TDetail;
  /** Bind the target agent runtime to an isolated artifact worktree before enqueue. */
  dispatchWorkspace?: string;
}>;

export type ResearchTeamRuntime<TContext> = Readonly<{
  teamId: string;
  coordinatorSlotId?: string;
  reasoningConcurrency: number;
  client: ResearchCoreTeamClient;
  context: TContext;
  /** Synchronous host precondition at queue/effect boundaries, not a Core turn-start guarantee. */
  assertExecutionAllowed?: () => void;
  signal?: AbortSignal;
  sleep?: (milliseconds: number, signal?: AbortSignal) => Promise<void>;
}>;

export type ResearchTeamDispatchEvent<TInput, TValidated, TPrepared> =
  | Readonly<{
      kind: 'dispatch.accepted';
      request: ResearchTeamDispatchRequest<TInput>;
      validated: TValidated;
      prepared: ResearchTeamPreparedDispatch<TPrepared>;
      state: ResearchCoreRunState;
      acknowledgement: ITeamRunAck;
    }>
  | Readonly<{
      kind: 'dispatch.target-busy';
      request: ResearchTeamDispatchRequest<TInput>;
      validated: TValidated;
      state: ResearchCoreRunState;
    }>
  | Readonly<{
      kind: 'dispatch.capacity';
      request: ResearchTeamDispatchRequest<TInput>;
      validated: TValidated;
      state: ResearchCoreRunState;
      activeWorkerSlotIds: readonly string[];
    }>
  | Readonly<{
      kind: 'dispatch.error';
      request: ResearchTeamDispatchRequest<TInput>;
      code: string;
      message: string;
      retryable: boolean;
    }>;

export type ResearchTeamStatusEvent =
  | Readonly<{
      kind: 'status.observed';
      request: ResearchTeamStatusRequest;
      initialState: ResearchCoreRunState;
      state: ResearchCoreRunState;
      selectedSlotIds: readonly string[];
      structuralStallSlotIds?: readonly string[];
      changed: boolean;
    }>
  | Readonly<{
      kind: 'status.error';
      request: ResearchTeamStatusRequest;
      code: string;
      message: string;
      retryable: boolean;
    }>;

export type ResearchTeamIntegrationEvent<TInput, TIntegration> =
  | Readonly<{
      kind: 'integration.accepted';
      request: TInput;
      integration: TIntegration;
    }>
  | Readonly<{
      kind: 'integration.error';
      request: TInput;
      code: string;
      message: string;
      retryable: boolean;
    }>;

export type ResearchTeamOrchestrationEvent<TDispatchInput, TValidated, TPrepared, TIntegrateInput, TIntegration> =
  | ResearchTeamDispatchEvent<TDispatchInput, TValidated, TPrepared>
  | ResearchTeamStatusEvent
  | ResearchTeamIntegrationEvent<TIntegrateInput, TIntegration>;

export type ResearchTeamOrchestratorHooks<
  TDispatchInput,
  TValidated,
  TPrepared,
  TIntegrateInput,
  TIntegration,
  TContext,
  TOutput,
> = Readonly<{
  validateAssignment: (
    request: ResearchTeamDispatchRequest<TDispatchInput>,
    runtime: ResearchTeamRuntime<TContext>
  ) => TValidated | Promise<TValidated>;
  prepare: (
    request: ResearchTeamDispatchRequest<TDispatchInput>,
    validated: TValidated,
    runtime: ResearchTeamRuntime<TContext>
  ) => ResearchTeamPreparedDispatch<TPrepared> | Promise<ResearchTeamPreparedDispatch<TPrepared>>;
  /** Best-effort cleanup for resources created by prepare when dispatch fails. */
  discardPrepared?: (
    request: ResearchTeamDispatchRequest<TDispatchInput>,
    validated: TValidated,
    prepared: ResearchTeamPreparedDispatch<TPrepared>,
    runtime: ResearchTeamRuntime<TContext>
  ) => void | Promise<void>;
  integrate: (input: TIntegrateInput, runtime: ResearchTeamRuntime<TContext>) => TIntegration | Promise<TIntegration>;
  present: (
    event: ResearchTeamOrchestrationEvent<TDispatchInput, TValidated, TPrepared, TIntegrateInput, TIntegration>,
    runtime: ResearchTeamRuntime<TContext>
  ) => TOutput | Promise<TOutput>;
}>;

export type ResearchTeamOrchestrator<
  TDispatchInput,
  TValidated,
  TPrepared,
  TIntegrateInput,
  TIntegration,
  TContext,
  TOutput,
> = Readonly<{
  dispatch: (
    request: ResearchTeamDispatchRequest<TDispatchInput>,
    runtime: ResearchTeamRuntime<TContext>
  ) => Promise<TOutput>;
  dispatchMany: (
    requests: readonly ResearchTeamDispatchRequest<TDispatchInput>[],
    runtime: ResearchTeamRuntime<TContext>
  ) => Promise<readonly TOutput[]>;
  status: (request: ResearchTeamStatusRequest, runtime: ResearchTeamRuntime<TContext>) => Promise<TOutput>;
  statusMany: (
    requests: readonly ResearchTeamStatusRequest[],
    runtime: ResearchTeamRuntime<TContext>
  ) => Promise<readonly TOutput[]>;
  integrate: (input: TIntegrateInput, runtime: ResearchTeamRuntime<TContext>) => Promise<TOutput>;
  integrateMany: (
    inputs: readonly TIntegrateInput[],
    runtime: ResearchTeamRuntime<TContext>
  ) => Promise<readonly TOutput[]>;
}>;

export class ResearchTeamOrchestrationError extends Error {
  readonly code: string;
  readonly retryable: boolean;

  constructor(code: string, message: string, retryable = false) {
    super(message);
    this.name = 'ResearchTeamOrchestrationError';
    this.code = code;
    this.retryable = retryable;
  }
}

const DEFAULT_STATUS_POLL_MAX_DELAY_MS = 5_000;

export function createResearchTeamOrchestrator<
  TDispatchInput,
  TValidated,
  TPrepared,
  TIntegrateInput,
  TIntegration,
  TContext,
  TOutput,
>(
  hooks: ResearchTeamOrchestratorHooks<
    TDispatchInput,
    TValidated,
    TPrepared,
    TIntegrateInput,
    TIntegration,
    TContext,
    TOutput
  >,
  options: Readonly<{
    idempotencyRetentionMs?: number;
    maximumWaitSeconds?: number;
    statusPollMaxDelayMs?: number;
  }> = {}
): ResearchTeamOrchestrator<TDispatchInput, TValidated, TPrepared, TIntegrateInput, TIntegration, TContext, TOutput> {
  const queues = new Map<string, Promise<void>>();
  const dispatches = new Map<string, Promise<TOutput>>();
  const structuralStallNotices = new Set<string>();
  const structuralStallEscalationNotices = new Set<string>();
  const idempotencyRetentionMs = normalizeNonnegativeInteger(options.idempotencyRetentionMs, 60_000);
  const maximumWaitSeconds = Math.min(
    TEAM_WAIT_MAX_SECONDS,
    normalizeNonnegativeInteger(options.maximumWaitSeconds, TEAM_WAIT_MAX_SECONDS)
  );
  const statusPollMaxDelayMs = Math.max(
    1_000,
    normalizePositiveInteger(options.statusPollMaxDelayMs, DEFAULT_STATUS_POLL_MAX_DELAY_MS)
  );

  const enqueue = <T>(teamId: string, operation: () => Promise<T>): Promise<T> => {
    const stableTeamId = stableId(teamId, 'team_id');
    const previous = queues.get(stableTeamId) ?? Promise.resolve();
    const current = previous.then(operation, operation);
    const tail = current.then(
      (): void => undefined,
      (): void => undefined
    );
    queues.set(stableTeamId, tail);
    void tail.then(() => {
      if (queues.get(stableTeamId) === tail) queues.delete(stableTeamId);
    });
    return current;
  };

  const dispatch = (
    request: ResearchTeamDispatchRequest<TDispatchInput>,
    runtime: ResearchTeamRuntime<TContext>
  ): Promise<TOutput> => {
    const teamId = stableId(runtime.teamId, 'team_id');
    const idempotencyKey = normalizeResearchTeamOpaqueId(request.idempotencyKey, 'idempotency_key');
    const targetSlotId = stableId(request.targetSlotId, 'target_slot_id');
    const normalizedRequest = Object.freeze({ ...request, idempotencyKey, targetSlotId });
    const cacheKey = `${teamId}:${targetSlotId}:${canonicalResearchTeamIdempotencyKey(idempotencyKey)}`;
    const cached = dispatches.get(cacheKey);
    if (cached) return cached;

    let retainIdempotencyReceipt = true;
    const pending = enqueue(teamId, async () => {
      let preparedForCleanup: ResearchTeamPreparedDispatch<TPrepared> | undefined;
      let validatedForCleanup: TValidated | undefined;
      let acceptedByCore = false;
      let dispatchAttempted = false;
      try {
        runtime.assertExecutionAllowed?.();
        const validated = await hooks.validateAssignment(normalizedRequest, runtime);
        validatedForCleanup = validated;
        runtime.assertExecutionAllowed?.();
        await runtime.client.ensureSession?.(teamId, runtime.signal);
        const state = await runtime.client.readRunState(teamId, runtime.signal);
        runtime.assertExecutionAllowed?.();
        const targetIsActive = state.activeSlotIds.includes(targetSlotId);
        const runLevelActivity = runLevelActivityCount(state);
        const activeWorkerSlotIds = state.activeSlotIds.filter((slotId) => slotId !== runtime.coordinatorSlotId);
        const targetSlot = state.slots.find((slot) => slot.slotId === targetSlotId);
        // Core can durably accept a message while a dormant runtime is still
        // starting. Such a slot is not in activeSlotIds yet, but it is already
        // occupied by the queued assignment and must not receive a duplicate.
        const targetHasPendingWork = Boolean(
          targetSlot &&
          (targetIsActive ||
            targetSlot.queuedForegroundCount > 0 ||
            targetSlot.queuedBackgroundCount > 0 ||
            targetSlot.pendingWakeCount > 0)
        );
        if (
          targetHasPendingWork &&
          targetSlot &&
          targetSlot.queuedForegroundCount + targetSlot.queuedBackgroundCount + targetSlot.pendingWakeCount > 0
        ) {
          retainIdempotencyReceipt = false;
          return await hooks.present(
            { kind: 'dispatch.target-busy', request: normalizedRequest, validated, state },
            runtime
          );
        }
        if (
          !targetIsActive &&
          Math.max(activeWorkerSlotIds.length, runLevelActivity > 0 ? 1 : 0) >=
            normalizePositiveInteger(runtime.reasoningConcurrency, 1)
        ) {
          retainIdempotencyReceipt = false;
          return await hooks.present(
            {
              kind: 'dispatch.capacity',
              request: normalizedRequest,
              validated,
              state,
              activeWorkerSlotIds: Object.freeze(activeWorkerSlotIds),
            },
            runtime
          );
        }
        // Core owns a durable per-slot queue. Enqueueing for an active Worker
        // preserves the assignment until its current turn ends; returning a
        // transient target-busy result here can strand the Lead with no wake.
        const prepared = await hooks.prepare(normalizedRequest, validated, runtime);
        preparedForCleanup = prepared;
        const message = prepared.message.trim();
        if (!message) throw new ResearchTeamOrchestrationError('empty_assignment', 'Prepared assignment is empty');
        // Once the POST crosses the Core boundary, an absent or malformed
        // response is ambiguous: the turn may already be queued or complete.
        // Never destroy the prepared worktree based only on a later idle
        // snapshot; reconciliation must resolve the idempotency identity.
        runtime.assertExecutionAllowed?.();
        dispatchAttempted = true;
        const acknowledgement = await runtime.client.dispatch(
          teamId,
          targetSlotId,
          message,
          runtime.signal,
          idempotencyKey,
          prepared.dispatchWorkspace
        );
        if (
          acknowledgement.team_id !== teamId ||
          acknowledgement.target_slot_id !== targetSlotId ||
          acknowledgement.accepted_slot_id !== targetSlotId ||
          acknowledgement.accepted_role !== 'teammate'
        ) {
          throw new ResearchTeamOrchestrationError(
            'acknowledgement_mismatch',
            'Core accepted the assignment for an unexpected Team slot.'
          );
        }
        if (!isTeamRunAckPersisted(acknowledgement)) {
          throw new ResearchTeamOrchestrationError(
            'dispatch_not_persisted',
            'Core did not persist the Research Team assignment.',
            true
          );
        }
        acceptedByCore = true;
        return await hooks.present(
          {
            kind: 'dispatch.accepted',
            request: normalizedRequest,
            validated,
            prepared,
            state,
            acknowledgement,
          },
          runtime
        );
      } catch (error) {
        // A transport failure can happen after Core durably enqueues the
        // assignment but before the acknowledgement reaches us.  Never delete
        // a prepared worktree until a follow-up state read proves that the
        // target slot has no queued/active work.
        let coreMayHaveAccepted = acceptedByCore;
        if (!coreMayHaveAccepted && preparedForCleanup && !dispatchAttempted) {
          try {
            const observed = await runtime.client.readRunState(teamId, runtime.signal);
            const target = observed.slots.find((slot) => slot.slotId === targetSlotId);
            coreMayHaveAccepted = Boolean(
              target &&
              (observed.activeSlotIds.includes(targetSlotId) ||
                target.queuedForegroundCount > 0 ||
                target.queuedBackgroundCount > 0 ||
                target.pendingWakeCount > 0)
            );
          } catch {
            // Unknown transport state is deliberately treated as ambiguous.
            coreMayHaveAccepted = true;
          }
        }
        if (
          !coreMayHaveAccepted &&
          !dispatchAttempted &&
          preparedForCleanup &&
          validatedForCleanup &&
          hooks.discardPrepared
        ) {
          try {
            await hooks.discardPrepared(normalizedRequest, validatedForCleanup, preparedForCleanup, runtime);
          } catch {
            // Preserve the original dispatch error; cleanup is best effort.
          }
        }
        retainIdempotencyReceipt = false;
        const normalized = normalizeError(error, 'dispatch_failed', true);
        return await hooks.present(
          {
            kind: 'dispatch.error',
            request: normalizedRequest,
            ...normalized,
          },
          runtime
        );
      }
    });

    const scheduleExpiry = (): void => {
      if (!retainIdempotencyReceipt) {
        if (dispatches.get(cacheKey) === pending) dispatches.delete(cacheKey);
        return;
      }
      const timer = setTimeout(() => {
        if (dispatches.get(cacheKey) === pending) dispatches.delete(cacheKey);
      }, idempotencyRetentionMs);
      timer.unref?.();
    };
    dispatches.set(cacheKey, pending);
    void pending.then(scheduleExpiry, scheduleExpiry);
    return pending;
  };

  /**
   * A Lead wave is already a bounded set of independent assignments. Keep the
   * Team queue around the whole wave for cross-wave ordering, but do not
   * serialize the independent Core sends inside it.
   */
  const dispatchWave = async (
    requests: readonly ResearchTeamDispatchRequest<TDispatchInput>[],
    runtime: ResearchTeamRuntime<TContext>
  ): Promise<readonly TOutput[]> => {
    if (!requests.length) return Object.freeze([]);
    const teamId = stableId(runtime.teamId, 'team_id');
    const results: Promise<TOutput>[] = [];
    const fresh: Array<{
      request: ResearchTeamDispatchRequest<TDispatchInput>;
      cacheKey: string;
      pending: Promise<TOutput>;
      resolve: (value: TOutput) => void;
      reject: (reason?: unknown) => void;
      settled: boolean;
      retain: boolean;
    }> = [];

    for (const request of requests) {
      const idempotencyKey = normalizeResearchTeamOpaqueId(request.idempotencyKey, 'idempotency_key');
      const targetSlotId = stableId(request.targetSlotId, 'target_slot_id');
      const normalizedRequest = Object.freeze({ ...request, idempotencyKey, targetSlotId });
      const cacheKey = teamId + ':' + targetSlotId + ':' + canonicalResearchTeamIdempotencyKey(idempotencyKey);
      const cached = dispatches.get(cacheKey);
      if (cached) {
        results.push(cached);
        continue;
      }
      let resolvePending!: (value: TOutput) => void;
      let rejectPending!: (reason?: unknown) => void;
      const pending = new Promise<TOutput>((resolve, reject) => {
        resolvePending = resolve;
        rejectPending = reject;
      });
      dispatches.set(cacheKey, pending);
      results.push(pending);
      fresh.push({
        request: normalizedRequest,
        cacheKey,
        pending,
        resolve: resolvePending,
        reject: rejectPending,
        settled: false,
        retain: true,
      });
    }
    if (!fresh.length) return await Promise.all(results);

    const finish = async (
      entry: (typeof fresh)[number],
      event: ResearchTeamOrchestrationEvent<TDispatchInput, TValidated, TPrepared, TIntegrateInput, TIntegration>,
      retain: boolean
    ): Promise<void> => {
      if (entry.settled) return;
      entry.retain = retain;
      try {
        entry.settled = true;
        entry.resolve(await hooks.present(event, runtime));
      } catch (error) {
        entry.retain = false;
        entry.settled = true;
        entry.reject(error);
      }
    };
    const finishError = async (entry: (typeof fresh)[number], error: unknown, retryable = true): Promise<void> => {
      const normalized = normalizeError(error, 'dispatch_failed', retryable);
      await finish(
        entry,
        {
          kind: 'dispatch.error',
          request: entry.request,
          ...normalized,
        },
        false
      );
    };
    const releaseExpired = (entry: (typeof fresh)[number]): void => {
      if (!entry.retain) {
        if (dispatches.get(entry.cacheKey) === entry.pending) dispatches.delete(entry.cacheKey);
        return;
      }
      const timer = setTimeout(() => {
        if (dispatches.get(entry.cacheKey) === entry.pending) dispatches.delete(entry.cacheKey);
      }, idempotencyRetentionMs);
      timer.unref?.();
    };

    void enqueue(teamId, async () => {
      runtime.assertExecutionAllowed?.();
      const validated = await Promise.all(
        fresh.map(async (entry) => {
          try {
            return { entry, value: await hooks.validateAssignment(entry.request, runtime) };
          } catch (error) {
            await finishError(entry, error, false);
            return { entry, error };
          }
        })
      );
      const valid = validated.flatMap((item) =>
        'value' in item ? [{ entry: item.entry, value: item.value as TValidated }] : []
      );
      if (!valid.length) return;

      let state: ResearchCoreRunState;
      try {
        runtime.assertExecutionAllowed?.();
        await runtime.client.ensureSession?.(teamId, runtime.signal);
        state = await runtime.client.readRunState(teamId, runtime.signal);
        runtime.assertExecutionAllowed?.();
      } catch (error) {
        await Promise.all(valid.map(({ entry }) => finishError(entry, error, true)));
        return;
      }

      const runLevelActivity = runLevelActivityCount(state);
      const activeWorkerSlotIds = state.activeSlotIds.filter((slotId) => slotId !== runtime.coordinatorSlotId);
      const concurrency = normalizePositiveInteger(runtime.reasoningConcurrency, 1);
      let reservedIdleSlots = 0;
      const reservedTargetSlots = new Set<string>();
      const accepted: Array<{ entry: (typeof fresh)[number]; value: TValidated }> = [];
      const capacity: Array<{ entry: (typeof fresh)[number]; value: TValidated }> = [];
      for (const { entry, value } of valid) {
        const targetIsActive = state.activeSlotIds.includes(entry.request.targetSlotId);
        const targetSlot = state.slots.find((slot) => slot.slotId === entry.request.targetSlotId);
        const targetHasPendingWork = Boolean(
          targetSlot &&
          (targetIsActive ||
            targetSlot.queuedForegroundCount > 0 ||
            targetSlot.queuedBackgroundCount > 0 ||
            targetSlot.pendingWakeCount > 0)
        );
        if (
          reservedTargetSlots.has(entry.request.targetSlotId) ||
          (targetHasPendingWork &&
            targetSlot !== undefined &&
            targetSlot.queuedForegroundCount + targetSlot.queuedBackgroundCount + targetSlot.pendingWakeCount > 0)
        ) {
          await finish(entry, { kind: 'dispatch.target-busy', request: entry.request, validated: value, state }, false);
          continue;
        }
        if (
          !targetIsActive &&
          Math.max(activeWorkerSlotIds.length, runLevelActivity > 0 ? 1 : 0) + reservedIdleSlots >= concurrency
        ) {
          capacity.push({ entry, value });
          continue;
        }
        if (!targetIsActive) reservedIdleSlots += 1;
        reservedTargetSlots.add(entry.request.targetSlotId);
        accepted.push({ entry, value });
      }
      await Promise.all(
        capacity.map(({ entry, value }) =>
          finish(
            entry,
            {
              kind: 'dispatch.capacity',
              request: entry.request,
              validated: value,
              state,
              activeWorkerSlotIds: Object.freeze(activeWorkerSlotIds),
            },
            false
          )
        )
      );

      const prepared = await Promise.all(
        accepted.map(async ({ entry, value }) => {
          try {
            runtime.assertExecutionAllowed?.();
            return { entry, value, prepared: await hooks.prepare(entry.request, value, runtime) };
          } catch (error) {
            await finishError(entry, error, true);
            return undefined;
          }
        })
      );
      const ready = prepared.filter(
        (
          item
        ): item is {
          entry: (typeof fresh)[number];
          value: TValidated;
          prepared: ResearchTeamPreparedDispatch<TPrepared>;
        } => Boolean(item)
      );
      await Promise.all(
        ready.map(async ({ entry, value, prepared: preparedDispatch }) => {
          let acceptedByCore = false;
          let dispatchAttempted = false;
          try {
            const message = preparedDispatch.message.trim();
            if (!message) throw new ResearchTeamOrchestrationError('empty_assignment', 'Prepared assignment is empty');
            runtime.assertExecutionAllowed?.();
            dispatchAttempted = true;
            const acknowledgement = await runtime.client.dispatch(
              teamId,
              entry.request.targetSlotId,
              message,
              runtime.signal,
              entry.request.idempotencyKey,
              preparedDispatch.dispatchWorkspace
            );
            if (
              acknowledgement.team_id !== teamId ||
              acknowledgement.target_slot_id !== entry.request.targetSlotId ||
              acknowledgement.accepted_slot_id !== entry.request.targetSlotId ||
              acknowledgement.accepted_role !== 'teammate'
            ) {
              throw new ResearchTeamOrchestrationError(
                'acknowledgement_mismatch',
                'Core accepted the assignment for an unexpected Team slot.'
              );
            }
            if (!isTeamRunAckPersisted(acknowledgement)) {
              throw new ResearchTeamOrchestrationError(
                'dispatch_not_persisted',
                'Core did not persist the Research Team assignment.',
                true
              );
            }
            acceptedByCore = true;
            await finish(
              entry,
              {
                kind: 'dispatch.accepted',
                request: entry.request,
                validated: value,
                prepared: preparedDispatch,
                state,
                acknowledgement,
              },
              true
            );
          } catch (error) {
            let coreMayHaveAccepted = acceptedByCore;
            if (!coreMayHaveAccepted && !dispatchAttempted && hooks.discardPrepared) {
              // A Core dispatch that was attempted but did not return a
              // durable ACK is ambiguous even when the immediate state read
              // is idle (the child may have completed between the two reads).
              // Keep the prepared artifact for receipt reconciliation.
              try {
                const observed = await runtime.client.readRunState(teamId, runtime.signal);
                const target = observed.slots.find((slot) => slot.slotId === entry.request.targetSlotId);
                coreMayHaveAccepted = Boolean(
                  target &&
                  (observed.activeSlotIds.includes(entry.request.targetSlotId) ||
                    target.queuedForegroundCount > 0 ||
                    target.queuedBackgroundCount > 0 ||
                    target.pendingWakeCount > 0)
                );
              } catch {
                // A lost ACK with an unavailable state read is ambiguous. Keep
                // the worktree so a later reconciliation can recover it.
                coreMayHaveAccepted = true;
              }
            }
            if (!coreMayHaveAccepted && !dispatchAttempted && hooks.discardPrepared) {
              try {
                await hooks.discardPrepared(entry.request, value, preparedDispatch, runtime);
              } catch {
                // Preserve the original dispatch error; cleanup is best effort.
              }
            }
            await finishError(entry, error, true);
          }
        })
      );
    }).catch(async (error) => {
      await Promise.all(fresh.map((entry) => finishError(entry, error, true)));
    });

    try {
      return await Promise.all(results);
    } finally {
      for (const entry of fresh) releaseExpired(entry);
    }
  };

  const statusManyWave = async (
    requests: readonly ResearchTeamStatusRequest[],
    runtime: ResearchTeamRuntime<TContext>
  ): Promise<readonly TOutput[]> => {
    if (!requests.length) return Object.freeze([]);
    const sleep = runtime.sleep ?? abortableSleep;
    type StatusEntry = {
      request: ResearchTeamStatusRequest;
      targetSlotIds?: readonly string[];
      waitSeconds?: number;
      normalizedRequest?: ResearchTeamStatusRequest;
      error?: Readonly<{ code: string; message: string; retryable: boolean }>;
    };
    const entries: StatusEntry[] = requests.map((request) => {
      try {
        const targetSlotIds = normalizeTargetSlotIds(request.targetSlotIds);
        const waitSeconds = Math.min(maximumWaitSeconds, normalizeTeamWaitSeconds(request.waitSeconds));
        return {
          request,
          targetSlotIds,
          waitSeconds,
          normalizedRequest: Object.freeze({ ...request, waitSeconds, targetSlotIds }),
        };
      } catch (error) {
        return { request, error: normalizeError(error, 'status_failed', true) };
      }
    });
    const valid = entries.filter(
      (
        entry
      ): entry is StatusEntry & {
        targetSlotIds: readonly string[];
        waitSeconds: number;
        normalizedRequest: ResearchTeamStatusRequest;
      } => entry.normalizedRequest !== undefined && entry.targetSlotIds !== undefined && entry.waitSeconds !== undefined
    );

    let teamId: string;
    try {
      teamId = stableId(runtime.teamId, 'team_id');
    } catch (error) {
      const normalized = normalizeError(error, 'status_failed', true);
      return await Promise.all(
        requests.map((request) => hooks.present({ kind: 'status.error', request, ...normalized }, runtime))
      );
    }

    let initialState: ResearchCoreRunState | undefined;
    let state: ResearchCoreRunState | undefined;
    try {
      if (valid.length) {
        // A status request is also a valid recovery entry point after Core
        // restarts. The concrete client deduplicates this idempotent restore.
        runtime.assertExecutionAllowed?.();
        await runtime.client.ensureSession?.(teamId, runtime.signal);
        initialState = await runtime.client.readRunState(teamId, runtime.signal);
        state = initialState;
      }
    } catch (error) {
      const normalized = normalizeError(error, 'status_failed', true);
      return await Promise.all(
        entries.map((entry) =>
          hooks.present(
            {
              kind: 'status.error',
              request: entry.request,
              ...('error' in entry && entry.error ? entry.error : normalized),
            },
            runtime
          )
        )
      );
    }

    const completed = new Map<number, { state: ResearchCoreRunState; changed: boolean }>();
    const statusErrors = new Map<number, Readonly<{ code: string; message: string; retryable: boolean }>>();
    const initialSignatures = new Map<number, string>();
    entries.forEach((entry, index) => {
      if (entry.error) statusErrors.set(index, entry.error);
    });
    if (initialState && state) {
      valid.forEach((entry) => {
        const originalIndex = entries.indexOf(entry);
        const initialSignature = runStateSignature(initialState, entry.targetSlotIds);
        // A bounded wait only makes sense while the selected target has work
        // in Core. If it is already idle or terminal, waiting cannot produce
        // a useful transition and would strand the Lead for the full window.
        if (entry.waitSeconds === 0 || !hasActiveTarget(initialState, entry.targetSlotIds)) {
          completed.set(originalIndex, { state: initialState, changed: false });
        } else {
          initialSignatures.set(originalIndex, initialSignature);
        }
      });

      const maxWaitSeconds = Math.max(...valid.map((entry) => entry.waitSeconds), 0);
      const pending = valid.filter((entry) => entry.waitSeconds > 0);
      const maxWaitMs = maxWaitSeconds * 1_000;
      let elapsedMs = 0;
      let pollIndex = 0;
      while (
        elapsedMs < maxWaitMs &&
        pending.some((entry) => {
          const index = entries.indexOf(entry);
          return !completed.has(index) && !statusErrors.has(index);
        })
      ) {
        const delayMs = Math.min(statusPollDelayMs(pollIndex, statusPollMaxDelayMs), maxWaitMs - elapsedMs);
        try {
          await sleep(delayMs, runtime.signal);
          elapsedMs += delayMs;
          state = await runtime.client.readRunState(teamId, runtime.signal);
        } catch (error) {
          const normalized = normalizeError(error, 'status_failed', true);
          for (const entry of pending) {
            const index = entries.indexOf(entry);
            if (!completed.has(index)) statusErrors.set(index, normalized);
          }
          break;
        }
        pollIndex += 1;
        for (const entry of pending) {
          const originalIndex = entries.indexOf(entry);
          if (completed.has(originalIndex) || statusErrors.has(originalIndex)) continue;
          const changed = runStateSignature(state, entry.targetSlotIds) !== initialSignatures.get(originalIndex);
          if (changed || elapsedMs >= entry.waitSeconds * 1_000) completed.set(originalIndex, { state, changed });
        }
      }
    }

    return await Promise.all(
      entries.map((entry, index) => {
        const error = statusErrors.get(index);
        if (error) return hooks.present({ kind: 'status.error', request: entry.request, ...error }, runtime);
        const observed = completed.get(index);
        if (!observed || !entry.normalizedRequest || !initialState || !entry.targetSlotIds) {
          return hooks.present(
            {
              kind: 'status.error',
              request: entry.request,
              code: 'status_failed',
              message: 'Core did not produce a complete Team status snapshot.',
              retryable: true,
            },
            runtime
          );
        }
        const activeTurnKeys = new Set(
          observed.state.slots.filter((slot) => slot.activeTurnId).map((slot) => `${slot.slotId}:${slot.activeTurnId}`)
        );
        for (const key of structuralStallNotices) {
          if (!activeTurnKeys.has(key)) structuralStallNotices.delete(key);
        }
        for (const key of structuralStallEscalationNotices) {
          if (!activeTurnKeys.has(key.replace(/:escalation$/u, ''))) structuralStallEscalationNotices.delete(key);
        }
        const structuralStallSlotIds = observed.state.slots
          .filter(
            (slot) =>
              entry.targetSlotIds.includes(slot.slotId) &&
              slot.state === 'running' &&
              slot.activeTurnSlow === true &&
              slot.activeTurnSlowThresholdMs !== undefined &&
              (slot.activeTurnElapsedMs ?? 0) >= slot.activeTurnSlowThresholdMs
          )
          .filter((slot) => {
            const key = `${slot.slotId}:${slot.activeTurnId ?? ''}`;
            const elapsed = slot.activeTurnElapsedMs ?? 0;
            const threshold = slot.activeTurnSlowThresholdMs ?? Number.POSITIVE_INFINITY;
            if (elapsed >= threshold * 2) {
              const escalationKey = `${key}:escalation`;
              if (structuralStallEscalationNotices.has(escalationKey)) return false;
              structuralStallEscalationNotices.add(escalationKey);
              return true;
            }
            if (structuralStallNotices.has(key)) return false;
            structuralStallNotices.add(key);
            return true;
          })
          .map((slot) => slot.slotId);
        return hooks.present(
          {
            kind: 'status.observed',
            request: entry.normalizedRequest,
            initialState,
            state: observed.state,
            selectedSlotIds: entry.targetSlotIds,
            structuralStallSlotIds,
            changed: observed.changed,
          },
          runtime
        );
      })
    );
  };

  const status = async (
    request: ResearchTeamStatusRequest,
    runtime: ResearchTeamRuntime<TContext>
  ): Promise<TOutput> => {
    const [result] = await statusManyWave([request], runtime);
    return result;
  };

  const runIntegration = async (input: TIntegrateInput, runtime: ResearchTeamRuntime<TContext>): Promise<TOutput> => {
    try {
      runtime.assertExecutionAllowed?.();
      const integration = await hooks.integrate(input, runtime);
      return await hooks.present({ kind: 'integration.accepted', request: input, integration }, runtime);
    } catch (error) {
      const normalized = normalizeError(error, 'integration_failed', false);
      return await hooks.present({ kind: 'integration.error', request: input, ...normalized }, runtime);
    }
  };
  const integrate = (input: TIntegrateInput, runtime: ResearchTeamRuntime<TContext>): Promise<TOutput> =>
    enqueue(runtime.teamId, () => runIntegration(input, runtime));

  const isAdvisoryIntegration = (input: TIntegrateInput): boolean => {
    if (!input || typeof input !== 'object') return false;
    const value = input as Record<string, unknown>;
    const result = value.result;
    return (
      value.executionMode === 'advisory' ||
      (typeof result === 'object' &&
        result !== null &&
        (result as Record<string, unknown>).executionMode === 'advisory')
    );
  };

  return Object.freeze({
    dispatch,
    dispatchMany: dispatchWave,
    status,
    statusMany: statusManyWave,
    integrate,
    integrateMany: async (inputs, runtime) => {
      const outputs = Array<TOutput | undefined>(inputs.length);
      const advisory = inputs
        .map((input, index) => ({ input, index }))
        .filter(({ input }) => isAdvisoryIntegration(input));
      // Advisory integrations do not touch a branch/worktree and can safely
      // overlap. Artifact integrations stay in one Team queue because Git
      // checkout/merge is inherently serialized per project.
      await Promise.all(
        advisory.map(async ({ input, index }) => {
          outputs[index] = await runIntegration(input, runtime);
        })
      );
      const artifact = inputs
        .map((input, index) => ({ input, index }))
        .filter(({ input }) => !isAdvisoryIntegration(input));
      if (artifact.length > 0) {
        await enqueue(runtime.teamId, async () => {
          for (const { input, index } of artifact) {
            outputs[index] = await runIntegration(input, runtime);
          }
        });
      }
      return outputs as readonly TOutput[];
    },
  });
}

function normalizeError(
  error: unknown,
  fallbackCode: string,
  fallbackRetryable: boolean
): Readonly<{ code: string; message: string; retryable: boolean }> {
  if (error instanceof ResearchTeamOrchestrationError) {
    return Object.freeze({ code: error.code, message: error.message, retryable: error.retryable });
  }
  return Object.freeze({
    code: fallbackCode,
    message: error instanceof Error ? error.message : String(error),
    retryable: fallbackRetryable,
  });
}

function runStateSignature(state: ResearchCoreRunState, targetSlotIds: readonly string[]): string {
  const runSignature = [
    state.runStatus ?? '',
    state.teamRunId ?? '',
    state.queuedIntentCount ?? 0,
    state.startingBatchCount ?? 0,
    state.runningBatchCount ?? 0,
    state.activeEnqueueLeaseCount ?? 0,
  ].join(':');
  const slotSignature = state.slots
    .filter((slot) => !targetSlotIds.length || targetSlotIds.includes(slot.slotId))
    .map(
      (slot) =>
        `${slot.slotId}:${slot.state}:${slot.queuedForegroundCount}:${slot.queuedBackgroundCount}:${slot.pendingWakeCount}:${slot.activeTurnId ?? ''}:${slot.activeTurnSlow ?? false}:${slot.blockedReason ?? ''}:${slot.runtimeHealth ?? ''}`
    )
    .join('|');
  return `${runSignature}|${slotSignature}`;
}

function runLevelActivityCount(state: ResearchCoreRunState): number {
  return Math.max(
    0,
    state.queuedIntentCount ?? 0,
    state.startingBatchCount ?? 0,
    state.runningBatchCount ?? 0,
    state.activeEnqueueLeaseCount ?? 0
  );
}

function hasActiveTarget(state: ResearchCoreRunState, targetSlotIds: readonly string[]): boolean {
  const targetIds = targetSlotIds.length ? new Set(targetSlotIds) : undefined;
  const activeSlotTarget = state.slots.some((slot) => {
    if (targetIds && !targetIds.has(slot.slotId)) return false;
    return (
      state.activeSlotIds.includes(slot.slotId) ||
      slot.queuedForegroundCount > 0 ||
      slot.queuedBackgroundCount > 0 ||
      slot.pendingWakeCount > 0
    );
  });
  if (activeSlotTarget) return true;
  // Run-level counters cover the enqueue handoff before a slot projection is
  // updated. They are only attributable to a selected target when that target
  // is already part of the active run; otherwise a busy Lead must not strand a
  // Worker-only status request.
  // Run-level counters cover the enqueue handoff before slot projection is
  // updated. They are intentionally treated as activity for every target:
  // attributing them to a single slot caused status callers to observe an idle
  // Worker and dispatch a duplicate during the handoff window.
  return runLevelActivityCount(state) > 0;
}

function normalizeTargetSlotIds(values: readonly string[] | undefined): readonly string[] {
  if (!values?.length) return Object.freeze([]);
  return Object.freeze([...new Set(values.map((value) => stableId(value, 'target_slot_id')))]);
}

function normalizePositiveInteger(value: unknown, fallback: number): number {
  return Number.isSafeInteger(value) && Number(value) > 0 ? Number(value) : fallback;
}

function normalizeNonnegativeInteger(value: unknown, fallback: number): number {
  return Number.isSafeInteger(value) && Number(value) >= 0 ? Number(value) : fallback;
}

function statusPollDelayMs(pollIndex: number, maximumDelayMs: number): number {
  const normalizedIndex = normalizeNonnegativeInteger(pollIndex, 0);
  return Math.min(maximumDelayMs, 1_000 * 2 ** Math.min(normalizedIndex, 4));
}

function stableId(value: unknown, field: string): string {
  const normalized = String(value ?? '').trim();
  if (!/^[A-Za-z0-9][A-Za-z0-9._:-]{0,127}$/u.test(normalized)) throw new Error(`${field} is invalid`);
  return normalized;
}

function abortableSleep(milliseconds: number, signal?: AbortSignal): Promise<void> {
  return new Promise((resolve, reject) => {
    if (signal?.aborted) {
      reject(signal.reason ?? new Error('Research Team wait was cancelled'));
      return;
    }
    let timer: NodeJS.Timeout;
    let onAbort: () => void;
    const cleanup = () => {
      clearTimeout(timer);
      signal?.removeEventListener('abort', onAbort);
    };
    onAbort = () => {
      cleanup();
      reject(signal?.reason ?? new Error('Research Team wait was cancelled'));
    };
    timer = setTimeout(() => {
      cleanup();
      resolve();
    }, milliseconds);
    signal?.addEventListener('abort', onAbort, { once: true });
  });
}
