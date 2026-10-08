/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

import process from 'node:process';
import { fromBackendTeamRunAck } from "../common/adapter/teamMapper";
import type { ITeamRunAck, TeamSlotBlockedReason, TeamSlotWorkState } from "../common/types/team/teamTypes";
import { canonicalResearchTeamIdempotencyKey } from "../common/types/team/researchTeamIdentity";

export type ResearchCoreSlotState = Readonly<{
  slotId: string;
  state: TeamSlotWorkState;
  queuedForegroundCount: number;
  queuedBackgroundCount: number;
  pendingWakeCount: number;
  activeTurnId?: string;
  teamRunId?: string;
  activeTurnStartedAtMs?: number;
  activeTurnElapsedMs?: number;
  activeTurnSlow?: boolean;
  activeTurnSlowThresholdMs?: number;
  blockedReason?: TeamSlotBlockedReason;
  runtimeHealth?: 'disconnected' | 'unhealthy';
}>;

export type ResearchCoreRunState = Readonly<{
  teamId: string;
  teamRunId?: string;
  runStatus?: 'accepted' | 'running' | 'cancelling' | 'completed' | 'cancelled' | 'failed';
  sessionGeneration?: string;
  /** Run-level work counters cover the handoff window before slot_work updates. */
  queuedIntentCount?: number;
  startingBatchCount?: number;
  runningBatchCount?: number;
  activeEnqueueLeaseCount?: number;
  slots: readonly ResearchCoreSlotState[];
  activeSlotIds: readonly string[];
}>;

/** Background notifications do not retain a sealed proof's writer authority. */
export function isResearchSlotReadyForSuccessor(state: ResearchCoreRunState, teamId: string, slotId: string): boolean {
  const slot = state.slots.find((entry) => entry.slotId === slotId);
  return Boolean(
    state.teamId === teamId &&
    slot?.state === 'idle' &&
    !state.activeSlotIds.includes(slotId) &&
    !slot.activeTurnId &&
    !slot.blockedReason &&
    !slot.runtimeHealth &&
    slot.queuedForegroundCount === 0
  );
}

export type ResearchCoreAgentUsage = Readonly<{
  measurement: 'token_totals' | 'context_window';
  inputTokens: number;
  cachedInputTokens: number;
  outputTokens: number;
  reasoningOutputTokens: number;
  totalTokens: number;
  contextWindowSize?: number;
  cost?: number;
}>;

/** The model actually bound to a Core Team slot's assistant runtime. */
export type ResearchCoreAgentModel = Readonly<{
  model: string;
}>;

export type ResearchCoreTeamClient = Readonly<{
  ensureSession?: (teamId: string, signal?: AbortSignal) => Promise<void>;
  /** Wake a dormant Team slot without enqueueing a message or creating work. */
  ensureAgentRuntime?: (teamId: string, slotId: string, signal?: AbortSignal) => Promise<void>;
  readRunState: (teamId: string, signal?: AbortSignal, fresh?: boolean) => Promise<ResearchCoreRunState>;
  readAgentUsage?: (
    teamId: string,
    slotId: string,
    signal?: AbortSignal
  ) => Promise<ResearchCoreAgentUsage | undefined>;
  readAgentModel?: (
    teamId: string,
    slotId: string,
    signal?: AbortSignal
  ) => Promise<ResearchCoreAgentModel | undefined>;
  dispatch: (
    teamId: string,
    slotId: string,
    message: string,
    signal?: AbortSignal,
    idempotencyKey?: string,
    workspace?: string
  ) => Promise<ITeamRunAck>;
  deliver?: (
    teamId: string,
    sourceSlotId: string,
    leadSlotId: string,
    message: string,
    signal?: AbortSignal,
    idempotencyKey?: string
  ) => Promise<ITeamRunAck>;
  cancelChildTurn?: (
    teamId: string,
    teamRunId: string,
    slotId: string,
    reason: string,
    signal?: AbortSignal
  ) => Promise<void>;
}>;

const ACTIVE_STATES = new Set<TeamSlotWorkState>(['queued', 'starting', 'running']);
const MAX_SESSION_CACHE_ENTRIES = 32;

export function createResearchCoreTeamClient(input: {
  baseUrl: string;
  fetchImpl?: typeof fetch;
  requestTimeoutMs?: number;
  retryDelaysMs?: readonly number[];
  sleep?: (delayMs: number, signal?: AbortSignal) => Promise<void>;
}): ResearchCoreTeamClient {
  const baseUrl = normalizeLocalCoreBaseUrl(input.baseUrl);
  const fetchImpl = input.fetchImpl ?? fetch;
  const runtimeHeaders = readRuntimeHeaders();
  const requestOptions = Object.freeze({
    requestTimeoutMs: normalizePositiveDuration(input.requestTimeoutMs, 8_000),
    retryDelaysMs: Object.freeze((input.retryDelaysMs ?? [150, 600]).map(normalizeRetryDelay)),
    sleep: input.sleep ?? abortableSleep,
  });
  // Session restoration is idempotent but still crosses the Core boundary.
  // Share the in-flight restore and reuse a successful restore until a later
  // Core request proves that the session has gone away (for example after a
  // Core restart).
  const sessionReady = new Set<string>();
  const sessionReadyOrder: string[] = [];
  const sessionRestore = new Map<string, Promise<void>>();
  const runStateCache = new Map<string, { expiresAt: number; state: ResearchCoreRunState }>();
  const runStateInFlight = new Map<string, Promise<ResearchCoreRunState>>();
  const teamMetadataCache = new Map<string, { expiresAt: number; team: Record<string, unknown> }>();
  const teamMetadataInFlight = new Map<string, Promise<Record<string, unknown>>>();

  const touchSession = (teamId: string): void => {
    const index = sessionReadyOrder.indexOf(teamId);
    if (index >= 0) sessionReadyOrder.splice(index, 1);
    sessionReadyOrder.push(teamId);
  };

  const ensureSession = async (teamId: string, signal?: AbortSignal): Promise<void> => {
    const stableTeamId = stableId(teamId, 'team_id');
    if (sessionReady.has(stableTeamId)) {
      touchSession(stableTeamId);
      return;
    }
    const existingRestore = sessionRestore.get(stableTeamId);
    if (existingRestore) {
      await awaitWithAbort(existingRestore, signal);
      if (sessionReady.has(stableTeamId)) return;
    }
    const restore = (async () => {
      await requestJson(
        fetchImpl,
        `${baseUrl}/api/teams/${encodeURIComponent(stableTeamId)}/session`,
        { method: 'POST' },
        'Team session restore',
        requestOptions
      );
      if (!sessionReady.has(stableTeamId)) sessionReadyOrder.push(stableTeamId);
      sessionReady.add(stableTeamId);
      touchSession(stableTeamId);
      while (sessionReadyOrder.length > MAX_SESSION_CACHE_ENTRIES) {
        const evicted = sessionReadyOrder.shift();
        if (evicted) sessionReady.delete(evicted);
      }
      runStateCache.delete(stableTeamId);
      teamMetadataCache.delete(stableTeamId);
    })();
    sessionRestore.set(stableTeamId, restore);
    try {
      await awaitWithAbort(restore, signal);
    } finally {
      if (sessionRestore.get(stableTeamId) === restore) sessionRestore.delete(stableTeamId);
    }
  };

  const invalidateSessionOnFailure = async <T>(
    teamId: string,
    operation: () => Promise<T>,
    signal?: AbortSignal
  ): Promise<T> => {
    try {
      return await operation();
    } catch (error) {
      if (signal?.aborted) throw error;
      const stableTeamId = stableId(teamId, 'team_id');
      sessionReady.delete(stableTeamId);
      const sessionIndex = sessionReadyOrder.indexOf(stableTeamId);
      if (sessionIndex >= 0) sessionReadyOrder.splice(sessionIndex, 1);
      // A failed request can mean that Core restarted or replaced the Team
      // session. Do not let a short-lived cache window replay snapshots from
      // the previous session after recovery.
      runStateCache.delete(stableTeamId);
      teamMetadataCache.delete(stableTeamId);
      throw error;
    }
  };

  const readTeamMetadata = async (teamId: string, signal?: AbortSignal): Promise<Record<string, unknown>> => {
    const stableTeamId = stableId(teamId, 'team_id');
    const cachedTeam = teamMetadataCache.get(stableTeamId);
    let teamRequest =
      cachedTeam && cachedTeam.expiresAt > Date.now()
        ? Promise.resolve(cachedTeam.team)
        : teamMetadataInFlight.get(stableTeamId);
    if (!teamRequest) {
      teamRequest = requestJson(
        fetchImpl,
        `${baseUrl}/api/teams/${encodeURIComponent(stableTeamId)}`,
        { method: 'GET' },
        'Team metadata',
        requestOptions
      ).then((rawTeam) => {
        const team = isRecord(rawTeam) && isRecord(rawTeam.team) ? rawTeam.team : rawTeam;
        if (!isRecord(team)) throw new Error('Core Team metadata is invalid');
        return team;
      });
      teamMetadataInFlight.set(stableTeamId, teamRequest);
      void teamRequest
        .then(
          (team) => {
            teamMetadataCache.set(stableTeamId, { expiresAt: Date.now() + 1_000, team });
          },
          (): void => undefined
        )
        .finally(() => {
          if (teamMetadataInFlight.get(stableTeamId) === teamRequest) teamMetadataInFlight.delete(stableTeamId);
        });
    }
    return await awaitWithAbort(teamRequest, signal);
  };

  const findTeamAssistant = async (
    teamId: string,
    slotId: string,
    signal?: AbortSignal
  ): Promise<Record<string, unknown> | undefined> => {
    const stableSlotId = stableId(slotId, 'slot_id');
    const team = await readTeamMetadata(teamId, signal);
    const assistants = Array.isArray(team.assistants) ? team.assistants : Array.isArray(team.agents) ? team.agents : [];
    const assistant = assistants.find(
      (value) => isRecord(value) && optionalText(value.slot_id ?? value.slotId) === stableSlotId
    );
    return isRecord(assistant) ? assistant : undefined;
  };

  return Object.freeze({
    ensureSession,
    ensureAgentRuntime: async (teamId, slotId, signal) => {
      await invalidateSessionOnFailure(
        teamId,
        async () => {
          const stableTeamId = stableId(teamId, 'team_id');
          const stableSlotId = stableId(slotId, 'slot_id');
          await ensureSession(stableTeamId, signal);
          await requestJson(
            fetchImpl,
            `${baseUrl}/api/teams/${encodeURIComponent(stableTeamId)}/agents/${encodeURIComponent(stableSlotId)}/runtime`,
            { method: 'POST', signal },
            'Research Team agent runtime ensure',
            { ...requestOptions, retryDelaysMs: [] }
          );
          runStateCache.delete(stableTeamId);
        },
        signal
      );
    },
    readRunState: async (teamId, signal, fresh = false) => {
      const stableTeamId = stableId(teamId, 'team_id');
      const cached = runStateCache.get(stableTeamId);
      if (!fresh && cached && cached.expiresAt > Date.now()) {
        return cached.state;
      }
      const existing = runStateInFlight.get(stableTeamId);
      if (!fresh && existing) return await awaitWithAbort(existing, signal);
      const request = invalidateSessionOnFailure(stableTeamId, async () => {
        const raw = await requestJson(
          fetchImpl,
          `${baseUrl}/api/teams/${encodeURIComponent(stableTeamId)}/run-state`,
          { method: 'GET' },
          'Team run state',
          requestOptions
        );
        const source = isRecord(raw) && isRecord(raw.run) ? raw.run : raw;
        if (!isRecord(source)) throw new Error('Core Team run state is invalid');
        if (fresh && !Array.isArray(source.slot_work)) throw new Error('Core Team slot snapshot is missing');
        const activeRun = isRecord(source.active_run) ? source.active_run : undefined;
        const runStatus = activeRun?.status;
        if (
          activeRun &&
          !['accepted', 'running', 'cancelling', 'completed', 'cancelled', 'failed'].includes(String(runStatus))
        )
          throw new Error('Core Team run status is invalid');
        if (
          fresh &&
          activeRun &&
          ['queued_intent_count', 'starting_batch_count', 'running_batch_count'].some(
            (key) => Object.hasOwn(activeRun, key) && optionalNonnegativeInteger(activeRun[key]) === undefined
          )
        ) {
          throw new Error('Core Team run counters are invalid');
        }
        const rawSlots = Array.isArray(source.slot_work) ? source.slot_work : [];
        const slots = rawSlots.map((value): ResearchCoreSlotState => {
          if (!isRecord(value)) throw new Error('Core Team slot state is invalid');
          // Recent Core snapshots no longer emit the legacy per-slot wake
          // counter.  Keep the canonical client shape while treating only an
          // omitted field as the compatible zero value.
          const pendingWakeCount = value.pending_wake_count === undefined ? 0 : value.pending_wake_count;
          if (
            fresh &&
            (typeof value.state !== 'string' ||
              [value.queued_foreground_count, value.queued_background_count, pendingWakeCount].some(
                (counter) => !Number.isSafeInteger(counter) || Number(counter) < 0
              ))
          )
            throw new Error('Core Team slot counters are invalid');
          const state = normalizeSlotState(value.state);
          return Object.freeze({
            slotId: stableId(value.slot_id, 'slot_id'),
            state,
            queuedForegroundCount: nonnegativeInteger(value.queued_foreground_count),
            queuedBackgroundCount: nonnegativeInteger(value.queued_background_count),
            pendingWakeCount: nonnegativeInteger(pendingWakeCount),
            ...(optionalText(value.active_turn_id) ? { activeTurnId: optionalText(value.active_turn_id) } : {}),
            ...(optionalText(value.team_run_id) ? { teamRunId: optionalText(value.team_run_id) } : {}),
            ...(optionalNonnegativeNumber(value.active_turn_started_at_ms) !== undefined
              ? { activeTurnStartedAtMs: optionalNonnegativeNumber(value.active_turn_started_at_ms) }
              : {}),
            ...(optionalNonnegativeNumber(value.active_turn_elapsed_ms) !== undefined
              ? { activeTurnElapsedMs: optionalNonnegativeNumber(value.active_turn_elapsed_ms) }
              : {}),
            ...(typeof value.active_turn_slow === 'boolean' ? { activeTurnSlow: value.active_turn_slow } : {}),
            ...(optionalNonnegativeNumber(value.active_turn_slow_threshold_ms) !== undefined
              ? { activeTurnSlowThresholdMs: optionalNonnegativeNumber(value.active_turn_slow_threshold_ms) }
              : {}),
            ...(isBlockedReason(value.blocked_reason) ? { blockedReason: value.blocked_reason } : {}),
            ...(isRuntimeHealth(value.runtime_health) ? { runtimeHealth: value.runtime_health } : {}),
          });
        });
        return Object.freeze({
          teamId: stableTeamId,
          ...(optionalText(source.team_run_id ?? activeRun?.team_run_id)
            ? { teamRunId: optionalText(source.team_run_id ?? activeRun?.team_run_id) }
            : {}),
          ...(optionalText(source.session_generation)
            ? { sessionGeneration: optionalText(source.session_generation) }
            : {}),
          ...(activeRun
            ? {
                runStatus: runStatus as ResearchCoreRunState['runStatus'],
                ...(optionalNonnegativeInteger(activeRun.queued_intent_count) !== undefined
                  ? { queuedIntentCount: optionalNonnegativeInteger(activeRun.queued_intent_count) }
                  : {}),
                ...(optionalNonnegativeInteger(activeRun.starting_batch_count) !== undefined
                  ? { startingBatchCount: optionalNonnegativeInteger(activeRun.starting_batch_count) }
                  : {}),
                ...(optionalNonnegativeInteger(activeRun.running_batch_count) !== undefined
                  ? { runningBatchCount: optionalNonnegativeInteger(activeRun.running_batch_count) }
                  : {}),
                activeEnqueueLeaseCount: nonnegativeInteger(activeRun.active_enqueue_lease_count),
              }
            : {}),
          slots: Object.freeze(slots),
          activeSlotIds: Object.freeze(
            slots.filter((slot) => ACTIVE_STATES.has(slot.state)).map((slot) => slot.slotId)
          ),
        });
      })
        .then((state) => {
          if (!fresh) runStateCache.set(stableTeamId, { expiresAt: Date.now() + 150, state });
          return state;
        })
        .finally(() => {
          if (runStateInFlight.get(stableTeamId) === request) runStateInFlight.delete(stableTeamId);
        });
      if (!fresh) runStateInFlight.set(stableTeamId, request);
      return await awaitWithAbort(request, signal);
    },
    readAgentUsage: async (teamId, slotId, signal) => {
      return await invalidateSessionOnFailure(
        teamId,
        async () => {
          const assistant = await findTeamAssistant(teamId, slotId, signal);
          if (!assistant) return undefined;
          const conversationId = optionalText(assistant.conversation_id ?? assistant.conversationId);
          if (!conversationId) return undefined;
          const rawUsage = await requestJson(
            fetchImpl,
            `${baseUrl}/api/conversations/${encodeURIComponent(conversationId)}/usage`,
            { method: 'GET', signal },
            'Conversation usage',
            requestOptions
          );
          return normalizeAgentUsage(rawUsage);
        },
        signal
      );
    },
    readAgentModel: async (teamId, slotId, signal) => {
      return await invalidateSessionOnFailure(
        teamId,
        async () => {
          const assistant = await findTeamAssistant(teamId, slotId, signal);
          if (!assistant) return undefined;
          const defaults = isRecord(assistant.defaults) ? assistant.defaults : undefined;
          const defaultModel = defaults && isRecord(defaults.model) ? defaults.model.value : undefined;
          const directModel = isRecord(assistant.model) ? assistant.model.value : assistant.model;
          const model = optionalText(directModel ?? assistant.model_id ?? assistant.modelId ?? defaultModel);
          return model && model.toLowerCase() !== 'default' ? Object.freeze({ model }) : undefined;
        },
        signal
      );
    },
    dispatch: async (teamId, slotId, message, signal, idempotencyKey, workspace) => {
      return await invalidateSessionOnFailure(
        teamId,
        async () => {
          const stableTeamId = stableId(teamId, 'team_id');
          runStateCache.delete(stableTeamId);
          const stableSlotId = stableId(slotId, 'slot_id');
          const stableIdempotencyKey = idempotencyKey ? canonicalResearchTeamIdempotencyKey(idempotencyKey) : undefined;
          const dispatchWorkspace = workspace?.trim();
          if (dispatchWorkspace && !dispatchWorkspace.startsWith('/')) {
            throw new Error('Research Team dispatch workspace must be absolute');
          }
          const content = message.trim();
          if (!content) throw new Error('Research Team assignment message is empty');
          const runtimeDispatch = runtimeHeaders !== undefined;
          const raw = await requestJson(
            fetchImpl,
            runtimeDispatch
              ? `${baseUrl}/api/runtime/team-tools/dispatch`
              : `${baseUrl}/api/teams/${encodeURIComponent(stableTeamId)}/agents/${encodeURIComponent(stableSlotId)}/messages`,
            {
              method: 'POST',
              headers: { 'content-type': 'application/json', ...(runtimeHeaders ?? {}) },
              body: JSON.stringify(
                runtimeDispatch
                  ? {
                      target_slot_id: stableSlotId,
                      content,
                      ...(stableIdempotencyKey ? { idempotency_key: stableIdempotencyKey } : {}),
                      ...(dispatchWorkspace ? { workspace: dispatchWorkspace } : {}),
                    }
                  : {
                      content,
                      ...(stableIdempotencyKey ? { idempotency_key: stableIdempotencyKey } : {}),
                      ...(dispatchWorkspace ? { workspace: dispatchWorkspace } : {}),
                    }
              ),
              signal,
            },
            'Research Team dispatch',
            stableIdempotencyKey ? requestOptions : { ...requestOptions, retryDelaysMs: [] }
          );
          return fromBackendTeamRunAck(stableTeamId, raw, stableSlotId);
        },
        signal
      );
    },
    deliver: async (teamId, sourceSlotId, leadSlotId, message, signal, idempotencyKey) => {
      return await invalidateSessionOnFailure(
        teamId,
        async () => {
          const stableTeamId = stableId(teamId, 'team_id');
          runStateCache.delete(stableTeamId);
          const stableSourceSlotId = stableId(sourceSlotId, 'source_slot_id');
          const stableLeadSlotId = stableId(leadSlotId, 'lead_slot_id');
          const stableIdempotencyKey = idempotencyKey ? canonicalResearchTeamIdempotencyKey(idempotencyKey) : undefined;
          const content = message.trim();
          if (!content) throw new Error('Research Team delivery message is empty');
          await ensureSession(stableTeamId, signal);
          const raw = await requestJson(
            fetchImpl,
            `${baseUrl}/api/teams/${encodeURIComponent(stableTeamId)}/agents/${encodeURIComponent(stableSourceSlotId)}/deliveries`,
            {
              method: 'POST',
              headers: { 'content-type': 'application/json' },
              body: JSON.stringify({
                content,
                ...(stableIdempotencyKey ? { idempotency_key: stableIdempotencyKey } : {}),
              }),
              signal,
            },
            'Research Team delivery',
            stableIdempotencyKey ? requestOptions : { ...requestOptions, retryDelaysMs: [] }
          );
          return fromAgentDeliveryAck(stableTeamId, stableSourceSlotId, stableLeadSlotId, stableIdempotencyKey, raw);
        },
        signal
      );
    },
    cancelChildTurn: async (teamId, teamRunId, slotId, reason, signal) => {
      await invalidateSessionOnFailure(
        teamId,
        async () => {
          const stableTeamId = stableId(teamId, 'team_id');
          const stableTeamRunId = stableId(teamRunId, 'team_run_id');
          const stableSlotId = stableId(slotId, 'slot_id');
          await ensureSession(stableTeamId, signal);
          await requestJson(
            fetchImpl,
            `${baseUrl}/api/teams/${encodeURIComponent(stableTeamId)}/runs/${encodeURIComponent(stableTeamRunId)}/agents/${encodeURIComponent(stableSlotId)}/cancel`,
            {
              method: 'POST',
              headers: { 'content-type': 'application/json' },
              body: JSON.stringify({ reason: reason.trim() || 'Research Team child-turn cancellation requested' }),
              signal,
            },
            'Research Team child-turn cancellation',
            { ...requestOptions, retryDelaysMs: [] }
          );
        },
        signal
      );
    },
  });
}

function normalizeAgentUsage(value: unknown): ResearchCoreAgentUsage | undefined {
  if (!isRecord(value)) return undefined;
  const metadata = isRecord(value._meta) ? value._meta : undefined;
  const sources = [
    isRecord(value.totals) ? value.totals : undefined,
    metadata && isRecord(metadata.totals) ? metadata.totals : undefined,
    metadata && isRecord(metadata.token_usage) ? metadata.token_usage : undefined,
    metadata && isRecord(metadata.tokenUsage) ? metadata.tokenUsage : undefined,
    value,
  ].filter((source): source is Record<string, unknown> => source !== undefined);
  for (const source of sources) {
    const totalTokens = optionalNonnegativeNumber(source.total_tokens ?? source.totalTokens);
    if (totalTokens === undefined) continue;
    const cost = optionalNonnegativeNumber(value.cost);
    return Object.freeze({
      measurement: 'token_totals',
      inputTokens: optionalNonnegativeNumber(source.input_tokens ?? source.inputTokens) ?? 0,
      cachedInputTokens: optionalNonnegativeNumber(source.cached_input_tokens ?? source.cachedInputTokens) ?? 0,
      outputTokens: optionalNonnegativeNumber(source.output_tokens ?? source.outputTokens) ?? 0,
      reasoningOutputTokens:
        optionalNonnegativeNumber(source.reasoning_output_tokens ?? source.reasoningOutputTokens) ?? 0,
      totalTokens,
      ...(cost !== undefined ? { cost } : {}),
    });
  }

  // ACP UsageUpdate exposes current context occupancy as used/size rather
  // than provider token totals. Keep the measurement explicit so callers do
  // not mistake a reused conversation's context size for one turn's cost.
  const contextTokensUsed = optionalNonnegativeNumber(value.used);
  if (contextTokensUsed === undefined) return undefined;
  const contextWindowSize = optionalNonnegativeNumber(value.size);
  const cost = optionalNonnegativeNumber(value.cost);
  return Object.freeze({
    measurement: 'context_window',
    inputTokens: 0,
    cachedInputTokens: 0,
    outputTokens: 0,
    reasoningOutputTokens: 0,
    totalTokens: contextTokensUsed,
    ...(contextWindowSize !== undefined ? { contextWindowSize } : {}),
    ...(cost !== undefined ? { cost } : {}),
  });
}

function fromAgentDeliveryAck(
  teamId: string,
  sourceSlotId: string,
  leadSlotId: string,
  idempotencyKey: string | undefined,
  value: unknown
): ITeamRunAck {
  if (!isRecord(value) || !isRecord(value.target)) {
    throw new Error('Research Team delivery acknowledgement is invalid');
  }
  const teamRunId = optionalText(value.team_run_id);
  const targetSlotId = optionalText(value.target.slot_id);
  const responseSourceSlotId = optionalText(value.source_slot_id);
  const responseIdempotencyKey = optionalText(value.idempotency_key);
  if (
    !teamRunId ||
    targetSlotId !== leadSlotId ||
    value.target.role !== 'lead' ||
    (responseSourceSlotId !== undefined && responseSourceSlotId !== sourceSlotId) ||
    (responseIdempotencyKey !== undefined && responseIdempotencyKey !== idempotencyKey)
  ) {
    throw new Error('Research Team delivery acknowledgement does not match the Lead');
  }
  normalizeSlotState(value.target.state);
  return Object.freeze({
    team_run_id: teamRunId,
    team_id: teamId,
    target_slot_id: leadSlotId,
    target_role: 'lead',
    accepted_slot_id: leadSlotId,
    accepted_role: 'lead',
    status: 'accepted',
    ...(responseSourceSlotId ? { source_slot_id: responseSourceSlotId } : {}),
    ...(optionalText(value.delivery_id) ? { delivery_id: optionalText(value.delivery_id) } : {}),
    ...(responseIdempotencyKey ? { idempotency_key: responseIdempotencyKey } : {}),
    ...(optionalText(value.payload_hash) ? { payload_hash: optionalText(value.payload_hash) } : {}),
    ...(typeof value.persisted === 'boolean' ? { persisted: value.persisted } : {}),
    ...(typeof value.replayed === 'boolean' ? { replayed: value.replayed } : {}),
  });
}

type RequestJsonOptions = Readonly<{
  requestTimeoutMs: number;
  retryDelaysMs: readonly number[];
  sleep: (delayMs: number, signal?: AbortSignal) => Promise<void>;
}>;

async function requestJson(
  fetchImpl: typeof fetch,
  url: string,
  init: RequestInit,
  label: string,
  options: RequestJsonOptions
): Promise<unknown> {
  let lastError: unknown;
  for (let attempt = 0; attempt <= options.retryDelaysMs.length; attempt += 1) {
    if (init.signal?.aborted) throw init.signal.reason ?? new DOMException('Aborted', 'AbortError');
    try {
      const parsed = await fetchWithTimeout(fetchImpl, url, init, options.requestTimeoutMs, async (response) => {
        if ((response.status === 429 || response.status >= 500) && attempt < options.retryDelaysMs.length) {
          await response.body?.cancel().catch(() => {});
          return { retry: true as const };
        }
        return { retry: false as const, value: await parseJsonResponse(response, label) };
      });
      if (parsed.retry) {
        await options.sleep(options.retryDelaysMs[attempt] ?? 0, init.signal ?? undefined);
        continue;
      }
      return parsed.value;
    } catch (error) {
      if (init.signal?.aborted) throw init.signal.reason ?? error;
      lastError = error;
      if (attempt >= options.retryDelaysMs.length || !isRetryableTransportError(error)) throw error;
      await options.sleep(options.retryDelaysMs[attempt] ?? 0, init.signal ?? undefined);
    }
  }
  throw lastError instanceof Error ? lastError : new Error(`${label} could not reach the current local Core`);
}

async function parseJsonResponse(response: Response, label: string): Promise<unknown> {
  const text = await response.text();
  let payload: unknown;
  try {
    payload = text ? JSON.parse(text) : {};
  } catch {
    throw new Error(`${label} returned non-JSON data`);
  }
  if (!response.ok) {
    const detail = isRecord(payload) && typeof payload.error === 'string' ? payload.error : response.statusText;
    throw new Error(`${label} failed (${response.status}): ${detail || 'unknown error'}`);
  }
  return unwrapCoreEnvelope(payload, label);
}

async function fetchWithTimeout<T>(
  fetchImpl: typeof fetch,
  url: string,
  init: RequestInit,
  timeoutMs: number,
  consume: (response: Response) => Promise<T>
): Promise<T> {
  const controller = new AbortController();
  const externalSignal = init.signal;
  const abortFromExternal = () => controller.abort(externalSignal?.reason);
  externalSignal?.addEventListener('abort', abortFromExternal, { once: true });
  const timeout = setTimeout(() => controller.abort(new Error('LOCAL_CORE_REQUEST_TIMEOUT')), timeoutMs);
  try {
    const response = await fetchImpl(url, { ...init, signal: controller.signal });
    return await consume(response);
  } finally {
    clearTimeout(timeout);
    externalSignal?.removeEventListener('abort', abortFromExternal);
  }
}

function isRetryableTransportError(error: unknown): boolean {
  return (
    error instanceof TypeError ||
    (error instanceof Error && (error.message.includes('LOCAL_CORE_REQUEST_TIMEOUT') || error.name === 'AbortError'))
  );
}

async function awaitWithAbort<T>(promise: Promise<T>, signal?: AbortSignal): Promise<T> {
  if (!signal) return promise;
  if (signal.aborted) throw signal.reason ?? new DOMException('Aborted', 'AbortError');
  return await new Promise<T>((resolve, reject) => {
    const onAbort = (): void => reject(signal.reason ?? new DOMException('Aborted', 'AbortError'));
    signal.addEventListener('abort', onAbort, { once: true });
    promise.then(
      (value) => {
        signal.removeEventListener('abort', onAbort);
        resolve(value);
      },
      (error) => {
        signal.removeEventListener('abort', onAbort);
        reject(error);
      }
    );
  });
}

async function abortableSleep(delayMs: number, signal?: AbortSignal): Promise<void> {
  if (delayMs <= 0) return;
  await new Promise<void>((resolve, reject) => {
    if (signal?.aborted) {
      reject(signal.reason ?? new DOMException('Aborted', 'AbortError'));
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
      reject(signal?.reason ?? new DOMException('Aborted', 'AbortError'));
    };
    timer = setTimeout(() => {
      cleanup();
      resolve();
    }, delayMs);
    signal?.addEventListener('abort', onAbort, { once: true });
  });
}

function normalizePositiveDuration(value: number | undefined, fallback: number): number {
  return typeof value === 'number' && Number.isFinite(value) && value > 0 ? Math.floor(value) : fallback;
}

function normalizeRetryDelay(value: number): number {
  return Number.isFinite(value) && value >= 0 ? Math.floor(value) : 0;
}

function unwrapCoreEnvelope(payload: unknown, label: string): unknown {
  if (!isRecord(payload)) return payload;
  if (payload.success === false) {
    const detail =
      typeof payload.error === 'string'
        ? payload.error
        : isRecord(payload.error) && typeof payload.error.message === 'string'
          ? payload.error.message
          : 'unknown error';
    throw new Error(`${label} failed: ${detail}`);
  }
  return payload.success === true && Object.hasOwn(payload, 'data') ? payload.data : payload;
}

function normalizeLocalCoreBaseUrl(value: string): string {
  const url = new URL(value.trim());
  if (url.protocol !== 'http:' || !['127.0.0.1', 'localhost', '::1', '[::1]'].includes(url.hostname)) {
    throw new Error('Research Team orchestration must target the local Core');
  }
  return url.toString().replace(/\/$/u, '');
}

function readRuntimeHeaders(): Record<string, string> | undefined {
  const userId = process.env.AIONUI_USER_ID?.trim();
  const conversationId = process.env.AIONUI_CONVERSATION_ID?.trim();
  const runtimeToken = process.env.AIONUI_RUNTIME_TOKEN?.trim();
  if (!userId || !conversationId || !runtimeToken) return undefined;
  return {
    'x-aionui-user-id': userId,
    'x-aionui-conversation-id': conversationId,
    'x-aionui-runtime-token': runtimeToken,
  };
}

function normalizeSlotState(value: unknown): TeamSlotWorkState {
  const state = String(value ?? 'idle') as TeamSlotWorkState;
  if (!['idle', 'queued', 'starting', 'running', 'paused', 'blocked'].includes(state)) {
    throw new Error('Core Team slot state is unsupported');
  }
  return state;
}

function nonnegativeInteger(value: unknown): number {
  return Number.isSafeInteger(value) && Number(value) >= 0 ? Number(value) : 0;
}

function optionalNonnegativeNumber(value: unknown): number | undefined {
  return typeof value === 'number' && Number.isFinite(value) && value >= 0 ? value : undefined;
}

function optionalNonnegativeInteger(value: unknown): number | undefined {
  return Number.isSafeInteger(value) && Number(value) >= 0 ? Number(value) : undefined;
}

function optionalText(value: unknown): string | undefined {
  return typeof value === 'string' && value.trim() ? value.trim() : undefined;
}

function isBlockedReason(value: unknown): value is TeamSlotBlockedReason {
  return ['runtime_starting', 'runtime_failed', 'removing', 'session_stopped'].includes(String(value));
}

function isRuntimeHealth(value: unknown): value is 'disconnected' | 'unhealthy' {
  return value === 'disconnected' || value === 'unhealthy';
}

function stableId(value: unknown, field: string): string {
  const normalized = String(value ?? '').trim();
  if (!/^[A-Za-z0-9][A-Za-z0-9._:-]{0,127}$/u.test(normalized)) {
    throw new Error(`Research Team ${field} is invalid`);
  }
  return normalized;
}

function isRecord(value: unknown): value is Record<string, unknown> {
  return typeof value === 'object' && value !== null && !Array.isArray(value);
}
