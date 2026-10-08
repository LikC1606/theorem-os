import { readMathLiteFeedback, readMathLiteProofLineage } from "./mathLiteFeedback";
import { mathLiteBlockerObservation, publishMathLiteBlockerContext } from "./mathLiteBlockerContext";
import { readMathPlanningContext, isMathPlanningSafetyError, type MathPlanningContext } from "./mathPlanningContext";
import { canonicalMathJson, mathDigest } from "./mathRuntimeIo";

// Disposable presentation projection. Never reused as authorization or proof evidence.
// Replaces the old post-construction digest cache in the MCP entry point.
const recentCheckpoints = new Map<
  string,
  {
    observationKey: string;
    evidenceRevision: string;
    artifactId?: string;
    planning: Pick<MathPlanningContext, 'contextDigest' | 'evidenceRefs' | 'historyCoverage'>;
  }
>();

/** Present ordinary lite probes once, keeping durable history available by reference. */
export function compactMathLeanProbeResponse(payload: Record<string, unknown>): Record<string, unknown> {
  if (payload.tool !== 'lean_workspace' || payload.action !== 'probe') return payload;
  const result = payload.result as Record<string, unknown> | undefined;
  const current = result?.current as Record<string, unknown> | undefined;
  if (
    result?.status !== 'probed' ||
    !current ||
    current.feedbackAvailable !== true ||
    typeof current.diagnostics !== 'string' ||
    !Array.isArray(current.goals) ||
    typeof result.historyRef !== 'string' ||
    typeof result.traceRef !== 'string'
  )
    return payload;
  const compact = { ...result };
  const state = compact.state as Record<string, unknown> | undefined;
  if (typeof state?.sourceFile === 'string') compact.sourceFile = state.sourceFile;
  delete compact.state;
  delete compact.runtimeMetrics;
  delete compact.branches;
  if (compact.diagnostics === current.diagnostics) delete compact.diagnostics;
  if (canonicalMathJson(compact.remainingGoals ?? null) === canonicalMathJson(current.goals))
    delete compact.remainingGoals;
  if (canonicalMathJson(compact.location ?? null) === canonicalMathJson(current.location ?? null))
    delete compact.location;
  return {
    ...payload,
    result: {
      ...compact,
      instruction:
        'Read current for compiler diagnostics and goals. Full history and attempts remain in historyRef and traceRef; use lean_workspace branches when choosing a stored branch.',
    },
  };
}

/** Enrich a completed check only when diagnostics or research changed. */
export async function enrichMathLeanCheckpoint({
  capability,
  payload,
  signal,
}: {
  capability: Parameters<typeof readMathLiteProofLineage>[0];
  payload: Record<string, unknown>;
  signal: AbortSignal;
}): Promise<Record<string, unknown>> {
  signal.throwIfAborted();
  const extras: Record<string, unknown> = {};
  try {
    const context = readMathLiteProofLineage(capability, signal, undefined, true);
    let evidenceRevision = '';
    const feedback = await readMathLiteFeedback({
      resolvedCapability: capability,
      signal,
      operationContext: context,
      consume: true,
      automatic: true,
      onEvidenceRevision: (revision) => {
        evidenceRevision = revision;
      },
    });
    signal.throwIfAborted();
    const newFindings = feedback.findings.length > 0;
    if (newFindings || feedback.usageFeedback.length)
      extras.researchFeedback = {
        ...feedback,
        delivery: 'lean_checkpoint',
        fullReports: 'Use artifact refs or research_team read_feedback for the durable full batch.',
      };
    // Successful checks do not rebuild history. Failed expression checks can still
    // recall history, but without a source binding they never publish or cache a blocker.
    const observation = mathLiteBlockerObservation(payload);
    const result = (payload.result ?? payload.probe) as { status?: string } | undefined;
    if (
      context.validate(context.target).kind !== 'formalize' ||
      (!observation && !['failed', 'action_failed'].includes(result?.status ?? ''))
    )
      return extras;
    const key = canonicalMathJson([context.binding.artifactStoreRoot, capability.teamId, capability.slotId]);
    const observationKey = mathDigest(canonicalMathJson([context.binding, context.target, observation ?? null]));
    const previous = recentCheckpoints.get(key);
    const sameObservation = previous?.observationKey === observationKey;
    if (sameObservation && previous.evidenceRevision === evidenceRevision && !newFindings) {
      extras.planningContext = {
        status: 'unchanged',
        ...previous.planning,
        text: 'Related history is unchanged. Read cited artifacts or research_team read_feedback for full frozen evidence.',
      };
      return extras;
    }
    // Failed refresh must remain retryable even if the feedback notification was consumed.
    recentCheckpoints.delete(key);
    const artifactId = sameObservation
      ? previous.artifactId
      : observation
        ? await publishMathLiteBlockerContext(context.binding, context.target, payload, signal)
        : undefined;
    const planning = await readMathPlanningContext({
      resolvedCapability: capability,
      signal,
      operationContext: context,
      includeAssignmentReminder: false,
      ...(artifactId ? { currentArtifactId: artifactId } : {}),
    });
    signal.throwIfAborted();
    extras.planningContext = planning;
    // A diagnostic that could not bind actual source is never cached as recorded.
    if (artifactId) {
      recentCheckpoints.delete(key);
      recentCheckpoints.set(key, {
        observationKey,
        evidenceRevision,
        artifactId,
        planning: {
          contextDigest: planning.contextDigest,
          evidenceRefs: planning.evidenceRefs,
          historyCoverage: planning.historyCoverage,
        },
      });
      if (recentCheckpoints.size > 64) recentCheckpoints.delete(recentCheckpoints.keys().next().value!);
    }
    return extras;
  } catch (error) {
    signal.throwIfAborted();
    if (isMathPlanningSafetyError(error)) throw error;
    const message = error instanceof Error ? error.message : '';
    if (['math_feedback_assignment_unavailable', 'math_feedback_formalizer_required'].includes(message)) return extras;
    return {
      ...extras,
      ...(!extras.researchFeedback
        ? {
            researchFeedback: {
              status: 'unavailable',
              provisional: true,
              instruction: 'Lean result is unchanged. Retry research_team read_feedback for current findings.',
            },
          }
        : {}),
      planningContext: {
        status: 'unavailable',
        instruction:
          'Lean result is unchanged. Read research_team feedback or retry the next changed-source checkpoint.',
      },
    };
  }
}
