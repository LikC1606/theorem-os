import type { ToolCallback } from '@modelcontextprotocol/sdk/server/mcp.js';
import type { z } from 'zod';
import { readMathLiteProofLineage } from "./mathLiteFeedback";

/** Explicit identities are never silently replaced. Existing handlers revalidate them. */
export function bindMathToolAssignment(
  capability: Parameters<typeof readMathLiteProofLineage>[0],
  requested: string | undefined,
  signal: AbortSignal
): string {
  signal.throwIfAborted();
  if (requested) return requested;
  if (capability.roleKind !== 'worker') throw new Error('math_tool_assignment_required');
  return readMathLiteProofLineage(capability, signal, undefined, true).target.assignmentId;
}

/** Recovery instructions are host observations, not fields supplied by an Agent.
 * No exception implies that an operation rolled back or that a theorem is false. */
export function mathToolFailure(error: unknown, action?: string, aborted = false) {
  const message = error instanceof Error ? error.message : String(error);
  const identity =
    /unauthorized|not authorized|identity|integrity|forbidden|capability|scope|outside|traversal|not_host_produced/iu.test(
      message
    );
  const cancelled = !identity && (aborted || /cancelled|canceled|abort/iu.test(message));
  const stale =
    !identity &&
    !cancelled &&
    /source_changed|source.*mismatch|stale|assignment_changed|expectedSourceHash/iu.test(message);
  const binding =
    !identity &&
    !cancelled &&
    !stale &&
    /assignment_(?:required|unavailable)|ambiguous|requires.*assignment|no current accepted/iu.test(message);
  const timeout = !identity && !cancelled && !stale && !binding && /deadline|timeout|timed out/iu.test(message);
  const resource =
    !identity &&
    !cancelled &&
    !stale &&
    !binding &&
    !timeout &&
    /snapshot exceeds|ENOSPC|EDQUOT|EROFS|no space left/iu.test(message);
  const invalid =
    !identity &&
    !cancelled &&
    !stale &&
    !binding &&
    !timeout &&
    !resource &&
    /invalid|unsupported|requires|must |Zod|limit/iu.test(message);
  const category = identity
    ? 'authorization_or_integrity'
    : cancelled
      ? 'cancelled'
      : stale
        ? 'stale_context'
        : binding
          ? 'assignment_context'
          : timeout
            ? 'incomplete_check'
            : resource
              ? 'host_resource_blocked'
              : invalid
                ? 'invalid_request'
                : 'operation_error';
  const nextAction = identity
    ? 'Stop this operation. Re-establish the authorized identity or exact frozen artifact; do not broaden permissions.'
    : cancelled
      ? 'Preserve existing work. Do not automatically restart a cancelled operation.'
      : stale
        ? 'Read the current assignment and source, then recompute the proposal. Do not apply a candidate against a different source hash.'
        : binding
          ? 'Read current assignment status. Select an existing authorized assignment explicitly if the binding is ambiguous; do not create duplicate work.'
          : timeout
            ? 'Inspect durable status before retrying. Resume the same check or replay a sealed operation exactly; an incomplete check does not justify a successor task.'
            : resource
              ? 'Inspect durable status and restore the authorized storage or sealed environment before retrying. Preserve the source, fixed dependencies and isolation limits; do not treat this as a proof failure.'
              : invalid
                ? 'Correct the reported input using the current tool contract. Keep the original target and existing assignment.'
                : 'Inspect durable status and diagnostics before retrying. Reuse the same operation when execution is uncertain; do not infer mathematical failure.';
  const payload = {
    tool: 'lean_workspace',
    action,
    error: message,
    recovery: {
      category,
      owner: identity || resource ? 'host' : 'worker',
      nextAction,
      sourceState: 'not_asserted',
      automaticRetry: false,
    },
    solverReady: false,
    originalTargetAccepted: false,
  };
  return {
    isError: true as const,
    content: [{ type: 'text' as const, text: JSON.stringify(payload) }],
    structuredContent: payload,
  };
}

/** Wrap the actual handler without retrying side effects or altering success payloads. */
export function withMathToolRecovery<Shape extends z.ZodRawShape>(handler: ToolCallback<Shape>): ToolCallback<Shape> {
  return (async (...args: Parameters<ToolCallback<Shape>>) => {
    try {
      return await handler(args[0], args[1]);
    } catch (error) {
      const input = args[0] as { action?: string };
      return mathToolFailure(error, input.action, args[1].signal.aborted);
    }
  }) as ToolCallback<Shape>;
}
