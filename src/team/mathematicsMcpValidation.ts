/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

import type { Transport } from '@modelcontextprotocol/sdk/shared/transport.js';
import { CallToolRequestSchema, type CallToolResult, type JSONRPCMessage } from '@modelcontextprotocol/sdk/types.js';
import { z } from 'zod';
import type { ProtocolIssue } from "../common/types/team/mathematicsTeam";
import { RESEARCH_TEAM_TOOL_RESULT_SCHEMA } from "./researchTeamTool";
import { mathLiteDeliveryIntentSchema, mathLiteProgressIntentSchema } from "../math/mathPublicWire";

const ISSUE_MESSAGES = {
  required: 'Required field is missing.',
  invalid: 'Field does not match the declared schema.',
  payload_too_large: 'Field exceeds the declared limit.',
  conflict: 'Remove undeclared fields from this object.',
} as const;

function schemaIssuePath(path: readonly (string | number)[], fields: ReadonlySet<string>): string {
  let result = '';
  for (const segment of path) {
    if (typeof segment === 'number') {
      result += '[]';
    } else if (fields.has(segment)) {
      result += `${result ? '.' : ''}${segment}`;
    } else {
      // Record keys are model-controlled, including private text. Never echo them.
      result += '.*';
      break;
    }
  }
  return Buffer.byteLength(result, 'utf8') <= 48
    ? result || '$'
    : `${path[0] === 'assignments' ? 'assignments[]' : '$'}.*`;
}

/** Uses the registered schema unchanged; invalid inputs never reach the runtime. */
export function createMathematicsMcpValidator(
  shape: z.ZodRawShape,
  options: Readonly<{ liteDelivery?: boolean }> = {}
): (input: unknown) => CallToolResult | undefined {
  const refineAction = (value: Record<string, unknown>, context: z.RefinementCtx) => {
    if (options.liteDelivery && value.action === 'share' && value.result === undefined) {
      context.addIssue({ code: z.ZodIssueCode.custom, path: ['result'], message: 'delivery_result_required' });
    }
    // The wire schema is shared by actions. Never silently discard a source
    // read because its fields were supplied to read_feedback or another action.
    if (value.action !== 'read_artifact') {
      for (const field of ['artifact_ref', 'offset_bytes', 'max_bytes']) {
        if (value[field] !== undefined)
          context.addIssue({ code: z.ZodIssueCode.custom, path: [field], message: 'artifact_read_action_required' });
      }
    }
  };
  const schema = z.object(shape).strict().superRefine(refineAction);
  const fields = new Set([
    ...Object.keys(shape),
    'maxMinutes',
    'maxAttempts',
    'delivery_id',
    'assignment_id',
    'result',
    ...(options.liteDelivery
      ? [
          'status',
          'summary',
          'files',
          'blockers',
          'wait_for_question_ids',
          'statement',
          'assumptions',
          'targetConnection',
        ]
      : []),
  ]);
  return (input) => {
    const requestAction = input && typeof input === 'object' && 'action' in input ? input.action : undefined;
    const actionSchema =
      options.liteDelivery && (requestAction === 'deliver' || requestAction === 'share')
        ? z
            .object({
              ...shape,
              result:
                requestAction === 'deliver' ? mathLiteDeliveryIntentSchema.optional() : mathLiteProgressIntentSchema,
            })
            .strict()
            .superRefine(refineAction)
        : schema;
    const parsed = actionSchema.safeParse(input);
    if (parsed.success) return undefined;
    const actionResult = shape.action.safeParse(
      input && typeof input === 'object' && !Array.isArray(input) && 'action' in input ? input.action : undefined
    );
    const action = actionResult.success ? actionResult.data : null;
    const grouped = new Map<string, ProtocolIssue>();
    for (const issue of parsed.error.issues) {
      const code =
        (issue.code === 'invalid_type' && issue.received === 'undefined') ||
        (issue.code === 'custom' && issue.message === 'delivery_result_required')
          ? 'required'
          : issue.code === 'too_big'
            ? 'payload_too_large'
            : issue.code === 'unrecognized_keys'
              ? 'conflict'
              : 'invalid';
      let message: string = ISSUE_MESSAGES[code];
      const deliveryField = options.liteDelivery && issue.path[0] === 'result' ? issue.path[1] : undefined;
      if (deliveryField === 'status' && issue.code === 'invalid_enum_value') {
        message = 'Use completed or blocked.';
      }
      if (issue.code === 'custom') {
        // Only schema-owned refinement messages are permitted, never Zod's input-bearing diagnostics.
        if (issue.message === 'Provide exactly one of assignment or task.') {
          message = 'Provide exactly one of assignment or task.';
        } else if (issue.message === 'The preferred task path requires base_commit.') {
          message = 'The task form requires base_commit.';
        } else if (issue.message === 'Provide exactly one of result, delivery_id, or assignment_id.') {
          message = 'Provide exactly one of result, delivery_id, or assignment_id.';
        } else if (issue.message === 'artifact_read_action_required') {
          message =
            'These fields require action="read_artifact". read_feedback returns findings, not the referenced source. No artifact was read; retry read_artifact with the exact reference and returned pagination offsets.';
        } else if (deliveryField === 'blockers' && issue.message === 'required') {
          message = 'Blocked delivery requires at least one blocker.';
        } else if (deliveryField === 'blockers' && issue.message === 'forbidden') {
          message = 'Completed delivery must not contain blockers.';
        } else if (deliveryField === 'files' && issue.message === 'duplicate') {
          message = 'List each relative file path once.';
        }
      }
      if (action === 'read_artifact' && issue.path[0] === 'max_bytes') {
        message =
          'Use an integer from 1 to 2048, or omit max_bytes. Continue with offset_bytes set to the returned nextOffsetBytes.';
      } else if (action === 'read_artifact' && issue.path[0] === 'offset_bytes') {
        message =
          'Use a nonnegative safe integer from the returned nextOffsetBytes, or omit offset_bytes for the first page.';
      }
      const normalized: ProtocolIssue = { path: schemaIssuePath(issue.path, fields), code, message };
      grouped.set(`${normalized.path}\0${code}\0${normalized.message}`, normalized);
    }
    const issues = [...grouped.entries()]
      .toSorted(([left], [right]) => (left < right ? -1 : left > right ? 1 : 0))
      .map(([, issue]) => issue);
    const overflow = Buffer.byteLength(JSON.stringify(issues), 'utf8') > 2048;
    const errors: readonly ProtocolIssue[] = overflow
      ? [
          {
            path: '$',
            code: 'payload_too_large',
            message: 'Too many schema errors. Rebuild the request using the declared tool schema.',
          },
        ]
      : issues;
    return {
      isError: true,
      content: [
        {
          type: 'text',
          text: JSON.stringify({
            schema: RESEARCH_TEAM_TOOL_RESULT_SCHEMA,
            action,
            status: 'unavailable',
            accepted: false,
            errors,
            ...(overflow ? { schema_error_groups: issues.length, errors_omitted: true } : {}),
            ...(action
              ? {
                  help: {
                    schema: 'deepscientist.math.protocol-help.v1',
                    action,
                    instruction:
                      'Correct the reported fields using the declared tool schema. No describe call is needed.',
                    ...(options.liteDelivery && action === 'integrate'
                      ? {
                          fields: ['deliveries[].target_slot_id', 'deliveries[].delivery_id'],
                          instruction:
                            'Use a nonempty deliveries array. Put the actual Worker slot and durable delivery_id inside each item, never at the top level. Copy these values from the acknowledged delivery; do not invent or omit the selector.',
                        }
                      : {}),
                    ...(options.liteDelivery && action === 'deliver'
                      ? {
                          example: {
                            action: 'deliver',
                            result: {
                              status: 'completed',
                              summary: 'Describe the result.',
                              files: ['Submission.lean'],
                            },
                          },
                          delivery_rules:
                            'Replace example paths with files relative to your assignment source root. Blocked results require nonempty blockers. Research-only results may omit files. Identity, hashes and delivery selectors are host-owned. This validation attempt does not seal files or modify an existing seal. If a prior request was sealed, call deliver without result to recover it; otherwise correct the request and retry.',
                        }
                      : {}),
                  },
                }
              : {}),
            error: {
              code: 'research_team_request_invalid',
              message: 'Invalid mathematics tool input.',
              retryable: false,
            },
          }),
        },
      ],
    };
  };
}

/**
 * Some model deployments serialize a structured array argument even when the
 * MCP schema advertises an array. Accept that wire-level compatibility form at
 * the transport boundary, then pass the parsed array to the registered schema
 * and handler. Invalid JSON is left untouched so the normal bounded schema
 * diagnostic is returned.
 */
function normalizeSerializedResearchTeamArguments(message: JSONRPCMessage): JSONRPCMessage {
  if (!('method' in message) || message.method !== 'tools/call' || !('params' in message)) return message;
  const params = message.params;
  if (!params || typeof params !== 'object' || Array.isArray(params) || params.name !== 'research_team') return message;
  const args = params.arguments;
  if (!args || typeof args !== 'object' || Array.isArray(args)) return message;
  const assignments = (args as Record<string, unknown>).assignments;
  if (typeof assignments !== 'string') return message;
  try {
    const parsed = JSON.parse(assignments) as unknown;
    if (!Array.isArray(parsed)) return message;
    return {
      ...message,
      params: {
        ...params,
        arguments: { ...(args as Record<string, unknown>), assignments: parsed },
      },
    } as JSONRPCMessage;
  } catch {
    return message;
  }
}

/** Public Transport boundary: leave SDK dispatch, cancellation and all other tools intact. */
export function withMathematicsMcpValidation(
  inner: Transport,
  validate: (input: unknown) => CallToolResult | undefined
): Transport {
  const transport: Transport = {
    start: async () => {
      inner.onmessage = (message, extra) => {
        const normalizedMessage = normalizeSerializedResearchTeamArguments(message);
        if ('method' in normalizedMessage && normalizedMessage.method === 'tools/call' && 'id' in normalizedMessage) {
          const request = CallToolRequestSchema.safeParse(normalizedMessage);
          if (request.success && request.data.params.name === 'research_team') {
            const rejected = validate(request.data.params.arguments);
            if (rejected) {
              void inner
                .send(
                  { jsonrpc: '2.0', id: normalizedMessage.id, result: rejected },
                  { relatedRequestId: normalizedMessage.id }
                )
                .catch(() => transport.onerror?.(new Error('Failed to send mathematics schema rejection.')));
              return;
            }
          }
        }
        transport.onmessage?.(normalizedMessage, extra);
      };
      inner.onerror = (error) => transport.onerror?.(error);
      inner.onclose = () => transport.onclose?.();
      await inner.start();
    },
    send: (message, options) => inner.send(message, options),
    close: () => inner.close(),
    get sessionId() {
      return inner.sessionId;
    },
    setProtocolVersion: (version) => inner.setProtocolVersion?.(version),
  };
  return transport;
}
