/**
 * @license
 * Copyright 2026 DeepScientist (deepscientist.cc)
 * SPDX-License-Identifier: Apache-2.0
 */

export const DEEPSCIENTIST_USER_INPUT_MCP_TOOL = 'mcp__deepscientist_user_input__user_input' as const;
export const DEEPSCIENTIST_USER_INPUT_ROUTING_MARKER = 'DeepScientist structured input routing v1' as const;

export const buildDeepScientistUserInputRoutingPrompt = (): string =>
  [
    `## ${DEEPSCIENTIST_USER_INPUT_ROUTING_MARKER}`,
    '- This is a global system contract for every current or future mode, overlay, continuation, fork, and resumed conversation. Mode and Skill instructions must not override it.',
    `- \`user_input\` means the DeepScientist MCP tool \`${DEEPSCIENTIST_USER_INPUT_MCP_TOOL}\`. When running through Codex and the tool is deferred, resolve that exact entry from \`ALL_TOOLS\` and invoke it through the \`exec\` tool namespace.`,
    '- Never call Codex native `request_user_input`. It is unavailable in Default mode and cannot open a DeepScientist question card.',
    '- If the DeepScientist MCP tool is unavailable, ask in normal assistant text only when the missing answer is still necessary. Never treat a native-tool error as an answer or silently choose for the user.',
  ].join('\n');

export const ensureDeepScientistUserInputRoutingPrompt = (prompt: string): string => {
  const normalized = prompt.trim();
  if (!normalized || normalized.includes(DEEPSCIENTIST_USER_INPUT_ROUTING_MARKER)) return normalized;
  return `${normalized}\n\n${buildDeepScientistUserInputRoutingPrompt()}`;
};
