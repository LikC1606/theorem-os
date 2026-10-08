import type { McpServer } from '@modelcontextprotocol/sdk/server/mcp.js';
import { z } from 'zod';
import {
  assertResearchTeamToolActionAuthorized,
  readResearchTeamToolPolicy,
} from "../common/types/team/researchTeamToolPolicy";
import { listProjectGitResearchTeamAssignments } from "../project-git/index";
import {
  resolveMathAssignmentContext,
  tryResolveMathAssignmentContext,
} from "../math/mathAssignmentContext";
import {
  mathResearchWorkflowCommand,
  readMathResearchWorkflowState,
  projectMathResearchCommandState,
  projectMathResearchState,
  updateMathResearchWorkflow,
} from "../math/mathResearchWorkflow";
import { canonicalMathJson, mathDigest } from "../math/mathRuntimeIo";
import { resolveResearchTeamRuntimeCapability } from "../team/toolCapability";
import { createResearchCoreTeamClient } from "../team/coreTeamClient";

// This compatibility entry is loaded only for the full research workflow.
export function registerMathResearchCompatibilityTool(
  server: McpServer,
  resolveModeProjectRoot: (root?: string) => Promise<string | undefined>
) {
  const jsonStructured = <T extends Record<string, unknown>>(value: T) => ({
    content: [{ type: 'text' as const, text: JSON.stringify(value, null, 2) }],
    structuredContent: value,
  });
  server.tool(
    'math_research',
    'Maintain the current run mathematics research notebook and route decisions. Available in the default full system. get supports a bounded working view and a paged full view, and returns initialization hints when needed. Record dependencies, findings, failed routes and next steps with evidence. Main-route proposals return to the Lead; local repairs remain in the same assignment. Notes never confer proof authority.',
    {
      projectRoot: z.string().optional(),
      problemId: z.string().min(1).max(160),
      assignmentId: z.string().min(1).max(160).optional(),
      command: z.union([mathResearchWorkflowCommand, z.object({ action: z.literal('overview') }).strict()]),
    },
    async ({ projectRoot, problemId, assignmentId, command }) => {
      assertResearchTeamToolActionAuthorized('math_research', command.action);
      const actor = readResearchTeamToolPolicy();
      if (!actor) throw new Error('Research workflow requires a runtime-bound Team role.');
      const root = await resolveModeProjectRoot(projectRoot);
      if (!root) throw new Error('Research workflow requires the bound project root.');
      const capability = await resolveResearchTeamRuntimeCapability(undefined);
      if (!capability) throw new Error('Research workflow requires an authenticated Core Team binding.');
      const receipts = listProjectGitResearchTeamAssignments({
        workspace: root,
        teamId: capability.teamId,
        strict: true,
      });
      if (command.action === 'overview') {
        const states = receipts
          .filter((item) => {
            if (actor.roleKind === 'worker' && capability.slotId !== item.slotId) return false;
            const context = tryResolveMathAssignmentContext({
              receipt: item,
              projectRoot: root,
              expectedTeamId: capability.teamId,
              ...(actor.roleKind === 'worker' ? { expectedSlotId: capability.slotId } : {}),
            });
            return context?.problemId === problemId;
          })
          .map((item) => {
            const assignedWorker = capability.roster.find(
              (member) => member.slotId === item.slotId && member.roleKind === 'worker'
            );
            if (!assignedWorker) throw new Error('Research workflow belongs to an unavailable Worker.');
            const research = readMathResearchWorkflowState(root, problemId, item.assignmentId);
            if (
              research &&
              (research.binding.teamId !== capability.teamId ||
                research.binding.slotId !== item.slotId ||
                research.binding.workerId !== assignedWorker.roleId ||
                research.workerId !== assignedWorker.roleId ||
                research.binding.assignmentDigest !== mathDigest(canonicalMathJson(item.assignment)))
            )
              throw new Error('Research workflow assignment binding changed.');
            return {
              assignmentId: item.assignmentId,
              lifecycle: item.state,
              research: projectMathResearchState(research),
            };
          });
        return jsonStructured({ problemId, assignments: states, authority: 'organization', solverReady: false });
      }
      if (!assignmentId) throw new Error('An assignmentId is required for this research action.');
      const receipt = receipts.find((item) => item.assignmentId === assignmentId);
      const leadNotebook =
        actor.roleKind === 'lead' &&
        ['initialize', 'record'].includes(command.action) &&
        ['accepted', 'delivered', 'integrated'].includes(receipt?.state ?? '');
      if (!receipt || (command.action !== 'get' && !leadNotebook && receipt.state !== 'accepted'))
        throw new Error('Research workflow requires an active durable assignment.');
      const assignedWorker = capability.roster.find(
        (member) => member.slotId === receipt.slotId && member.roleKind === 'worker'
      );
      if (!assignedWorker || (actor.roleKind === 'worker' && capability.slotId !== receipt.slotId))
        throw new Error('Research workflow belongs to a different Worker.');
      const assignmentContext = resolveMathAssignmentContext({
        receipt,
        projectRoot: root,
        expectedTeamId: capability.teamId,
        expectedSlotId: receipt.slotId,
        expectedAssignmentId: assignmentId,
      });
      if (assignmentContext.problemId !== problemId)
        throw new Error('Research workflow problem does not match its durable assignment.');
      const binding = {
        teamId: capability.teamId,
        slotId: receipt.slotId,
        workerId: assignedWorker.roleId,
        statementHash: assignmentContext.statementHash,
        initialRouteFingerprint: assignmentContext.initialRouteFingerprint,
        routeRevisionsSupported: assignmentContext.routeRevisionsSupported,
        assignmentDigest: assignmentContext.assignmentDigest,
      };
      const client = createResearchCoreTeamClient({ baseUrl: process.env.AIONUI_BASE_URL || '' });
      const result = await updateMathResearchWorkflow({
        projectRoot: root,
        problemId,
        assignmentId,
        actor: { roleId: actor.roleId, roleKind: actor.roleKind },
        command,
        binding,
        notify: async (notification, state) => {
          const target = capability.roster.find((member) =>
            notification.target === 'lead' ? member.roleKind === 'lead' : member.roleId === state.workerId
          );
          if (!target) throw new Error('Research workflow notification target is unavailable.');
          if (notification.target === 'lead') {
            await client.deliver!(
              capability.teamId,
              receipt.slotId,
              target.slotId,
              notification.message,
              undefined,
              notification.key
            );
          } else {
            await client.dispatch(capability.teamId, target.slotId, notification.message, undefined, notification.key);
          }
        },
      });
      return jsonStructured({
        ...result,
        state: projectMathResearchCommandState(result.state, command),
      });
    }
  );
}
