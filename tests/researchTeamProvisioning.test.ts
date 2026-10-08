import { describe, expect, it, vi } from 'vitest';
import { createHeadlessMathematicsTeamProfile } from '../src/common/chat/team/modeProfiles';
import { BUILTIN_RESEARCH_TEAM_NAME } from '../src/common/config/builtinMcpConstants';
import type { Assistant } from '../src/common/types/agent/assistantTypes';
import { prepareResearchTeamRoleMcpServers } from '../src/common/types/team/researchTeamMcp';
import {
  provisionResearchTeam,
  type ProvisionResearchTeamInput,
  type ResearchTeamProvisioningDeps,
} from '../src/common/types/team/researchTeamProvisioning';

function fixture(acknowledge = true) {
  const profile = createHeadlessMathematicsTeamProfile();
  let nextMcpId = 0;
  let ready = false;
  const input: ProvisionResearchTeamInput = {
    profile, projectRoot: '/math/project', userId: 'local-user', teamName: 'Proof Team',
    backend: 'codex', model: 'gpt-6.1-sol', sessionMode: 'agent-full-access', initialMessage: 'Prove the target.',
    modeConversationExtra: { headless_proof_search: true },
    requiredMcpServers: () => [BUILTIN_RESEARCH_TEAM_NAME],
    requiredSkillIds: () => [],
    buildConversationParams: role => ({ extra: {
      preset_context: `Frozen problem context\n\n${role.prompt}`,
      preset_rules: 'obsolete context alias',
      selected_session_mcp_servers: prepareResearchTeamRoleMcpServers([
        { id: 'team-mcp', name: BUILTIN_RESEARCH_TEAM_NAME,
          transport: { type: 'stdio', command: 'node', args: ['team.js'] } },
      ], profile, role, '/math/project'),
    } }),
  };
  const deps: ResearchTeamProvisioningDeps = {
    updateConversation: vi.fn(async () => undefined),
    listAssistants: vi.fn(async () => [{ id: 'bare:codex', agent_id: 'codex-runtime', enabled: true,
      team_selectable: false, agent: { acp_backend: 'codex' } } as Assistant]),
    createAssistant: vi.fn(async params => ({ id: params.id! })),
    writeAssistantRule: vi.fn(async () => undefined),
    removeAssistant: vi.fn(async () => undefined),
    createMcpServer: vi.fn(async params => ({ id: `mcp-${nextMcpId++}`, name: params.name, enabled: true })),
    toggleMcpServer: vi.fn(async ({ id }) => ({ id, name: id, enabled: true })),
    updateMcpServer: vi.fn(async () => undefined),
    removeMcpServer: vi.fn(async () => undefined),
    createTeam: vi.fn(async params => ({
      ...params, id: 'team', leader_agent_id: 'slot-0', created_at: 0, updated_at: 0,
      coordination_protocol: acknowledge ? params.coordination_protocol : { kind: 'core_native' as const },
      agents: params.agents.map((agent, index) => ({ ...agent, slot_id: `slot-${index}`, conversation_id: `conv-${index}` })),
    })),
    removeTeam: vi.fn(async () => undefined),
    setSessionMode: vi.fn(async () => undefined),
    ensureSession: vi.fn(async () => undefined),
    waitForMcpToolsReady: vi.fn(({ slotIds, onSlotReady, registerSessionReady }) => new Promise<void>(resolve => {
      registerSessionReady!(() => {
        ready = true;
        slotIds.forEach(slotId => onSlotReady!(slotId));
        resolve();
      });
    })),
    sendMessage: vi.fn(async ({ team_id }) => {
      expect(ready).toBe(true);
      return { team_id, team_run_id: 'run', target_slot_id: 'slot-0', target_role: 'lead',
        accepted_slot_id: 'slot-0', accepted_role: 'lead', status: 'accepted' };
    }),
  };
  return { input, deps };
}

describe('headless mathematics Team provisioning', () => {
  it('binds role identity and authority before starting the first turn', async () => {
    const { input, deps } = fixture();
    const result = await provisionResearchTeam(input, deps);
    expect(result.leaderConversationId).toBe('conv-0');
    expect(deps.createTeam).toHaveBeenCalledWith(expect.objectContaining({
      coordination_protocol: { kind: 'managed_mcp', logicalTool: 'research_team' },
    }));
    const rules = vi.mocked(deps.writeAssistantRule).mock.calls.map(([params]) => params.content);
    for (const [index, role] of input.profile.roles.entries()) {
      expect(rules[index]).toContain(`# Mathematics Team Operating Contract`);
      expect(rules[index].split(role.prompt)).toHaveLength(2);
      expect(rules[index]).toContain(`Current conversation id: conv-${index}`);
      expect(rules[index]).not.toContain('obsolete context alias');
      expect(rules[index].includes('Core-authenticated Research Team roster:')).toBe(role.kind === 'lead');
    }
    expect(vi.mocked(deps.writeAssistantRule).mock.invocationCallOrder.at(-1))
      .toBeLessThan(vi.mocked(deps.ensureSession).mock.invocationCallOrder[0]);
    expect(vi.mocked(deps.ensureSession).mock.invocationCallOrder[0])
      .toBeLessThan(vi.mocked(deps.sendMessage).mock.invocationCallOrder[0]);
    for (const [params] of vi.mocked(deps.updateConversation).mock.calls) {
      expect(params.updates.extra?.preset_rules).toBe('');
    }
  });

  it.each(['interactive', 'foreign'] as const)('rejects %s configuration before creating resources', async kind => {
    const { input, deps } = fixture();
    if (kind === 'interactive') input.modeConversationExtra = {};
    else input.profile = Object.freeze({ ...input.profile, id: 'other-profile' });
    await expect(provisionResearchTeam(input, deps)).rejects.toThrow('RESEARCH_TEAM_HEADLESS_MATHEMATICS_REQUIRED');
    expect(deps.listAssistants).not.toHaveBeenCalled();
    expect(deps.createMcpServer).not.toHaveBeenCalled();
  });

  it('rolls back when Core does not acknowledge managed coordination', async () => {
    const { input, deps } = fixture(false);
    await expect(provisionResearchTeam(input, deps)).rejects.toThrow('RESEARCH_TEAM_COORDINATION_PROTOCOL_NOT_OBSERVED');
    expect(deps.ensureSession).not.toHaveBeenCalled();
    expect(deps.sendMessage).not.toHaveBeenCalled();
    expect(deps.removeTeam).toHaveBeenCalledWith({ id: 'team' });
    expect(deps.removeAssistant).toHaveBeenCalledTimes(input.profile.roles.length);
    expect(deps.removeMcpServer).toHaveBeenCalledTimes(input.profile.roles.length);
  });

  it('retains first-turn failures and removes the provisioned resources', async () => {
    const { input, deps } = fixture();
    const failure = new Error('dispatch failed');
    vi.mocked(deps.sendMessage).mockRejectedValueOnce(failure);
    await expect(provisionResearchTeam(input, deps)).rejects.toBe(failure);
    expect(deps.removeTeam).toHaveBeenCalledWith({ id: 'team' });
    expect(deps.removeAssistant).toHaveBeenCalledTimes(input.profile.roles.length);
    expect(deps.removeMcpServer).toHaveBeenCalledTimes(input.profile.roles.length);
  });
});
