import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import { afterEach, describe, expect, it } from 'vitest';
import { Client } from '@modelcontextprotocol/sdk/client/index.js';
import { getDefaultEnvironment, StdioClientTransport } from '@modelcontextprotocol/sdk/client/stdio.js';
import { BUILTIN_RESEARCH_TEAM_NAME, RESEARCH_TEAM_CAPABILITY_ACTIONS_ENV } from '../src/common/config/builtinMcpConstants';
import { createHeadlessMathematicsTeamProfile } from '../src/common/chat/team/modeProfiles';
import { getResearchTeamRoleMcpActions, prepareResearchTeamRoleMcpServers } from '../src/common/types/team/researchTeamMcp';
import { freezeMathRunInputs } from '../src/math/mathRunInputs';
import { MATHEMATICS_INTERACTION_PROFILE_ENV, MATHEMATICS_LITE_INTERACTION_PROFILE } from '../src/math/mathRuntimeEnvironment';

const bundle = path.resolve('out/main/builtin-mcp-research-team.js');
const roots: string[] = [];
afterEach(() => {
  for (const root of roots.splice(0)) {
    for (const entry of fs.readdirSync(root, { withFileTypes: true })) {
      if (entry.isDirectory()) fs.chmodSync(path.join(root, entry.name), 0o700);
    }
    fs.rmSync(root, { recursive: true, force: true });
  }
});

function fixture(kind: 'lead' | 'worker') {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), 'math-team-mcp-'));
  roots.push(root);
  const workspace = path.join(root, 'solver');
  fs.mkdirSync(workspace);
  const frozen = freezeMathRunInputs({ parentDirectory: root, workspace, task: 'Prove the original theorem.',
    environment: { [MATHEMATICS_INTERACTION_PROFILE_ENV]: MATHEMATICS_LITE_INTERACTION_PROFILE } });
  const profile = createHeadlessMathematicsTeamProfile();
  const role = profile.roles.find(role => role.kind === kind)!;
  const [server] = prepareResearchTeamRoleMcpServers([
    { id: 'team-mcp', name: BUILTIN_RESEARCH_TEAM_NAME, transport: { type: 'stdio', command: process.execPath, args: [bundle] } },
  ], profile, role, workspace);
  if (server.transport.type !== 'stdio') throw new Error('Expected stdio');
  const env = { ...getDefaultEnvironment(), ...frozen.environment, ...server.transport.env } as Record<string, string>;
  return { env, actions: getResearchTeamRoleMcpActions(role, profile.id) };
}

describe('mathematics MCP entrypoint', () => {
  it.each(['lead', 'worker'] as const)('preserves the %s tool catalog and action ceiling', async kind => {
    const { env, actions } = fixture(kind);
    // The removed Competition runtime cannot influence the mathematical catalog.
    env.DEEPSCIENTIST_IOAI_CAPABILITY_SCHEMA = 'stale-challenge-capability';
    const transport = new StdioClientTransport({ command: process.execPath, args: [bundle], env, stderr: 'pipe' });
    let diagnostics = '';
    transport.stderr!.on('data', data => { diagnostics = (diagnostics + data).slice(-4096); });
    const client = new Client({ name: 'math-entrypoint-test', version: '1.0.0' });
    try {
      await client.connect(transport);
      const { tools } = await client.listTools();
      expect(client.getServerVersion()?.name).toBe('DeepScientist Research Team');
      expect(tools.map(tool => tool.name)).toEqual(['research_team']);
      expect((tools[0].inputSchema.properties!.action as { enum: string[] }).enum).toEqual(actions);
      const forbiddenAction = kind === 'worker' ? 'dispatch' : 'deliver';
      const rejected = await client.callTool({ name: 'research_team', arguments: { action: forbiddenAction } });
      expect(rejected).toMatchObject({ isError: true,
        content: [{ type: 'text', text: expect.stringContaining('research_team_request_invalid') }] });
    } finally {
      await client.close();
    }
    expect(diagnostics).not.toContain('Fatal error');
  });

  it('requires a Research Team capability even with stale Challenge configuration', () => {
    const result = spawnSync(process.execPath, [bundle], { env: { ...getDefaultEnvironment(),
      DEEPSCIENTIST_IOAI_CAPABILITY_SCHEMA: 'stale-challenge-capability' },
      input: '', encoding: 'utf8', timeout: 10_000, maxBuffer: 8192 });
    expect(result.status).toBe(1);
    expect(result.stderr).toContain('requires a bound Research Team role capability');
  });

  it('rejects a Worker capability that grants Lead actions', () => {
    const { env } = fixture('worker');
    env[RESEARCH_TEAM_CAPABILITY_ACTIONS_ENV] = JSON.stringify(['describe', 'dispatch']);
    const result = spawnSync(process.execPath, [bundle], { env, input: '', encoding: 'utf8', timeout: 10_000, maxBuffer: 8192 });
    expect(result.status).toBe(1);
    expect(result.stderr).toContain('exceeds its hard action ceiling');
  });
});
