import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import {
  afterEach,
  describe,
  expect,
  it,
} from 'vitest';
import { Client } from '@modelcontextprotocol/sdk/client/index.js';
import { getDefaultEnvironment, StdioClientTransport } from '@modelcontextprotocol/sdk/client/stdio.js';
import {
  BUILTIN_RESEARCH_TEAM_NAME,
  BUILTIN_SCIENCE_ARTIFACT_NAME,
  RESEARCH_TEAM_CAPABILITY_ACTIONS_ENV,
} from '../src/common/config/builtinMcpConstants';
import { createHeadlessMathematicsTeamProfile } from '../src/common/chat/team/modeProfiles';
import {
  getResearchTeamRoleMcpActions,
  prepareResearchTeamRoleMcpServers,
} from '../src/common/types/team/researchTeamMcp';
import { freezeMathRunInputs } from '../src/math/mathRunInputs';
import {
  MATHEMATICS_INTERACTION_PROFILE_ENV,
  MATHEMATICS_LITE_INTERACTION_PROFILE,
} from '../src/math/mathRuntimeEnvironment';

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

function fixture(kind: 'lead' | 'worker', science = false) {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), 'math-team-mcp-'));
  roots.push(root);
  const workspace = path.join(root, 'solver');
  fs.mkdirSync(workspace);
  const frozen = freezeMathRunInputs({ parentDirectory: root, workspace, task: 'Prove the original theorem.',
    environment: { [MATHEMATICS_INTERACTION_PROFILE_ENV]: MATHEMATICS_LITE_INTERACTION_PROFILE } });
  const profile = createHeadlessMathematicsTeamProfile();
  const role = profile.roles.find(role => role.kind === kind && (!science || kind === 'lead' || role.laneId === 'lean-engineering'))!;
  const servers = prepareResearchTeamRoleMcpServers([
    { id: 'team-mcp', name: BUILTIN_RESEARCH_TEAM_NAME,
      transport: { type: 'stdio', command: process.execPath, args: [bundle] } },
    ...(science ? [{ id: 'science-mcp', name: BUILTIN_SCIENCE_ARTIFACT_NAME,
      transport: { type: 'stdio' as const, command: process.execPath, args: [bundle] } }] : []),
  ], profile, role, workspace);
  const server = servers.at(-1)!;
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

describe('mathematics tool service', () => {
  it('keeps evidence transactions atomic and publishes ordinary mathematical reports', async () => {
    const client = new Client({ name: 'math-report-test', version: '1.0.0' });
    await client.connect(new StdioClientTransport({ command: process.execPath,
      args: [path.resolve('out/main/builtin-mcp-science-artifact.js')], env: getDefaultEnvironment(), stderr: 'pipe' }));
    const call = async (args: Record<string, unknown>) => {
      const result = await client.callTool({ name: 'science_artifact', arguments: args });
      const text = (result.content as Array<{ text: string }>)[0].text;
      return { result, text, json: () => JSON.parse(text) };
    };
    try {
      const { tools } = await client.listTools();
      const artifact = tools.find(tool => tool.name === 'science_artifact')!;
      expect((artifact.inputSchema.properties!.action as { enum: string[] }).enum).not.toEqual(expect.arrayContaining(['submit_idea']));
      const description = await call({ action: 'describe' });
      expect(description.text).not.toMatch(/financeCompletion|target_portfolio|get_optimization_frontier/);
      const created = await call({ action: 'create', runId: 'report-fixture', target: { kind: 'evidence', id: 'source-1' },
        payload: { title: 'Checked local source', sourceType: 'file', confidence: 'high', summary: 'Original source' } });
      expect(created.result.isError).not.toBe(true);
      const revision = created.json().object.revision;
      const failed = await call({ action: 'transact', runId: 'report-fixture', operations: [
        { opId: 'first', action: 'patch', target: { kind: 'evidence', id: 'source-1' }, baseRevision: revision,
          payload: { summary: 'Must roll back' } },
        { opId: 'second', action: 'patch', target: { kind: 'evidence', id: 'missing-source' }, payload: { title: 'Missing' } },
      ] });
      expect(failed.result.isError).toBe(true);
      const unchanged = await call({ action: 'get', runId: 'report-fixture', target: { kind: 'evidence', id: 'source-1' } });
      expect(unchanged.json().object).toMatchObject({ summary: 'Original source', revision });
      const publication = await call({ action: 'publish', runId: 'report-fixture', payload: {
        status: 'partial', report: { title: 'Mathematical progress', sections: [{ id: 'summary', heading: 'Result',
          blocks: [{ type: 'paragraph', text: 'A local result is recorded; the full proof remains open.', evidenceIds: ['source-1'] }] }] },
      } });
      expect(publication.result.isError).not.toBe(true);
      expect(publication.json().panel).toMatchObject({ status: 'partial', report: { title: 'Mathematical progress' } });
      expect(publication.json()).not.toHaveProperty('financeReceipt');
    } finally {
      await client.close();
    }
  });

  it.each(['lead', 'worker'] as const)('preserves the %s catalog and publication boundary', async kind => {
    const { env } = fixture(kind, true);
    const transport = new StdioClientTransport({ command: process.execPath,
      args: [path.resolve('out/main/builtin-mcp-science-artifact.js')], env, stderr: 'pipe' });
    let diagnostics = '';
    transport.stderr!.on('data', data => { diagnostics = (diagnostics + data).slice(-4096); });
    const client = new Client({ name: 'math-tool-service-test', version: '1.0.0' });
    try {
      await client.connect(transport);
      const { tools } = await client.listTools();
      expect(tools.map(tool => tool.name)).toEqual(kind === 'lead'
        ? ['project_workspace', 'lean_workspace', 'formal_verifier', 'science_artifact']
        : ['lean_workspace', 'formal_verifier', 'math_portfolio', 'science_artifact']);
      const publication = await client.callTool({ name: 'science_artifact', arguments: { action: 'publish' } });
      expect(publication).toMatchObject({ isError: true,
        content: [{ type: 'text', text: expect.stringContaining('not authorized') }] });
      const verifier = await client.callTool({ name: 'formal_verifier', arguments: { action: 'check' } });
      expect(verifier).toMatchObject({ isError: true,
        content: [{ type: 'text', text: expect.stringContaining('not authorized') }] });
      if (kind === 'worker') {
        const description = await client.callTool({ name: 'lean_workspace', arguments: { action: 'describe' } });
        expect(description.isError).not.toBe(true);
        expect(description.structuredContent).toMatchObject({ tool: 'lean_workspace', action: 'describe' });
      }
    } finally {
      await client.close();
    }
    expect(diagnostics).not.toContain('Fatal error');
  });
});
