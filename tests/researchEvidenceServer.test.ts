import http from 'node:http';
import path from 'node:path';
import {
  afterEach,
  describe,
  expect,
  it,
} from 'vitest';
import { Client } from '@modelcontextprotocol/sdk/client/index.js';
import { getDefaultEnvironment, StdioClientTransport } from '@modelcontextprotocol/sdk/client/stdio.js';
import { BUILTIN_RESEARCH_EVIDENCE_NAME, BUILTIN_RESEARCH_TEAM_NAME } from '../src/common/config/builtinMcpConstants';
import { createHeadlessMathematicsTeamProfile } from '../src/common/chat/team/modeProfiles';
import { prepareResearchTeamRoleMcpServers } from '../src/common/types/team/researchTeamMcp';

const clients: Client[] = [];
const servers: http.Server[] = [];
afterEach(async () => {
  await Promise.all(clients.splice(0).map(client => client.close()));
  await Promise.all(servers.splice(0).map(server => new Promise<void>((resolve, reject) => server.close(error => error ? reject(error) : resolve()))));
});

async function connect(env: Record<string, string> = {}) {
  const client = new Client({ name: 'math-evidence-test', version: '1.0.0' });
  clients.push(client);
  await client.connect(new StdioClientTransport({ command: process.execPath,
    args: [path.resolve('out/main/builtin-mcp-research-evidence.js')],
    env: { ...getDefaultEnvironment(), PAPERCLIP_ENABLED: 'false', DEEPSCIENTIST_LITERATURE_SEARCH_ENABLED: 'false', ...env },
    stderr: 'pipe' }));
  return client;
}

async function call(client: Client, args: Record<string, unknown>) {
  const result = await client.callTool({ name: 'research_evidence', arguments: args });
  const text = (result.content as Array<{ text: string }>)[0].text;
  return { result, text, json: () => JSON.parse(text) };
}

describe('mathematical literature MCP', () => {
  it('advertises literature providers and routes an unconfigured search to public paper search', async () => {
    const client = await connect();
    const { tools } = await client.listTools();
    expect(tools.map(tool => tool.name)).toEqual(['research_evidence']);
    expect((tools[0].inputSchema.properties!.provider as { enum: string[] }).enum).toEqual(['auto', 'paperclip', 'paper_search']);
    expect((await call(client, { action: 'status' })).json().providers).toMatchObject({
      paperclip: { enabled: false }, paper_search: { enabled: false },
    });
    expect(Object.keys((await call(client, { action: 'status' })).json().providers)).toEqual(['paperclip', 'paper_search']);
    expect((await call(client, { action: 'list_tools' })).json().provider).toBe('paper_search');
    const search = await call(client, { action: 'search', query: 'Lean theorem' });
    expect(search.result.isError).toBe(true);
    expect(search.text).toContain('Paper search provider is disabled');
  });

  it('preserves PaperClip search results and anchored full-text reads', async () => {
    const commands: string[] = [];
    const server = http.createServer(async (request, response) => {
      let body = '';
      for await (const chunk of request) body += chunk;
      commands.push(JSON.parse(body).params.arguments.command);
      response.setHeader('content-type', 'application/json');
      response.end(JSON.stringify({ result: { content: [{ type: 'text', text: commands.length === 1
        ? 'Found 2 papers; saved as s_math\n1. Theorem\n2. Proof' : '12. Exact source statement' }] } }));
    });
    servers.push(server);
    await new Promise<void>(resolve => server.listen(0, '127.0.0.1', resolve));
    const address = server.address() as { port: number };
    const client = await connect({ PAPERCLIP_ENABLED: 'true', PAPERCLIP_API_KEY: 'fixture-key', PAPERCLIP_BASE_URL: `http://127.0.0.1:${address.port}` });
    const query = 'a "quoted" theorem';
    const search = await call(client, { action: 'search', provider: 'paperclip', source: 'arxiv', query });
    expect(search.result.isError, search.text).not.toBe(true);
    expect(search.json().results[0]).toMatchObject({ provider: 'paperclip', found: 2, savedSearchId: 's_math' });
    const read = await call(client, { action: 'read', virtualPath: '/papers/math/content.lines', anchor: { lineStart: 12, lineEnd: 15 } });
    expect(read.json().rawOutput).toBe('12. Exact source statement');
    expect(commands).toEqual([`search -s arxiv ${JSON.stringify(query)} -n 8`, 'cat "/papers/math/content.lines" --lines 12-15']);
  });

  it('keeps Worker search/read permissions and rejects broader provider actions', async () => {
    const profile = createHeadlessMathematicsTeamProfile();
    const role = profile.roles.find(role => role.kind === 'worker')!;
    const [server] = prepareResearchTeamRoleMcpServers([
      { id: 'evidence', name: BUILTIN_RESEARCH_EVIDENCE_NAME, transport: { type: 'stdio', command: process.execPath } },
      { id: 'team', name: BUILTIN_RESEARCH_TEAM_NAME, transport: { type: 'stdio', command: process.execPath } },
    ], profile, role, '/fixture');
    if (server.transport.type !== 'stdio') throw new Error('Expected stdio');
    const client = await connect(server.transport.env);
    expect((await call(client, { action: 'status' })).text).toContain('not authorized');
    expect((await call(client, { action: 'search', query: 'Lean theorem' })).text).toContain('Paper search provider is disabled');
    expect((await call(client, { action: 'read', virtualPath: '/papers/math/content.lines' })).text).toContain('PaperClip is not configured');
  });
});
