import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import { afterEach, beforeEach, describe, expect, it } from 'vitest';
import { MathRuntime } from '../src/runtime/mathRuntime';
import type { MathAgentOptions, MathAgentSession } from '../src/runtime/codexSession';
import { freezeMathRunInputs } from '../src/math/mathRunInputs';
import { createMathRunBinding, readMathRunBinding } from '../src/math/mathRunBinding';
import { writeMathJsonDurable, mathDigest } from '../src/math/mathRuntimeIo';
import { MathAssignmentRegistry } from '../src/math/mathAssignmentRegistry';
import { listProjectGitResearchTeamAssignments, recordProjectGitResearchTeamAssignment } from '../src/project-git/ProjectGitService';
import { fromBackendTeam } from '../src/common/adapter/teamMapper';
import { createResearchCoreTeamClient } from '../src/team/coreTeamClient';

describe('math-only Team runtime', () => {
  let directory: string;
  let workspace: string;
  let runtime: MathRuntime;
  let team: any;
  let inputs: ReturnType<typeof freezeMathRunInputs>['inputs'];
  let sessions: MathAgentOptions[];
  let turns: string[];
  let pending: Map<string, (status: string) => void>;
  const baseUrl = 'http://127.0.0.1:25820';
  const createSession = async (options: MathAgentOptions): Promise<MathAgentSession> => {
    sessions.push(options);
    let active: string | undefined;
    return {
      threadId: options.threadId ?? `thread-${sessions.length}`,
      run: async (message, id, _workspace, started) => {
        active = message;
        turns.push(message);
        started(id);
        return new Promise(resolve => pending.set(message, status => {
          pending.delete(message);
          active = undefined;
          options.onUsage({ inputTokens: 11, outputTokens: 7, totalTokens: 18 });
          resolve(status);
        }));
      },
      interrupt: async () => { if (active) pending.get(active)?.('interrupted'); },
      close: async () => { if (active) pending.get(active)?.('interrupted'); },
    };
  };
  const host = () => new MathRuntime({ dataDirectory: path.join(directory, 'state'), root: path.resolve('.'),
    baseUrl, codexExecutable: 'unused', codexProfile: 'unused', createSession });
  const response = (endpoint: string, method = 'GET', body?: any, headers = {}) => runtime.handle(new Request(baseUrl + endpoint, {
    method, headers: { 'content-type': 'application/json', ...headers }, ...(body ? { body: JSON.stringify(body) } : {}),
  }));
  const request = async (endpoint: string, method = 'GET', body?: any) => {
    const res = await response(endpoint, method, body);
    const result = await res.json() as any;
    if (!res.ok) throw new Error(`${res.status}:${result.error}`);
    return result.data;
  };
  const url = (agent: any, action = 'messages') => `/api/teams/${team.id}/agents/${agent.slot_id}/${action}`;
  const send = (agent: any, content: string, key = content) => request(url(agent), 'POST', { content, idempotency_key: key });
  beforeEach(async () => {
    directory = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'math-host-')));
    workspace = path.join(directory, 'solver');
    fs.mkdirSync(workspace);
    expect(spawnSync('git', ['init', workspace], { stdio: 'ignore' }).status).toBe(0);
    sessions = []; turns = []; pending = new Map();
    inputs = freezeMathRunInputs({ parentDirectory: directory, workspace, task: 'Prove the public target', environment: {},
      createBinding: inputs => {
        const artifactStoreRoot = path.join(directory, 'runs', mathDigest(inputs.root), 'artifacts');
        fs.mkdirSync(artifactStoreRoot, { recursive: true, mode: 0o700 });
        return createMathRunBinding({ inputs, workspace, projectRoot: workspace,
        baseCommit: 'a'.repeat(40), leanToolchain: 'leanprover/lean4:v4.31.0', lakeExecutableDigest: 'b'.repeat(64),
        toolManifestDigest: 'c'.repeat(64), buildManifestRef: path.join(directory, 'build.json'),
        buildManifestDigest: 'd'.repeat(64), artifactStoreRoot });
      },
    }).inputs;
    runtime = host();
    const agents = [];
    for (let index = 0; index < 3; index++) {
      const server = await request('/api/mcp/servers', 'POST', { name: `math-${index}`, transport: {
        type: 'stdio', command: 'node', args: ['math.js'], env: { DEEPSCIENTIST_RESEARCH_TEAM_REASONING_CONCURRENCY: '1' },
      } });
      await request(`/api/mcp/servers/${server.id}/toggle`, 'POST');
      const assistant = await request('/api/assistants', 'POST', { name: `role-${index}`, defaults: { mcps: { value: [server.id] } } });
      await request('/api/skills/assistant-rule/write', 'POST', { assistant_id: assistant.id, content: `Rules for role ${index}` });
      agents.push({ name: `role-${index}`, role: index === 0 ? 'lead' : 'teammate', model: 'gpt-6.1-sol', assistant_id: assistant.id });
    }
    team = await request('/api/teams', 'POST', { name: 'Proof Team', workspace, agents,
      coordination_protocol: { kind: 'managed_mcp', logicalTool: 'research_team' } });
    for (const agent of team.assistants) await request(`/api/conversations/${agent.conversation_id}`, 'PATCH', {
      merge_extra: true, extra: { mathematics_runtime: { run_inputs: inputs }, thought_level: 'xhigh' },
    });
    await request(`/api/teams/${team.id}/session`, 'POST');
  });
  afterEach(async () => {
    await runtime?.close();
    if (inputs) fs.chmodSync(inputs.root, 0o700);
    fs.rmSync(directory, { recursive: true, force: true });
  });

  it('preserves client contracts, durable idempotency and serial turns', async () => {
    expect(fromBackendTeam(team).agents).toHaveLength(3);
    const client = createResearchCoreTeamClient({ baseUrl, retryDelaysMs: [],
      fetchImpl: (async (input, init) => runtime.handle(new Request(input as string, init))) as typeof fetch });
    const lead = team.assistants[0];
    const first = await client.dispatch(team.id, lead.slot_id, 'first', undefined, 'first');
    await expect.poll(() => turns).toEqual(['first']);
    const replay = await client.dispatch(team.id, lead.slot_id, 'first', undefined, 'first');
    expect(replay.team_run_id).toBe(first.team_run_id);
    await expect(send(lead, 'changed', 'first')).rejects.toThrow('409:math_idempotency_payload_changed');
    await send(lead, 'second');
    const state = await client.readRunState(team.id, undefined, true);
    expect(state.slots[0].queuedForegroundCount).toBe(1);
    expect(turns).toEqual(['first']);
    pending.get('first')!('completed');
    await expect.poll(() => turns).toEqual(['first', 'second']);
    pending.get('second')!('completed');
    await expect.poll(async () => (await client.readRunState(team.id, undefined, true)).runStatus).toBe('completed');
    expect(await client.readAgentUsage!(team.id, lead.slot_id)).toMatchObject({ totalTokens: 18, inputTokens: 11 });
    expect(await client.readAgentModel!(team.id, lead.slot_id)).toEqual({ model: 'gpt-6.1-sol' });
    expect(sessions).toHaveLength(1);
  });

  it('limits Worker concurrency and lets cancellation release the next Worker', async () => {
    const [, first, second] = team.assistants;
    const ack = await send(first, 'worker-one');
    await send(second, 'worker-two');
    await expect.poll(() => turns).toEqual(['worker-one']);
    await request(`/api/teams/${team.id}/runs/${ack.team_run_id}/agents/${first.slot_id}/cancel`, 'POST');
    await expect.poll(() => turns).toEqual(['worker-one', 'worker-two']);
    expect((await request(`/api/teams/${team.id}/run-state`)).active_run.status).toBe('running');
    pending.get('worker-two')!('completed');
  });

  it('scopes role tokens, freezes live MCP configuration and rejects changed inputs', async () => {
    const mcp = Object.values(sessions[0].mcpServers)[0] as any;
    const headers = { 'x-aionui-runtime-token': mcp.env.AIONUI_RUNTIME_TOKEN,
      'x-aionui-conversation-id': mcp.env.AIONUI_CONVERSATION_ID, 'x-aionui-user-id': 'local-user' };
    expect((await response('/api/runtime/team-tools/context', 'GET', undefined, headers)).status).toBe(200);
    expect((await response('/api/assistants', 'POST', { name: 'escape' }, headers)).status).toBe(403);
    expect((await response(`/api/conversations/${team.assistants[1].conversation_id}`, 'GET', undefined, headers)).status).toBe(403);
    await send(team.assistants[1], 'worker');
    await expect.poll(() => sessions.length).toBe(2);
    const workerMcp = Object.values(sessions[1].mcpServers)[0] as any;
    const workerHeaders = { ...headers, 'x-aionui-runtime-token': workerMcp.env.AIONUI_RUNTIME_TOKEN,
      'x-aionui-conversation-id': workerMcp.env.AIONUI_CONVERSATION_ID };
    expect((await response('/api/runtime/team-tools/dispatch', 'POST', {
      target_slot_id: team.assistants[2].slot_id, content: 'escape',
    }, workerHeaders)).status).toBe(403);
    const conversation = await request(`/api/conversations/${team.assistants[0].conversation_id}`);
    await expect(request(`/api/mcp/servers/${conversation.extra.mcp_server_ids[0]}`, 'PUT', { name: 'changed' }))
      .rejects.toThrow('409:math_active_mcp_frozen');
    await expect(request(url(team.assistants[0]), 'POST', { content: 'escape', workspace: directory }))
      .rejects.toThrow('403:math_dispatch_workspace_outside_run');
    fs.chmodSync(inputs.task.path, 0o600);
    fs.appendFileSync(inputs.task.path, 'changed');
    fs.chmodSync(inputs.task.path, 0o400);
    expect((await response(url(team.assistants[0]), 'POST', { content: 'invalid' })).status).toBe(400);
  });

  it('resumes queued work with the retained thread without replaying a crashed active turn', async () => {
    const lead = team.assistants[0];
    const ack = await send(lead, 'active');
    await expect.poll(() => turns).toEqual(['active']);
    await send(lead, 'queued');
    const file = path.join(directory, 'state/math-runtime.json');
    const crash = JSON.parse(fs.readFileSync(file, 'utf8'));
    await runtime.close();
    writeMathJsonDurable(file, crash);
    runtime = host();
    expect((await request(`/api/teams/${team.id}/run-state`)).active_run.status).toBe('failed');
    await request(`/api/teams/${team.id}/session`, 'POST');
    await expect.poll(() => turns).toEqual(['active', 'queued']);
    expect(sessions[1].threadId).toBe('thread-1');
    expect((await send(lead, 'active')).team_run_id).toBe(ack.team_run_id);
    expect(turns).toEqual(['active', 'queued']);
    pending.get('queued')!('completed');
  });

  it('permits only the target Worker to use its durably bound private worktree', async () => {
    const binding = readMathRunBinding(inputs);
    const worker = team.assistants[1];
    const registry = new MathAssignmentRegistry({ binding, teamId: team.id,
      workerIds: new Set([worker.slot_id]), flockExecutable: '/usr/bin/flock', assertBinding: () => {},
      ports: {
        readAssignments: () => listProjectGitResearchTeamAssignments({ workspace, teamId: team.id, strict: true }),
        recordAssignment: recordProjectGitResearchTeamAssignment, currentCommit: () => binding.baseCommit,
        assertReadPath: () => {}, assertWritePath: () => {}, grantArtifacts: async () => [], predecessorEnded: async () => true,
      },
    });
    const receipt = await registry.prepare({ idempotencyKey: 'worktree', targetSlotId: worker.slot_id,
      kind: 'formalize', objective: 'Prove the public target', acceptance: ['Lean verifies the target'] });
    const privateWorktree = path.join(directory, 'private-worker');
    fs.mkdirSync(privateWorktree);
    recordProjectGitResearchTeamAssignment({ ...receipt, workspace, state: 'prepared',
      preparedGit: { branch: 'worker', baseCommit: binding.baseCommit, worktreePath: privateWorktree } });
    await request(url(worker), 'POST', { content: 'private-proof', workspace: privateWorktree });
    await expect.poll(() => turns).toEqual(['private-proof']);
    expect(sessions[1].workspace).toBe(privateWorktree);
    expect((await response(url(team.assistants[2]), 'POST', { content: 'escape', workspace: privateWorktree })).status).toBe(403);
    pending.get('private-proof')!('completed');
  });
});
