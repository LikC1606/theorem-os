import fs from 'node:fs';
import path from 'node:path';
import { randomUUID, randomBytes, timingSafeEqual } from 'node:crypto';
import { createCodexMathSession, type MathAgentOptions, type MathAgentSession } from './codexSession';
import { verifyMathRunInputs, readMathRunEnvironmentProjection, MATH_RUN_INPUTS_ENV } from '../math/mathRunInputs';
import { readMathRunBinding, isMathPathWithin } from '../math/mathRunBinding';
import { writeMathJsonDurable, canonicalMathJson, mathDigest } from '../math/mathRuntimeIo';
import { mathBuildFile } from '../math/mathBuildManifest';
import { listProjectGitResearchTeamAssignments } from '../project-git/ProjectGitService';

type Json = Record<string, any>;
type Job = { id: string; content: string; workspace: string; background: boolean };
type Agent = Json & { slot_id: string; conversation_id: string; role: string; queue: Job[]; active?: Job & { turn_id?: string; started_at: number }; error?: string };
type Team = Json & { id: string; assistants: Agent[]; session_enabled: boolean; run?: Json; acknowledgements: Record<string, { digest: string; value: Json }> };
type State = { schema: 'deepscientist.math.runtime.v1'; assistants: Record<string, Json>; servers: Record<string, Json>; conversations: Record<string, Json>; teams: Record<string, Team> };
export type MathRuntimeOptions = {
  dataDirectory: string;
  root: string;
  baseUrl: string;
  codexExecutable: string;
  codexProfile: string;
  entryFile?: string;
  createSession?: (options: MathAgentOptions) => Promise<MathAgentSession>;
  onEvent?: (name: string, data: Json) => void;
};

class RuntimeError extends Error {
  constructor(readonly status: number, message: string) { super(message); }
}
const object = (value: unknown): Json => {
  if (!value || typeof value !== 'object' || Array.isArray(value)) throw new RuntimeError(400, 'math_runtime_object_required');
  return value as Json;
};
const text = (value: unknown): string => {
  if (typeof value !== 'string' || !value.trim()) throw new RuntimeError(400, 'math_runtime_text_required');
  return value.trim();
};
const identifier = (value: unknown): string => {
  const id = text(value);
  if (!/^[a-zA-Z0-9._:-]{1,200}$/.test(id) || ['__proto__', 'constructor', 'prototype'].includes(id))
    throw new RuntimeError(400, 'math_runtime_id_invalid');
  return id;
};

/** Math-only host implementing the existing Team/MCP boundary without native Core. */
export class MathRuntime {
  private state: State;
  private file: string;
  private sessions = new Map<string, Promise<MathAgentSession>>();
  private pumps = new Map<string, Promise<void>>();
  private tokens = new Map<string, string>();
  private cancelling = new Set<string>();
  private stopping = false;
  private generation = randomUUID();
  private entry?: ReturnType<typeof mathBuildFile>;

  constructor(private options: MathRuntimeOptions) {
    this.entry = options.entryFile ? mathBuildFile(fs.realpathSync(options.entryFile)) : undefined;
    const url = new URL(options.baseUrl);
    if (!['127.0.0.1', 'localhost', '[::1]'].includes(url.hostname)) throw new Error('math_runtime_must_be_local');
    fs.mkdirSync(options.dataDirectory, { recursive: true, mode: 0o700 });
    const stat = fs.lstatSync(options.dataDirectory);
    if (!stat.isDirectory() || stat.isSymbolicLink() || (stat.mode & 0o077) ||
        (process.getuid && stat.uid !== process.getuid())) throw new Error('math_runtime_data_directory_not_private');
    this.file = path.join(options.dataDirectory, 'math-runtime.json');
    if (fs.existsSync(this.file)) {
      const stat = fs.lstatSync(this.file);
      if (!stat.isFile() || stat.nlink !== 1 || (stat.mode & 0o077)) throw new Error('math_runtime_state_not_private');
      this.state = JSON.parse(fs.readFileSync(this.file, 'utf8'));
      if (this.state.schema !== 'deepscientist.math.runtime.v1') throw new Error('math_runtime_state_schema_invalid');
      for (const team of Object.values(this.state.teams)) {
        team.session_enabled = false;
        for (const agent of team.assistants) {
          // An acknowledged active turn may already have changed a worktree.
          // Preserve its interruption, never silently replay it after a crash.
          if (agent.active) {
            agent.interrupted_message_id = agent.active.id;
            agent.active = undefined;
            if (team.run) team.run.status = 'failed';
          }
        }
      }
    } else {
      this.state = { schema: 'deepscientist.math.runtime.v1', assistants: {}, servers: {}, conversations: {}, teams: {} };
    }
    this.save();
  }

  private save(): void { writeMathJsonDurable(this.file, this.state); }
  private event(team: Team, name: string, extra: Json = {}): void {
    this.options.onEvent?.(name, { team_id: team.id, team_run_id: team.run?.team_run_id, status: team.run?.status ?? 'accepted', ...extra });
  }
  private team(id: string): Team {
    const team = this.state.teams[identifier(id)];
    if (!team) throw new RuntimeError(404, 'math_team_not_found');
    return team;
  }
  private agent(team: Team, id: string): Agent {
    const agent = team.assistants.find(agent => agent.slot_id === id);
    if (!agent) throw new RuntimeError(404, 'math_agent_not_found');
    return agent;
  }
  private conversation(id: string): Json {
    const conversation = this.state.conversations[identifier(id)];
    if (!conversation) throw new RuntimeError(404, 'math_conversation_not_found');
    return conversation;
  }
  private inputs(agent: Agent): ReturnType<typeof verifyMathRunInputs> {
    const conversation = this.conversation(agent.conversation_id);
    const inputs = verifyMathRunInputs(conversation.extra?.mathematics_runtime?.run_inputs);
    if (!inputs.binding) throw new RuntimeError(400, 'math_run_binding_required');
    readMathRunBinding(inputs);
    return inputs;
  }
  private workspace(agent: Agent, value?: unknown): string {
    const conversation = this.conversation(agent.conversation_id);
    const root = fs.realpathSync(text(conversation.extra?.workspace));
    const requested = value === undefined ? root : fs.realpathSync(text(value));
    const binding = readMathRunBinding(this.inputs(agent));
    if (requested !== root && !isMathPathWithin(binding.generatedSourceRoot, requested)) {
      const authorized = listProjectGitResearchTeamAssignments({ workspace: binding.workspace,
        teamId: conversation.extra.team_id, strict: true }).some(receipt => {
        const assignment = receipt.assignment as Json;
        return receipt.slotId === agent.slot_id && !['integrated', 'superseded'].includes(receipt.state) &&
          receipt.preparedGit?.worktreePath === requested && assignment.runId === binding.runId &&
          assignment.bindingDigest === mathDigest(canonicalMathJson(binding));
      });
      if (!authorized) throw new RuntimeError(403, 'math_dispatch_workspace_outside_run');
    }
    return requested;
  }
  private snapshot(team: Team): Json {
    const slots = team.assistants.map(agent => ({
      slot_id: agent.slot_id, role: agent.role,
      state: agent.active ? (agent.active.turn_id ? 'running' : 'starting') : agent.queue.length ? 'queued' : 'idle',
      queued_foreground_count: agent.queue.filter(job => !job.background).length,
      queued_background_count: agent.queue.filter(job => job.background).length,
      pending_wake_count: 0,
      ...(agent.active ? { active_turn_id: agent.active.turn_id, active_turn_started_at_ms: agent.active.started_at,
        active_turn_elapsed_ms: Date.now() - agent.active.started_at, team_run_id: team.run?.team_run_id } : {}),
      ...(agent.error ? { blocked_reason: 'runtime_failed' } : {}),
    }));
    const run = team.run ? { ...team.run, slot_work: slots,
      queued_intent_count: team.assistants.reduce((n, agent) => n + agent.queue.length, 0),
      starting_batch_count: team.assistants.filter(agent => agent.active && !agent.active.turn_id).length,
      running_batch_count: team.assistants.filter(agent => agent.active?.turn_id).length,
      active_enqueue_lease_count: 0,
    } : null;
    return { team_id: team.id, session_generation: this.generation, active_run: run, slot_work: slots };
  }
  private teamView(team: Team): Json {
    return { id: team.id, name: team.name, workspace: team.workspace, workspace_mode: 'isolated',
      user_id: 'local-user', session_mode: team.session_mode, coordination_protocol: team.coordination_protocol,
      leader_assistant_id: team.assistants.find(agent => agent.role === 'lead')?.slot_id,
      assistants: team.assistants.map(({ queue, active, error, ...agent }) => ({ ...agent, status: active ? 'working' : 'idle' })),
    };
  }

  private async ensureAgent(team: Team, agent: Agent, workspace?: string): Promise<MathAgentSession> {
    if (this.stopping) throw new RuntimeError(503, 'math_runtime_stopping');
    this.inputs(agent);
    const existing = this.sessions.get(agent.conversation_id);
    if (existing) return existing;
    const start = (async () => {
      const conversation = this.conversation(agent.conversation_id);
      const extra = object(conversation.extra);
      const assistant = this.state.assistants[agent.assistant_id];
      const env = object(readMathRunEnvironmentProjection(this.inputs(agent)));
      const token = randomBytes(32).toString('hex');
      this.tokens.set(agent.conversation_id, token);
      if (!Array.isArray(extra.mcp_server_ids) || !extra.mcp_server_ids.length) throw new Error('math_role_mcp_missing');
      const servers = Object.fromEntries(extra.mcp_server_ids.map((id: string) => {
        const server = this.state.servers[id];
        if (!server?.enabled || server.transport?.type !== 'stdio') throw new Error('math_role_mcp_unavailable');
        const transport = server.transport;
        return [identifier(server.name), { command: text(transport.command), args: transport.args ?? [], enabled: true,
          env: { ...transport.env, ...env, [MATH_RUN_INPUTS_ENV]: JSON.stringify(this.inputs(agent)),
            DEEPSCIENTIST_MATH_ENV_FILE: this.inputs(agent).environment.path,
            AIONUI_BASE_URL: this.options.baseUrl, AIONUI_USER_ID: 'local-user',
            AIONUI_CONVERSATION_ID: agent.conversation_id, AIONUI_RUNTIME_TOKEN: token },
        }];
      }));
      const skill = path.join(this.options.root, 'resources/skills/deepscientist-mathematics/SKILL.md');
      const instructions = [extra.preset_context || assistant.rule || '', fs.readFileSync(skill, 'utf8')].join('\n\n');
      const session = await (this.options.createSession ?? createCodexMathSession)({
        executable: this.options.codexExecutable, profile: this.options.codexProfile,
        workspace: workspace ?? this.workspace(agent), model: text(agent.model), effort: extra.thought_level ?? 'xhigh',
        instructions, mcpServers: servers, threadId: agent.thread_id,
        onUsage: usage => { agent.usage = usage; this.save(); },
      });
      agent.thread_id = session.threadId;
      agent.error = undefined;
      this.save();
      this.event(team, 'team.agentReady', { slot_id: agent.slot_id });
      return session;
    })();
    this.sessions.set(agent.conversation_id, start);
    try { return await start; }
    catch (error) { this.sessions.delete(agent.conversation_id); this.tokens.delete(agent.conversation_id); throw error; }
  }

  private schedule(team: Team, agent: Agent): void {
    if (this.stopping || !team.session_enabled || this.cancelling.has(agent.conversation_id) ||
        this.pumps.has(agent.slot_id) || !agent.queue.length || agent.error) return;
    const limit = Number(team.reasoning_concurrency ?? 1);
    if (agent.role !== 'lead' && team.assistants.filter(agent => agent.role !== 'lead' && agent.active).length >= limit) return;
    const pump = this.pump(team, agent).finally(() => {
      this.pumps.delete(agent.slot_id);
      for (const next of team.assistants) this.schedule(team, next);
    });
    this.pumps.set(agent.slot_id, pump);
  }
  private async pump(team: Team, agent: Agent): Promise<void> {
    while (!this.stopping && team.session_enabled && !this.cancelling.has(agent.conversation_id) && agent.queue.length && !agent.error) {
      const job = agent.queue.shift()!;
      agent.active = { ...job, started_at: Date.now() };
      if (!team.assistants.some(agent => agent.error)) team.run!.status = 'running';
      this.save();
      this.event(team, 'team.runUpdated');
      try {
        this.inputs(agent);
        const session = await this.ensureAgent(team, agent, job.workspace);
        if (this.stopping || !team.session_enabled || this.cancelling.has(agent.conversation_id)) break;
        // Verify again after session initialization, before the provider request.
        this.inputs(agent);
        this.workspace(agent, job.workspace);
        const status = await session.run(job.content, job.id, job.workspace, turnId => {
          if (!agent.active) throw new Error('math_turn_cancelled_before_start');
          agent.active.turn_id = turnId;
          this.save();
          this.event(team, 'team.childTurnStarted', { slot_id: agent.slot_id, turn_id: turnId });
        });
        if (status === 'failed') throw new Error('math_model_turn_failed');
      } catch {
        if (!this.stopping && team.session_enabled && !this.cancelling.has(agent.conversation_id)) {
          agent.error = 'math_agent_turn_failed';
          team.run!.status = 'failed';
        }
      } finally {
        const turnId = agent.active?.turn_id ?? job.id;
        if (this.stopping) agent.interrupted_message_id = job.id;
        agent.active = undefined;
        if (team.assistants.every(agent => !agent.active && !agent.queue.length) && team.run!.status === 'running') team.run!.status = 'completed';
        this.save();
        this.event(team, 'team.childTurnCompleted', { slot_id: agent.slot_id, turn_id: turnId });
        this.event(team, 'team.runUpdated');
      }
    }
  }
  private enqueue(team: Team, agent: Agent, body: Json, background = false): Json {
    if (!team.session_enabled) throw new RuntimeError(409, 'math_session_stopped');
    this.inputs(agent);
    const workspace = this.workspace(agent, body.workspace);
    const content = text(body.content);
    if (Buffer.byteLength(content) > 4 * 1024 * 1024) throw new RuntimeError(413, 'math_message_too_large');
    const key = body.idempotency_key ? identifier(body.idempotency_key) : randomUUID();
    const scopedKey = `${agent.slot_id}:${background ? 'delivery' : 'message'}:${key}`;
    const digest = mathDigest(canonicalMathJson({ content, workspace }));
    const old = team.acknowledgements[scopedKey];
    if (old) {
      if (old.digest !== digest) throw new RuntimeError(409, 'math_idempotency_payload_changed');
      return { ...old.value, replayed: true };
    }
    if (agent.error) throw new RuntimeError(409, 'math_agent_runtime_failed');
    if (!team.run || (['completed', 'cancelled', 'failed'].includes(team.run.status) &&
        team.assistants.every(agent => !agent.active && !agent.queue.length))) {
      team.run = { team_id: team.id, team_run_id: randomUUID(), status: 'accepted', target_slot_id: agent.slot_id, target_role: agent.role };
    }
    const job = { id: randomUUID(), content, workspace, background };
    agent.queue.push(job);
    const value = { team_id: team.id, team_run_id: team.run.team_run_id, target_slot_id: agent.slot_id,
      target_role: agent.role, accepted_slot_id: agent.slot_id, accepted_role: agent.role, status: 'accepted',
      enqueue_status: agent.active ? 'queued' : 'accepted', message_id: job.id, replayed: false };
    team.acknowledgements[scopedKey] = { digest, value };
    this.save();
    this.event(team, 'team.runUpdated');
    queueMicrotask(() => this.schedule(team, agent));
    return value;
  }

  private async stopAgent(team: Team, agent: Agent, preserveQueued = false): Promise<void> {
    this.cancelling.add(agent.conversation_id);
    if (!preserveQueued) agent.queue = [];
    const session = this.sessions.get(agent.conversation_id);
    this.sessions.delete(agent.conversation_id);
    if (session) {
      const runtime = await session.catch(() => undefined);
      if (runtime) { await runtime.interrupt().catch(() => {}); await runtime.close(); }
    }
    await this.pumps.get(agent.slot_id);
    agent.active = undefined;
    agent.error = undefined;
    this.tokens.delete(agent.conversation_id);
    this.cancelling.delete(agent.conversation_id);
    this.save();
  }
  private async stopTeam(team: Team, preserveQueued = false): Promise<void> {
    team.session_enabled = false;
    if (team.run) team.run.status = 'cancelled';
    this.save();
    await Promise.all(team.assistants.map(agent => this.stopAgent(team, agent, preserveQueued)));
    this.event(team, 'team.runUpdated');
  }
  async close(): Promise<void> {
    this.stopping = true;
    await Promise.all(Object.values(this.state.teams).map(team => this.stopTeam(team, true)));
    this.save();
  }

  async handle(request: Request): Promise<Response> {
    try {
      const origin = request.headers.get('origin');
      if (origin && origin !== this.options.baseUrl) throw new RuntimeError(403, 'math_runtime_origin_forbidden');
      const url = new URL(request.url);
      const parts = url.pathname.split('/').filter(Boolean).map(decodeURIComponent);
      const method = request.method;
      let body: Json = {};
      if (['POST', 'PATCH', 'PUT'].includes(method)) {
        if (request.headers.get('content-type') && !request.headers.get('content-type')!.startsWith('application/json'))
          throw new RuntimeError(415, 'math_runtime_json_required');
        const data = await request.text();
        if (Buffer.byteLength(data) > 5 * 1024 * 1024) throw new RuntimeError(413, 'math_request_too_large');
        if (data) body = object(JSON.parse(data));
      }
      let caller: Json | undefined;
      if (request.headers.has('x-aionui-runtime-token') || parts[1] === 'runtime') {
        const id = request.headers.get('x-aionui-conversation-id') ?? '';
        const actual = request.headers.get('x-aionui-runtime-token') ?? '';
        const expected = this.tokens.get(id);
        if (!expected || actual.length !== expected.length || !timingSafeEqual(Buffer.from(actual), Buffer.from(expected)) ||
            request.headers.get('x-aionui-user-id') !== 'local-user') throw new RuntimeError(403, 'math_runtime_token_invalid');
        caller = this.conversation(id);
      }
      const result = await this.route(parts, method, body, caller);
      return Response.json({ success: true, data: result });
    } catch (error) {
      const status = error instanceof RuntimeError ? error.status : 400;
      return Response.json({ success: false, error: error instanceof Error ? error.message : 'math_runtime_request_failed' }, { status });
    }
  }

  private async route(parts: string[], method: string, body: Json, caller?: Json): Promise<unknown> {
    const [, resource, id, action, target, subaction, childId, childAction] = parts;
    if (parts[0] !== 'api') throw new RuntimeError(404, 'math_runtime_route_not_found');
    if (caller) {
      const allowed = (resource === 'runtime' && id === 'team-tools') || (method === 'GET' && (
        (resource === 'conversations' && id === caller.id) ||
        (resource === 'teams' && id === caller.extra.team_id && (!action || action === 'run-state')) ||
        (resource === 'mcp' && id === 'servers' && caller.extra.mcp_server_ids?.includes(action))
      ));
      if (!allowed) throw new RuntimeError(403, 'math_runtime_role_scope_forbidden');
    }
    if (resource === 'system' && id === 'info') return { runtime: 'deepscientist-math', runtime_kind: 'bun', runtime_process_id: process.pid };
    if (resource === 'conversations' && id === 'runtime-capabilities' && method === 'GET') return {
      runtime_process_id: process.pid, math_run_inputs: { supported_versions: [2] },
      runtime_kind: 'deepscientist-math.bun.v1', runtime_entry: this.entry,
      math_acp_isolation: { enabled: false, protocol_version: 1 },
    };
    if (resource === 'runtime' && id === 'team-tools') {
      const team = this.team(caller!.extra.team_id);
      const source = this.agent(team, caller!.extra.team_slot_id);
      if (action === 'context' && method === 'GET') return { in_team: true, team_id: team.id, slot_id: source.slot_id };
      if (action === 'dispatch' && method === 'POST') {
        const agent = this.agent(team, text(body.target_slot_id));
        if (source.role !== 'lead' && agent !== source && agent.role !== 'lead') throw new RuntimeError(403, 'math_role_dispatch_forbidden');
        return this.enqueue(team, agent, body);
      }
    }
    if (resource === 'assistants') {
      if (!id && method === 'GET') return Object.values(this.state.assistants);
      if (!id && method === 'POST') {
        const key = identifier(body.id ?? randomUUID());
        if (this.state.assistants[key]) throw new RuntimeError(409, 'math_assistant_exists');
        this.state.assistants[key] = { ...body, id: key, backend: 'codex' };
        this.save(); return this.state.assistants[key];
      }
      if (id && method === 'DELETE') { delete this.state.assistants[identifier(id)]; this.save(); return {}; }
    }
    if (resource === 'skills' && id === 'assistant-rule' && action === 'write' && method === 'POST') {
      const assistant = this.state.assistants[identifier(body.assistant_id)];
      if (!assistant) throw new RuntimeError(404, 'math_assistant_not_found');
      assistant.rule = text(body.content); this.save(); return {};
    }
    if (resource === 'mcp' && id === 'servers') {
      if (!action && method === 'GET') return Object.values(this.state.servers);
      if (!action && method === 'POST') {
        const key = randomUUID(); this.state.servers[key] = { ...body, id: key, enabled: false };
        this.save(); return this.state.servers[key];
      }
      const server = this.state.servers[identifier(action)];
      if (!server) throw new RuntimeError(404, 'math_mcp_server_not_found');
      if (method === 'GET') return server;
      if (Object.values(this.state.conversations).some(conversation =>
          this.sessions.has(conversation.id) && conversation.extra.mcp_server_ids?.includes(action)))
        throw new RuntimeError(409, 'math_active_mcp_frozen');
      if (method === 'DELETE') delete this.state.servers[action];
      else if (method === 'POST' && target === 'toggle') server.enabled = !server.enabled;
      else if (method === 'PUT') Object.assign(server, body, { id: action });
      else throw new RuntimeError(404, 'math_runtime_route_not_found');
      this.save(); return server;
    }
    if (resource === 'conversations') {
      const conversation = this.conversation(id);
      const team = this.team(conversation.extra.team_id);
      const agent = this.agent(team, conversation.extra.team_slot_id);
      if (caller && caller.id !== id) throw new RuntimeError(403, 'math_conversation_scope_forbidden');
      if (method === 'GET' && !action) return conversation;
      if (method === 'PATCH' && !action) {
        if (this.sessions.has(id)) throw new RuntimeError(409, 'math_active_conversation_frozen');
        const oldExtra = conversation.extra;
        const next: Json = { ...conversation, ...body, id, extra: body.merge_extra ? { ...oldExtra, ...body.extra } : body.extra ?? oldExtra };
        if (next.extra.team_id !== team.id || next.extra.team_slot_id !== agent.slot_id)
          throw new RuntimeError(400, 'math_conversation_identity_changed');
        delete next.merge_extra;
        Object.assign(conversation, next);
        this.save(); return conversation;
      }
      if (method === 'GET' && action === 'usage') {
        const usage = agent.usage ?? {};
        return { measurement: 'token_totals', input_tokens: usage.inputTokens ?? 0, cached_input_tokens: usage.cachedInputTokens ?? 0,
          output_tokens: usage.outputTokens ?? 0, reasoning_output_tokens: usage.reasoningOutputTokens ?? 0, total_tokens: usage.totalTokens ?? 0 };
      }
      if (method === 'POST' && action === 'cancel') { await this.stopAgent(team, agent); return {}; }
    }
    if (resource === 'teams') {
      if (!id && method === 'POST') {
        const key = randomUUID();
        if (body.coordination_protocol?.kind !== 'managed_mcp' || body.coordination_protocol.logicalTool !== 'research_team' ||
            !Array.isArray(body.agents) || !body.agents.length || body.agents.filter((agent: Json) => agent.role === 'lead').length !== 1)
          throw new RuntimeError(400, 'math_team_contract_invalid');
        const agents: Agent[] = body.agents.map((requested: Json) => {
          const assistant = this.state.assistants[identifier(requested.assistant_id)];
          if (!assistant) throw new RuntimeError(404, 'math_assistant_not_found');
          return { ...requested, role: text(requested.role), assistant_backend: 'codex', agent_type: 'codex',
            slot_id: randomUUID(), conversation_id: randomUUID(), queue: [], model: text(requested.model),
            defaults: assistant.defaults };
        });
        const team: Team = { id: key, name: text(body.name), workspace: text(body.workspace),
          coordination_protocol: body.coordination_protocol, assistants: agents, session_enabled: false, acknowledgements: {} };
        this.state.teams[key] = team;
        for (const agent of agents) this.state.conversations[agent.conversation_id] = { id: agent.conversation_id,
          type: 'acp', extra: { team_id: key, team_slot_id: agent.slot_id, workspace: team.workspace,
            backend: 'codex', mcp_server_ids: agent.defaults?.mcps?.value ?? [] } };
        this.save(); return this.teamView(team);
      }
      const team = this.team(id);
      if (caller && caller.extra.team_id !== team.id) throw new RuntimeError(403, 'math_team_scope_forbidden');
      if (!action && method === 'GET') return this.teamView(team);
      if (!action && method === 'DELETE') {
        await this.stopTeam(team);
        for (const agent of team.assistants) delete this.state.conversations[agent.conversation_id];
        delete this.state.teams[team.id]; this.save(); return {};
      }
      if (action === 'run-state' && method === 'GET') return this.snapshot(team);
      if (action === 'session-mode' && method === 'POST') { team.session_mode = text(body.mode); this.save(); return {}; }
      if (action === 'session' && method === 'POST') {
        for (const agent of team.assistants) this.inputs(agent);
        const lead = team.assistants.find(agent => agent.role === 'lead')!;
        const ids = this.conversation(lead.conversation_id).extra.mcp_server_ids;
        const env = ids.map((id: string) => this.state.servers[id]?.transport?.env)
          .find((env: Json) => env?.DEEPSCIENTIST_RESEARCH_TEAM_REASONING_CONCURRENCY);
        const concurrency = Number(env?.DEEPSCIENTIST_RESEARCH_TEAM_REASONING_CONCURRENCY ?? 1);
        if (!Number.isSafeInteger(concurrency) || concurrency < 1) throw new RuntimeError(400, 'math_team_concurrency_invalid');
        team.reasoning_concurrency = concurrency;
        await this.ensureAgent(team, lead);
        team.session_enabled = true; this.save();
        for (const agent of team.assistants) this.schedule(team, agent);
        return {};
      }
      if (action === 'session' && method === 'DELETE') { await this.stopTeam(team); return {}; }
      if (action === 'agents') {
        const agent = this.agent(team, target);
        if (subaction === 'runtime' && method === 'POST') { await this.ensureAgent(team, agent); return {}; }
        if (subaction === 'messages' && method === 'POST') return this.enqueue(team, agent, body);
        if (subaction === 'deliveries' && method === 'POST') {
          const lead = team.assistants.find(agent => agent.role === 'lead')!;
          const ack = this.enqueue(team, lead, body, true);
          return { ...ack, target: { slot_id: lead.slot_id, role: 'lead', state: 'queued' }, source_slot_id: agent.slot_id,
            idempotency_key: body.idempotency_key, delivery_id: ack.message_id, payload_hash: mathDigest(text(body.content)), persisted: true };
        }
      }
      if (action === 'runs' && target === team.run?.team_run_id && method === 'POST') {
        if (subaction === 'cancel') { await this.stopTeam(team); return {}; }
        if (subaction === 'agents' && childAction === 'cancel') { await this.stopAgent(team, this.agent(team, childId)); return {}; }
      }
    }
    throw new RuntimeError(404, 'math_runtime_route_not_found');
  }
}
