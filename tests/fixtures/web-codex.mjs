#!/usr/bin/env node
// Offline app-server fixture. It never loads a provider SDK or opens a network connection.
import fs from 'node:fs';
import path from 'node:path';
import readline from 'node:readline';

const send = value => process.stdout.write(`${JSON.stringify(value)}\n`);
const args = process.argv.slice(2);
if (args[0] === '--version') {
  process.stdout.write('codex-cli 0.0.0-web-smoke\n');
  process.exit(0);
}
if (args[0] !== 'app-server' || args[1] !== '--listen' || args[2] !== 'stdio://') {
  process.stderr.write('web_fixture_unexpected_arguments\n');
  process.exit(2);
}

let settings;
let turn;
let threadId = 'web-fixture-thread';
function checkProvider() {
  const apiKey = process.env.THEOREMOS_PROVIDER_API_KEY;
  const profile = process.env.CODEX_HOME;
  if (!apiKey?.startsWith('sk-theoremos-smoke-') || !profile) throw new Error('web_fixture_missing_byok');
  const configFile = path.join(profile, 'config.toml');
  const config = fs.readFileSync(configFile, 'utf8');
  if (config.includes(apiKey)) throw new Error('web_fixture_key_written_to_config');
  if (!/env_key\s*=\s*"THEOREMOS_PROVIDER_API_KEY"/.test(config) ||
      !/wire_api\s*=\s*"responses"/.test(config) ||
      !/requires_openai_auth\s*=\s*false/.test(config) ||
      !/exclude\s*=\s*\[\s*"THEOREMOS_PROVIDER_API_KEY"\s*\]/.test(config)) {
    throw new Error('web_fixture_bad_provider_configuration');
  }
  if ((fs.statSync(configFile).mode & 0o077) || (fs.statSync(profile).mode & 0o077))
    throw new Error('web_fixture_world_readable_configuration');
  return { apiKeyFromEnvironment: true, keyAbsentFromConfig: true, shellKeyExcluded: true,
    responsesProvider: true, privateProfile: true };
}
function complete(status = 'completed') {
  send({ method: 'turn/completed', params: { threadId, turn: { ...turn, status } } });
}

readline.createInterface({ input: process.stdin }).on('line', line => {
  let request;
  try {
    request = JSON.parse(line);
    const reply = value => send({ id: request.id, result: value });
    if (request.method === 'initialize') { reply({}); return; }
    if (request.method === 'initialized') return;
    if (request.method === 'thread/start' || request.method === 'thread/resume') {
      checkProvider();
      settings = request.params;
      threadId = settings.threadId || threadId;
      reply({ thread: { id: threadId }, model: settings.model, approvalPolicy: settings.approvalPolicy,
        reasoningEffort: settings.config.model_reasoning_effort });
      return;
    }
    if (request.method === 'turn/start') {
      const checks = checkProvider();
      const workspace = fs.realpathSync(request.params.cwd);
      if (workspace !== fs.realpathSync(settings.cwd)) throw new Error('web_fixture_workspace_changed');
      const source = path.join(workspace, 'generated/problem/Submission.lean');
      if (!fs.existsSync(source) || fs.lstatSync(source).isSymbolicLink()) throw new Error('web_fixture_missing_source');
      const message = request.params.input.filter(item => item.type === 'text').map(item => item.text).join('\n');
      turn = { id: request.params.clientUserMessageId, status: 'inProgress' };
      reply({ turn });
      fs.writeFileSync(path.join(process.env.CODEX_HOME, 'web-fixture-checks.json'), JSON.stringify(checks), { mode: 0o600 });
      send({ method: 'item/started', params: { threadId,
        item: { id: 'web-fixture-byok', type: 'commandExecution', command: 'offline fixture checks passed' } } });
      if (message.includes('WEB_SMOKE_WAIT_FOR_CANCEL') || message.includes('WEB_SMOKE_MATHLIB_WAIT_FOR_CANCEL')) return;
      const mathlib = message.includes('WEB_SMOKE_MATHLIB_');
      const original = fs.readFileSync(source, 'utf8');
      if (mathlib && !/^import Mathlib\s/m.test(original)) throw new Error('web_fixture_mathlib_import_missing');
      const proof = mathlib
        ? original.replace(/by sorry/g, message.includes('WEB_SMOKE_MATHLIB_INVALID') ? 'by exact True.intro' : 'by ring')
        : message.includes('WEB_SMOKE_INVALID_PROOF')
          ? 'namespace Tutorial\n\ntheorem add_zero (n : Nat) : n + 0 = n := by exact True.intro\n\ntheorem zero_add (n : Nat) : 0 + n = n := by exact True.intro\n\nend Tutorial\n'
          : 'namespace Tutorial\n\ntheorem add_zero (n : Nat) : n + 0 = n := by rfl\n\ntheorem zero_add (n : Nat) : 0 + n = n := by exact Nat.zero_add n\n\nend Tutorial\n';
      fs.writeFileSync(source, proof);
      send({ method: 'thread/tokenUsage/updated', params: { threadId,
        tokenUsage: { total: { totalTokens: 0 }, last: { inputTokens: 0 } } } });
      complete();
      return;
    }
    if (request.method === 'turn/interrupt') { reply({}); complete('interrupted'); return; }
    if (request.method === 'turn/steer') { reply({ turnId: turn?.id }); return; }
    if (request.id !== undefined) send({ id: request.id, error: { code: -32601, message: 'web_fixture_unknown_method' } });
  } catch (error) {
    // Fixture diagnostics identify the failed assertion without forwarding input or a key.
    const code = error instanceof Error && /^web_fixture_[a-z_]+$/.test(error.message)
      ? error.message : 'web_fixture_invalid_request';
    process.stderr.write(`${code}\n`);
    if (request?.id !== undefined) send({ id: request.id, error: { code: -32000, message: code } });
    else process.exitCode = 1;
  }
});
