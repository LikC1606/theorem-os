import assert from 'node:assert/strict';
import crypto from 'node:crypto';
import fs from 'node:fs';
import path from 'node:path';
import { spawn } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import { parseArgs } from 'node:util';
import { WebJobs } from '../apps/web/jobs';
import { DockerWebRunner } from '../apps/web/runner';
import { webTemplates } from '../apps/web/config';
import { getLeanTaskEnvironment } from '../src/math/leanTaskEnvironment';
import type { WebEnvironment, WebRun, WebRunInput, WorkerMessage } from '../apps/web/shared';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const pause = (ms: number) => new Promise(resolve => setTimeout(resolve, ms));
export function assertWebContainerBoundary(inspectJson: string, apiKey: string, environment: WebEnvironment = 'standard') {
  assert.ok(!inspectJson.includes(apiKey), 'Docker metadata must not contain the API key.');
  const container = JSON.parse(inspectJson)[0];
  assert.equal(container.State.Running, true, 'Cancellation must target a running fixture.');
  assert.equal(container.Config.User, '10001:10001', 'The worker must run as its unprivileged user.');
  assert.equal(container.HostConfig.ReadonlyRootfs, true, 'The worker root filesystem must be read-only.');
  assert.ok(container.HostConfig.CapDrop?.some((value: string) => value.toUpperCase() === 'ALL'), 'The worker must drop all Linux capabilities.');
  assert.equal(container.HostConfig.Privileged, false, 'The worker must not run privileged.');
  const memory = (environment === 'mathlib' ? 8 : 4) * 1024 ** 3;
  assert.equal(container.HostConfig.Memory, memory, 'The worker must retain its environment memory limit.');
  assert.equal(container.HostConfig.MemorySwap, memory, 'The worker must retain its environment swap limit.');
  assert.equal(container.HostConfig.PidsLimit, 256, 'The worker must retain its process limit.');
  assert.equal(container.HostConfig.NanoCpus, 2 * 1e9, 'The worker must retain its CPU limit.');
  assert.equal(container.HostConfig.MaskedPaths?.length || 0, 0, 'Nested nonprivileged sandboxes require unmasked system paths.');
  assert.equal(container.HostConfig.ReadonlyPaths?.length || 0, 0, 'Nested nonprivileged sandboxes require no default read-only system paths.');
  assert.notEqual(container.HostConfig.PidMode, 'host', 'The worker must keep an isolated process namespace.');
  assert.ok(container.HostConfig.SecurityOpt?.some((value: string) => /^no-new-privileges(?::true)?$/.test(value)),
    'The worker must prohibit gaining privileges.');
  assert.equal(container.HostConfig.Binds?.length || 0, 0, 'Worker containers must not bind any host paths or Docker sockets.');
  assert.ok(!container.Mounts?.some((mount: { Type?: string }) => mount.Type === 'bind'), 'Inspect mounts must not contain host binds.');
  const volumes = container.Mounts?.filter((mount: { Type?: string }) => mount.Type === 'volume') || [];
  if (environment === 'mathlib') {
    assert.equal(container.HostConfig.Devices?.length, 1, 'The worker must receive only its FUSE device.');
    assert.equal(container.HostConfig.Devices[0].PathOnHost, '/dev/fuse', 'The worker must not receive unrelated host devices.');
    assert.equal(container.HostConfig.Devices[0].PathInContainer, '/dev/fuse');
    assert.equal(container.HostConfig.Devices[0].CgroupPermissions, 'rw', 'FUSE access must not grant device creation.');
    assert.equal(volumes.length, 1, 'Each Mathlib worker must own one anonymous verification volume.');
    assert.equal(volumes[0].Destination, '/var/tmp');
    assert.equal(volumes[0].Driver, 'local');
    assert.equal(volumes[0].RW, true);
    assert.match(volumes[0].Name, /^[a-f0-9]{64}$/, 'The verification volume must have a Docker-generated anonymous name.');
  } else {
    assert.equal(container.HostConfig.Devices?.length || 0, 0, 'Standard-library workers must not receive host devices.');
    assert.equal(volumes.length, 0, 'Standard-library workers must not receive persistent volumes.');
  }
  assert.ok(container.HostConfig.Tmpfs?.['/work'], 'The isolated work directory must be temporary.');
  assert.ok(container.HostConfig.Tmpfs?.['/tmp'], 'The isolated temporary directory must be temporary.');
  return volumes.map((volume: { Name: string }) => volume.Name);
}

export function assertWebEnvironmentReport(report: Record<string, unknown>, environment: WebEnvironment) {
  const trusted = getLeanTaskEnvironment(environment);
  assert.deepEqual(report.environment, { id: trusted.id, toolchain: trusted.toolchain, dependencyDigest: trusted.dependencyDigest,
    ...(trusted.mathlibRevision ? { mathlibRevision: trusted.mathlibRevision } : {}) }, 'The report must bind its exact trusted dependency environment.');
}

async function docker(args: string[], options: { allowFailure?: boolean; stream?: boolean; timeout?: number } = {}) {
  return await new Promise<{ code: number; stdout: string; stderr: string }>((resolve, reject) => {
    const child = spawn('docker', args, { cwd: root, stdio: ['ignore', 'pipe', 'pipe'] });
    let stdout = '', stderr = '', timedOut = false;
    const timer = setTimeout(() => { timedOut = true; child.kill('SIGKILL'); }, options.timeout || 30_000);
    child.stdout.on('data', chunk => { stdout += chunk; if (options.stream) process.stdout.write(chunk); });
    child.stderr.on('data', chunk => { stderr += chunk; if (options.stream) process.stderr.write(chunk); });
    child.once('error', error => { clearTimeout(timer); reject(error); });
    child.once('close', code => {
      clearTimeout(timer);
      if (timedOut) { reject(new Error(`Docker fixture command timed out: ${args[0]}`)); return; }
      if (code !== 0 && !options.allowFailure) {
        reject(new Error(`Docker fixture command failed (${args[0]}): ${stderr.trim() || code}`)); return;
      }
      resolve({ code: code ?? 1, stdout, stderr });
    });
  });
}

export async function runWebRuntimeSmoke(argv = process.argv.slice(2)) {
  const { values } = parseArgs({ args: argv, options: {
    'base-image': { type: 'string', default: 'theorem-os-worker:local' },
    image: { type: 'string', default: `theorem-os-worker:web-smoke-${process.pid}` },
    case: { type: 'string', default: 'all' },
    'skip-build': { type: 'boolean', default: false }, 'keep-image': { type: 'boolean', default: false },
    help: { type: 'boolean', default: false },
  } });
  if (values.help) {
    console.log('bun scripts/test-web-runtime.ts [--base-image theorem-os-worker:local] [--image TAG] [--case all|valid|invalid|mathlib-valid|mathlib-invalid|cancel|mathlib-cancel|cancel-early] [--skip-build] [--keep-image]');
    console.log('Uses an offline fake Codex app-server and real isolated Lean checks. No model is called.');
    return;
  }
  if (!['all', 'valid', 'invalid', 'mathlib-valid', 'mathlib-invalid', 'cancel', 'mathlib-cancel', 'cancel-early'].includes(values.case!)) throw new Error('Unknown smoke case.');
  const image = values.image!;
  assert.notEqual(image, values['base-image'], 'Use a distinct fixture image tag; the real worker image must remain intact.');
  const runner = new DockerWebRunner({ workerImage: image });
  const owner = `web-runtime-smoke-${crypto.randomUUID()}`;
  const messages = new Map<string, { type: WorkerMessage['type']; observedAt: string;
    runStatus?: WebRun['status']; resultAlreadyPresent: boolean }[]>();
  const jobs = new WebJobs({ readiness: () => runner.readiness(), run: (input, onMessage, signal) =>
    runner.run(input, message => {
      onMessage(message);
      const run = jobs.get(owner, input.id);
      const observed = messages.get(input.id) ?? [];
      observed.push({ type: message.type, observedAt: new Date().toISOString(),
        runStatus: run?.status, resultAlreadyPresent: Boolean(run?.result) });
      messages.set(input.id, observed);
    }, signal) }, { concurrency: 1, queueLimit: 3 });
  const provider = { id: 'offline-fixture', name: 'Offline fixture', baseUrl: 'https://no-provider.invalid/v1' };
  const apiKey = `sk-theoremos-smoke-${crypto.randomBytes(24).toString('hex')}`;
  const containerIds = new Set<string>();
  const observedVolumes = new Set<string>();
  const outcomes: Record<string, unknown>[] = [];
  let builtFixture = false;
  const makeInput = (marker: string): WebRunInput => {
    const environment = marker.includes('WEB_SMOKE_MATHLIB_') ? 'mathlib' : 'standard';
    const template = webTemplates.find(template => template.id === (environment === 'mathlib' ? 'polynomial' : 'addition'));
    assert.ok(template && template.environment === environment, 'Smoke source must use the matching published template.');
    return { providerId: provider.id, apiKey, environment, model: 'offline-fixture', effort: 'xhigh', source: template.source,
      task: `${marker}\n${template.task}`, maxTurns: 1, maxRunSeconds: environment === 'mathlib' ? 180 : 90,
      workers: 1, coordination: 'independent' };
  };
  const terminal = (run: WebRun) => ['completed', 'error', 'cancelled'].includes(run.status);
  const waitFor = async (run: WebRun, predicate: () => boolean, timeout = run.environment === 'mathlib' ? 900_000 : 300_000) => {
    const deadline = Date.now() + timeout;
    let phase = '', lastLog = 0;
    while (!predicate()) {
      if (run.phase !== phase || Date.now() - lastLog >= 30_000) {
        phase = run.phase; lastLog = Date.now();
        console.log(`Smoke ${run.title.split('\n')[0]}: ${phase} (${Math.round((Date.now() - (deadline - timeout)) / 1_000)}s)`);
      }
      if (Date.now() > deadline) throw new Error(`Smoke case timed out in ${run.phase}: ${run.error || run.result?.status || run.status}`);
      if (terminal(run)) throw new Error(`Smoke ended before its checkpoint: ${run.error || run.result?.status || run.status}`);
      await pause(200);
    }
  };
  const noContainer = async (run: Pick<WebRun, 'id'>) => {
    const name = `theoremos-web-${run.id}`;
    const deadline = Date.now() + 25_000;
    for (;;) {
      const inspected = await docker(['container', 'inspect', name], { allowFailure: true });
      if (inspected.code !== 0) {
        assert.match(inspected.stderr, /No such (?:object|container)/i, 'Container absence must be confirmed by Docker.');
        return;
      }
      if (Date.now() >= deadline) throw new Error(`Smoke container was not removed: ${name}`);
      await pause(200);
    }
  };
  const noVolume = async (name: string) => {
    const deadline = Date.now() + 25_000;
    for (;;) {
      const removed = await docker(['volume', 'inspect', name], { allowFailure: true });
      if (removed.code !== 0) {
        assert.match(removed.stderr, /no such volume|volume .* not found/i, 'Volume absence must be confirmed by Docker.');
        return;
      }
      if (Date.now() >= deadline) throw new Error('The anonymous verification volume was not removed with its container.');
      await pause(200);
    }
  };
  try {
    await docker(['info', '--format', '{{.ServerVersion}}']);
    if (!values['skip-build']) {
      await docker(['image', 'inspect', values['base-image']!]);
      await docker(['build', '--pull=false', '--build-arg', `BASE_IMAGE=${values['base-image']}`,
        '--file', 'tests/fixtures/web-runtime.Dockerfile', '--tag', image, '.'], { stream: true, timeout: 120_000 });
      builtFixture = true;
    }
    const inspected = await docker(['image', 'inspect', image]);
    const metadata = JSON.parse(inspected.stdout)[0];
    assert.equal(metadata.Config?.Labels?.['org.theoremos.fixture'], 'web-runtime-no-provider',
      'Refusing to run smoke against an image without the offline fixture label.');
    assert.equal((await runner.readiness()).ready, true);
    for (const name of ['valid', 'invalid', 'mathlib-valid', 'mathlib-invalid', 'cancel', 'mathlib-cancel', 'cancel-early'] as const) {
      if (values.case !== 'all' && values.case !== name) continue;
      if (name === 'cancel-early') {
        const id = crypto.randomUUID();
        containerIds.add(id);
        const controller = new AbortController();
        const messages: unknown[] = [];
        // run() synchronously spawns docker create before its first await. Abort now,
        // then await settlement so an incomplete create cannot make absence look final.
        const execution = runner.run({ id, input: makeInput('WEB_SMOKE_WAIT_FOR_CANCEL'), provider },
          message => messages.push(message), controller.signal);
        controller.abort();
        await assert.rejects(execution, { name: 'AbortError' });
        await noContainer({ id });
        assert.equal(messages.length, 0, 'Early cancellation must prevent the worker from starting.');
        outcomes.push({ case: name, status: 'cancelled', containerRemoved: true, workerStarted: false });
        console.log(`Smoke ${name}: passed`);
        continue;
      }
      const marker = name === 'mathlib-valid' ? 'WEB_SMOKE_MATHLIB_VALID' : name === 'mathlib-invalid' ? 'WEB_SMOKE_MATHLIB_INVALID' :
        name === 'mathlib-cancel' ? 'WEB_SMOKE_MATHLIB_WAIT_FOR_CANCEL' : name === 'invalid' ? 'WEB_SMOKE_INVALID_PROOF' :
          name === 'cancel' ? 'WEB_SMOKE_WAIT_FOR_CANCEL' : 'WEB_SMOKE_VALID_PROOF';
      const input = makeInput(marker);
      const run = jobs.create(owner, input, provider);
      containerIds.add(run.id);
      if (name === 'cancel' || name === 'mathlib-cancel') {
        await waitFor(run, () => run.events.some(event => event.type === 'worker_activity'));
        const running = await docker(['container', 'inspect', `theoremos-web-${run.id}`]);
        const volumes = assertWebContainerBoundary(running.stdout, apiKey, input.environment);
        for (const name of volumes) {
          observedVolumes.add(name);
          const inspected = await docker(['volume', 'inspect', name]);
          const volume = JSON.parse(inspected.stdout)[0];
          assert.equal(volume.Driver, 'local');
          assert.ok(!volume.Options || Object.keys(volume.Options).length === 0, 'An anonymous verification volume must not bind a host directory.');
        }
        jobs.cancel(owner, run.id);
        assert.equal(run.status, 'cancelled');
        await noContainer(run);
        for (const name of volumes) await noVolume(name);
        outcomes.push({ case: name, status: run.status, containerRemoved: true, containerBoundaryVerified: true,
          keyAbsentFromDockerMetadata: true, anonymousVolumesRemoved: volumes.length });
      } else {
        await waitFor(run, () => terminal(run));
        try {
          assert.ok(run.result, `Worker produced no result: ${run.error || run.status}`);
          assert.equal(run.status, 'completed', `Runtime failed before Lean verification: ${JSON.stringify(run.result)}`);
          assertWebEnvironmentReport(run.result.report, input.environment!);
          const expectedCandidate = input.environment === 'mathlib'
            ? input.source.replaceAll('by sorry', name === 'mathlib-valid' ? 'by ring' : 'by exact True.intro')
            : name === 'valid' ? input.source.replace('by sorry', 'by rfl').replace('by sorry', 'by exact Nat.zero_add n')
              : input.source.replaceAll('by sorry', 'by exact True.intro');
          assert.notEqual(expectedCandidate, input.source, 'The offline fixture must change the original Lean source.');
          assert.ok(run.artifact, 'A real worker must publish live source through Docker and jobs.');
          assert.equal(run.artifact.status, 'candidate', 'Live source must remain an unaccepted candidate.');
          assert.equal(run.artifact.workerId, 'solver', 'The one-worker fixture must identify its actual proof worker.');
          assert.equal(run.artifact.source, expectedCandidate, 'Live source must contain the actual changed fixture candidate.');
          assert.equal(run.result.proof, expectedCandidate, 'The final proof must retain the candidate that was displayed live.');
          const trace = messages.get(run.id) ?? [];
          const artifactIndex = trace.findIndex(message => message.type === 'artifact');
          const resultIndex = trace.findIndex(message => message.type === 'result');
          assert.ok(artifactIndex >= 0 && resultIndex > artifactIndex, 'Docker must deliver the artifact before the final result.');
          assert.equal(trace[artifactIndex].runStatus, 'running', 'Jobs must expose the candidate while research is still running.');
          assert.equal(trace[artifactIndex].resultAlreadyPresent, false, 'A live candidate must exist before a final result is stored.');
          if (name === 'valid' || name === 'mathlib-valid') {
            assert.equal(run.result.status, 'evaluated_passed', `Valid proof was not accepted: ${JSON.stringify(run.result.report)}`);
            assert.match(run.result.proof, name === 'mathlib-valid' ? /by ring/ : /exact Nat\.zero_add n/);
            assert.equal(run.result.report.solver_ready_receipt_valid, true);
            assert.equal(run.result.report.completion_signal_valid, true);
            const evaluation = run.result.report.evaluator as { status?: string; verification?: { passed?: boolean } };
            assert.equal(evaluation.status, 'passed');
            assert.equal(evaluation.verification?.passed, true);
          } else {
            assert.equal(run.result.status, 'incomplete', 'An invalid Lean proof must remain incomplete.');
            assert.ok(run.events.some(event => event.type === 'proof_checked'), 'The negative case must reach real Lean candidate checking.');
            assert.notEqual((run.result.report.evaluator as { status?: string })?.status, 'passed');
          }
        } catch (error) {
          console.error('Smoke assertion diagnostics: ' + JSON.stringify({ case: name, status: run.status,
            phase: run.phase, error: run.error, events: run.events, artifact: run.artifact,
            result: run.result, messages: messages.get(run.id) }).replaceAll(apiKey, '[REDACTED]'));
          throw error;
        }
        assert.ok(!JSON.stringify(run).includes(apiKey), 'A public run must not contain its API key.');
        await noContainer(run);
        outcomes.push({ case: name, status: run.status, acceptance: run.result.status, environment: run.result.report.environment,
          candidate: { status: run.artifact!.status, workerId: run.artifact!.workerId, capturedAt: run.artifact!.capturedAt,
            sourceMatchesExpected: true, publishedBeforeResult: true, observedWhileRunning: true },
          messages: messages.get(run.id), containerRemoved: true });
      }
      console.log(`Smoke ${name}: passed`);
    }
    const outputRoot = path.join(root, 'out/web-runtime-smoke');
    fs.mkdirSync(outputRoot, { recursive: true });
    const report = { schema: 'theorem-os.web-runtime-smoke.v1', checkedAt: new Date().toISOString(),
      image, baseImage: values['base-image'], modelInvoked: false,
      realLeanChecks: outcomes.some(outcome => typeof outcome.acceptance === 'string'), cases: outcomes };
    const serialized = JSON.stringify(report, null, 2) + '\n';
    fs.writeFileSync(path.join(outputRoot, 'report.json'), serialized);
    fs.writeFileSync(path.join(outputRoot, `report.${values.case}.json`), serialized);
    console.log('Offline Docker / BYOK / real Lean smoke checks passed. Report: out/web-runtime-smoke/report.json');
  } finally {
    await jobs.close();
    for (const id of containerIds) await docker(['rm', '--force', '--volumes', `theoremos-web-${id}`], { allowFailure: true });
    for (const name of observedVolumes) {
      // Only remove volumes this script observed on its own containers, never a global prune.
      await docker(['volume', 'rm', name], { allowFailure: true });
    }
    if (!values['keep-image'] && builtFixture) await docker(['image', 'rm', image], { allowFailure: true });
  }
}

if (process.argv[1] && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  runWebRuntimeSmoke().catch(error => {
    console.error(error instanceof Error ? error.message : 'Offline web runtime smoke failed.');
    process.exitCode = 1;
  });
}
