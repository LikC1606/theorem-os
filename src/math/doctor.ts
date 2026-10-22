import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { parse as parseToml } from 'smol-toml';
import { runMathProcess } from './mathProcess';
import { DEFAULT_MATHEMATICS_ENV_FILE, resolveMathematicsRuntimeEnvironment } from './mathRuntimeEnvironment';
import { checkResolvedLeanToolchainReadiness } from './leanToolchainReadiness';
import { checkCodexProviderConnectivity } from '../runtime/codexConnectivity';
import { resolveMathematicsLakePackagesCache } from './verifier';
import { prepareMathProofEnvironment } from './mathProofEnvironment';
import { DEFAULT_MATH_PROOF_ENVIRONMENT_CACHE_ROOT } from './mathProofEnvironmentCache';

export type DoctorCheck = {
  id: string;
  status: 'pass' | 'warn' | 'fail';
  message: string;
  fix?: string;
};
export type DoctorReport = {
  status: 'ready' | 'needs_attention';
  checks: DoctorCheck[];
};

function executable(name: string, env: NodeJS.ProcessEnv): string | undefined {
  const candidates = name.includes(path.sep) ? [path.resolve(name)] :
    (env.PATH || '').split(path.delimiter).filter(Boolean).map(directory => path.join(directory, name));
  return candidates.find(file => {
    try { fs.accessSync(file, fs.constants.X_OK); return fs.statSync(file).isFile(); }
    catch { return false; }
  });
}

export async function diagnoseEnvironment(options: {
  env?: NodeJS.ProcessEnv;
  project?: string;
  codex?: string;
  network?: boolean;
  leanOnly?: boolean;
  prepare?: boolean;
  cacheDir?: string;
} = {}): Promise<DoctorReport> {
  const source = options.env ?? process.env;
  const checks: DoctorCheck[] = [];
  const add = (id: string, status: DoctorCheck['status'], message: string, fix?: string) =>
    checks.push({ id, status, message, ...(fix ? { fix } : {}) });
  const report = (): DoctorReport => ({
    status: checks.some(check => check.status === 'fail') ? 'needs_attention' : 'ready', checks,
  });
  add('platform', process.platform === 'linux' ? 'pass' : 'fail', `System: ${process.platform}`,
    process.platform === 'linux' ? undefined : 'Run TheoremOS on a Linux host.');
  const envFile = source.DEEPSCIENTIST_MATH_ENV_FILE?.trim() || DEFAULT_MATHEMATICS_ENV_FILE;
  let env: NodeJS.ProcessEnv;
  try {
    if (source.DEEPSCIENTIST_MATH_ENV_FILE) fs.accessSync(envFile, fs.constants.R_OK);
    env = resolveMathematicsRuntimeEnvironment(source);
    add('environment', 'pass', fs.existsSync(envFile) ? `Environment: ${envFile}` : 'Using the current shell environment.');
  } catch {
    add('environment', 'fail', 'The mathematics environment file is missing, unreadable or invalid.',
      'Check DEEPSCIENTIST_MATH_ENV_FILE and the template at examples/imo2026/math.env.example.');
    return report();
  }
  const probe = (command: string, args: string[], cwd = process.cwd()) =>
    runMathProcess(command, args, { cwd, env, timeoutMs: 5_000, outputLimit: 2_000, outputCapture: 'head' });
  const tool = (id: string, names: string[], fix: string, required = true): string | undefined => {
    const file = names.map(name => executable(name, env)).find(Boolean);
    add(id, file ? 'pass' : required ? 'fail' : 'warn', file ? `${id}: ${file}` : `${id}: not found.`, file ? undefined : fix);
    return file;
  };
  const node = tool('node', ['node'], 'Install Node.js 22 or newer and add it to PATH.');
  const bun = tool('bun', ['bun'], 'Install Bun 1.2 or newer and add it to PATH.');
  const git = tool('git', ['git'], 'Install Git and add it to PATH.');
  tool('python', ['/usr/bin/python3'], 'Install Python 3 at /usr/bin/python3.');
  tool('flock', ['/usr/bin/flock'], 'Install util-linux, including /usr/bin/flock.');
  const lean = tool('lean', ['lean'], 'Install Elan and the Lean toolchain required by the problem.');
  tool('lake', ['lake'], 'Add the Lean / Elan bin directory to PATH in your mathematics environment.');
  const codex = options.leanOnly ? undefined : tool('codex', [options.codex || source.DEEPSCIENTIST_MATH_CODEX_EXECUTABLE || 'codex'],
    'Install Codex CLI or pass --codex /absolute/path/to/codex.');
  const bwrap = tool('bwrap', ['bwrap'], 'Install Bubblewrap and enable unprivileged user namespaces.');
  const tools = await Promise.all([
    ...[{ id: 'node-version', file: node, minimum: [22, 0], label: 'Node.js 22+' },
      { id: 'bun-version', file: bun, minimum: [1, 2], label: 'Bun 1.2+' }].map(async entry => {
      if (!entry.file) return;
      const result = await probe(entry.file, ['--version']);
      const version = /^v?(\d+)\.(\d+)\.(\d+)/u.exec(result.stdout.trim());
      const valid = result.exitCode === 0 && version &&
        (Number(version[1]) > entry.minimum[0] || Number(version[1]) === entry.minimum[0] && Number(version[2]) >= entry.minimum[1]);
      return { id: entry.id, status: valid ? 'pass' : 'fail', message: `${entry.label}: ${version?.[0] ?? 'version unavailable'}.`,
        ...(valid ? {} : { fix: `Install ${entry.label} and check PATH.` }) } as DoctorCheck;
    }),
    (async (): Promise<DoctorCheck | undefined> => {
      if (!git) return;
      const result = await probe(git, ['--version']);
      return { id: 'git-executable', status: result.exitCode === 0 ? 'pass' : 'fail', message:
        result.exitCode === 0 ? 'Git can run.' : 'Git could not run.', ...(result.exitCode === 0 ? {} : { fix: 'Check your Git installation.' }) };
    })(),
  ]);
  checks.push(...tools.filter((check): check is DoctorCheck => Boolean(check)));

  const profile = source.CODEX_HOME || path.join(os.homedir(), '.config/deepscientist/math-sol-codex');
  if (codex) {
    try {
      const configFile = path.join(profile, 'config.toml');
      const config = fs.existsSync(configFile) ? parseToml(fs.readFileSync(configFile, 'utf8')) : {};
      const provider = typeof config.model_provider === 'string' && config.model_providers && typeof config.model_providers === 'object'
        ? config.model_providers[config.model_provider] : undefined;
      if (provider && typeof provider === 'object' && provider.requires_openai_auth !== true) {
        if (typeof provider.env_key === 'string') {
          const key = provider.env_key;
          if (!/^[A-Za-z_][A-Za-z0-9_]{0,127}$/u.test(key)) throw new Error('invalid provider environment key');
          // Tool environments intentionally exclude credentials; inspect the host source only.
          const available = Boolean(source[key]?.trim());
          add('codex-auth', available ? 'pass' : 'fail', available
            ? `Provider credential is set in ${key}.` : `Provider credential is missing: ${key}.`,
          available ? undefined : `Set ${key} in the calling environment before running the CLI.`);
        } else if (provider.env_key !== undefined) {
          throw new Error('invalid provider environment key');
        } else if (provider.auth && typeof provider.auth === 'object') {
          const auth = provider.auth;
          if (typeof auth.command !== 'string' || !auth.command.trim() ||
              auth.args !== undefined && (!Array.isArray(auth.args) || auth.args.some(arg => typeof arg !== 'string')) ||
              auth.cwd !== undefined && typeof auth.cwd !== 'string') throw new Error('invalid provider authentication command');
          const result = await runMathProcess(auth.command, (auth.args ?? []) as string[], {
            cwd: typeof auth.cwd === 'string' ? auth.cwd : process.cwd(), env: { ...env, CODEX_HOME: profile },
            timeoutMs: 5_000, outputLimit: 2_000,
          });
          const available = result.exitCode === 0 && Boolean(result.stdout.trim()) && !/[\r\n]/u.test(result.stdout.trim());
          add('codex-auth', available ? 'pass' : 'fail', available
            ? 'The provider authentication command returned a credential.' : 'The provider authentication command could not return a credential.',
          available ? undefined : 'Check the selected provider auth command and its credential source.');
        } else if (typeof provider.experimental_bearer_token === 'string' && provider.experimental_bearer_token.trim()) {
          add('codex-auth', 'pass', 'A bearer credential is configured for the selected provider.');
        } else {
          add('codex-auth', 'warn', 'The custom provider does not declare credential authentication.',
            'If the provider requires a key, configure env_key or an auth command in its Codex profile.');
        }
      } else {
        const auth = await runMathProcess(codex, ['login', 'status'], { cwd: process.cwd(),
          env: { ...env, CODEX_HOME: profile }, timeoutMs: 5_000, outputLimit: 2_000 });
        add('codex-auth', auth.exitCode === 0 ? 'pass' : 'fail', auth.exitCode === 0
          ? `Codex reports a login for profile: ${profile}` : 'Codex could not confirm a login for the selected profile.',
        auth.exitCode === 0 ? undefined : 'Use your existing authenticated CODEX_HOME, or run codex login with that profile.');
      }
    } catch {
      add('codex-auth', 'fail', 'The provider authentication configuration could not be checked.',
        'Check config.toml in the selected CODEX_HOME.');
    }
  }
  if (bwrap && process.platform === 'linux') {
    const sandbox = await probe(bwrap, ['--unshare-all', '--die-with-parent', '--ro-bind', '/', '/', '--proc', '/proc', '--dev', '/dev', '--', '/bin/true']);
    add('sandbox', sandbox.exitCode === 0 ? 'pass' : 'fail', sandbox.exitCode === 0
      ? 'Bubblewrap can create an isolated process.' : 'Bubblewrap is installed, but an isolated process could not start.',
    sandbox.exitCode === 0 ? undefined : 'Check user namespace permissions on this host, or use a Linux host that permits Bubblewrap.');
  }
  tool('squashfs', ['mksquashfs'], 'Install squashfs-tools for immutable Mathlib dependencies.', false);
  tool('fuse-mount', ['squashfuse', 'snapfuse'], 'Install squashfuse or snapfuse for immutable Mathlib dependencies.', false);
  tool('fuse-unmount', ['fusermount3', 'fusermount'], 'Install fuse3 or fuse for immutable Mathlib dependencies.', false);
  try {
    const fd = fs.openSync('/dev/fuse', fs.constants.O_RDWR);
    fs.closeSync(fd);
    add('fuse-permission', 'pass', '/dev/fuse can be opened. A real mount is checked during problem preparation.');
  } catch {
    add('fuse-permission', 'warn', '/dev/fuse is unavailable or cannot be opened.',
      'Mathlib runs need FUSE access. Check device permissions and container/host mount settings.');
  }
  for (const [index, root] of (env.DEEPSCIENTIST_MATH_TRUSTED_CACHE_ROOTS || '').split(path.delimiter).filter(Boolean).entries()) {
    try {
      fs.accessSync(root, fs.constants.R_OK | fs.constants.X_OK);
      if (!fs.statSync(root).isDirectory()) throw new Error('not a directory');
      add(`cache-${index}`, 'pass', `Configured dependency cache is accessible: ${root}`);
    } catch {
      add(`cache-${index}`, 'fail', `Configured dependency cache is unavailable: ${root}`,
        'Correct DEEPSCIENTIST_MATH_TRUSTED_CACHE_ROOTS. The startup preflight checks package versions.');
    }
  }
  if (options.project) {
    try {
      // Elan's compiler shim may install missing toolchains; inspect its installed list first.
      const project = fs.realpathSync(options.project);
      const pinned = fs.readFileSync(path.join(project, 'lean-toolchain'), 'utf8').trim();
      let projectReady = false;
      const elan = executable('elan', env);
      const leanIsShim = lean && (path.basename(fs.realpathSync(lean)) === 'elan' ||
        elan && fs.realpathSync(lean) === fs.realpathSync(elan));
      const installed = elan ? await probe(elan, ['toolchain', 'list']) : undefined;
      if (leanIsShim && (!installed || installed.exitCode !== 0 || !installed.stdout.split('\n').some(line => line.split(/\s/u)[0] === pinned))) {
        add('project-toolchain', 'fail', 'The project toolchain is not confirmed as installed.',
          `Install the toolchain named in ${path.join(project, 'lean-toolchain')} before checking it.`);
      } else if (lean) {
        const readiness = checkResolvedLeanToolchainReadiness({ projectRoot: project, env, timeoutMs: 5_000 });
        projectReady = readiness.status === 'ready';
        add('project-toolchain', readiness.status === 'ready' ? 'pass' : 'fail', readiness.status === 'ready'
          ? `Pinned Lean compiler is available: ${readiness.toolchain}` : 'The pinned Lean compiler is unavailable or has the wrong version.',
        readiness.status === 'ready' ? undefined : 'Check lean-toolchain, PATH and ELAN_HOME. Run the problem startup preflight for full diagnostics.');
      }
      const manifest = path.join(project, 'lake-manifest.json');
      const required = fs.existsSync(manifest) ? JSON.parse(fs.readFileSync(manifest, 'utf8')).packages ?? [] : [];
      const packages = resolveMathematicsLakePackagesCache(project, env);
      add('project-dependencies', packages || !required.length ? 'pass' : 'fail', packages
        ? `Pinned package revisions match: ${packages}` : required.length
          ? 'No dependency cache matches every package in the project manifest.' : 'No external packages required.',
      packages || !required.length ? undefined : `Prepare the complete pinned cache, including: ${required.map((item: { name: string; rev?: string }) => `${item.name}@${item.rev ?? 'path'}`).join(', ')}.`);
      if (options.prepare && projectReady && packages && !checks.some(check => check.status === 'fail')) {
        let prepared: Awaited<ReturnType<typeof prepareMathProofEnvironment>> | undefined;
        try {
          prepared = await prepareMathProofEnvironment(project, packages, { env,
            cacheRoot: options.cacheDir || DEFAULT_MATH_PROOF_ENVIRONMENT_CACHE_ROOT });
          add('project-image', 'pass', `Immutable dependency image verified: ${prepared.stats.files} files, ${prepared.stats.bytes} bytes.`);
        } catch (error) {
          add('project-image', 'fail', error instanceof Error ? error.message : 'Dependency image preparation failed.',
            'Check FUSE permissions, squashfs tools and disk capacity.');
        } finally { await prepared?.dispose(); }
      }
    } catch {
      add('project-toolchain', 'fail', 'The Lean project or its lean-toolchain file is unavailable.',
        'Pass --project with the Lean project directory containing lean-toolchain.');
    }
  } else {
    if (options.prepare) add('project-image', 'fail', '--prepare requires --project DIR.');
    add('project-toolchain', 'warn', 'No project selected; the required Lean version and dependencies have not been checked.',
      'Run doctor --project /absolute/path/to/lean-project, then the problem startup preflight.');
  }
  if (options.network) {
    try {
      const connectivity = await checkCodexProviderConnectivity({ profile, env });
      add('provider', connectivity.status === 'reachable' ? 'pass' : 'fail', connectivity.status === 'reachable'
        ? 'The provider HTTP endpoint is reachable. Model access is checked only during a real run.' : 'The provider HTTP endpoint could not be reached.',
      connectivity.status === 'reachable' ? undefined : 'Check the provider base URL, proxy and network route.');
    } catch {
      add('provider', 'fail', 'The provider configuration could not be checked.', 'Check config.toml in the selected CODEX_HOME.');
    }
  }
  return report();
}

export function formatDoctorReport(report: DoctorReport): string {
  return ['TheoremOS environment check', '', ...report.checks.flatMap(check => [
    `[${check.status.toUpperCase()}] ${check.message}`, ...(check.fix ? [`       ${check.fix}`] : []),
  ]), '', report.status === 'ready'
    ? 'Basic checks passed. Review any warnings, then run the problem startup preflight.'
    : 'Resolve the failures above, then run doctor again.',
  'This check does not start a model session or verify a proof.'].join('\n');
}
