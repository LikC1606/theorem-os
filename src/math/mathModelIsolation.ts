import fs from 'node:fs';
import path from 'node:path';
import { createHash } from 'node:crypto';
import { spawnSync } from 'node:child_process';
import { z } from 'zod';

const absolute = z
  .string()
  .refine((value) => path.isAbsolute(value) && path.normalize(value) === value && !value.includes('\0'));
export const mathModelIsolationPolicySchema = z
  .object({
    schema: z.literal('deepscientist.math.model-isolation.v1'),
    workspaces: z.array(absolute).min(1),
    publicReadOnlyPaths: z.array(absolute),
    runtimeReadOnlyPaths: z.array(absolute),
    nodeExecutable: absolute,
    codexExecutable: absolute,
    acpScript: absolute,
    launcher: absolute,
    coreExecutable: absolute,
    mcpScripts: z.array(absolute).min(1),
    stateDirectory: absolute,
    providerBaseUrl: z.string().url(),
    model: z
      .string()
      .regex(/^[a-zA-Z0-9][a-zA-Z0-9._:/-]{0,127}$/u)
      .optional(),
    provider: z
      .string()
      .regex(/^[a-zA-Z0-9_-]{1,128}$/u)
      .optional(),
    apiKeyEnv: z
      .string()
      .regex(/^[A-Z_][A-Z0-9_]{0,127}$/u)
      .optional(),
    /**
     * Declares that the upstream model accepts Responses `reasoning.effort` and
     * which level is the session default. Codex has no bundled metadata for
     * custom models such as gpt-6.1-sol, so without a declared catalog it sends
     * `reasoning: null` and codex-acp never advertises a thought_level option;
     * every role then silently ran at the provider default (run 23 attempts
     * 1-15, despite `--*-thought-level`). Omitted means unchanged behavior.
     */
    reasoningEffort: z.enum(['low', 'medium', 'high', 'xhigh']).optional(),
  })
  .strict();
export type MathModelIsolationPolicy = z.infer<typeof mathModelIsolationPolicySchema>;

export function isolationContains(root: string, candidate: string): boolean {
  const relative = path.relative(root, candidate);
  return relative === '' || (!relative.startsWith(`..${path.sep}`) && relative !== '..' && !path.isAbsolute(relative));
}

export function isolationCanonical(file: string): string {
  if (fs.realpathSync(file) !== file) throw new Error('math_isolation_noncanonical_path');
  return file;
}

export function readMathModelIsolationPolicy(file: string): { policy: MathModelIsolationPolicy; digest: string } {
  isolationCanonical(file);
  const stat = fs.lstatSync(file);
  if (!stat.isFile() || stat.nlink !== 1 || stat.size > 65536 || (stat.mode & 0o077) !== 0)
    throw new Error('math_isolation_policy_file_invalid');
  const bytes = fs.readFileSync(file);
  const policy = mathModelIsolationPolicySchema.parse(JSON.parse(bytes.toString('utf8')));
  for (const entry of [
    ...policy.workspaces,
    ...policy.publicReadOnlyPaths,
    ...policy.runtimeReadOnlyPaths,
    policy.nodeExecutable,
    policy.codexExecutable,
    policy.acpScript,
    policy.launcher,
    policy.coreExecutable,
    ...policy.mcpScripts,
    policy.stateDirectory,
  ])
    isolationCanonical(entry);
  const upstream = new URL(policy.providerBaseUrl);
  if (
    (upstream.protocol !== 'https:' &&
      !(upstream.protocol === 'http:' && ['127.0.0.1', '[::1]'].includes(upstream.hostname))) ||
    upstream.username ||
    upstream.password ||
    upstream.search ||
    upstream.hash
  )
    throw new Error('math_isolation_provider_invalid');
  if ((fs.statSync(policy.stateDirectory).mode & 0o077) !== 0) throw new Error('math_isolation_state_not_private');
  for (const root of policy.workspaces) {
    if (root === '/' || policy.workspaces.filter((other) => isolationContains(other, root)).length !== 1)
      throw new Error('math_isolation_workspace_overlap');
    for (const mount of [...policy.publicReadOnlyPaths, ...policy.runtimeReadOnlyPaths]) {
      if (isolationContains(mount, root) || isolationContains(root, mount))
        throw new Error('math_isolation_mount_overlap');
    }
    if (isolationContains(root, policy.stateDirectory) || isolationContains(policy.stateDirectory, root))
      throw new Error('math_isolation_state_overlap');
    if (
      [
        file,
        policy.nodeExecutable,
        policy.codexExecutable,
        policy.acpScript,
        policy.launcher,
        policy.coreExecutable,
        ...policy.mcpScripts,
      ].some((trusted) => isolationContains(root, trusted))
    )
      throw new Error('math_isolation_trusted_file_in_workspace');
  }
  for (const mount of [...policy.publicReadOnlyPaths, ...policy.runtimeReadOnlyPaths]) {
    // An operator must select individual runtime/dependency installations, never a home or experiment root.
    if (mount.split('/').filter(Boolean).length < 3 || isolationContains(mount, policy.stateDirectory))
      throw new Error('math_isolation_mount_too_broad');
  }
  return { policy, digest: createHash('sha256').update(bytes).digest('hex') };
}

export function mathModelIsolationWorkspace(
  policy: MathModelIsolationPolicy,
  cwd: string,
  options: Readonly<{ baselineCommit?: string }> = {}
) {
  isolationCanonical(cwd);
  const trial = policy.workspaces.find((root) => isolationContains(root, cwd));
  if (!trial) throw new Error('math_isolation_workspace_denied');
  let source = cwd;
  while (!fs.existsSync(path.join(source, '.git'))) {
    if (source === trial) throw new Error('math_isolation_git_missing');
    source = path.dirname(source);
  }
  const git = path.join(source, '.git');
  const commonGit = path.join(trial, '.git');
  isolationCanonical(commonGit);
  if (!fs.lstatSync(commonGit).isDirectory()) throw new Error('math_isolation_git_invalid');
  const gitStat = fs.lstatSync(git);
  if (git !== commonGit) {
    if (!gitStat.isFile() || gitStat.size > 4096) throw new Error('math_isolation_git_invalid');
    const pointer = /^gitdir: ([^\r\n]+)\n?$/u.exec(fs.readFileSync(git, 'utf8'));
    if (!pointer || !isolationContains(path.join(commonGit, 'worktrees'), path.resolve(source, pointer[1])))
      throw new Error('math_isolation_git_escape');
    isolationCanonical(path.resolve(source, pointer[1]));
  }
  // Reject object stores that reach an original benchmark repository.
  if (
    fs.existsSync(path.join(commonGit, 'objects/info/alternates')) ||
    fs.existsSync(path.join(commonGit, 'commondir'))
  )
    throw new Error('math_isolation_git_alternates_denied');
  const head = spawnSync('git', ['-C', source, 'rev-parse', '--verify', 'HEAD'], {
    encoding: 'utf8',
    stdio: ['ignore', 'pipe', 'ignore'],
  });
  const headCommit = head.status === 0 ? head.stdout.trim() : '';
  if (!/^[a-f0-9]{40,64}$/u.test(headCommit)) throw new Error('math_isolation_git_history_denied');
  if (options.baselineCommit) {
    if (!/^[a-f0-9]{40,64}$/u.test(options.baselineCommit)) throw new Error('math_isolation_git_history_denied');
    const ancestor = spawnSync(
      'git',
      ['-C', source, 'merge-base', '--is-ancestor', options.baselineCommit, headCommit],
      {
        encoding: 'utf8',
        stdio: ['ignore', 'ignore', 'ignore'],
      }
    );
    if (ancestor.status !== 0) throw new Error('math_isolation_git_history_denied');
  } else {
    const history = spawnSync('git', ['-C', source, 'rev-list', '--all', '--count'], {
      encoding: 'utf8',
      stdio: ['ignore', 'pipe', 'ignore'],
    });
    if (history.status !== 0 || !/^1\n?$/u.test(history.stdout.trim()))
      throw new Error('math_isolation_git_history_denied');
  }
  return { trial, source, git, commonGit, headCommit };
}

export function mathModelIsolationMounts(
  policy: MathModelIsolationPolicy,
  cwd: string,
  options: Readonly<{ baselineCommit?: string }> = {}
): string[] {
  const workspace = mathModelIsolationWorkspace(policy, cwd, options);
  const args = [
    '--unshare-all',
    '--die-with-parent',
    '--new-session',
    '--cap-drop',
    'ALL',
    '--proc',
    '/proc',
    '--dev',
    '/dev',
    '--tmpfs',
    '/tmp',
    '--dir',
    '/run',
    '--dir',
    '/opt',
    '--dir',
    '/home',
    '--dir',
    '/home/model',
    '--dir',
    '/home/model/.codex',
  ];
  for (const directory of ['/usr', '/bin', '/sbin', '/lib', '/lib64']) {
    if (!fs.existsSync(directory)) continue;
    const stat = fs.lstatSync(directory);
    args.push(
      ...(stat.isSymbolicLink()
        ? ['--symlink', fs.readlinkSync(directory), directory]
        : ['--ro-bind', directory, directory])
    );
  }
  for (const file of ['/etc/ld.so.cache', '/etc/localtime'])
    if (fs.existsSync(file)) args.push('--ro-bind', file, file);
  if (fs.existsSync('/etc/passwd')) args.push('--ro-bind', '/etc/passwd', '/etc/passwd');
  if (fs.existsSync('/etc/group')) args.push('--ro-bind', '/etc/group', '/etc/group');
  for (const mount of [...policy.runtimeReadOnlyPaths, ...policy.publicReadOnlyPaths])
    args.push('--ro-bind', mount, mount);
  const toolchains = [...new Set(policy.publicReadOnlyPaths)].filter(
    (root) =>
      fs.statSync(root).isDirectory() &&
      fs.statSync(path.join(root, 'bin'), { throwIfNoEntry: false })?.isDirectory() &&
      ['lake', 'lean'].every((tool) => fs.lstatSync(path.join(root, 'bin', tool), { throwIfNoEntry: false }))
  );
  if (toolchains.length > 1) throw new Error('math_isolation_toolchain_ambiguous');
  if (toolchains.length === 1) {
    const root = isolationCanonical(toolchains[0]);
    args.push('--dir', '/opt/math-tools');
    for (const tool of ['lake', 'lean']) {
      const executable = fs.realpathSync(path.join(root, 'bin', tool));
      if (!isolationContains(root, executable) || !fs.statSync(executable).isFile())
        throw new Error('math_isolation_toolchain_escape');
      try {
        fs.accessSync(executable, fs.constants.X_OK);
      } catch {
        throw new Error('math_isolation_toolchain_not_executable');
      }
      args.push('--symlink', executable, `/opt/math-tools/${tool}`);
    }
  }
  for (const file of [
    policy.nodeExecutable,
    policy.codexExecutable,
    policy.acpScript,
    policy.coreExecutable,
    ...policy.mcpScripts,
  ])
    if (![...policy.runtimeReadOnlyPaths, '/usr'].some((root) => isolationContains(root, file)))
      args.push('--ro-bind', file, file);
  args.push('--bind', workspace.source, workspace.source);
  // The bootstrap repository contains exactly one public baseline commit. Keep
  // its metadata writable so the model can create the solver-ready commit;
  // multi-commit or alternate-object repositories are rejected above.
  args.push('--bind', workspace.commonGit, workspace.commonGit);
  if (workspace.git !== workspace.commonGit) args.push('--ro-bind', workspace.git, workspace.git);
  const visit = (directory: string, depth: number) => {
    if (depth > 6) return;
    const packages = path.join(directory, '.lake/packages');
    if (fs.existsSync(packages)) {
      const target = fs.realpathSync(packages);
      // A mutable package link must never reopen hidden host state or a sibling
      // worker. Local packages are already visible only at their original path.
      // A Core-created detached worktree may point back to the run workspace's
      // shared package cache; it is still inside an authorized policy workspace
      // and is mounted read-only below.
      const localPackages = target === packages && isolationContains(workspace.source, target);
      const authorizedWorkspacePackages = policy.workspaces.some(
        (root) => isolationContains(root, target) && !isolationContains(path.join(root, '.deepscientist'), target)
      );
      if (!localPackages && !authorizedWorkspacePackages && !policy.publicReadOnlyPaths.includes(target))
        throw new Error('math_isolation_dependency_escape');
      // Bubblewrap deliberately refuses a symlink mount destination. Preserve
      // the workspace link and expose only its authorized canonical target.
      args.push('--ro-bind', target, target);
    }
    for (const entry of fs.readdirSync(directory, { withFileTypes: true })) {
      if (entry.isDirectory() && !['.git', '.lake', '.deepscientist', 'node_modules'].includes(entry.name))
        visit(path.join(directory, entry.name), depth + 1);
    }
  };
  visit(workspace.source, 0);
  // Mask last, so no dependency bind can reopen private host state.
  args.push('--tmpfs', path.join(workspace.source, '.deepscientist'));
  args.push('--chdir', cwd);
  return args;
}

/**
 * Add run-scoped data after the model workspace's private-state mask. These
 * mounts are only used for trusted MCP children; the model namespace never
 * receives them.
 */
export function mathModelIsolationMcpMounts(
  policy: MathModelIsolationPolicy,
  cwd: string,
  options: Readonly<{ readOnlyPaths?: readonly string[]; writablePaths?: readonly string[] }> = {}
): string[] {
  const args: string[] = [];
  const add = (mode: '--ro-bind' | '--bind', file: string) => {
    if (!path.isAbsolute(file) || path.resolve(file) !== file || !fs.existsSync(file))
      throw new Error('math_isolation_mcp_mount_invalid');
    isolationCanonical(file);
    const stat = fs.lstatSync(file);
    if (!(stat.isFile() || stat.isDirectory()) || stat.isSymbolicLink())
      throw new Error('math_isolation_mcp_mount_invalid');
    args.push(mode, file, file);
  };
  const readOnly = [...new Set(options.readOnlyPaths ?? [])];
  const writable = [...new Set(options.writablePaths ?? [])];
  for (const file of readOnly) add('--ro-bind', file);
  for (const directory of writable) add('--bind', directory);
  return args;
}

export function validateMathIsolatedMcp(policy: MathModelIsolationPolicy, value: unknown) {
  const server = z
    .object({
      name: z.string().min(1).max(256),
      command: absolute,
      args: z.array(z.string()).default([]),
      env: z
        .array(
          z
            .object({
              name: z.string().regex(/^[A-Za-z_][A-Za-z0-9_]*$/u),
              value: z.string().refine((entryValue) => !entryValue.includes('\0')),
            })
            .strict()
        )
        .default([]),
      type: z.literal('stdio').optional(),
      _meta: z.record(z.string(), z.unknown()).optional(),
    })
    .strict()
    .parse(value);
  const command = fs.realpathSync(server.command);
  if (
    !(
      (path.basename(command) === 'node' && server.args.length === 1 && policy.mcpScripts.includes(server.args[0])) ||
      (command === policy.coreExecutable && server.args.length === 1 && server.args[0] === 'mcp-team-stdio')
    )
  )
    throw new Error('math_isolation_mcp_denied');
  if (server.env.some(({ name }) => /^(?:NODE_OPTIONS|NODE_PATH|LD_|DYLD_|PYTHON|BASH_ENV|ENV$)/u.test(name)))
    throw new Error('math_isolation_mcp_environment_denied');
  return { ...server, command: path.basename(command) === 'node' ? policy.nodeExecutable : command };
}
