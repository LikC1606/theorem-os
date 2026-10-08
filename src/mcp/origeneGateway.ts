/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

import { spawn, spawnSync, type ChildProcessWithoutNullStreams } from 'node:child_process';
import {
  chmodSync,
  cpSync,
  existsSync,
  lstatSync,
  mkdirSync,
  readFileSync,
  readdirSync,
  realpathSync,
  renameSync,
  rmSync,
  statSync,
  writeFileSync,
} from 'node:fs';
import net from 'node:net';
import os from 'node:os';
import path from 'node:path';
import { randomBytes } from 'node:crypto';
import { Client } from '@modelcontextprotocol/sdk/client/index.js';
import { StreamableHTTPClientTransport } from '@modelcontextprotocol/sdk/client/streamableHttp.js';

const ORIGENE_COMMIT = 'b22913ecae629c9ec10aaf6c8e03abf091de4211';
const MANAGED_UV_VERSION = '0.8.22';
const RUNTIME_REVISION = '2';
const PREPARE_TIMEOUT_MS = 20 * 60 * 1000;
const PREPARE_LOCK_STALE_MS = PREPARE_TIMEOUT_MS * 2 + 5 * 60 * 1000;
const START_TIMEOUT_MS = 120_000;

export const ORIGENE_SERVICES = [
  'chembl_mcp',
  'kegg_mcp',
  'string_mcp',
  'search_mcp',
  'pubchem_mcp',
  'ncbi_mcp',
  'uniprot_mcp',
  'tcga_mcp',
  'depmap_mcp',
  'ensembl_mcp',
  'ucsc_mcp',
  'fda_drug_mcp',
  'opentargets_mcp',
  'monarch_mcp',
  'clinicaltrials_mcp',
  'pdb_mcp',
  'dbsearch_mcp',
] as const;

export type OrigeneService = (typeof ORIGENE_SERVICES)[number];

type OrigeneToolResult = {
  content?: Array<{ type?: string; text?: string; data?: string; mimeType?: string }>;
  structuredContent?: unknown;
  isError?: boolean;
  [key: string]: unknown;
};

const commandExists = (command: string): boolean => {
  const result = spawnSync(command, ['--version'], { encoding: 'utf8', timeout: 5000 });
  return result.status === 0;
};

const resolveExecutable = (configured: string | undefined, candidates: string[]): string | undefined => {
  if (configured?.trim() && commandExists(configured.trim())) return configured.trim();
  return (
    candidates.find((candidate) => existsSync(candidate) && commandExists(candidate)) ||
    (commandExists('uv') ? 'uv' : undefined)
  );
};

const getFreePort = async (): Promise<number> =>
  await new Promise((resolve, reject) => {
    const server = net.createServer();
    server.unref();
    server.once('error', reject);
    server.listen(0, '127.0.0.1', () => {
      const address = server.address();
      const port = typeof address === 'object' && address ? address.port : 0;
      server.close((error) => (error ? reject(error) : resolve(port)));
    });
  });

const buildOrigeneEnvironment = (overrides: Record<string, string> = {}): NodeJS.ProcessEnv => {
  const environment: NodeJS.ProcessEnv = {};
  for (const key of [
    'PATH',
    'Path',
    'HOME',
    'USERPROFILE',
    'TMPDIR',
    'TMP',
    'TEMP',
    'SYSTEMROOT',
    'WINDIR',
    'COMSPEC',
    'LANG',
    'LC_ALL',
    'HTTP_PROXY',
    'HTTPS_PROXY',
    'NO_PROXY',
    'http_proxy',
    'https_proxy',
    'no_proxy',
  ]) {
    if (process.env[key] !== undefined) environment[key] = process.env[key];
  }
  for (const [key, value] of Object.entries(process.env)) {
    if (value !== undefined && /^(?:UV|PYTHON|PIP|DEEPSCIENTIST_ORIGENE)_/iu.test(key)) environment[key] = value;
  }
  for (const key of [
    'TAVILY_API_KEY',
    'JINA_API_KEY',
    'NCBI_API_KEY',
    'NCBI_EMAIL',
    'OPENFDA_API_KEY',
    'DEPMAP_API_KEY',
  ]) {
    if (process.env[key] !== undefined) environment[key] = process.env[key];
  }
  return { ...environment, ...overrides };
};

const runCommand = async (
  command: string,
  args: string[],
  cwd: string,
  timeoutMs: number,
  envOverride: Record<string, string> = {}
): Promise<{ stdout: string; stderr: string }> =>
  await new Promise((resolve, reject) => {
    const child = spawn(command, args, {
      cwd,
      env: buildOrigeneEnvironment({ PYTHONUNBUFFERED: '1', ...envOverride }),
      stdio: 'pipe',
    });
    const stdout: string[] = [];
    const stderr: string[] = [];
    const timer = setTimeout(() => {
      child.kill('SIGTERM');
      reject(new Error(`Command timed out after ${Math.round(timeoutMs / 1000)}s: ${command} ${args.join(' ')}`));
    }, timeoutMs);
    child.stdout.on('data', (chunk) => stdout.push(String(chunk)));
    child.stderr.on('data', (chunk) => stderr.push(String(chunk)));
    child.once('error', (error) => {
      clearTimeout(timer);
      reject(error);
    });
    child.once('exit', (code) => {
      clearTimeout(timer);
      const output = { stdout: stdout.join(''), stderr: stderr.join('') };
      if (code === 0) resolve(output);
      else reject(new Error(output.stderr.slice(-4000) || `Command exited with code ${code}`));
    });
  });

export class OrigeneGateway {
  private child?: ChildProcessWithoutNullStreams;
  private port?: number;
  private token?: string;
  private preparePromise?: Promise<void>;
  private prepareState: 'idle' | 'preparing' | 'ready' | 'failed' = 'idle';
  private prepareError?: string;
  private startPromise?: Promise<void>;
  private clients = new Map<string, { client: Client; transport: StreamableHTTPClientTransport }>();
  private stderrTail = '';

  readonly sourceRoot = this.resolveSourceRoot();
  readonly runtimeRoot = this.resolveRuntimeRoot();
  readonly preparedRoot = process.env.DEEPSCIENTIST_ORIGENE_PREPARED_ROOT?.trim()
    ? path.resolve(process.env.DEEPSCIENTIST_ORIGENE_PREPARED_ROOT.trim())
    : undefined;
  readonly cacheRoot =
    process.env.DEEPSCIENTIST_ORIGENE_CACHE_ROOT ||
    path.join(os.homedir(), '.deepscientist', 'origene-mcp', ORIGENE_COMMIT.slice(0, 12));
  private managedUvPath = path.join(this.cacheRoot, '.runtime', process.platform === 'win32' ? 'uv.exe' : 'uv');

  status() {
    const prepared = this.isPrepared();
    return {
      provider: 'origene' as const,
      enabled: true,
      configured: Boolean(this.preparedRoot || (this.sourceRoot && this.runtimeRoot)),
      sourceRoot: this.sourceRoot,
      runtimeRoot: this.runtimeRoot,
      preparedRoot: this.preparedRoot,
      cacheRoot: this.cacheRoot,
      upstreamCommit: ORIGENE_COMMIT,
      uvPath: this.resolveUvPath(),
      managedUvVersion: MANAGED_UV_VERSION,
      prepared,
      prepareState: prepared ? 'ready' : this.prepareState,
      prepareError: this.prepareError,
      running: Boolean(this.child && this.child.exitCode == null),
      port: this.port,
      services: [...ORIGENE_SERVICES],
      degradedReason: this.preparedRoot
        ? !existsSync(this.preparedRoot)
          ? `The prepared Origene runtime was not found at ${this.preparedRoot}.`
          : undefined
        : !this.sourceRoot
          ? 'Vendored OrigeneMCP source was not found.'
          : !this.runtimeRoot
            ? 'DeepScientist Origene runtime wrapper was not found.'
            : undefined,
      stderrPreview: this.stderrTail.slice(-1200) || undefined,
    };
  }

  async prepare(): Promise<void> {
    if (this.isPrepared()) {
      this.prepareState = 'ready';
      return;
    }
    if (this.preparePromise) return await this.preparePromise;
    this.prepareState = 'preparing';
    this.prepareError = undefined;
    this.preparePromise = this.prepareInternal().catch((error) => {
      this.preparePromise = undefined;
      this.prepareState = 'failed';
      this.prepareError = error instanceof Error ? error.message : String(error);
      throw error;
    });
    await this.preparePromise;
    this.prepareState = 'ready';
  }

  beginPrepare(): ReturnType<OrigeneGateway['status']> {
    void this.prepare().catch((): undefined => undefined);
    return this.status();
  }

  async listTools(service: string, includeSchemas = false): Promise<Array<Record<string, unknown>>> {
    const client = await this.getClient(service);
    const tools = (await client.listTools()).tools as Array<Record<string, unknown>>;
    return includeSchemas
      ? tools
      : tools.map(({ inputSchema: _inputSchema, outputSchema: _outputSchema, ...tool }) => tool);
  }

  async callTool(service: string, tool: string, args: Record<string, unknown>): Promise<OrigeneToolResult> {
    const client = await this.getClient(service);
    return (await client.callTool({ name: tool, arguments: args })) as OrigeneToolResult;
  }

  async close(): Promise<void> {
    const child = this.child;
    this.child = undefined;
    this.startPromise = undefined;
    if (child && child.exitCode == null) child.kill('SIGTERM');
    const clients = [...this.clients.values()];
    this.clients.clear();
    await Promise.all(clients.map(({ transport }) => transport.close().catch((): undefined => undefined)));
  }

  private resolveSourceRoot(): string | undefined {
    const candidates = [
      process.env.DEEPSCIENTIST_ORIGENE_SOURCE_ROOT,
      path.resolve(process.cwd(), 'third_party/origene-mcp/upstream'),
      path.resolve(path.dirname(process.argv[1] || ''), '../../third_party/origene-mcp/upstream'),
    ].filter(Boolean) as string[];
    return candidates.find((candidate) => existsSync(path.join(candidate, 'pyproject.toml')));
  }

  private resolveRuntimeRoot(): string | undefined {
    const candidates = [
      process.env.DEEPSCIENTIST_ORIGENE_RUNTIME_ROOT,
      path.resolve(process.cwd(), 'resources/origene-runtime'),
      path.resolve(path.dirname(process.argv[1] || ''), '../../resources/origene-runtime'),
    ].filter(Boolean) as string[];
    return candidates.find((candidate) => existsSync(path.join(candidate, 'deepscientist_entrypoint.py')));
  }

  private async prepareInternal(): Promise<void> {
    if (!this.preparedRoot && (!this.sourceRoot || !this.runtimeRoot)) {
      throw new Error(this.status().degradedReason || 'Origene runtime resources are missing.');
    }
    mkdirSync(path.dirname(this.cacheRoot), { recursive: true });
    const lockPath = `${this.cacheRoot}.prepare-lock`;
    if (!this.acquirePrepareLock(lockPath)) {
      await this.waitForExternalPreparation(lockPath);
      return;
    }
    try {
      if (this.isPrepared()) return;
      if (this.preparedRoot) {
        await this.installPreparedRuntime(this.preparedRoot);
        return;
      }
      if (!existsSync(path.join(this.cacheRoot, 'pyproject.toml'))) {
        cpSync(this.sourceRoot!, this.cacheRoot, { recursive: true, force: false });
      }
      cpSync(
        path.join(this.runtimeRoot!, 'deepscientist_entrypoint.py'),
        path.join(this.cacheRoot, 'deepscientist_entrypoint.py'),
        { force: true }
      );
      const uvPath = this.resolveUvPath() || (await this.installManagedUv());
      writeFileSync(path.join(this.cacheRoot, 'local.conf.toml'), this.buildLocalConfig(), 'utf8');
      await runCommand(
        uvPath,
        ['sync', '--python', '3.13', '--frozen', '--no-dev'],
        this.cacheRoot,
        PREPARE_TIMEOUT_MS
      );
      try {
        await this.verifyPythonRuntime(uvPath);
      } catch {
        // The upstream snapshot's lock can lag pyproject markers on a new OS/Python build.
        // Reconcile only the user-cache copy; the pinned source snapshot stays unchanged.
        await runCommand(uvPath, ['sync', '--python', '3.13', '--no-dev'], this.cacheRoot, PREPARE_TIMEOUT_MS);
        await this.verifyPythonRuntime(uvPath);
      }
      const markerPath = path.join(this.cacheRoot, '.deepscientist-prepared');
      writeFileSync(markerPath, `${RUNTIME_REVISION}\n${new Date().toISOString()}\n${ORIGENE_COMMIT}\n`, 'utf8');
    } finally {
      rmSync(lockPath, { recursive: true, force: true });
    }
  }

  private acquirePrepareLock(lockPath: string): boolean {
    try {
      mkdirSync(lockPath);
      try {
        writeFileSync(
          path.join(lockPath, 'owner.json'),
          JSON.stringify({ pid: process.pid, startedAt: new Date().toISOString() }),
          'utf8'
        );
      } catch (error) {
        rmSync(lockPath, { recursive: true, force: true });
        throw error;
      }
      return true;
    } catch (error) {
      if ((error as NodeJS.ErrnoException).code !== 'EEXIST') throw error;
    }
    if (!this.isPrepareLockStale(lockPath)) return false;
    const stalePath = `${lockPath}.stale-${process.pid}-${randomBytes(4).toString('hex')}`;
    try {
      renameSync(lockPath, stalePath);
    } catch (error) {
      if ((error as NodeJS.ErrnoException).code === 'ENOENT') return this.acquirePrepareLock(lockPath);
      return false;
    }
    rmSync(stalePath, { recursive: true, force: true });
    return this.acquirePrepareLock(lockPath);
  }

  private isPrepareLockStale(lockPath: string): boolean {
    try {
      const owner = JSON.parse(readFileSync(path.join(lockPath, 'owner.json'), 'utf8')) as { pid?: unknown };
      if (typeof owner.pid === 'number' && owner.pid > 0) {
        try {
          process.kill(owner.pid, 0);
          return false;
        } catch (error) {
          if ((error as NodeJS.ErrnoException).code !== 'ESRCH') return false;
        }
      }
      return Date.now() - statSync(lockPath).mtimeMs > 1000;
    } catch {
      return Date.now() - statSync(lockPath).mtimeMs > PREPARE_LOCK_STALE_MS;
    }
  }

  private async waitForExternalPreparation(lockPath: string): Promise<void> {
    const deadline = Date.now() + PREPARE_LOCK_STALE_MS;
    while (Date.now() < deadline) {
      if (this.isPrepared()) return;
      if (!existsSync(lockPath) || this.isPrepareLockStale(lockPath)) {
        await this.prepareInternal();
        return;
      }
      await new Promise((resolve) => setTimeout(resolve, 1000));
    }
    throw new Error('Timed out waiting for another DeepScientist process to prepare OrigeneMCP.');
  }

  private async ensureStarted(): Promise<void> {
    if (this.child && this.child.exitCode == null && this.port && this.token) return;
    if (!this.isPrepared()) {
      this.beginPrepare();
      throw new Error(
        'OrigeneMCP is preparing its pinned Python 3.13 environment. Call target_discovery(action="status") and retry when prepareState is "ready".'
      );
    }
    if (this.startPromise) return await this.startPromise;
    this.startPromise = this.startInternal().catch((error) => {
      this.startPromise = undefined;
      throw error;
    });
    return await this.startPromise;
  }

  private async startInternal(): Promise<void> {
    await this.prepare();
    const uvPath = this.resolveUvPath();
    if (!uvPath) throw new Error('The managed uv runtime was not prepared.');
    this.port = await getFreePort();
    this.token = randomBytes(24).toString('hex');
    const localConfig = this.buildLocalConfig(this.port);
    writeFileSync(path.join(this.cacheRoot, 'local.conf.toml'), localConfig, 'utf8');
    this.stderrTail = '';
    const command = this.preparedRoot ? this.preparedPythonPath() : uvPath;
    const args = this.preparedRoot
      ? ['deepscientist_entrypoint.py']
      : ['run', '--no-sync', 'python', 'deepscientist_entrypoint.py'];
    const child = spawn(command, args, {
      cwd: this.cacheRoot,
      env: buildOrigeneEnvironment({
        PYTHONUNBUFFERED: '1',
        DEEPSCIENTIST_ORIGENE_PORT: String(this.port),
        DEEPSCIENTIST_ORIGENE_TOKEN: this.token || '',
      }),
      stdio: 'pipe',
    });
    child.stderr.on('data', (chunk) => {
      this.stderrTail = `${this.stderrTail}${String(chunk)}`.slice(-8000);
    });
    child.once('exit', () => {
      this.clients.clear();
      this.child = undefined;
      this.startPromise = undefined;
    });
    this.child = child;

    const deadline = Date.now() + START_TIMEOUT_MS;
    while (Date.now() < deadline) {
      if (child.exitCode != null) throw new Error(this.stderrTail || `OrigeneMCP exited with code ${child.exitCode}.`);
      try {
        const response = await fetch(`http://127.0.0.1:${this.port}/healthz`);
        if (response.ok) return;
      } catch {
        // The Python application is still importing its tool services.
      }
      await new Promise((resolve) => setTimeout(resolve, 500));
    }
    child.kill('SIGTERM');
    throw new Error(
      `OrigeneMCP did not become ready within ${START_TIMEOUT_MS / 1000}s. ${this.stderrTail.slice(-2000)}`
    );
  }

  private assertService(service: string): asserts service is OrigeneService {
    if (!ORIGENE_SERVICES.includes(service as OrigeneService)) {
      throw new Error(`Unknown Origene service "${service}". Use target_discovery(action="list_services").`);
    }
  }

  private resolveUvPath(): string | undefined {
    if (this.preparedRoot && commandExists(this.managedUvPath)) return this.managedUvPath;
    return resolveExecutable(process.env.DEEPSCIENTIST_ORIGENE_UV, [
      this.managedUvPath,
      path.join(os.homedir(), '.local', 'bin', process.platform === 'win32' ? 'uv.exe' : 'uv'),
      '/opt/homebrew/bin/uv',
      '/usr/local/bin/uv',
    ]);
  }

  private buildLocalConfig(port?: number): string {
    const baseUrl = port ? `http://127.0.0.1:${port}` : 'http://127.0.0.1:8788';
    return readFileSync(path.join(this.cacheRoot, 'default.conf.toml'), 'utf8')
      .replace(/mcp_index_base_url\s*=\s*"[^"]*"/u, `mcp_index_base_url = "${baseUrl}"`)
      .replace(/port\s*=\s*\d+/u, `port = ${port || 8788}`)
      .replace(/workers\s*=\s*\d+/u, 'workers = 1')
      .replace(
        /tavily_api_key\s*=\s*"[^"]*"/u,
        `tavily_api_key = "${process.env.TAVILY_API_KEY || 'deepscientist-disabled'}"`
      )
      .replace(
        /jina_api_key\s*=\s*"[^"]*"/u,
        `jina_api_key = "${process.env.JINA_API_KEY || 'deepscientist-disabled'}"`
      );
  }

  private isPrepared(): boolean {
    const markerPath = path.join(this.cacheRoot, '.deepscientist-prepared');
    if (!existsSync(markerPath)) return false;
    try {
      const markerLines = readFileSync(markerPath, 'utf8').split(/\r?\n/u);
      if (markerLines[0] !== RUNTIME_REVISION) return false;
      if (this.preparedRoot) {
        if (markerLines[2] !== ORIGENE_COMMIT) return false;
        this.validatePreparedRuntimeLayout(this.cacheRoot, false);
      }
      return true;
    } catch {
      return false;
    }
  }

  private async installPreparedRuntime(preparedRoot: string): Promise<void> {
    this.validatePreparedRuntimeLayout(preparedRoot, true);

    const suffix = `${process.pid}-${randomBytes(6).toString('hex')}`;
    const temporaryRoot = `${this.cacheRoot}.prepared-${suffix}`;
    const previousRoot = `${this.cacheRoot}.previous-${suffix}`;
    const markerName = '.deepscientist-prepared';
    const pendingMarkerName = '.deepscientist-prepared.pending';
    let previousMoved = false;
    let replacementInstalled = false;

    rmSync(temporaryRoot, { recursive: true, force: true });
    try {
      cpSync(preparedRoot, temporaryRoot, {
        recursive: true,
        force: false,
        errorOnExist: true,
        preserveTimestamps: true,
        verbatimSymlinks: true,
      });
      this.makeTreeOwnerWritable(temporaryRoot);
      this.validatePreparedRuntimeLayout(temporaryRoot, true);
      renameSync(path.join(temporaryRoot, markerName), path.join(temporaryRoot, pendingMarkerName));

      if (existsSync(this.cacheRoot)) {
        renameSync(this.cacheRoot, previousRoot);
        previousMoved = true;
      }
      renameSync(temporaryRoot, this.cacheRoot);
      replacementInstalled = true;

      const installedUvPath = path.join(this.cacheRoot, '.runtime', process.platform === 'win32' ? 'uv.exe' : 'uv');
      await this.verifyPythonRuntime(installedUvPath);
      renameSync(path.join(this.cacheRoot, pendingMarkerName), path.join(this.cacheRoot, markerName));
      this.validatePreparedRuntimeLayout(this.cacheRoot, true);

      if (previousMoved) rmSync(previousRoot, { recursive: true, force: true });
    } catch (error) {
      if (replacementInstalled) rmSync(this.cacheRoot, { recursive: true, force: true });
      if (previousMoved && existsSync(previousRoot)) renameSync(previousRoot, this.cacheRoot);
      const reason = error instanceof Error ? error.message : String(error);
      throw new Error(`Unable to install the prepared Origene runtime from ${preparedRoot}: ${reason}`);
    } finally {
      rmSync(temporaryRoot, { recursive: true, force: true });
    }
  }

  private validatePreparedRuntimeLayout(root: string, verifyExecutables: boolean): void {
    if (!existsSync(root) || !statSync(root).isDirectory()) {
      throw new Error(`Prepared Origene runtime directory does not exist: ${root}`);
    }
    if (verifyExecutables) this.assertPreparedRuntimeIsSelfContained(root);

    const requiredFiles = [
      'pyproject.toml',
      'default.conf.toml',
      'deepscientist_entrypoint.py',
      '.deepscientist-prepared',
      path.join('.venv', 'pyvenv.cfg'),
    ];
    for (const relativePath of requiredFiles) {
      const absolutePath = path.join(root, relativePath);
      if (!existsSync(absolutePath) || !statSync(absolutePath).isFile()) {
        throw new Error(`Prepared Origene runtime is missing required file: ${relativePath}`);
      }
    }

    const markerLines = readFileSync(path.join(root, '.deepscientist-prepared'), 'utf8').split(/\r?\n/u);
    if (markerLines[0] !== RUNTIME_REVISION) {
      throw new Error(
        `Prepared Origene runtime revision is ${markerLines[0] || 'missing'}; expected ${RUNTIME_REVISION}.`
      );
    }
    if (markerLines[2] !== ORIGENE_COMMIT) {
      throw new Error(`Prepared Origene runtime commit is ${markerLines[2] || 'missing'}; expected ${ORIGENE_COMMIT}.`);
    }

    const uvPath = path.join(root, '.runtime', process.platform === 'win32' ? 'uv.exe' : 'uv');
    const pythonPath = path.join(
      root,
      '.venv',
      process.platform === 'win32' ? 'Scripts' : 'bin',
      process.platform === 'win32' ? 'python.exe' : 'python'
    );
    for (const [label, executablePath] of [
      ['managed uv', uvPath],
      ['Python virtual environment', pythonPath],
    ] as const) {
      if (!existsSync(executablePath) || !statSync(executablePath).isFile()) {
        throw new Error(`Prepared Origene runtime is missing ${label} executable: ${executablePath}`);
      }
      if (verifyExecutables && !commandExists(executablePath)) {
        throw new Error(`Prepared Origene runtime ${label} executable cannot run: ${executablePath}`);
      }
    }
  }

  private makeTreeOwnerWritable(root: string): void {
    const visit = (entryPath: string): void => {
      const stat = lstatSync(entryPath);
      if (stat.isSymbolicLink()) return;
      chmodSync(entryPath, stat.mode | (stat.isDirectory() ? 0o700 : 0o600));
      if (stat.isDirectory()) {
        for (const name of readdirSync(entryPath)) visit(path.join(entryPath, name));
      }
    };
    visit(root);
  }

  private assertPreparedRuntimeIsSelfContained(root: string): void {
    const canonicalRoot = realpathSync(root);
    const visit = (entryPath: string): void => {
      const stat = lstatSync(entryPath);
      if (stat.isSymbolicLink()) {
        let targetPath: string;
        try {
          targetPath = realpathSync(entryPath);
        } catch {
          throw new Error(`Prepared Origene runtime contains a broken symbolic link: ${entryPath}`);
        }
        const relativeTarget = path.relative(canonicalRoot, targetPath);
        if (relativeTarget === '..' || relativeTarget.startsWith(`..${path.sep}`) || path.isAbsolute(relativeTarget)) {
          throw new Error(`Prepared Origene runtime symbolic link escapes the bundle: ${entryPath}`);
        }
        return;
      }
      if (stat.isDirectory()) {
        for (const name of readdirSync(entryPath)) visit(path.join(entryPath, name));
      }
    };
    visit(root);
  }

  private async verifyPythonRuntime(uvPath: string): Promise<void> {
    if (this.preparedRoot) {
      await runCommand(
        this.preparedPythonPath(),
        ['-c', 'import deploy.web; print("origene runtime import ok")'],
        this.cacheRoot,
        120_000
      );
      return;
    }
    await runCommand(
      uvPath,
      ['run', '--no-sync', 'python', '-c', 'import deploy.web; print("origene runtime import ok")'],
      this.cacheRoot,
      120_000
    );
  }

  private preparedPythonPath(): string {
    return path.join(
      this.cacheRoot,
      '.venv',
      process.platform === 'win32' ? 'Scripts' : 'bin',
      process.platform === 'win32' ? 'python.exe' : 'python'
    );
  }

  private async installManagedUv(): Promise<string> {
    const installDir = path.dirname(this.managedUvPath);
    mkdirSync(installDir, { recursive: true });
    const extension = process.platform === 'win32' ? 'ps1' : 'sh';
    const installerUrl = `https://astral.sh/uv/${MANAGED_UV_VERSION}/install.${extension}`;
    const response = await fetch(installerUrl);
    if (!response.ok) throw new Error(`Unable to download the pinned uv installer (${response.status}).`);
    const installerPath = path.join(installDir, `install.${extension}`);
    writeFileSync(installerPath, await response.text(), { encoding: 'utf8', mode: 0o700 });
    const installEnv = { UV_INSTALL_DIR: installDir, UV_NO_MODIFY_PATH: '1' };
    if (process.platform === 'win32') {
      await runCommand(
        'powershell.exe',
        ['-NoProfile', '-ExecutionPolicy', 'Bypass', '-File', installerPath],
        installDir,
        120_000,
        installEnv
      );
    } else {
      await runCommand('sh', [installerPath], installDir, 120_000, installEnv);
    }
    if (!commandExists(this.managedUvPath)) {
      throw new Error('The pinned uv installer completed without producing a runnable binary.');
    }
    return this.managedUvPath;
  }

  private async getClient(service: string): Promise<Client> {
    this.assertService(service);
    await this.ensureStarted();
    const existing = this.clients.get(service);
    if (existing) return existing.client;
    const transport = new StreamableHTTPClientTransport(new URL(`http://127.0.0.1:${this.port}/${service}/mcp/`), {
      requestInit: { headers: { 'x-deepscientist-token': this.token || '' } },
    });
    const client = new Client({ name: `deepscientist-origene-${service}`, version: '1.0.0' });
    await client.connect(transport);
    this.clients.set(service, { client, transport });
    return client;
  }
}
