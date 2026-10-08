import fs from 'node:fs';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import crypto from 'node:crypto';
import { parse as parseToml } from 'smol-toml';
import { z } from 'zod';
import type { MathRunBinding } from "../common/types/team/mathRuntimeContracts";
import { canonicalMathJson, mathDigest } from "./mathRuntimeIo";
import { readMathRunBindingProjection, readMathRunEnvironmentProjection, type MathRunInputs } from "./mathRunInputs";

const digest = z.string().regex(/^[a-f0-9]{64}$/u);
const absolute = z.string().refine((value) => path.isAbsolute(value));
const verificationTarget = z
  .object({
    targetId: z.string().regex(/^[A-Za-z0-9_-]{1,128}$/u),
    pathRelative: z.string().trim().min(1).max(1024),
    theoremName: z.string().trim().min(1).max(512),
    statementHash: digest,
    leanStatementHash: digest.optional(),
    expectedSourceDeclarationHash: digest,
    claim: z.enum(['statement', 'negation']).optional(),
  })
  .strict();
const problemBinding = z
  .object({
    problemId: z.string().trim().min(1).max(160),
    statementHash: digest,
    leanStatementHash: digest.optional(),
    formalStatement: z
      .string()
      .trim()
      .min(1)
      .max(2 * 1024 * 1024)
      .optional(),
    initialRouteFingerprint: z.string().trim().min(1).max(160),
    verificationTargets: z.array(verificationTarget).min(1).max(16).optional(),
  })
  .strict();
const schema = z
  .object({
    schema: z.literal('deepscientist.math.run-binding.v2'),
    runId: z.string().regex(/^[A-Za-z0-9_-]{1,128}$/u),
    taskFile: absolute,
    taskHash: digest,
    workspace: absolute,
    projectRoot: absolute,
    baseCommit: z.string().regex(/^(?:[a-f0-9]{40}|[a-f0-9]{64})$/u),
    allowedWriteRoots: z.array(absolute).min(1),
    environmentFile: absolute,
    environmentDigest: digest,
    leanToolchain: z.string().min(1).max(256),
    lakeExecutableDigest: digest,
    toolManifestDigest: digest,
    leanSourceRoots: z.array(absolute).min(1),
    generatedSourceRoot: absolute,
    artifactStoreRoot: absolute,
    artifactStorePolicyDigest: digest,
    buildManifestRef: absolute,
    buildManifestDigest: digest,
    evaluatorConfigured: z.boolean(),
    evaluatorPolicyDigest: digest.optional(),
    problem: problemBinding.optional(),
  })
  .strict();

export class MathRunBindingError extends Error {
  constructor() {
    super('math_run_binding_integrity: Frozen runtime binding is invalid or changed.');
    this.name = 'MathRunBindingError';
  }
}

export const isMathPathWithin = (root: string, target: string): boolean => {
  const relative = path.relative(root, target);
  return relative === '' || (!path.isAbsolute(relative) && relative !== '..' && !relative.startsWith(`..${path.sep}`));
};

const objectValue = (value: unknown): Record<string, unknown> | undefined =>
  value !== null && typeof value === 'object' && !Array.isArray(value) ? (value as Record<string, unknown>) : undefined;

const lakeRelativeDirectory = (value: unknown, fallback: string): string => {
  if (value === undefined) return fallback;
  if (typeof value !== 'string' || !value || path.isAbsolute(value)) throw new MathRunBindingError();
  const normalized = path.normalize(value);
  if (normalized === '..' || normalized.startsWith(`..${path.sep}`)) throw new MathRunBindingError();
  return normalized;
};

const readStableLakefile = (file: string): string => {
  const descriptor = fs.openSync(file, fs.constants.O_RDONLY | fs.constants.O_NOFOLLOW | fs.constants.O_NONBLOCK);
  try {
    const before = fs.fstatSync(descriptor, { bigint: true });
    if (!before.isFile() || before.nlink !== BigInt(1) || before.size > BigInt(256 * 1024))
      throw new MathRunBindingError();
    const contents = fs.readFileSync(descriptor, 'utf8');
    const after = fs.fstatSync(descriptor, { bigint: true });
    const named = fs.lstatSync(file, { bigint: true });
    if (
      before.size !== after.size ||
      before.mtimeNs !== after.mtimeNs ||
      before.ctimeNs !== after.ctimeNs ||
      before.dev !== named.dev ||
      before.ino !== named.ino ||
      fs.realpathSync(file) !== file
    )
      throw new MathRunBindingError();
    return contents;
  } finally {
    fs.closeSync(descriptor);
  }
};

const stableExternalFileDigest = (file: string, executable = false): string => {
  assertMathCanonicalPath(file);
  const descriptor = fs.openSync(file, fs.constants.O_RDONLY | fs.constants.O_NOFOLLOW | fs.constants.O_NONBLOCK);
  try {
    const before = fs.fstatSync(descriptor, { bigint: true });
    if (!before.isFile() || before.nlink !== BigInt(1) || (executable && (before.mode & BigInt(0o111)) === BigInt(0)))
      throw new MathRunBindingError();
    const fileHash = crypto.createHash('sha256');
    const buffer = Buffer.alloc(64 * 1024);
    let offset = 0;
    for (;;) {
      const count = fs.readSync(descriptor, buffer, 0, buffer.length, offset);
      if (!count) break;
      fileHash.update(buffer.subarray(0, count));
      offset += count;
    }
    const after = fs.fstatSync(descriptor, { bigint: true });
    const named = fs.lstatSync(file, { bigint: true });
    if (
      before.size !== after.size ||
      before.mtimeNs !== after.mtimeNs ||
      before.ctimeNs !== after.ctimeNs ||
      before.mode !== after.mode ||
      before.nlink !== after.nlink ||
      before.dev !== named.dev ||
      before.ino !== named.ino ||
      after.mode !== named.mode ||
      after.nlink !== named.nlink ||
      fs.realpathSync(file) !== file
    )
      throw new MathRunBindingError();
    return fileHash.digest('hex');
  } finally {
    fs.closeSync(descriptor);
  }
};

const runBindingCommand = (
  command: string,
  args: readonly string[],
  cwd: string,
  env: NodeJS.ProcessEnv,
  input?: string
): Readonly<{ status: number; stdout: string }> => {
  const result = spawnSync(command, [...args], {
    cwd,
    env,
    encoding: 'utf8',
    timeout: 30_000,
    maxBuffer: 64 * 1024,
    ...(input === undefined ? {} : { input }),
  });
  if (result.error || result.status === null) throw new MathRunBindingError();
  return { status: result.status, stdout: result.stdout };
};

/** Resolve the writable Lean source root from Lake's frozen config and its live import search path. */
export function resolveMathGeneratedSourceRoot(
  input: Readonly<{ projectRoot: string; lakeExecutable?: string; environment?: NodeJS.ProcessEnv }>
): Readonly<{ leanSourceRoots: readonly string[]; generatedSourceRoot: string }> {
  try {
    const { projectRoot } = input;
    assertMathCanonicalPath(projectRoot);
    if (!fs.lstatSync(projectRoot).isDirectory()) throw new MathRunBindingError();
    const environment = input.environment ?? process.env;
    const gitEnv = { ...environment, GIT_OPTIONAL_LOCKS: '0' };
    const repository = runBindingCommand('git', ['rev-parse', '--show-toplevel'], projectRoot, gitEnv);
    if (repository.status !== 0) throw new MathRunBindingError();
    const gitTopLevel = repository.stdout.trim();
    assertMathCanonicalPath(gitTopLevel);
    if (!fs.lstatSync(gitTopLevel).isDirectory() || !isMathPathWithin(gitTopLevel, projectRoot))
      throw new MathRunBindingError();
    const lakefile = path.join(projectRoot, 'lakefile.toml');
    assertMathCanonicalPath(lakefile);
    const lake = objectValue(parseToml(readStableLakefile(lakefile)));
    const libraries = Array.isArray(lake?.lean_lib) ? lake.lean_lib.map(objectValue) : [];
    if (!libraries.length || libraries.some((library) => !library || typeof library.name !== 'string'))
      throw new MathRunBindingError();
    const buildRoot = path.join(projectRoot, lakeRelativeDirectory(lake?.buildDir, '.lake/build'));
    assertMathCanonicalPath(buildRoot);
    if (!isMathPathWithin(projectRoot, buildRoot)) throw new MathRunBindingError();
    const expectedLeanPath = path.join(buildRoot, 'lib', 'lean');
    assertMathCanonicalPath(expectedLeanPath);
    const leanPath = runBindingCommand(
      input.lakeExecutable ?? 'lake',
      ['env', 'printenv', 'LEAN_PATH'],
      projectRoot,
      environment
    );
    if (leanPath.status !== 0 || !leanPath.stdout || leanPath.stdout.includes('\0')) throw new MathRunBindingError();
    const searchRoots = leanPath.stdout.replace(/\r?\n$/u, '').split(path.delimiter);
    if (!searchRoots.includes(expectedLeanPath)) throw new MathRunBindingError();
    const sourceRoots = [
      ...new Set(
        libraries.map((library) => {
          const root = path.join(projectRoot, lakeRelativeDirectory(library?.srcDir, '.'));
          assertMathCanonicalPath(root);
          if (!isMathPathWithin(projectRoot, root) || !fs.lstatSync(root).isDirectory())
            throw new MathRunBindingError();
          return root;
        })
      ),
    ];
    const generatedSourceRoot = sourceRoots.find((root) => {
      const candidate = path.join(root, 'DeepScientistGenerated', 'A_probe', 'Probe.lean');
      assertMathCanonicalPath(candidate);
      const ignored = runBindingCommand(
        'git',
        ['check-ignore', '--no-index', '-q', '--', candidate],
        projectRoot,
        gitEnv
      );
      if (ignored.status === 0) return false;
      if (ignored.status !== 1) throw new MathRunBindingError();
      return true;
    });
    if (!generatedSourceRoot) throw new MathRunBindingError();
    // Lean receives the probe through stdin, never through a solver-owned source file.
    const probe = runBindingCommand(
      input.lakeExecutable ?? 'lake',
      ['env', 'lean', '--stdin'],
      projectRoot,
      environment,
      'import Lean\n#check Lean.Environment\n'
    );
    if (probe.status !== 0) throw new MathRunBindingError();
    return Object.freeze({ leanSourceRoots: Object.freeze(sourceRoots), generatedSourceRoot });
  } catch {
    throw new MathRunBindingError();
  }
}

/** Validate existing ancestors without requiring a not-yet-created owned directory. */
export function assertMathCanonicalPath(target: string): void {
  if (!path.isAbsolute(target) || path.resolve(target) !== target) throw new MathRunBindingError();
  let current = target;
  while (!fs.existsSync(current)) {
    try {
      if (fs.lstatSync(current).isSymbolicLink()) throw new MathRunBindingError();
    } catch (error) {
      if ((error as NodeJS.ErrnoException).code !== 'ENOENT') throw error;
    }
    const parent = path.dirname(current);
    if (parent === current) throw new MathRunBindingError();
    current = parent;
  }
  if (fs.realpathSync(current) !== current) throw new MathRunBindingError();
}

/** Keep Git identity at the Team workspace while resolving Lean paths in that worktree. */
export function resolveMathRunProjectPaths(
  binding: MathRunBinding,
  teamWorkspace: string,
  worktreePath?: string
): Readonly<{ workspace: string; projectRoot: string; solverProjectRoot: string }> {
  for (const root of [binding.workspace, binding.projectRoot, teamWorkspace, ...(worktreePath ? [worktreePath] : [])])
    assertMathCanonicalPath(root);
  if (teamWorkspace !== binding.workspace || !isMathPathWithin(binding.workspace, binding.projectRoot))
    throw new MathRunBindingError();
  const executionWorkspace = worktreePath ?? binding.workspace;
  const solverProjectRoot = path.resolve(executionWorkspace, path.relative(binding.workspace, binding.projectRoot));
  assertMathCanonicalPath(solverProjectRoot);
  if (!isMathPathWithin(executionWorkspace, solverProjectRoot)) throw new MathRunBindingError();
  return Object.freeze({ workspace: binding.workspace, projectRoot: binding.projectRoot, solverProjectRoot });
}

export function normalizeMathRunBinding(value: unknown): MathRunBinding {
  try {
    const binding = schema.parse(value) as MathRunBinding;
    if (binding.problem?.verificationTargets) {
      const targets = binding.problem.verificationTargets;
      const targetIds = new Set<string>();
      const declarations = new Set<string>();
      for (const target of targets) {
        const declaration = `${target.pathRelative}\u0000${target.theoremName}`;
        if (targetIds.has(target.targetId) || declarations.has(declaration)) throw new MathRunBindingError();
        targetIds.add(target.targetId);
        declarations.add(declaration);
      }
    }
    for (const target of [
      binding.workspace,
      binding.projectRoot,
      binding.taskFile,
      binding.environmentFile,
      binding.artifactStoreRoot,
      binding.buildManifestRef,
      binding.generatedSourceRoot,
      ...binding.leanSourceRoots,
      ...binding.allowedWriteRoots,
    ])
      assertMathCanonicalPath(target);
    if (
      !isMathPathWithin(binding.workspace, binding.projectRoot) ||
      isMathPathWithin(binding.workspace, binding.taskFile) ||
      isMathPathWithin(binding.workspace, binding.environmentFile) ||
      isMathPathWithin(binding.workspace, binding.artifactStoreRoot) ||
      isMathPathWithin(binding.artifactStoreRoot, binding.workspace) ||
      isMathPathWithin(binding.workspace, binding.buildManifestRef) ||
      !binding.leanSourceRoots.includes(binding.generatedSourceRoot) ||
      !binding.allowedWriteRoots.some((root) => isMathPathWithin(root, binding.generatedSourceRoot)) ||
      binding.allowedWriteRoots.some((root) => !isMathPathWithin(binding.projectRoot, root)) ||
      new Set(binding.allowedWriteRoots).size !== binding.allowedWriteRoots.length ||
      new Set(binding.leanSourceRoots).size !== binding.leanSourceRoots.length ||
      binding.evaluatorConfigured !== Boolean(binding.evaluatorPolicyDigest)
    )
      throw new MathRunBindingError();
    return Object.freeze({
      ...binding,
      allowedWriteRoots: Object.freeze(binding.allowedWriteRoots),
      leanSourceRoots: Object.freeze(binding.leanSourceRoots),
      ...(binding.problem
        ? {
            problem: Object.freeze({
              ...binding.problem,
              ...(binding.problem.verificationTargets
                ? {
                    verificationTargets: Object.freeze(
                      binding.problem.verificationTargets.map((target) => Object.freeze({ ...target }))
                    ),
                  }
                : {}),
            }),
          }
        : {}),
    });
  } catch {
    throw new MathRunBindingError();
  }
}

export function readMathRunBinding(inputs: MathRunInputs): MathRunBinding {
  const binding = normalizeMathRunBinding(readMathRunBindingProjection(inputs));
  if (
    binding.taskFile !== inputs.task.path ||
    binding.environmentFile !== inputs.environment.path ||
    binding.taskHash !== inputs.task.digest
  )
    throw new MathRunBindingError();
  const environment = readMathRunEnvironmentProjection(inputs);
  if (mathDigest(canonicalMathJson(environment)) !== binding.environmentDigest) throw new MathRunBindingError();
  return binding;
}

export function verifyMathRunBindingArtifacts(
  inputs: MathRunInputs,
  artifacts: Readonly<{ lakeExecutable: string; toolManifestRef: string }>
): MathRunBinding {
  try {
    const binding = readMathRunBinding(inputs);
    const environment = z.record(z.string(), z.string()).parse(readMathRunEnvironmentProjection(inputs));
    if (environment.DEEPSCIENTIST_LEAN_EVAL_TOOL_MANIFEST !== artifacts.toolManifestRef)
      throw new MathRunBindingError();
    if (
      stableExternalFileDigest(binding.buildManifestRef) !== binding.buildManifestDigest ||
      stableExternalFileDigest(artifacts.lakeExecutable, true) !== binding.lakeExecutableDigest ||
      stableExternalFileDigest(artifacts.toolManifestRef) !== binding.toolManifestDigest
    )
      throw new MathRunBindingError();
    return binding;
  } catch {
    throw new MathRunBindingError();
  }
}

export function mathAssignmentSourceRoot(binding: MathRunBinding, assignmentId: string): string {
  if (!/^[A-Za-z0-9_-]{1,128}$/u.test(assignmentId)) throw new MathRunBindingError();
  // A fixed-length identifier also fits filesystem component limits for 128-byte IDs.
  const encoded = `A_${mathDigest(assignmentId)}`;
  return path.join(binding.generatedSourceRoot, 'DeepScientistGenerated', encoded);
}

/** Build the runtime-owned v2 binding while the input projection is frozen. */
export function createMathRunBinding(
  input: Readonly<{
    inputs: MathRunInputs;
    workspace: string;
    projectRoot: string;
    baseCommit: string;
    leanToolchain: string;
    lakeExecutableDigest: string;
    toolManifestDigest: string;
    buildManifestRef: string;
    buildManifestDigest: string;
    artifactStoreRoot: string;
    evaluatorPolicyDigest?: string;
  }>
): MathRunBinding {
  const generatedSourceRoot = path.join(input.projectRoot, 'DeepScientistGenerated');
  const binding = {
    schema: 'deepscientist.math.run-binding.v2' as const,
    runId: mathDigest(input.inputs.root),
    taskFile: input.inputs.task.path,
    taskHash: input.inputs.task.digest,
    workspace: path.resolve(input.workspace),
    projectRoot: path.resolve(input.projectRoot),
    baseCommit: input.baseCommit,
    allowedWriteRoots: [generatedSourceRoot],
    environmentFile: input.inputs.environment.path,
    // freezeMathRunInputs invokes this callback before sealing its temporary
    // input directory; the final projection is still verified read-only after
    // binding.json has been written.
    environmentDigest: mathDigest(
      canonicalMathJson(readMathRunEnvironmentProjection(input.inputs, { allowWritableRoot: true }))
    ),
    leanToolchain: input.leanToolchain,
    lakeExecutableDigest: input.lakeExecutableDigest,
    toolManifestDigest: input.toolManifestDigest,
    leanSourceRoots: [path.resolve(input.projectRoot), generatedSourceRoot],
    generatedSourceRoot,
    artifactStoreRoot: path.resolve(input.artifactStoreRoot),
    artifactStorePolicyDigest: mathDigest('deepscientist.math.artifact-store.v1'),
    buildManifestRef: path.resolve(input.buildManifestRef),
    buildManifestDigest: input.buildManifestDigest,
    evaluatorConfigured: Boolean(input.evaluatorPolicyDigest),
    ...(input.evaluatorPolicyDigest ? { evaluatorPolicyDigest: input.evaluatorPolicyDigest } : {}),
  } satisfies MathRunBinding;
  return normalizeMathRunBinding(binding);
}
