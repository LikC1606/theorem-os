import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { mathGitBytes, mathGitText, mathGitResult } from './mathGit';
import { mathDigest as sha256 } from './mathRuntimeIo';
import { isMathPathWithin as isWithin } from './paths';
import { inspectScopedLeanDeclarations } from './leanSource';
import { canonicalMathProblemStatementPayloads, normalizeMathProblemContract, type MathProblemContract } from "./contracts";

export const IMO2026_ADAPTER_ID = 'imo2026' as const;
export const IMO2026_ADAPTER_VERSION = '1' as const;
export const IMO2026_BOOTSTRAP_SCHEMA = 'deepscientist.mathematics.imo2026-bootstrap-receipt.v1' as const;
export const IMO2026_REPOSITORY_URL = 'https://github.com/humanfia/imo2026.git' as const;
export const IMO2026_SOURCE_COMMIT = '834c01f2ecac89b648759b1c95bc6180b0ede149' as const;
export const IMO2026_SUPPORTED_PROBLEMS = Object.freeze([
  'imo2026_q1',
  'imo2026_q2',
  'imo2026_q3',
  'imo2026_q4',
  'imo2026_q5',
  'imo2026_q6',
] as const);

type ImoProblemId = (typeof IMO2026_SUPPORTED_PROBLEMS)[number];

const PROBLEM_NUMBER: Readonly<Record<ImoProblemId, string>> = Object.freeze({
  imo2026_q1: 'Q1',
  imo2026_q2: 'Q2',
  imo2026_q3: 'Q3',
  imo2026_q4: 'Q4',
  imo2026_q5: 'Q5',
  imo2026_q6: 'Q6',
});

const EXPECTED_THEOREMS: Readonly<Record<ImoProblemId, readonly string[]>> = Object.freeze({
  imo2026_q1: Object.freeze([
    'statement_a_termination',
    'statement_a_unique_large',
    'statement_b_invariance',
    'terminal_value_eq_Mval',
    'Mval_gt_one',
  ]),
  imo2026_q2: Object.freeze(['main_theorem']),
  imo2026_q3: Object.freeze([
    'pieceLengths_sum',
    'pieceLengths_length',
    'L_mem_Icc',
    'V_eq',
    'lower_bound',
    'upper_bound',
  ]),
  imo2026_q4: Object.freeze(['main_theorem']),
  imo2026_q5: Object.freeze(['main_theorem']),
  imo2026_q6: Object.freeze(['main_theorem']),
});

const EXPECTED_TRUSTED_FILES = Object.freeze([
  'Challenge.lean',
  'lakefile.lean',
  'lakefile.toml',
  'lake-manifest.json',
  'lean-toolchain',
  'MathFlowBench/CacheWarm.lean',
  'MathFlowBench/DeepScientistGenerated/A_probe/Probe.lean',
  'docs/humanize/math-contract.json',
] as const);

const IMO2026_LAKEFILE_TOML = [
  'name = "IMO2026Humanize"',
  'defaultTargets = ["Submission"]',
  '',
  '[leanOptions]',
  'autoImplicit = false',
  '',
  '[[require]]',
  'name = "mathlib"',
  'git = "https://github.com/leanprover-community/mathlib4.git"',
  'rev = "v4.31.0"',
  '',
  '[[lean_lib]]',
  'name = "MathFlowBench"',
  'srcDir = "MathFlowBench"',
  '',
  '[[lean_lib]]',
  'name = "Submission"',
  '',
].join('\n');
const IMO2026_PROBE_SOURCE = 'import Mathlib\n\nnamespace DeepScientistGenerated\n\nend DeepScientistGenerated\n';

export type Imo2026EvaluatorPolicy = Readonly<{
  mode: 'local_compile_only';
  command: string;
  policyDigest: string;
  official: false;
}>;

export type Imo2026BootstrapReceipt = Readonly<{
  schema: typeof IMO2026_BOOTSTRAP_SCHEMA;
  adapterId: typeof IMO2026_ADAPTER_ID;
  adapterVersion: typeof IMO2026_ADAPTER_VERSION;
  receiptId: string;
  problemId: ImoProblemId;
  sourceRepositoryUrl: typeof IMO2026_REPOSITORY_URL;
  sourceRepositoryRoot: string;
  sourceCommit: typeof IMO2026_SOURCE_COMMIT;
  sourceRelativePath: string;
  sourceSha256: string;
  theoremNames: readonly string[];
  workspaceRoot: string;
  projectRoot: string;
  activeProblemPath: string;
  baseCommit: string;
  trustedFiles: readonly string[];
  solverOwnedFiles: readonly string[];
  toolchain: string;
  contract: MathProblemContract;
  evaluator: Imo2026EvaluatorPolicy;
  createdAt: number;
}>;

export type Imo2026BootstrapOptions = Readonly<{
  repositoryRoot: string;
  problemId: ImoProblemId;
  workspaceRoot?: string;
}>;

const fullGitObjectId = /^[0-9a-f]{40,64}$/u;
const hash = /^[0-9a-f]{64}$/u;

const asProblemId = (value: string): ImoProblemId => {
  if (!IMO2026_SUPPORTED_PROBLEMS.includes(value as ImoProblemId)) throw new Error('imo2026_problem_unsupported');
  return value as ImoProblemId;
};

const git = (root: string, args: readonly string[]) => mathGitText(root, args,
  { maxBuffer: 4 * 1024 * 1024, errorMessage: 'imo2026_git_identity_unavailable' });

/** Read an immutable input from Git without normalising its bytes. */
const gitBlob = (cwd: string, commit: string, relativePath: string): Buffer => {
  const object = `${commit}:${relativePath}`;
  const tree = mathGitBytes(cwd, ['ls-tree', '-z', commit, '--', relativePath], {
    maxBuffer: 1024 * 1024, errorMessage: 'imo2026_source_blob_unavailable',
  });
  const entries = tree.toString('utf8').split('\0').filter(Boolean);
  if (entries.length !== 1) throw new Error('imo2026_source_blob_unavailable');
  const treeEntry = entries[0]!.match(/^(\d{6}) (blob|tree|commit) [0-9a-f]{40,64}\t(.+)$/u);
  if (!treeEntry || treeEntry[3] !== relativePath || treeEntry[1] !== '100644' || treeEntry[2] !== 'blob')
    throw new Error('imo2026_source_blob_unavailable');
  if (mathGitText(cwd, ['cat-file', '-t', object],
      { maxBuffer: 1024, errorMessage: 'imo2026_source_blob_unavailable' }) !== 'blob') {
    throw new Error('imo2026_source_blob_unavailable');
  }
  return mathGitBytes(cwd, ['cat-file', 'blob', object], {
    maxBuffer: 16 * 1024 * 1024, errorMessage: 'imo2026_source_blob_unavailable',
  });
};

const assertCanonicalDirectory = (directory: string, field: string): string => {
  const resolved = path.resolve(directory);
  if (resolved !== directory) throw new Error(`imo2026_${field}_must_be_absolute`);
  const stat = fs.lstatSync(resolved);
  if (stat.isSymbolicLink() || !stat.isDirectory()) throw new Error(`imo2026_${field}_must_be_directory`);
  if (fs.realpathSync(resolved) !== resolved) throw new Error(`imo2026_${field}_must_not_be_symlink`);
  return resolved;
};

const assertRegularFile = (file: string, field: string): string => {
  const resolved = path.resolve(file);
  const stat = fs.lstatSync(resolved);
  if (stat.isSymbolicLink() || !stat.isFile()) throw new Error(`imo2026_${field}_must_be_regular_file`);
  if (fs.realpathSync(resolved) !== resolved) throw new Error(`imo2026_${field}_must_not_be_symlink`);
  return resolved;
};

const theoremNamesFromSource = (source: string): readonly string[] => {
  const names = [...source.matchAll(/^\s*theorem\s+([A-Za-z_][A-Za-z0-9_']*)/gmu)].map((match) => match[1]!);
  return Object.freeze([...new Set(names)]);
};

export const theoremQualifiedNamesFromSource = (source: string): readonly string[] => {
  return Object.freeze([...new Set(inspectScopedLeanDeclarations(source).filter(declaration => declaration.kind === 'theorem')
    .map(declaration => declaration.qualifiedName))]);
};

const sourceBytesFor = (repositoryRoot: string, relativePath: string): Buffer =>
  gitBlob(repositoryRoot, IMO2026_SOURCE_COMMIT, relativePath);

/** Read a pinned tree file and reject links/submodules before reading bytes. */
const pinnedTrustedBytes = (repositoryRoot: string, relative: string): Buffer =>
  sourceBytesFor(repositoryRoot, `base/${relative}`);

const copyTrustedBytes = (bytes: Uint8Array, target: string): void => {
  fs.mkdirSync(path.dirname(target), { recursive: true, mode: 0o700 });
  const descriptor = fs.openSync(target, fs.constants.O_WRONLY | fs.constants.O_CREAT | fs.constants.O_TRUNC, 0o600);
  try {
    fs.writeFileSync(descriptor, bytes);
    fs.fsyncSync(descriptor);
  } finally {
    fs.closeSync(descriptor);
  }
};

const writeTrustedText = (target: string, contents: string): void => {
  fs.mkdirSync(path.dirname(target), { recursive: true, mode: 0o700 });
  fs.writeFileSync(target, contents, { mode: 0o600 });
  fs.chmodSync(target, 0o600);
};

const runtimeTrustedText = (relative: string): string | undefined => {
  if (relative === 'lakefile.toml') return IMO2026_LAKEFILE_TOML;
  if (relative === 'MathFlowBench/DeepScientistGenerated/A_probe/Probe.lean') return IMO2026_PROBE_SOURCE;
  return undefined;
};

const writeJson = (file: string, value: unknown): void => writeTrustedText(file, `${JSON.stringify(value, null, 2)}\n`);

const ensureFreshWorkspace = (workspaceRoot: string): string => {
  const resolved = path.resolve(workspaceRoot);
  if (fs.existsSync(resolved)) {
    const stat = fs.lstatSync(resolved);
    if (stat.isSymbolicLink() || !stat.isDirectory() || fs.readdirSync(resolved).length > 0)
      throw new Error('imo2026_workspace_must_be_fresh');
  } else {
    fs.mkdirSync(resolved, { recursive: true, mode: 0o700 });
  }
  return assertCanonicalDirectory(resolved, 'workspace');
};

const initializeGit = (workspaceRoot: string): string => {
  for (const args of [
    ['init', '--quiet'],
    ['config', 'user.email', 'deepscientist@localhost'],
    ['config', 'user.name', 'DeepScientist'],
    ['add', '--', 'generated'],
    ['commit', '--quiet', '-m', 'IMO2026 public solver baseline'],
  ] as const) {
    mathGitText(workspaceRoot, args, { maxBuffer: 4 * 1024 * 1024, errorMessage: 'imo2026_workspace_git_init_failed' });
  }
  // The receipt is written after the baseline commit; Lake also creates local
  // build/cache files during preflight. Neither is candidate source. Keep them
  // out of Git's dirty-source gate without ignoring any Lean source or notes.
  fs.appendFileSync(
    path.join(workspaceRoot, '.git', 'info', 'exclude'),
    '\n/active-problem.json\n/generated/*/.lake/\n',
    'utf8'
  );
  return git(workspaceRoot, ['rev-parse', 'HEAD']);
};

const contractFor = (problemId: ImoProblemId, source: string): MathProblemContract => {
  const problemNumber = PROBLEM_NUMBER[problemId];
  const informalStatement = `IMO 2026 ${problemNumber}: authoritative public Lean statement from the pinned Humanfia source.`;
  const assumptions = Object.freeze([] as string[]);
  const payloads = canonicalMathProblemStatementPayloads({ informalStatement, formalStatement: source, assumptions });
  return normalizeMathProblemContract({
    problemId,
    informalStatement,
    formalStatement: source,
    assumptions,
    statementHash: sha256(payloads.informal),
    leanStatementHash: sha256(payloads.lean),
    knownTraps: [
      'Do not edit Challenge.lean or the pinned public source metadata.',
      'Do not edit lakefile.toml or the runtime-owned source probe marker.',
      'Do not use sorry, admit, native_decide, unsafe, or unapproved axioms.',
      'Existing candidate proofs outside this runtime-owned workspace are not inputs.',
    ],
    acceptanceCriteria: [
      `Preserve the exact public declarations for ${EXPECTED_THEOREMS[problemId].join(', ')}.`,
      'Produce a compiling solver-owned Submission.lean in the isolated workspace.',
      'Pass the host-owned evaluator after the solver commit is frozen.',
    ],
    officialVerificationCommand: 'lake env lean Submission.lean',
  });
};

const evaluatorPolicy = (): Imo2026EvaluatorPolicy => {
  const command = 'lake env lean Submission.lean';
  return Object.freeze({
    mode: 'local_compile_only',
    command,
    policyDigest: sha256(JSON.stringify({ schema: 'deepscientist.mathematics.imo2026-evaluator-policy.v1', command })),
    official: false,
  });
};

const contractDocumentFor = (
  problemId: ImoProblemId,
  contract: MathProblemContract
): Readonly<Record<string, unknown>> =>
  Object.freeze({
    schema: 'deepscientist.imo2026.math-contract.v1',
    problemContract: contract,
    alignmentTemplate: {
      problemId,
      statementHash: contract.statementHash,
      leanStatementHash: contract.leanStatementHash,
      goalInOwnWords: contract.formalStatement,
      quantifiedObjects: [`All quantified objects in ${problemId}.`],
      assumptions: [...contract.assumptions],
      forbiddenChanges: [...contract.knownTraps],
      officialVerificationCommand: contract.officialVerificationCommand,
      verdict: 'exact',
      assumptionDelta: [] as string[],
      quantifierDelta: [] as string[],
      domainDelta: [] as string[],
    },
  });

export function expectedImo2026Theorems(problemId: string): readonly string[] {
  return EXPECTED_THEOREMS[asProblemId(problemId)];
}

export async function bootstrapImo2026Problem(options: Imo2026BootstrapOptions): Promise<Imo2026BootstrapReceipt> {
  const repositoryRoot = assertCanonicalDirectory(path.resolve(options.repositoryRoot), 'repository');
  if (git(repositoryRoot, ['rev-parse', '--show-toplevel']) !== repositoryRoot)
    throw new Error('imo2026_repository_identity');
  if (git(repositoryRoot, ['rev-parse', 'HEAD']).toLowerCase() !== IMO2026_SOURCE_COMMIT) {
    throw new Error('imo2026_source_commit_mismatch');
  }
  const problemId = asProblemId(options.problemId);
  const problemNumber = PROBLEM_NUMBER[problemId];
  const sourceRelativePath = `base/IMO2026/${problemNumber}/problem.lean`;
  // The pinned commit is authoritative. The checkout is only used for Git
  // identity and for unrelated runtime templates, so a dirty source file
  // cannot silently change the problem contract.
  const sourceBytes = sourceBytesFor(repositoryRoot, sourceRelativePath);
  const source = new TextDecoder('utf-8', { fatal: true }).decode(sourceBytes);
  const theoremNames = theoremNamesFromSource(source);
  const expectedTheorems = EXPECTED_THEOREMS[problemId];
  if (JSON.stringify(theoremNames) !== JSON.stringify(expectedTheorems))
    throw new Error('imo2026_theorem_identity_mismatch');

  const workspaceRoot = ensureFreshWorkspace(
    options.workspaceRoot ?? fs.mkdtempSync(path.join(os.tmpdir(), `deepscientist-${problemId}-`))
  );
  const projectRoot = path.join(workspaceRoot, 'generated', problemId);
  fs.mkdirSync(projectRoot, { recursive: true, mode: 0o700 });
  const trustedFiles = [...EXPECTED_TRUSTED_FILES];
  writeTrustedText(path.join(projectRoot, 'Challenge.lean'), source);
  for (const relative of EXPECTED_TRUSTED_FILES) {
    if (relative === 'Challenge.lean' || relative === 'docs/humanize/math-contract.json') continue;
    const runtimeText = runtimeTrustedText(relative);
    if (runtimeText) writeTrustedText(path.join(projectRoot, relative), runtimeText);
    else copyTrustedBytes(pinnedTrustedBytes(repositoryRoot, relative), path.join(projectRoot, relative));
  }
  writeTrustedText(path.join(projectRoot, 'Submission.lean'), source);
  const contract = contractFor(problemId, source);
  writeJson(path.join(projectRoot, 'docs/humanize/math-contract.json'), contractDocumentFor(problemId, contract));
  const baseCommit = initializeGit(workspaceRoot);
  const receipt: Imo2026BootstrapReceipt = Object.freeze({
    schema: IMO2026_BOOTSTRAP_SCHEMA,
    adapterId: IMO2026_ADAPTER_ID,
    adapterVersion: IMO2026_ADAPTER_VERSION,
    receiptId: `imo2026-bootstrap:${problemId}:${sha256(`${IMO2026_SOURCE_COMMIT}\0${sha256(source)}`).slice(0, 24)}`,
    problemId,
    sourceRepositoryUrl: IMO2026_REPOSITORY_URL,
    sourceRepositoryRoot: repositoryRoot,
    sourceCommit: IMO2026_SOURCE_COMMIT,
    sourceRelativePath,
    sourceSha256: sha256(sourceBytes),
    theoremNames: Object.freeze([...theoremNames]),
    workspaceRoot,
    projectRoot,
    activeProblemPath: path.join(workspaceRoot, 'active-problem.json'),
    baseCommit,
    trustedFiles: Object.freeze(trustedFiles),
    solverOwnedFiles: Object.freeze(['Submission.lean']),
    toolchain: fs.readFileSync(path.join(projectRoot, 'lean-toolchain'), 'utf8').trim(),
    contract,
    evaluator: evaluatorPolicy(),
    createdAt: Date.now(),
  });
  writeJson(receipt.activeProblemPath, receipt);
  return receipt;
}

export function readImo2026BootstrapReceipt(file: string): Imo2026BootstrapReceipt {
  const receiptPath = assertRegularFile(path.resolve(file), 'receipt');
  const parsed = JSON.parse(fs.readFileSync(receiptPath, 'utf8')) as Partial<Imo2026BootstrapReceipt>;
  if (
    parsed.schema !== IMO2026_BOOTSTRAP_SCHEMA ||
    parsed.adapterId !== IMO2026_ADAPTER_ID ||
    parsed.adapterVersion !== IMO2026_ADAPTER_VERSION ||
    typeof parsed.problemId !== 'string' ||
    !IMO2026_SUPPORTED_PROBLEMS.includes(parsed.problemId as ImoProblemId) ||
    parsed.sourceCommit !== IMO2026_SOURCE_COMMIT ||
    typeof parsed.sourceSha256 !== 'string' ||
    !hash.test(parsed.sourceSha256) ||
    typeof parsed.baseCommit !== 'string' ||
    !fullGitObjectId.test(parsed.baseCommit) ||
    !Array.isArray(parsed.theoremNames) ||
    JSON.stringify(parsed.theoremNames) !== JSON.stringify(expectedImo2026Theorems(parsed.problemId))
  ) {
    throw new Error('imo2026_receipt_invalid');
  }
  const contract = normalizeMathProblemContract(parsed.contract as MathProblemContract);
  if (contract.problemId !== parsed.problemId) throw new Error('imo2026_receipt_contract_mismatch');
  return parsed as Imo2026BootstrapReceipt;
}

export function verifyImo2026BootstrapReceipt(receipt: Imo2026BootstrapReceipt): void {
  if (
    receipt.schema !== IMO2026_BOOTSTRAP_SCHEMA ||
    receipt.adapterId !== IMO2026_ADAPTER_ID ||
    receipt.adapterVersion !== IMO2026_ADAPTER_VERSION ||
    receipt.sourceRepositoryUrl !== IMO2026_REPOSITORY_URL ||
    !IMO2026_SUPPORTED_PROBLEMS.includes(receipt.problemId)
  ) {
    throw new Error('imo2026_receipt_invalid');
  }
  const problemNumber = PROBLEM_NUMBER[receipt.problemId];
  const expectedSourceRelativePath = `base/IMO2026/${problemNumber}/problem.lean`;
  if (receipt.sourceRelativePath !== expectedSourceRelativePath) {
    throw new Error('imo2026_source_path_mismatch');
  }
  const expectedWorkspaceRoot = path.resolve(receipt.workspaceRoot);
  const expectedProjectRoot = path.join(expectedWorkspaceRoot, 'generated', receipt.problemId);
  if (receipt.workspaceRoot !== expectedWorkspaceRoot || receipt.projectRoot !== expectedProjectRoot) {
    throw new Error('imo2026_receipt_workspace_binding_mismatch');
  }
  if (JSON.stringify(receipt.trustedFiles) !== JSON.stringify(EXPECTED_TRUSTED_FILES)) {
    throw new Error('imo2026_trusted_files_invalid');
  }
  if (JSON.stringify(receipt.solverOwnedFiles) !== JSON.stringify(['Submission.lean'])) {
    throw new Error('imo2026_solver_ownership_invalid');
  }
  const expectedTheorems = expectedImo2026Theorems(receipt.problemId);
  if (JSON.stringify(receipt.theoremNames) !== JSON.stringify(expectedTheorems)) {
    throw new Error('imo2026_theorem_identity_mismatch');
  }
  const sourceRoot = assertCanonicalDirectory(receipt.sourceRepositoryRoot, 'repository');
  if (git(sourceRoot, ['rev-parse', 'HEAD']).toLowerCase() !== IMO2026_SOURCE_COMMIT)
    throw new Error('imo2026_source_commit_mismatch');
  const sourceBytes = sourceBytesFor(sourceRoot, receipt.sourceRelativePath);
  const source = new TextDecoder('utf-8', { fatal: true }).decode(sourceBytes);
  if (sha256(sourceBytes) !== receipt.sourceSha256) throw new Error('imo2026_source_hash_mismatch');
  if (JSON.stringify(theoremNamesFromSource(source)) !== JSON.stringify(expectedTheorems)) {
    throw new Error('imo2026_theorem_identity_mismatch');
  }
  const workspace = assertCanonicalDirectory(receipt.workspaceRoot, 'workspace');
  const project = assertCanonicalDirectory(receipt.projectRoot, 'project');
  if (
    !isWithin(workspace, project) ||
    path.resolve(receipt.activeProblemPath) !== path.join(workspace, 'active-problem.json')
  )
    throw new Error('imo2026_receipt_workspace_binding_mismatch');
  // The bootstrap commit is the trust baseline. Solver work is expected to
  // advance the workspace HEAD, so require the current history to descend
  // from that baseline rather than requiring an unchanged HEAD.
  const ancestry = mathGitResult(workspace, ['merge-base', '--is-ancestor', receipt.baseCommit, 'HEAD'], { maxBuffer: 4 * 1024 * 1024 });
  if (ancestry.error) throw new Error('imo2026_git_identity_unavailable');
  if (ancestry.status !== 0) throw new Error('imo2026_workspace_commit_mismatch');
  if (sha256(fs.readFileSync(path.join(project, 'Challenge.lean')) as Buffer) !== receipt.sourceSha256)
    throw new Error('imo2026_challenge_hash_mismatch');
  for (const relative of EXPECTED_TRUSTED_FILES) {
    const target = assertRegularFile(path.join(project, relative), `trusted_file_${relative.replaceAll('/', '_')}`);
    if (relative === 'Challenge.lean' || relative === 'docs/humanize/math-contract.json') continue;
    const runtimeText = runtimeTrustedText(relative);
    const expectedDigest = runtimeText ? sha256(runtimeText) : sha256(pinnedTrustedBytes(sourceRoot, relative));
    if (sha256(fs.readFileSync(target)) !== expectedDigest) {
      throw new Error('imo2026_trusted_file_hash_mismatch');
    }
  }
  const expectedContract = contractFor(receipt.problemId, source);
  if (JSON.stringify(receipt.contract) !== JSON.stringify(expectedContract)) {
    throw new Error('imo2026_contract_mismatch');
  }
  let actualContractDocument: unknown;
  try {
    actualContractDocument = JSON.parse(
      fs.readFileSync(path.join(project, 'docs/humanize/math-contract.json'), 'utf8')
    ) as unknown;
  } catch {
    throw new Error('imo2026_contract_document_invalid');
  }
  if (
    JSON.stringify(actualContractDocument) !== JSON.stringify(contractDocumentFor(receipt.problemId, expectedContract))
  ) {
    throw new Error('imo2026_contract_document_mismatch');
  }
  if (receipt.toolchain !== fs.readFileSync(path.join(project, 'lean-toolchain'), 'utf8').trim()) {
    throw new Error('imo2026_toolchain_mismatch');
  }
  const expectedEvaluator = evaluatorPolicy();
  if (JSON.stringify(receipt.evaluator) !== JSON.stringify(expectedEvaluator)) {
    throw new Error('imo2026_evaluator_policy_mismatch');
  }
  assertRegularFile(path.join(project, 'Submission.lean'), 'submission');
}
