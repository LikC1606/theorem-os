/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

import fs from 'node:fs';
import path from 'node:path';
import { mathGitBytes, mathGitText } from './mathGit';
import { mathDigest as sha256 } from './mathRuntimeIo';
import { parse as parseToml } from 'smol-toml';
import { canonicalMathProblemStatementPayloads, normalizeMathOfficialProblemManifest, normalizeMathProblemContract, type MathOfficialProblemManifest, type MathProblemContract } from "./contracts";
import { canonicalMathOfficialManifestPayload, normalizedRepositoryUrl } from "./verifier";
import { hashMathFormalSourceDeclaration } from "./leanSource";
import { assertLeanEvalSubmissionComplete } from "./leanEvalSubmission";

const LEAN_EVAL_ADAPTER_ID = 'lean-eval' as const;
const LEAN_EVAL_ADAPTER_VERSION = '1' as const;
const LEAN_EVAL_OFFICIAL_COMMAND = 'lake test' as const;
const LEAN_EVAL_MANIFEST_PATH = '.deepscientist/math/official-manifest.json' as const;
const LEAN_EVAL_AUTHORITY_PATH = '.deepscientist/math/official-manifest.authority.json' as const;
const LEAN_EVAL_PERMITTED_AXIOMS = Object.freeze(['Classical.choice', 'Quot.sound', 'propext']);
const REQUIRED_TRUSTED_FILES = Object.freeze([
  'Challenge.lean',
  'Solution.lean',
  'WorkspaceTest.lean',
  'config.json',
  'holes.json',
  'lakefile.toml',
  'lean-toolchain',
]);
const MAX_GIT_OUTPUT_BYTES = 64 * 1024 * 1024;
const MAX_TRACKED_FILE_BYTES = 16 * 1024 * 1024;
const MAX_TRACKED_FILES = 1024;

type LeanEvalConfig = Readonly<{
  challenge_module: string;
  solution_module: string;
  theorem_names: readonly string[];
  definition_names: readonly string[];
  permitted_axioms: readonly string[];
  enable_nanoda: boolean;
}>;

type LeanEvalHole = Readonly<{
  name: string;
  basename: string;
  kind: 'theorem' | 'def';
  body: string;
}>;

type GitTreeFile = Readonly<{
  mode: string;
  oid: string;
  path: string;
}>;

export type LeanEvalProblemBindingRequest = Readonly<{
  projectRoot: string;
  problemId: string;
  title: string;
  informalStatement?: string;
  assumptions?: readonly string[];
  statementRevision: number;
  baselineCommit: string;
  repositoryUrl: string;
}>;

export type LeanEvalProblemBinding = Readonly<{
  repositoryRoot: string;
  projectRoot: string;
  problemRelativePath: string;
  baselineCommit: string;
  holeNames: readonly string[];
  publicObligations: readonly Readonly<{ name: string; kind: 'theorem' | 'def'; declarationHash: string }>[];
  solverOwnedPaths: readonly string[];
  officialManifestPath: typeof LEAN_EVAL_MANIFEST_PATH;
  authorityPath: typeof LEAN_EVAL_AUTHORITY_PATH;
  problemContract: MathProblemContract;
  officialManifest: MathOfficialProblemManifest;
  officialManifestContent: string;
  authorityContent: string;
}>;


const requireText = (value: unknown, field: string): string => {
  if (typeof value !== 'string' || !value.trim()) throw new Error(`${field} must be a non-empty string.`);
  return value.trim();
};

const requireStringList = (value: unknown, field: string): readonly string[] => {
  if (value === undefined) return Object.freeze([]);
  if (!Array.isArray(value)) throw new Error(`${field} must be an array of strings.`);
  const normalized = value.map((item, index) => requireText(item, `${field}[${index}]`));
  if (new Set(normalized).size !== normalized.length) throw new Error(`${field} must not contain duplicates.`);
  return Object.freeze(normalized);
};

const requireBoolean = (value: unknown, field: string): boolean => {
  if (typeof value !== 'boolean') throw new Error(`${field} must be a boolean.`);
  return value;
};

const runGitText = (root: string, args: readonly string[]) => mathGitText(root, args, { maxBuffer: MAX_GIT_OUTPUT_BYTES });
const runGitBytes = (root: string, args: readonly string[]) => mathGitBytes(root, args, { maxBuffer: MAX_GIT_OUTPUT_BYTES });

const normalizeRelativePath = (value: string, field: string): string => {
  const normalized = value.trim().replaceAll('\\', '/').replace(/^\.\//u, '');
  if (!normalized || normalized.includes('\0') || path.posix.isAbsolute(normalized)) {
    throw new Error(`${field} must be a repository-relative path.`);
  }
  if (normalized.split('/').some((part) => !part || part === '.' || part === '..')) {
    throw new Error(`${field} must not contain traversal or empty segments.`);
  }
  return normalized;
};

const parseTree = (output: Buffer): readonly GitTreeFile[] =>
  Object.freeze(
    output
      .toString('utf8')
      .split('\0')
      .filter(Boolean)
      .map((record) => {
        const separator = record.indexOf('\t');
        const header = separator >= 0 ? record.slice(0, separator) : '';
        const filePath = separator >= 0 ? record.slice(separator + 1) : '';
        const match = /^(\d{6}) blob ([0-9a-f]{40,64})$/u.exec(header);
        if (!match || !filePath) throw new Error('LeanEval baseline contains an unsupported Git tree entry.');
        return Object.freeze({ mode: match[1], oid: match[2], path: normalizeRelativePath(filePath, 'tree path') });
      })
  );

const relativeToProblem = (problemRelativePath: string, repositoryRelativePath: string): string => {
  if (repositoryRelativePath === problemRelativePath) return '';
  const prefix = `${problemRelativePath}/`;
  if (!repositoryRelativePath.startsWith(prefix)) {
    throw new Error(`LeanEval tree entry escaped the selected problem: ${repositoryRelativePath}`);
  }
  return repositoryRelativePath.slice(prefix.length);
};

const isSolverOwnedPath = (problemPath: string): boolean =>
  problemPath === 'Submission.lean' || (problemPath.startsWith('Submission/') && problemPath.endsWith('.lean'));

const readBaselineFile = (repositoryRoot: string, baselineCommit: string, filePath: string): Buffer => {
  const contents = runGitBytes(repositoryRoot, ['show', `${baselineCommit}:${filePath}`]);
  if (contents.length > MAX_TRACKED_FILE_BYTES) {
    throw new Error(`LeanEval baseline file exceeds ${MAX_TRACKED_FILE_BYTES} bytes: ${filePath}`);
  }
  return contents;
};

const assertCurrentTrustedFileMatches = (repositoryRoot: string, file: GitTreeFile, baselineContents: Buffer): void => {
  const absolutePath = path.join(repositoryRoot, file.path);
  let stat: fs.Stats;
  try {
    stat = fs.lstatSync(absolutePath);
  } catch (error) {
    throw new Error(`LeanEval trusted file is missing from the current checkout: ${file.path}`, { cause: error });
  }
  if (!stat.isFile() || stat.isSymbolicLink()) {
    throw new Error(`LeanEval trusted file must be a regular non-symlink file: ${file.path}`);
  }
  if (sha256(fs.readFileSync(absolutePath)) !== sha256(baselineContents)) {
    throw new Error(`LeanEval trusted file differs from the selected baseline: ${file.path}`);
  }
};

const assertCurrentProtectedBlobMatches = (repositoryRoot: string, file: GitTreeFile): void => {
  const absolutePath = path.join(repositoryRoot, file.path);
  const stat = fs.lstatSync(absolutePath);
  if (!stat.isFile() || stat.isSymbolicLink()) {
    throw new Error(`LeanEval protected file must be a regular non-symlink file: ${file.path}`);
  }
  const currentOid = runGitText(repositoryRoot, ['hash-object', '--no-filters', '--', file.path]).toLowerCase();
  if (currentOid !== file.oid.toLowerCase()) {
    throw new Error(`LeanEval trusted file differs from the selected baseline: ${file.path}`);
  }
};

/** Parse one protected metadata file, rejecting malformed or non-object content with that file's own message. */
const parsedObject = (parse: () => unknown, invalid: string, notObject: string): Record<string, unknown> => {
  let parsed: unknown;
  try {
    parsed = parse();
  } catch (error) {
    throw new Error(invalid, { cause: error });
  }
  if (!parsed || typeof parsed !== 'object' || Array.isArray(parsed)) throw new Error(notObject);
  return parsed as Record<string, unknown>;
};

const parseLeanEvalConfig = (contents: Buffer): Readonly<{ config: LeanEvalConfig; holeNames: readonly string[] }> => {
  const config = parsedObject(() => JSON.parse(contents.toString('utf8')),
    'LeanEval config.json is not valid JSON.', 'LeanEval config.json must contain an object.');
  const challengeModule = requireText(config.challenge_module, 'config.challenge_module');
  const solutionModule = requireText(config.solution_module, 'config.solution_module');
  if (challengeModule !== 'Challenge' || solutionModule !== 'Solution') {
    throw new Error('LeanEval config must compare the trusted Challenge and Solution modules.');
  }
  const theoremNames = requireStringList(config.theorem_names, 'config.theorem_names');
  const definitionNames = requireStringList(config.definition_names, 'config.definition_names');
  const holeNames = [...theoremNames, ...definitionNames];
  if (!holeNames.length || new Set(holeNames).size !== holeNames.length) {
    throw new Error('LeanEval config must name at least one unique theorem or definition hole.');
  }
  const localHoleNames = holeNames.map((name) => name.split('.').at(-1)!);
  if (new Set(localHoleNames).size !== localHoleNames.length) {
    throw new Error('LeanEval config hole names must have unique local basenames.');
  }
  const permittedAxioms = requireStringList(config.permitted_axioms, 'config.permitted_axioms').toSorted();
  if (JSON.stringify(permittedAxioms) !== JSON.stringify(LEAN_EVAL_PERMITTED_AXIOMS.toSorted())) {
    throw new Error('LeanEval config permitted_axioms does not match the benchmark foundational-axiom policy.');
  }
  return Object.freeze({
    config: Object.freeze({
      challenge_module: challengeModule,
      solution_module: solutionModule,
      theorem_names: theoremNames,
      definition_names: definitionNames,
      permitted_axioms: Object.freeze(permittedAxioms),
      enable_nanoda: requireBoolean(config.enable_nanoda, 'config.enable_nanoda'),
    }),
    holeNames: Object.freeze(holeNames),
  });
};

const parseLeanEvalHoles = (contents: Buffer, problemId: string): readonly LeanEvalHole[] => {
  const metadata = parsedObject(() => JSON.parse(contents.toString('utf8')),
    'LeanEval holes.json is not valid JSON.', 'LeanEval holes.json must contain an object.');
  if (requireText(metadata.id, 'holes.id') !== problemId) {
    throw new Error('LeanEval holes.json id must match the problem id.');
  }
  requireText(metadata.module, 'holes.module');
  if (!Array.isArray(metadata.holes) || !metadata.holes.length) {
    throw new Error('LeanEval holes.json must contain at least one hole.');
  }
  const holes = metadata.holes.map((value, index): LeanEvalHole => {
    if (!value || typeof value !== 'object' || Array.isArray(value)) {
      throw new Error(`holes.holes[${index}] must be an object.`);
    }
    const hole = value as Record<string, unknown>;
    const name = requireText(hole.name, `holes.holes[${index}].name`);
    const basename = requireText(hole.basename, `holes.holes[${index}].basename`);
    const kind = requireText(hole.kind, `holes.holes[${index}].kind`);
    if (kind !== 'theorem' && kind !== 'def') {
      throw new Error(`holes.holes[${index}].kind must be theorem or def.`);
    }
    if (name.split('.').at(-1) !== basename) {
      throw new Error(`holes.holes[${index}] name and basename do not match.`);
    }
    return Object.freeze({
      name,
      basename,
      kind,
      body: requireText(hole.body, `holes.holes[${index}].body`),
    });
  });
  if (new Set(holes.map((hole) => hole.name)).size !== holes.length) {
    throw new Error('LeanEval holes.json must not contain duplicate hole names.');
  }
  return Object.freeze(holes);
};

const validateLeanEvalHoleDeclarations = (
  config: LeanEvalConfig,
  holes: readonly LeanEvalHole[],
  challengeSource: string,
  submissionTemplateSource: string
): void => {
  const expectedIdentities = [
    ...config.theorem_names.map((name) => `theorem\0${name.split('.').at(-1)}`),
    ...config.definition_names.map((name) => `def\0${name.split('.').at(-1)}`),
  ].toSorted();
  const actualIdentities = holes.map((hole) => `${hole.kind}\0${hole.basename}`).toSorted();
  if (JSON.stringify(actualIdentities) !== JSON.stringify(expectedIdentities)) {
    throw new Error('LeanEval config hole identities do not match holes.json.');
  }

  const configuredNameByIdentity = new Map<string, string>();
  for (const name of config.theorem_names) configuredNameByIdentity.set(`theorem\0${name.split('.').at(-1)}`, name);
  for (const name of config.definition_names) configuredNameByIdentity.set(`def\0${name.split('.').at(-1)}`, name);
  for (const hole of holes) {
    const identity = `${hole.kind}\0${hole.basename}`;
    const configuredName = configuredNameByIdentity.get(identity)!;
    const metadataHash = hashMathFormalSourceDeclaration(hole.body, hole.basename);
    const challengeHash = hashMathFormalSourceDeclaration(challengeSource, configuredName);
    const submissionHash = hashMathFormalSourceDeclaration(submissionTemplateSource, configuredName);
    if (!metadataHash || challengeHash !== metadataHash || submissionHash !== metadataHash) {
      throw new Error(`LeanEval hole declaration does not match config, Challenge, and Submission: ${configuredName}`);
    }
  }
};

const validateLakefile = (contents: Buffer, problemId: string): void => {
  const lakefile = parsedObject(() => parseToml(contents.toString('utf8')),
    'LeanEval lakefile.toml is not valid TOML.', 'LeanEval lakefile.toml must contain a TOML table.');
  if (requireText(lakefile.name, 'lakefile.name') !== problemId) {
    throw new Error('LeanEval lakefile package name must match the problem id.');
  }
  if (requireText(lakefile.testDriver, 'lakefile.testDriver') !== 'workspace_test') {
    throw new Error('LeanEval lakefile must use workspace_test as its test driver.');
  }
  const targets = new Set(requireStringList(lakefile.defaultTargets, 'lakefile.defaultTargets'));
  for (const required of ['Challenge', 'Solution', 'Submission']) {
    if (!targets.has(required)) throw new Error(`LeanEval lakefile defaultTargets must include ${required}.`);
  }
};

const manifestAuthorityContent = (manifest: MathOfficialProblemManifest): string =>
  `${JSON.stringify(
    {
      schema: 'deepscientist.mathematics.official-manifest-authority.v1',
      manifestHash: manifest.manifestHash,
      manifestId: manifest.manifestId,
      problemId: manifest.problemId,
      statementHash: manifest.statementHash,
      leanStatementHash: manifest.leanStatementHash,
      officialVerificationCommand: manifest.officialVerificationCommand,
      repositoryUrl: manifest.repositoryUrl,
      baselineCommit: manifest.baselineCommit,
      benchmarkAdapterId: manifest.benchmarkAdapterId,
      benchmarkAdapterVersion: manifest.benchmarkAdapterVersion,
    },
    null,
    2
  )}\n`;

export const prepareLeanEvalProblemBinding = (request: LeanEvalProblemBindingRequest): LeanEvalProblemBinding => {
  const projectRoot = fs.realpathSync(path.resolve(request.projectRoot));
  const repositoryRoot = fs.realpathSync(runGitText(projectRoot, ['rev-parse', '--show-toplevel']));
  const problemRelativePath = normalizeRelativePath(path.relative(repositoryRoot, projectRoot), 'projectRoot');
  const problemId = requireText(request.problemId, 'problemId');
  const title = requireText(request.title, 'title');
  if (!Number.isSafeInteger(request.statementRevision) || request.statementRevision < 1) {
    throw new Error('statementRevision must be a positive integer.');
  }
  const requestedBaseline = request.baselineCommit.trim().toLowerCase();
  if (!/^[0-9a-f]{40,64}$/u.test(requestedBaseline)) {
    throw new Error('baselineCommit must be a full Git object id.');
  }
  const baselineCommit = runGitText(repositoryRoot, ['rev-parse', `${requestedBaseline}^{commit}`]).toLowerCase();
  if (baselineCommit !== requestedBaseline) throw new Error('baselineCommit did not resolve to the requested commit.');
  const repositoryUrl = requireText(request.repositoryUrl, 'repositoryUrl');
  const origin = runGitText(repositoryRoot, ['config', '--get', 'remote.origin.url']);
  if (normalizedRepositoryUrl(origin) !== normalizedRepositoryUrl(repositoryUrl)) {
    throw new Error('LeanEval repositoryUrl does not match remote.origin.url.');
  }

  const tree = parseTree(
    runGitBytes(repositoryRoot, ['ls-tree', '-r', '-z', baselineCommit, '--', problemRelativePath])
  );
  if (!tree.length) throw new Error('LeanEval problem is absent from the selected baseline.');
  const filesByProblemPath = new Map<string, Readonly<{ tree: GitTreeFile; contents: Buffer }>>();
  const trackedFiles: Array<Readonly<{ path: string; sha256: string }>> = [];
  const solverOwnedPaths: string[] = [];
  for (const file of tree) {
    const problemPath = relativeToProblem(problemRelativePath, file.path);
    if (!problemPath) continue;
    if (file.mode === '120000') throw new Error(`LeanEval baseline must not contain symlinks: ${file.path}`);
    if (problemPath.startsWith('Submission/') && !problemPath.endsWith('.lean')) {
      throw new Error(`LeanEval Submission directory contains a non-Lean file: ${problemPath}`);
    }
    // The evaluator solution is protected material.  Presence and tree mode
    // are enough for the binding; never load its bytes into the solver path.
    const contents =
      problemPath === 'Solution.lean' ? Buffer.alloc(0) : readBaselineFile(repositoryRoot, baselineCommit, file.path);
    filesByProblemPath.set(problemPath, Object.freeze({ tree: file, contents }));
    if (isSolverOwnedPath(problemPath)) {
      solverOwnedPaths.push(problemPath);
      continue;
    }
    if (problemPath === 'Solution.lean') {
      assertCurrentProtectedBlobMatches(repositoryRoot, file);
      continue;
    }
    assertCurrentTrustedFileMatches(repositoryRoot, file, contents);
    trackedFiles.push(Object.freeze({ path: file.path, sha256: sha256(contents) }));
  }
  for (const required of [...REQUIRED_TRUSTED_FILES, 'Submission.lean']) {
    if (!filesByProblemPath.has(required)) throw new Error(`LeanEval baseline is missing ${required}.`);
  }
  if (trackedFiles.length > MAX_TRACKED_FILES) {
    throw new Error(`LeanEval problem has more than ${MAX_TRACKED_FILES} trusted files.`);
  }
  const sortedTrackedFiles = trackedFiles.toSorted((left, right) => left.path.localeCompare(right.path));
  const sortedSolverOwnedPaths = solverOwnedPaths.toSorted();

  const challengeSource = filesByProblemPath.get('Challenge.lean')!.contents.toString('utf8').trim();
  const submissionTemplateSource = filesByProblemPath.get('Submission.lean')!.contents.toString('utf8');
  const { config, holeNames } = parseLeanEvalConfig(filesByProblemPath.get('config.json')!.contents);
  const holes = parseLeanEvalHoles(filesByProblemPath.get('holes.json')!.contents, problemId);
  validateLeanEvalHoleDeclarations(config, holes, challengeSource, submissionTemplateSource);
  // Fail closed before any comparator invocation when the solver namespace or
  // one configured declaration is absent from the baseline template.
  assertLeanEvalSubmissionComplete(holeNames, submissionTemplateSource);
  validateLakefile(filesByProblemPath.get('lakefile.toml')!.contents, problemId);
  requireText(filesByProblemPath.get('lean-toolchain')!.contents.toString('utf8'), 'lean-toolchain');

  const informalStatement = request.informalStatement?.trim() || title;
  const assumptions = Object.freeze([...(request.assumptions ?? [])]);
  const statementPayloads = canonicalMathProblemStatementPayloads({
    informalStatement,
    formalStatement: challengeSource,
    assumptions,
  });
  const statementHash = sha256(statementPayloads.informal);
  const leanStatementHash = sha256(statementPayloads.lean);
  const manifestPayload = {
    schema: 'deepscientist.mathematics.official-manifest.v1' as const,
    manifestId: `lean-eval:${problemId}:r${request.statementRevision}:${baselineCommit}`,
    problemId,
    informalStatement,
    formalStatement: challengeSource,
    assumptions,
    statementHash,
    leanStatementHash,
    officialVerificationCommand: LEAN_EVAL_OFFICIAL_COMMAND,
    repositoryUrl,
    baselineCommit,
    benchmarkAdapterId: LEAN_EVAL_ADAPTER_ID,
    benchmarkAdapterVersion: LEAN_EVAL_ADAPTER_VERSION,
    trackedFiles: Object.freeze(sortedTrackedFiles),
  };
  const manifestHash = sha256(canonicalMathOfficialManifestPayload(manifestPayload));
  const officialManifest = normalizeMathOfficialProblemManifest({ ...manifestPayload, manifestHash });
  const problemContract = normalizeMathProblemContract({
    problemId,
    informalStatement,
    formalStatement: challengeSource,
    assumptions,
    statementHash,
    leanStatementHash,
    knownTraps: [
      'Do not edit Challenge.lean, Solution.lean, config.json, lakefile.toml, or WorkspaceTest.lean.',
      'Solution.lean is protected evaluator material: do not read, search, quote, copy, or import it.',
      'LeanEval rejects sorry, admit, native_decide, and axioms outside its fixed foundational allowlist.',
      'A missing Mathlib theorem or high-level API is a solver-owned proof dependency, not an infrastructure blocker; implement the smallest required helper under Submission.lean or Submission/**/*.lean.',
      'Use targeted lake builds while constructing the proof. Reserve lake test and the official comparator for the final unchanged reviewed revision.',
    ],
    acceptanceCriteria: [
      `Define every configured hole in namespace Submission: ${holeNames.join(', ')}.`,
      'Keep solver source within Submission.lean and Submission/**/*.lean.',
      'Pass lake test, including comparator and independent nanoda replay.',
    ],
    officialVerificationCommand: LEAN_EVAL_OFFICIAL_COMMAND,
    officialManifestId: officialManifest.manifestId,
    officialManifestHash: officialManifest.manifestHash,
  });
  return Object.freeze({
    repositoryRoot,
    projectRoot,
    problemRelativePath,
    baselineCommit,
    holeNames,
    publicObligations: Object.freeze(holes.map(hole => Object.freeze({
      name: hole.name,
      kind: hole.kind,
      declarationHash: hashMathFormalSourceDeclaration(hole.body, hole.basename),
    }))),
    solverOwnedPaths: Object.freeze(sortedSolverOwnedPaths),
    officialManifestPath: LEAN_EVAL_MANIFEST_PATH,
    authorityPath: LEAN_EVAL_AUTHORITY_PATH,
    problemContract,
    officialManifest,
    officialManifestContent: `${JSON.stringify(officialManifest, null, 2)}\n`,
    authorityContent: manifestAuthorityContent(officialManifest),
  });
};

const ensureSafeBindingParent = (repositoryRoot: string, filePath: string): void => {
  const relativePath = path.relative(repositoryRoot, filePath);
  if (!relativePath || relativePath.startsWith('..') || path.isAbsolute(relativePath)) {
    throw new Error('LeanEval binding path must remain inside the repository.');
  }
  let current = repositoryRoot;
  for (const segment of path.dirname(relativePath).split(path.sep)) {
    current = path.join(current, segment);
    if (!fs.existsSync(current)) {
      fs.mkdirSync(current, { mode: 0o700 });
      continue;
    }
    const stat = fs.lstatSync(current);
    if (stat.isSymbolicLink() || !stat.isDirectory()) {
      throw new Error(`LeanEval binding parent must be a regular non-symlink directory: ${current}`);
    }
  }
};

const writeNewOrMatchingFile = (repositoryRoot: string, filePath: string, contents: string): void => {
  ensureSafeBindingParent(repositoryRoot, filePath);
  if (fs.existsSync(filePath)) {
    const stat = fs.lstatSync(filePath);
    if (stat.isSymbolicLink() || !stat.isFile() || fs.readFileSync(filePath, 'utf8') !== contents) {
      throw new Error(`LeanEval binding already exists with different contents: ${filePath}`);
    }
    return;
  }
  fs.writeFileSync(filePath, contents, { encoding: 'utf8', flag: 'wx', mode: 0o600 });
};

export const materializeLeanEvalProblemBinding = (
  binding: LeanEvalProblemBinding
): Readonly<{ officialManifestPath: string; authorityPath: string }> => {
  const officialManifestPath = path.join(binding.repositoryRoot, binding.officialManifestPath);
  const authorityPath = path.join(binding.repositoryRoot, binding.authorityPath);
  writeNewOrMatchingFile(binding.repositoryRoot, officialManifestPath, binding.officialManifestContent);
  writeNewOrMatchingFile(binding.repositoryRoot, authorityPath, binding.authorityContent);
  return Object.freeze({ officialManifestPath, authorityPath });
};

export const collectLeanEvalSubmissionFiles = (
  projectRootInput: string,
  expectedHoleNames?: readonly string[]
): readonly string[] => {
  const projectRoot = fs.realpathSync(path.resolve(projectRootInput));
  const collected: string[] = [];
  const inspect = (relativePath: string): void => {
    const absolutePath = path.join(projectRoot, relativePath);
    const stat = fs.lstatSync(absolutePath);
    if (stat.isSymbolicLink()) throw new Error(`LeanEval solver file must not be a symlink: ${relativePath}`);
    if (stat.isDirectory()) {
      for (const entry of fs.readdirSync(absolutePath).toSorted()) inspect(`${relativePath}/${entry}`);
      return;
    }
    if (!stat.isFile() || !isSolverOwnedPath(relativePath)) {
      throw new Error(`LeanEval solver output is outside the allowed Lean source paths: ${relativePath}`);
    }
    if (stat.size > MAX_TRACKED_FILE_BYTES) throw new Error(`LeanEval solver file is too large: ${relativePath}`);
    collected.push(relativePath);
  };
  inspect('Submission.lean');
  const submissionDirectory = path.join(projectRoot, 'Submission');
  if (fs.existsSync(submissionDirectory)) inspect('Submission');
  if (expectedHoleNames?.length) {
    const source = collected
      .map((relativePath) => fs.readFileSync(path.join(projectRoot, relativePath), 'utf8'))
      .join('\n');
    assertLeanEvalSubmissionComplete(expectedHoleNames, source);
  }
  return Object.freeze(collected.toSorted());
};
