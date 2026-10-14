/**
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

/**
 * Immutable identity and acceptance contract for one mathematical problem.
 *
 * The natural-language and Lean statements are deliberately carried together:
 * a proof is never allowed to silently drift to a nearby formalization.
 */
export type MathProblemContract = Readonly<{
  problemId: string;
  informalStatement: string;
  formalStatement: string;
  /** Canonical Lean declaration for the negation, required before a formal refutation can be terminal. */
  formalNegationStatement?: string;
  assumptions: readonly string[];
  statementHash: string;
  leanStatementHash: string;
  leanNegationHash?: string;
  knownTraps: readonly string[];
  acceptanceCriteria: readonly string[];
  officialVerificationCommand: string;
  /** Optional identity of the committed official problem manifest. */
  officialManifestId?: string;
  officialManifestHash?: string;
}>;

/**
 * Problem identity published by an official benchmark repository.  The
 * verifier reads this file from the exact target commit before running the
 * comparator; worker-supplied prose is never treated as the authority.
 */
export type MathOfficialProblemManifest = Readonly<{
  schema: 'deepscientist.mathematics.official-manifest.v1';
  manifestId: string;
  manifestHash: string;
  problemId: string;
  informalStatement: string;
  formalStatement: string;
  formalNegationStatement?: string;
  assumptions: readonly string[];
  statementHash: string;
  leanStatementHash: string;
  leanNegationHash?: string;
  officialVerificationCommand: string;
  repositoryUrl: string;
  baselineCommit: string;
  benchmarkAdapterId: string;
  benchmarkAdapterVersion: string;
  trackedFiles: readonly Readonly<{ path: string; sha256: string }>[];
  targetCommit?: string;
}>;

function normalizeStatementIdentity(input: MathProblemContract | MathOfficialProblemManifest, field: string) {
  const problemId = requiredText(input.problemId, `${field}.problemId`);
  const informalStatement = requiredText(input.informalStatement, `${field}.informalStatement`);
  const formalStatement = requiredText(input.formalStatement, `${field}.formalStatement`);
  const formalNegationStatement = optionalText(input.formalNegationStatement);
  const assumptions = textList(input.assumptions, `${field}.assumptions`);
  const statementHash = requiredHash(input.statementHash, `${field}.statementHash`);
  const leanStatementHash = requiredHash(input.leanStatementHash, `${field}.leanStatementHash`);
  const leanNegationHash = optionalText(input.leanNegationHash);
  if (Boolean(formalNegationStatement) !== Boolean(leanNegationHash)) {
    throw new TypeError(`${field === 'officialManifest' ? field : `Mathematics ${field}`} formal negation statement and hash must be supplied together`);
  }
  return { problemId, informalStatement, formalStatement,
    ...(formalNegationStatement ? { formalNegationStatement } : {}), assumptions, statementHash, leanStatementHash,
    ...(leanNegationHash ? { leanNegationHash: requiredHash(leanNegationHash, `${field}.leanNegationHash`) } : {}) };
}

export function normalizeMathOfficialProblemManifest(input: MathOfficialProblemManifest): MathOfficialProblemManifest {
  const manifestId = requiredText(input.manifestId, 'officialManifest.manifestId');
  const manifestHash = requiredHash(input.manifestHash, 'officialManifest.manifestHash');
  const identity = normalizeStatementIdentity(input, 'officialManifest');
  const officialVerificationCommand = requiredText(
    input.officialVerificationCommand,
    'officialManifest.officialVerificationCommand'
  );
  const repositoryUrl = requiredText(input.repositoryUrl, 'officialManifest.repositoryUrl');
  if (!/^(?:https:\/\/[^\s]+|ssh:\/\/[^\s]+|git@[^\s:]+:[^\s]+)$/u.test(repositoryUrl)) {
    throw new TypeError('officialManifest.repositoryUrl must be an HTTPS or SSH repository URL');
  }
  const baselineCommit = input.baselineCommit?.trim().toLowerCase();
  if (!baselineCommit || !/^(?:[0-9a-f]{40}|[0-9a-f]{64})$/u.test(baselineCommit)) {
    throw new TypeError('officialManifest.baselineCommit must be a full Git object id');
  }
  const benchmarkAdapterId = requiredText(input.benchmarkAdapterId, 'officialManifest.benchmarkAdapterId');
  const benchmarkAdapterVersion = requiredText(
    input.benchmarkAdapterVersion,
    'officialManifest.benchmarkAdapterVersion'
  );
  if (!Array.isArray(input.trackedFiles) || input.trackedFiles.length < 1 || input.trackedFiles.length > 1024) {
    throw new TypeError('officialManifest.trackedFiles must contain 1-1024 official file hashes');
  }
  const trackedFilePathSet = new Set<string>();
  const trackedFiles = Object.freeze(
    input.trackedFiles.map((file, index) => {
      const filePath = requiredText(file.path, `officialManifest.trackedFiles[${index}].path`)
        .replaceAll('\\', '/')
        .replace(/^\.\//u, '');
      if (filePath.startsWith('/') || filePath.split('/').includes('..') || filePath.includes('\0')) {
        throw new TypeError(`officialManifest.trackedFiles[${index}].path must be repository-relative`);
      }
      trackedFilePathSet.add(filePath);
      return Object.freeze({
        path: filePath,
        sha256: requiredHash(file.sha256, `officialManifest.trackedFiles[${index}].sha256`),
      });
    })
  );
  if (trackedFilePathSet.size !== trackedFiles.length) {
    throw new TypeError('officialManifest.trackedFiles paths must be unique');
  }
  const targetCommit = input.targetCommit?.trim();
  if (targetCommit && !/^(?:[0-9a-f]{40}|[0-9a-f]{64})$/u.test(targetCommit)) {
    throw new TypeError('officialManifest.targetCommit must be a full Git object id');
  }
  return Object.freeze({
    schema: 'deepscientist.mathematics.official-manifest.v1',
    manifestId,
    manifestHash,
    ...identity,
    officialVerificationCommand,
    repositoryUrl,
    baselineCommit,
    benchmarkAdapterId,
    benchmarkAdapterVersion,
    trackedFiles,
    ...(targetCommit ? { targetCommit } : {}),
  });
}

export function assertMathProblemContractMatchesOfficialManifest(
  contract: MathProblemContract,
  manifest: MathOfficialProblemManifest
): void {
  const normalizedContract = normalizeMathProblemContract(contract);
  const normalizedManifest = normalizeMathOfficialProblemManifest(manifest);
  if (
    normalizedContract.problemId !== normalizedManifest.problemId ||
    normalizedContract.statementHash !== normalizedManifest.statementHash ||
    normalizedContract.leanStatementHash !== normalizedManifest.leanStatementHash ||
    normalizedContract.informalStatement !== normalizedManifest.informalStatement ||
    normalizedContract.formalStatement !== normalizedManifest.formalStatement ||
    normalizedContract.formalNegationStatement !== normalizedManifest.formalNegationStatement ||
    normalizedContract.leanNegationHash !== normalizedManifest.leanNegationHash ||
    JSON.stringify(normalizedContract.assumptions) !== JSON.stringify(normalizedManifest.assumptions) ||
    normalizedContract.officialVerificationCommand !== normalizedManifest.officialVerificationCommand
  ) {
    throw new TypeError('Mathematics problem contract does not match the official problem manifest');
  }
  if (
    normalizedContract.officialManifestId &&
    normalizedContract.officialManifestId !== normalizedManifest.manifestId
  ) {
    throw new TypeError('Mathematics problem contract officialManifestId does not match the official manifest');
  }
  if (
    normalizedContract.officialManifestHash &&
    normalizedContract.officialManifestHash !== normalizedManifest.manifestHash
  ) {
    throw new TypeError('Mathematics problem contract officialManifestHash does not match the official manifest');
  }
}

/** Canonical bytes hashed by trusted process boundaries for statement identity. */
export function canonicalMathProblemStatementPayloads(
  input: Pick<MathProblemContract, 'informalStatement' | 'formalStatement' | 'assumptions'>
): Readonly<{ informal: string; lean: string }> {
  const assumptions = textList(input.assumptions, 'problemContract.assumptions');
  return Object.freeze({
    informal: JSON.stringify({
      schema: 'deepscientist.mathematics.informal-statement.v1',
      statement: requiredText(input.informalStatement, 'problemContract.informalStatement'),
      assumptions,
    }),
    lean: JSON.stringify({
      schema: 'deepscientist.mathematics.lean-statement.v1',
      statement: requiredText(input.formalStatement, 'problemContract.formalStatement'),
      assumptions,
    }),
  });
}

export function canonicalMathProblemNegationPayload(
  input: Pick<MathProblemContract, 'formalNegationStatement' | 'assumptions'>
): string | undefined {
  const formalNegationStatement = optionalText(input.formalNegationStatement);
  if (!formalNegationStatement) return undefined;
  return JSON.stringify({
    schema: 'deepscientist.mathematics.lean-negation.v1',
    statement: formalNegationStatement,
    assumptions: textList(input.assumptions, 'problemContract.assumptions'),
  });
}

export const MATH_FOUNDATIONAL_LEAN_AXIOMS = Object.freeze([
  'Classical.choice',
  'Quot.sound',
  'choice',
  'propext',
] as const);

const MATH_FOUNDATIONAL_LEAN_AXIOM_SET = new Set<string>(MATH_FOUNDATIONAL_LEAN_AXIOMS);

export const isMathFoundationalLeanAxiom = (value: string): boolean =>
  MATH_FOUNDATIONAL_LEAN_AXIOM_SET.has(value.trim());

export type MathReceiptAttestation = Readonly<{
  algorithm: 'hmac-sha256';
  keyId: string;
  value: string;
}>;

/** Official-command receipt produced by OFFICIAL_GATE for the unchanged frozen candidate. */
export type MathOfficialGateReceipt = Readonly<{
  receiptId: string;
  targetCommit: string;
  statementHash: string;
  /** Omitted only by legacy receipts, where `statement` is implied. */
  claim?: 'statement' | 'negation';
  routeFingerprint?: string;
  localGateReceiptId: string;
  theoremName: string;
  proofHash: string;
  theoremDeclarationHash: string;
  /** Runtime-derived source theorem header identity mirrored from LOCAL_GATE. */
  sourceDeclarationHash?: string;
  status: 'official_verified';
  verifier: 'official-comparator';
  command: string;
  exitCode: 0;
  timedOut: false;
  stdoutSha256: string;
  stderrSha256: string;
  durationMs: number;
  checkedAt: number;
  /** Identity of the committed official manifest used by the comparator. */
  problemId?: string;
  officialManifestPath?: string;
  officialManifestId?: string;
  officialManifestHash?: string;
  leanStatementHash?: string;
  officialRepositoryUrl: string;
  officialBaselineCommit: string;
  benchmarkAdapterId: string;
  benchmarkAdapterVersion: string;
  attestation: MathReceiptAttestation;
}>;

export function normalizeMathProblemContract(input: MathProblemContract): MathProblemContract {
  const identity = normalizeStatementIdentity(input, 'problemContract');
  const knownTraps = textList(input.knownTraps, 'problemContract.knownTraps');
  const acceptanceCriteria = requiredTextList(input.acceptanceCriteria, 'problemContract.acceptanceCriteria');
  const officialManifestId = input.officialManifestId?.trim();
  const officialManifestHash = input.officialManifestHash?.trim();
  if (Boolean(officialManifestId) !== Boolean(officialManifestHash)) {
    throw new TypeError('Mathematics problemContract official manifest id and hash must be supplied together');
  }
  return Object.freeze({
    ...identity,
    knownTraps,
    acceptanceCriteria,
    officialVerificationCommand: requiredText(
      input.officialVerificationCommand,
      'problemContract.officialVerificationCommand'
    ),
    ...(officialManifestId ? { officialManifestId } : {}),
    ...(officialManifestHash
      ? { officialManifestHash: requiredHash(officialManifestHash, 'problemContract.officialManifestHash') }
      : {}),
  });
}

export function normalizeMathOfficialGateReceipt(input: MathOfficialGateReceipt): MathOfficialGateReceipt {
  if (input.status !== 'official_verified' || input.verifier !== 'official-comparator') {
    throw new TypeError('Mathematics official gate receipt must be verified by the official comparator');
  }
  if (input.exitCode !== 0 || input.timedOut !== false) {
    throw new TypeError('Mathematics official gate receipt requires exitCode=0 and timedOut=false');
  }
  if (!Number.isFinite(input.durationMs) || input.durationMs < 0) {
    throw new TypeError('Mathematics official gate receipt durationMs must be nonnegative');
  }
  if (!Number.isFinite(input.checkedAt) || input.checkedAt <= 0) {
    throw new TypeError('Mathematics official gate receipt checkedAt must be a positive timestamp');
  }
  const problemId = optionalText(input.problemId);
  const officialManifestPath = optionalText(input.officialManifestPath);
  const officialManifestId = optionalText(input.officialManifestId);
  const officialManifestHash = optionalText(input.officialManifestHash);
  const leanStatementHash = optionalText(input.leanStatementHash);
  return Object.freeze({
    receiptId: requiredText(input.receiptId, 'officialGateReceipt.receiptId'),
    targetCommit: requiredGitOid(input.targetCommit, 'officialGateReceipt.targetCommit'),
    statementHash: requiredHash(input.statementHash, 'officialGateReceipt.statementHash'),
    ...(input.claim ? { claim: input.claim === 'negation' ? 'negation' : 'statement' } : {}),
    ...(input.routeFingerprint ? { routeFingerprint: normalizeMathRouteFingerprint(input.routeFingerprint) } : {}),
    localGateReceiptId: requiredText(input.localGateReceiptId, 'officialGateReceipt.localGateReceiptId'),
    theoremName: requiredText(input.theoremName, 'officialGateReceipt.theoremName'),
    proofHash: requiredHash(input.proofHash, 'officialGateReceipt.proofHash'),
    theoremDeclarationHash: requiredHash(input.theoremDeclarationHash, 'officialGateReceipt.theoremDeclarationHash'),
    ...(optionalText(input.sourceDeclarationHash)
      ? {
          sourceDeclarationHash: requiredHash(input.sourceDeclarationHash, 'officialGateReceipt.sourceDeclarationHash'),
        }
      : {}),
    status: 'official_verified',
    verifier: 'official-comparator',
    command: requiredText(input.command, 'officialGateReceipt.command'),
    exitCode: 0,
    timedOut: false,
    stdoutSha256: requiredHash(input.stdoutSha256, 'officialGateReceipt.stdoutSha256'),
    stderrSha256: requiredHash(input.stderrSha256, 'officialGateReceipt.stderrSha256'),
    durationMs: input.durationMs,
    checkedAt: input.checkedAt,
    ...(problemId ? { problemId } : {}),
    ...(officialManifestPath ? { officialManifestPath } : {}),
    ...(officialManifestId ? { officialManifestId } : {}),
    ...(officialManifestHash
      ? { officialManifestHash: requiredHash(officialManifestHash, 'officialGateReceipt.officialManifestHash') }
      : {}),
    ...(leanStatementHash
      ? { leanStatementHash: requiredHash(leanStatementHash, 'officialGateReceipt.leanStatementHash') }
      : {}),
    officialRepositoryUrl: requiredText(input.officialRepositoryUrl, 'officialGateReceipt.officialRepositoryUrl'),
    officialBaselineCommit: requiredGitOid(input.officialBaselineCommit, 'officialGateReceipt.officialBaselineCommit'),
    benchmarkAdapterId: requiredText(input.benchmarkAdapterId, 'officialGateReceipt.benchmarkAdapterId'),
    benchmarkAdapterVersion: requiredText(input.benchmarkAdapterVersion, 'officialGateReceipt.benchmarkAdapterVersion'),
    attestation: normalizeMathReceiptAttestation(input.attestation, 'officialGateReceipt.attestation'),
  });
}

export function normalizeMathRouteFingerprint(value: string): string {
  const normalized = requiredText(value, 'routeFingerprint').toLowerCase().replace(/\s+/gu, ' ');
  if (normalized.length > 512) throw new TypeError('Mathematics routeFingerprint is too long');
  return normalized;
}

function requiredHash(value: unknown, field: string): string {
  const normalized = requiredText(value, field).toLowerCase();
  if (!/^[0-9a-f]{64}$/u.test(normalized)) throw new TypeError(`Mathematics ${field} must be SHA-256`);
  return normalized;
}

function normalizeMathReceiptAttestation(value: MathReceiptAttestation, field: string): MathReceiptAttestation {
  if (!value || value.algorithm !== 'hmac-sha256') {
    throw new TypeError(`Mathematics ${field} must use hmac-sha256`);
  }
  const keyId = requiredText(value.keyId, `${field}.keyId`).toLowerCase();
  if (!/^[0-9a-f]{16}$/u.test(keyId)) {
    throw new TypeError(`Mathematics ${field}.keyId must be a 16-character hexadecimal key id`);
  }
  return Object.freeze({
    algorithm: 'hmac-sha256',
    keyId,
    value: requiredHash(value.value, `${field}.value`),
  });
}

function requiredText(value: unknown, field: string): string {
  if (typeof value !== 'string') throw new TypeError(`Mathematics ${field} is required`);
  const normalized = value.trim();
  if (!normalized) throw new TypeError(`Mathematics ${field} is required`);
  return normalized;
}

function textList(values: readonly string[], field: string): readonly string[] {
  if (!Array.isArray(values)) throw new TypeError(`Mathematics ${field} must be an array`);
  const normalized: string[] = [];
  const seen = new Set<string>();
  for (let index = 0; index < values.length; index += 1) {
    const value = requiredText(values[index], `${field}[${index}]`);
    normalized.push(value);
    seen.add(value);
  }
  if (seen.size !== normalized.length) throw new TypeError(`Mathematics ${field} must be unique`);
  return Object.freeze(normalized);
}

function requiredTextList(values: readonly string[], field: string): readonly string[] {
  const normalized = textList(values, field);
  if (!normalized.length) throw new TypeError(`Mathematics ${field} must not be empty`);
  return normalized;
}

function optionalText(value: unknown): string | undefined {
  if (typeof value !== 'string') return undefined;
  return value.trim() || undefined;
}

function requiredGitOid(value: unknown, field: string): string {
  const normalized = requiredText(value, field).toLowerCase();
  if (!/^(?:[0-9a-f]{40}|[0-9a-f]{64})$/u.test(normalized)) {
    throw new TypeError(`Mathematics ${field} must be a full Git object id`);
  }
  return normalized;
}
