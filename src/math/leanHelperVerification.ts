/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

import crypto from 'node:crypto';
import fs from 'node:fs';
import path from 'node:path';
import { isAllowedMathProofSource } from "./mathProofSourcePolicy";
import { assertMathConstructionSources } from "./mathConstructionSources";
import {
  normalizeMathHelperReceipt,
  type MathHelperReceipt,
  type MathSourceProvenance,
} from "../common/types/team/mathematicsTeam";
import {
  hashMathFormalSourceDeclaration,
  inspectLeanDeclarations,
  runFormalVerification,
  type MathematicsVerifierResult,
} from "./verifier";

export type MathematicsHelperVerificationRequest = Readonly<{
  projectRoot: string;
  proofPath: string;
  theoremName: string;
  declarationKind: 'theorem' | 'definition';
  helperPlanNodeId: string;
  parentPlanNodeId: string;
  statementHash: string;
  routeFingerprint: string;
  targetCommit: string;
  importModules: readonly string[];
  sourceProvenance: readonly MathSourceProvenance[];
  timeoutMs?: number;
  expectedDeclarationType?: string;
  forbiddenImportModules?: readonly string[];
}>;

export type MathematicsHelperVerificationResult = Readonly<{
  status: MathematicsVerifierResult['status'];
  verifierResult: MathematicsVerifierResult;
  receipt?: MathHelperReceipt;
  error?: string;
}>;

const normalizeProofPath = (value: string): string => {
  const normalized = value.trim().replaceAll('\\', '/').replace(/^\.\//u, '');
  if (
    !normalized ||
    normalized.startsWith('/') ||
    normalized.split('/').includes('..') ||
    !isAllowedMathProofSource(normalized)
  ) {
    throw new Error('Mathematics helper proofPath must be a project-relative Lean path');
  }
  return normalized;
};

const declarationFor = (
  source: string,
  theoremName: string,
  declarationKind: MathematicsHelperVerificationRequest['declarationKind']
): string => {
  const localName = theoremName.split('.').at(-1) || theoremName;
  const declarations = inspectLeanDeclarations(source).filter(
    (candidate) => candidate.name === theoremName || candidate.name.split('.').at(-1) === localName
  );
  if (declarations.length > 1) {
    throw new Error(`Helper declaration is ambiguous in ${theoremName}`);
  }
  const declaration = declarations[0];
  if (!declaration) throw new Error(`Helper declaration was not found in ${theoremName}`);
  const expectedKind = declarationKind === 'theorem' ? 'theorem' : 'definition';
  if (declaration.kind !== expectedKind) {
    throw new Error(`Helper declaration kind does not match ${theoremName}: expected ${declarationKind}`);
  }
  return declaration.declarationType;
};

/** Verify a committed helper and translate the verifier result into a node receipt. */
export async function verifyMathematicsHelperNode(
  request: MathematicsHelperVerificationRequest
): Promise<MathematicsHelperVerificationResult> {
  const proofPath = normalizeProofPath(request.proofPath);
  const verifierResult = await runFormalVerification(
    {
      projectRoot: request.projectRoot,
      proofPath,
      theoremName: request.theoremName,
      statementHash: request.statementHash,
      targetCommit: request.targetCommit,
      timeoutMs: request.timeoutMs,
    },
    {
      prepareLocalDependencies: true,
      ...(request.expectedDeclarationType ? { expectedDeclarationType: request.expectedDeclarationType } : {}),
      ...(request.forbiddenImportModules ? { forbiddenImportModules: request.forbiddenImportModules } : {}),
    }
  );
  if (verifierResult.status !== 'kernel_verified') {
    return Object.freeze({
      status: verifierResult.status,
      verifierResult,
      ...(verifierResult.error ? { error: verifierResult.error } : {}),
    });
  }
  const absolutePath = path.resolve(request.projectRoot, proofPath);
  let source: string;
  try {
    assertMathConstructionSources(request.projectRoot, [proofPath]);
    source = fs.readFileSync(absolutePath, 'utf8');
  } catch (error) {
    return Object.freeze({
      status: 'failed',
      verifierResult,
      error: `Mathematics helper source could not be read: ${error instanceof Error ? error.message : String(error)}`,
    });
  }
  if (
    !verifierResult.theoremDeclarationHash ||
    verifierResult.goalsRemaining !== 0 ||
    verifierResult.sorryCount !== 0 ||
    verifierResult.admitCount !== 0
  ) {
    return Object.freeze({
      status: 'failed',
      verifierResult,
      error: 'Mathematics helper verifier did not return a complete theorem declaration',
    });
  }
  let declarationType: string;
  try {
    declarationType = declarationFor(source, request.theoremName, request.declarationKind);
  } catch (error) {
    return Object.freeze({
      status: 'failed',
      verifierResult,
      error: error instanceof Error ? error.message : String(error),
    });
  }
  const expectedSourceDeclarationHash = hashMathFormalSourceDeclaration(source, request.theoremName);
  const expectedProofHash = crypto.createHash('sha256').update(source, 'utf8').digest('hex');
  if (
    !expectedSourceDeclarationHash ||
    !verifierResult.sourceDeclarationHash ||
    verifierResult.sourceDeclarationHash !== expectedSourceDeclarationHash
  ) {
    return Object.freeze({
      status: 'failed',
      verifierResult,
      error: 'Mathematics helper source declaration does not match the kernel-verified declaration',
    });
  }
  if (verifierResult.proofHash !== expectedProofHash || verifierResult.proofPath !== proofPath) {
    return Object.freeze({
      status: 'failed',
      verifierResult,
      error: 'Mathematics helper source does not match the kernel-verified proof artifact',
    });
  }
  const receipt = normalizeMathHelperReceipt({
    receiptId: verifierResult.receiptId,
    targetCommit: verifierResult.targetCommit,
    statementHash: verifierResult.statementHash,
    routeFingerprint: request.routeFingerprint,
    helperPlanNodeId: request.helperPlanNodeId,
    parentPlanNodeId: request.parentPlanNodeId,
    status: 'kernel_verified',
    verifier: 'lean-kernel',
    declarationKind: request.declarationKind,
    declarationName: request.theoremName,
    declarationType,
    proofHash: verifierResult.proofHash,
    declarationHash: verifierResult.theoremDeclarationHash,
    ...(verifierResult.sourceDeclarationHash ? { sourceDeclarationHash: verifierResult.sourceDeclarationHash } : {}),
    sourceFile: proofPath,
    importModules: request.importModules,
    sourceProvenance: request.sourceProvenance,
    goalsRemaining: 0 as const,
    sorryCount: 0 as const,
    admitCount: 0 as const,
    axioms: verifierResult.axioms,
    checkedAt: verifierResult.checkedAt,
  });
  return Object.freeze({ status: 'kernel_verified', verifierResult, receipt });
}
