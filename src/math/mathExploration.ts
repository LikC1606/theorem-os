import { z } from 'zod';
import { isAllowedMathProofSource } from "./mathProofSourcePolicy";
import { verifyMathematicsHelperNode } from "./leanHelperVerification";
import { mathDigest, canonicalMathJson } from "./mathRuntimeIo";
import { runFormalVerification, hashMathFormalSourceDeclaration } from "./verifier";

const modulePath = z
  .string()
  .regex(/^[A-Za-z_][A-Za-z0-9_']*(?:\/[A-Za-z_][A-Za-z0-9_']*)*\.lean$/u)
  .refine(isAllowedMathProofSource, 'Construction reference sources are excluded');
const declaration = z
  .object({ sourceFile: modulePath, theoremName: z.string().regex(/^[A-Za-z_][A-Za-z0-9_'.]*$/u) })
  .strict();
export const mathExplorationInput = z
  .object({
    parentStatementHash: z.string().regex(/^[a-f0-9]{64}$/u),
    targetCommit: z.string().regex(/^[a-f0-9]{40}(?:[a-f0-9]{24})?$/u),
    routeFingerprint: z.string().min(1).max(160),
    candidateId: z.string().min(1).max(160),
    version: z.number().int().positive(),
    candidateType: z.string().min(1).max(6000),
    parentType: z.string().min(1).max(6000),
    candidate: declaration,
    connection: declaration,
    integration: declaration.optional(),
  })
  .strict();
export type MathExplorationInput = z.infer<typeof mathExplorationInput>;

/** Candidate and conditional connection are independently checked, even if either side is unfinished. */
export async function verifyMathExploration(
  projectRoot: string,
  raw: MathExplorationInput,
  options: {
    parentBinding?: Readonly<{ statementHash: string; leanStatementHash: string; formalStatement: string }>;
  } = {}
) {
  const input = mathExplorationInput.parse(raw);
  if (options.parentBinding && options.parentBinding.statementHash !== input.parentStatementHash)
    throw new Error('Exploration parent does not match the immutable problem statement.');
  if (input.candidate.sourceFile === input.connection.sourceFile)
    throw new Error('Candidate and connection require independent source modules.');
  const asModule = (file: string) => file.slice(0, -5).replaceAll('/', '.');
  const candidateIdentity = mathDigest(
    canonicalMathJson({
      candidateId: input.candidateId,
      version: input.version,
      type: input.candidateType,
      parent: input.parentStatementHash,
    })
  );
  const verify = (side: 'candidate' | 'connection') =>
    verifyMathematicsHelperNode({
      projectRoot,
      proofPath: input[side].sourceFile,
      theoremName: input[side].theoremName,
      declarationKind: 'theorem',
      helperPlanNodeId: side,
      parentPlanNodeId: 'parent',
      statementHash: input.parentStatementHash,
      routeFingerprint: input.routeFingerprint,
      targetCommit: input.targetCommit,
      importModules: [asModule(input[side].sourceFile)],
      sourceProvenance: [
        {
          kind: 'local',
          locator: input[side].sourceFile,
          compatibility: 'exact',
          commit: input.targetCommit,
          evidenceRef: candidateIdentity,
        },
      ],
      expectedDeclarationType:
        side === 'candidate' ? input.candidateType : `(${input.candidateType}) -> (${input.parentType})`,
      forbiddenImportModules: [asModule(input[side === 'candidate' ? 'connection' : 'candidate'].sourceFile)],
    });
  const candidate = await verify('candidate');
  const connection = await verify('connection');
  const expectedSourceDeclarationHash =
    options.parentBinding && input.integration
      ? hashMathFormalSourceDeclaration(options.parentBinding.formalStatement, input.integration.theoremName)
      : undefined;
  if (options.parentBinding && input.integration && !expectedSourceDeclarationHash)
    throw new Error('The parent adapter cannot bind this integration declaration to the immutable formal statement.');
  const integration = input.integration
    ? await runFormalVerification(
        {
          projectRoot,
          proofPath: input.integration.sourceFile,
          theoremName: input.integration.theoremName,
          statementHash: input.parentStatementHash,
          ...(options.parentBinding ? { leanStatementHash: options.parentBinding.leanStatementHash } : {}),
          ...(expectedSourceDeclarationHash ? { expectedSourceDeclarationHash } : {}),
          targetCommit: input.targetCommit,
        },
        {
          prepareLocalDependencies: true,
          expectedDeclarationType: input.parentType,
          dependencyCandidates: [input.candidate.theoremName, input.connection.theoremName],
        }
      )
    : undefined;
  const usedCandidate = integration?.usedDeclarationDependencies?.includes(input.candidate.theoremName);
  const parentKernelVerified = integration?.status === 'kernel_verified';
  const integrated = parentKernelVerified && usedCandidate && Boolean(candidate.receipt && connection.receipt);
  return Object.freeze({
    candidateIdentity,
    candidateStatus: candidate.receipt ? ('verified' as const) : ('unfinished' as const),
    connectionStatus: integrated
      ? ('integrated' as const)
      : connection.receipt
        ? ('conditional' as const)
        : ('unfinished' as const),
    candidate,
    connection,
    ...(integration ? { integration } : {}),
    parentKernelVerified,
    parentIdentity: options.parentBinding ? ('runtime-bound' as const) : ('caller-supplied' as const),
    attribution: !parentKernelVerified
      ? ('unfinished' as const)
      : usedCandidate
        ? integrated
          ? ('candidate_used' as const)
          : ('unresolved' as const)
        : ('direct_success' as const),
    parentComplete: false as const,
    integrationRequired: !parentKernelVerified,
    // A conditional receipt is explicitly scoped to L -> G, never to G.
    conditionalType: `(${input.candidateType}) -> (${input.parentType})`,
  });
}
