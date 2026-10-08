import { z } from 'zod';
import { MATHEMATICS_PORTFOLIO_SCHEMA } from "../common/chat/mathematics";
import { MATH_RESEARCH_PROBE_KINDS } from "../common/types/team/mathematicsTeam";

// Mutation-only schemas. Lite read/bootstrap tools never load this module.
const mathematicsToolchainInput = z
  .object({
    lean: z.string(),
    mathlib: z.string().optional(),
    lake: z.string().optional(),
    lockfilePath: z.string().optional(),
    lockfileHash: z.string().optional(),
  })
  .passthrough();

const mathematicsFeasibilityInput = z
  .object({
    candidateId: z.string().trim().min(1).max(256).optional(),
    acceptedCreditCount: z.number().int().min(0),
    holeCount: z.number().int().min(0),
    importCoverage: z.number().finite().min(0).max(1),
    literatureAvailability: z.number().finite().min(0).max(1),
    relatedFormalizationAvailability: z.number().finite().min(0).max(1),
    definitionSurface: z.number().finite().min(0).max(1),
    missingFoundationDepth: z.number().finite().min(0).max(1),
    formalDegeneracyPotential: z.number().finite().min(0).max(1),
    firstMilestoneCost: z.number().finite().min(0).max(1),
    toolchainCompatibility: z.number().finite().min(0).max(1),
    benchmarkCommit: z.string().trim().min(40).max(64).optional(),
    statementRevision: z.number().int().min(0).optional(),
    active: z.boolean().optional(),
    visible: z.boolean().optional(),
    inV1: z.boolean().optional(),
    evidenceSource: z.string().trim().min(1).max(256).optional(),
    evidenceFreshAt: z.number().int().min(0).optional(),
  })
  .strict();

const mathematicsSourceProvenanceInput = z
  .object({
    kind: z.enum(['paper', 'mathlib', 'lean_package', 'local']),
    locator: z.string(),
    compatibility: z.enum(['exact', 'portable', 'conceptual', 'rejected']),
    commit: z.string().optional(),
    license: z.string().optional(),
    evidenceRef: z.string(),
  })
  .passthrough();

const mathematicsResearchContractInput = z
  .object({
    problemId: z.string(),
    objective: z.string(),
    context: z.string().optional(),
    knownResults: z.array(z.string()).optional(),
    establishedClaims: z.array(z.string()).optional(),
    conjectures: z.array(z.string()).optional(),
    failedApproaches: z.array(z.string()).optional(),
    openObligations: z.array(z.string()).optional(),
    evidenceNotes: z.array(z.string()).max(8).optional(),
    insights: z.array(z.record(z.string(), z.unknown())).max(8).optional(),
    probeSummary: z.array(z.record(z.string(), z.unknown())).max(MATH_RESEARCH_PROBE_KINDS.length).optional(),
    bottleneckDiagnosis: z.string().max(800).optional(),
    consumedEvidenceKeys: z.array(z.string()).optional(),
    activeBottleneck: z.string().optional(),
    solutionSketchRef: z.string().optional(),
    nextAction: z.string().optional(),
  })
  .passthrough();

const mathematicsPlanNodeInput = z
  .object({
    id: z.string(),
    informalClaim: z.string(),
    provisionalLeanStatement: z.string(),
    dependsOn: z.array(z.string()),
    role: z.enum(['goal', 'reduction', 'auxiliary', 'case_split', 'bridge']),
    status: z.enum([
      'proposed',
      'sourced',
      'counterexample_checked',
      'typed',
      'compiling',
      'compiled',
      'kernel_verified',
      'refuted',
    ]),
    evidenceRefs: z.array(z.string()),
    parentNodeId: z.string().optional(),
    kind: z.enum(['theorem', 'definition', 'api_bridge', 'ported_helper']).optional(),
    estimatedEffort: z.number().finite().min(1).max(5).optional(),
    successProbability: z.number().finite().min(0).max(1).optional(),
    downstreamValue: z.number().finite().min(1).max(5).optional(),
    sourceProvenance: z.array(mathematicsSourceProvenanceInput).max(8).optional(),
  })
  .passthrough();

const mathematicsRouteCardInput = z
  .object({
    statementHash: z.string(),
    routeFingerprint: z.string(),
    proposerSessionId: z.string(),
    approach: z.string(),
    structuralCommitment: z.string(),
    decisiveLemma: z.string(),
    decisiveTest: z.string(),
    falsificationSignal: z.string(),
    dependencies: z.array(z.string()),
    premiseBundle: z
      .object({
        strategySketch: z.string(),
        leanSkeleton: z.string(),
        premises: z.array(
          z
            .object({
              declarationName: z.string(),
              declarationType: z.string(),
              sourceKind: z.enum(['library', 'verified_local']),
              sourceModule: z.string().optional(),
              sourceCommit: z.string().optional(),
              sourceFile: z.string().optional(),
              proofHash: z.string().optional(),
              importModules: z.array(z.string()).optional(),
              checkedAtCommit: z.string().optional(),
              intendedUse: z.string(),
              status: z.enum(['proposed', 'located', 'typed', 'rejected']),
              evidenceRefs: z.array(z.string()),
            })
            .passthrough()
        ),
        coverage: z.array(
          z
            .object({
              planNodeId: z.string(),
              premiseDeclarationNames: z.array(z.string()),
              selfContained: z.boolean(),
              unresolvedNeed: z.string().optional(),
            })
            .strict()
        ),
        unresolvedNeeds: z.array(z.string()),
      })
      .passthrough(),
    planNodes: z.array(mathematicsPlanNodeInput),
    bridges: z.array(
      z
        .object({
          dependencyNodeId: z.string(),
          consumerNodeId: z.string(),
          mathematicalBridge: z.string(),
          leanUse: z.string(),
        })
        .passthrough()
    ),
    rootNodeId: z.string(),
    bottleneckNodeId: z.string().optional(),
    openFrontierNodeIds: z.array(z.string()),
    assessment: z
      .object({
        assessorSessionId: z.string(),
        probePlanNodeId: z.string(),
        faithfulness: z.enum(['pass', 'fail', 'unknown']),
        mathematicalValidity: z.enum(['pass', 'fail', 'unknown']),
        decompositionUsefulness: z.enum(['pass', 'fail', 'unknown']),
        probeOutcome: z.enum(['not_run', 'inconclusive', 'supported', 'kernel_verified', 'refuted']),
        probeSummary: z.string(),
        evidenceRefs: z.array(z.string()),
        semanticViabilityChecks: z
          .array(
            z
              .object({
                kind: z.enum(['premise_domain', 'state_invariant', 'boundary_cases', 'terminal_closure']),
                planNodeId: z.string(),
                verdict: z.enum(['pass', 'fail', 'unknown']),
                summary: z.string(),
                evidenceRefs: z.array(z.string()),
              })
              .strict()
          )
          .max(4)
          .optional(),
        checkedAt: z.number(),
      })
      .passthrough()
      .optional(),
    expectedInformationGain: z.number(),
    estimatedCost: z.number(),
    formalizationRisk: z.number(),
    noveltySource: z.string(),
    doNotRepeatRefs: z.array(z.string()),
    evidenceRefs: z.array(z.string()),
    extendedPlanReason: z.string().optional(),
  })
  .passthrough();

const mathematicsAlignmentCheckInput = z
  .object({
    problemId: z.string(),
    statementHash: z.string(),
    leanStatementHash: z.string(),
    contractCommit: z.string(),
    assessorSessionId: z.string(),
    goalInOwnWords: z.string(),
    quantifiedObjects: z.array(z.string()),
    assumptions: z.array(z.string()),
    forbiddenChanges: z.array(z.string()),
    officialVerificationCommand: z.string(),
    verdict: z.enum(['exact', 'stronger', 'weaker', 'mismatch', 'unknown']),
    assumptionDelta: z.array(z.string()),
    quantifierDelta: z.array(z.string()),
    domainDelta: z.array(z.string()),
    firstMismatch: z.string().optional(),
  })
  .passthrough();

const mathematicsRouteSelectionInput = z
  .object({
    statementHash: z.string(),
    selectionCommit: z.string(),
    primaryFingerprint: z.string(),
    reserveFingerprint: z.string().optional(),
    comparedFingerprints: z.array(z.string()),
    rationale: z.string(),
    selectedAt: z.number(),
  })
  .passthrough();

const mathematicsLessonInput = z
  .object({
    lessonId: z.string(),
    statementHash: z.string(),
    routeFingerprint: z.string(),
    sourceCommit: z.string(),
    failureCategory: z.string(),
    disposition: z.enum(['avoid_route', 'avoid_pattern', 'reuse']),
    trigger: z.string(),
    failedPattern: z.string(),
    rootCause: z.string(),
    reusableRule: z.string(),
    evidenceRefs: z.array(z.string()),
    createdAt: z.number(),
  })
  .passthrough();

export const mathematicsPortfolioInput = z
  .object({
    schema: z.literal(MATHEMATICS_PORTFOLIO_SCHEMA),
    version: z.literal(1),
    title: z.string(),
    stage: z.enum([
      'intake',
      'exploration',
      'candidate',
      'formalization',
      'review',
      'final_verification',
      'done',
      'examples',
      'proving',
      'verified',
      'refuted',
    ]),
    status: z.enum(['planning', 'running', 'needs_review', 'verified', 'refuted', 'inconclusive', 'blocked']),
    updatedAt: z.number(),
    stageHistory: z
      .array(
        z
          .object({
            from: z.enum([
              'intake',
              'exploration',
              'candidate',
              'formalization',
              'review',
              'final_verification',
              'done',
              'examples',
              'proving',
              'verified',
              'refuted',
            ]),
            to: z.enum([
              'intake',
              'exploration',
              'candidate',
              'formalization',
              'review',
              'final_verification',
              'done',
              'examples',
              'proving',
              'verified',
              'refuted',
            ]),
            commit: z.string(),
            timestamp: z.number(),
            reason: z.string(),
          })
          .strict()
      )
      .optional(),
    projectRoot: z.string().optional(),
    activeProblemId: z.string().optional(),
    toolchain: mathematicsToolchainInput.optional(),
    problems: z.array(
      z
        .object({
          id: z.string(),
          title: z.string(),
          informalStatement: z.string(),
          formalStatement: z.string().optional(),
          assumptions: z.array(z.string()),
          statementHash: z.string().optional(),
          problemContract: z
            .object({
              problemId: z.string(),
              informalStatement: z.string(),
              formalStatement: z.string(),
              formalNegationStatement: z.string().optional(),
              assumptions: z.array(z.string()),
              statementHash: z.string(),
              leanStatementHash: z.string(),
              leanNegationHash: z.string().optional(),
              knownTraps: z.array(z.string()),
              acceptanceCriteria: z.array(z.string()),
              officialVerificationCommand: z.string(),
              officialManifestId: z.string().optional(),
              officialManifestHash: z.string().optional(),
            })
            .passthrough()
            .optional(),
          researchContract: mathematicsResearchContractInput.optional(),
          feasibility: mathematicsFeasibilityInput.optional(),
          alignmentCheck: mathematicsAlignmentCheckInput.optional(),
          fastCheck: z
            .object({
              statementHash: z.string(),
              checkedAt: z.number(),
              method: z.string(),
              checkedCaseCount: z.number().int().min(1),
              outcome: z.enum(['no_counterexample_found', 'counterexample_found', 'inconclusive']),
              candidateClaim: z.enum(['statement', 'negation']),
              directAttemptRecommended: z.boolean(),
              summary: z.string(),
              evidenceRefs: z.array(z.string()),
              runtimeProbe: z
                .object({
                  expression: z.string().min(1).max(12_000),
                  precondition: z.string().min(1).max(12_000).optional(),
                  cases: z.array(z.string().min(1).max(4_000)).min(1).max(16).optional(),
                  mode: z.enum(['proposition', 'boolean']).optional(),
                  imports: z
                    .array(z.string().regex(/^[A-Za-z][A-Za-z0-9_.]*$/u))
                    .max(16)
                    .optional(),
                  timeoutMs: z.number().int().min(1_000).max(60_000).optional(),
                })
                .strict()
                .optional(),
            })
            .strict()
            .optional(),
          routeCards: z.array(mathematicsRouteCardInput).optional(),
          routeSelection: mathematicsRouteSelectionInput.optional(),
          localGateReceipt: z.record(z.string(), z.unknown()).optional(),
          officialGateReceipt: z.record(z.string(), z.unknown()).optional(),
          status: z.enum(['draft', 'formalized', 'candidate', 'verified', 'refuted', 'inconclusive', 'blocked']),
          attemptIds: z.array(z.string()),
          exampleIds: z.array(z.string()),
          verificationId: z.string().optional(),
          reviewId: z.string().optional(),
          reviewIds: z.array(z.string()).optional(),
          updatedAt: z.number(),
        })
        .passthrough()
    ),
    attempts: z.array(
      z
        .object({
          id: z.string(),
          problemId: z.string(),
          strategy: z.string(),
          status: z.enum(['draft', 'running', 'candidate', 'verified', 'refuted', 'failed', 'stale']),
          artifactId: z.string().optional(),
          artifactVersion: z.number().optional(),
          branch: z.string().optional(),
          commit: z.string().optional(),
          proofPath: z.string().optional(),
          theoremName: z.string().optional(),
          parentAttemptId: z.string().optional(),
          recoveryCheckpoint: z.record(z.string(), z.unknown()).optional(),
          lessons: z.array(mathematicsLessonInput).optional(),
          createdAt: z.number(),
          updatedAt: z.number(),
        })
        .passthrough()
    ),
    examples: z.array(
      z
        .object({
          id: z.string(),
          problemId: z.string(),
          kind: z.enum(['positive', 'negative', 'boundary', 'counterexample']),
          input: z.string(),
          expected: z.string().optional(),
          observed: z.string().optional(),
          scope: z.string().optional(),
          replayCommand: z.string().optional(),
          seed: z.string().optional(),
          artifactId: z.string().optional(),
          evidenceIds: z.array(z.string()),
          createdAt: z.number(),
        })
        .passthrough()
    ),
    evidence: z
      .array(
        z
          .object({
            id: z.string(),
            problemId: z.string(),
            statementHash: z.string().optional(),
            polarity: z.enum(['supporting', 'refuting', 'context']),
            strength: z.enum(['observed', 'reproduced', 'supporting', 'refuting', 'formal']),
            scope: z.string(),
            method: z.string(),
            inputRefs: z.array(z.string()),
            outputRefs: z.array(z.string()),
            evidenceIds: z.array(z.string()).min(1),
            observed: z.string(),
            reproducibility: z.enum(['single_run', 'reproduced', 'independent', 'formal']),
            commit: z.string(),
            command: z.string().optional(),
            source: z.string().optional(),
            seed: z.string().optional(),
            createdAt: z.number(),
          })
          .passthrough()
      )
      .default([]),
    verifications: z.array(
      z
        .object({
          id: z.string(),
          problemId: z.string(),
          status: z.enum(['pending', 'kernel_verified', 'failed', 'blocked', 'unavailable']),
          targetCommit: z.string(),
          statementHash: z.string(),
          claim: z.enum(['statement', 'negation']).optional(),
          toolchain: mathematicsToolchainInput,
          theoremName: z.string().optional(),
          proofHash: z.string().optional(),
          logPath: z.string().optional(),
          goalsRemaining: z.number(),
          sorryCount: z.number(),
          admitCount: z.number(),
          axioms: z.array(z.string()),
          verifier: z.enum(['lean-kernel', 'bounded-check', 'unavailable']),
          checkedAt: z.number().optional(),
          error: z.string().optional(),
        })
        .passthrough()
    ),
    reviews: z.array(
      z
        .object({
          id: z.string(),
          problemId: z.string(),
          status: z.enum([
            'not_requested',
            'queued',
            'running',
            'passed',
            'changes_requested',
            'refuted',
            'inconclusive',
            'stale',
          ]),
          targetCommit: z.string(),
          statementHash: z.string(),
          reviewerSessionId: z.string().optional(),
          verdict: z.enum(['passed', 'changes_requested', 'refuted', 'inconclusive']).optional(),
          summary: z.string().optional(),
          issueIds: z.array(z.string()),
          reportArtifactId: z.string().optional(),
          candidateReview: z
            .object({
              verdict: z.enum(['sound', 'gap', 'wrong']),
              firstFault: z.string().optional(),
              repairTarget: z.string().optional(),
              problemId: z.string(),
              targetCommit: z.string(),
              statementHash: z.string(),
              reviewerSessionId: z.string(),
              evidenceRefs: z.array(z.string()),
            })
            .passthrough()
            .optional(),
          updatedAt: z.number(),
        })
        .passthrough()
    ),
    blockers: z.array(z.string()),
    nextActions: z.array(
      z
        .object({
          id: z.string(),
          label: z.string(),
          kind: z.enum(['formalize', 'search', 'verify', 'review', 'decision']),
          priority: z.enum(['now', 'next', 'later']),
          owner: z.enum(['agent', 'user', 'reviewer']).optional(),
        })
        .passthrough()
    ),
  })
  .passthrough();

export const mathematicsPortfolioPatchInput = z
  .object({
    title: mathematicsPortfolioInput.shape.title.optional(),
    stage: mathematicsPortfolioInput.shape.stage.optional(),
    status: mathematicsPortfolioInput.shape.status.optional(),
    updatedAt: mathematicsPortfolioInput.shape.updatedAt.optional(),
    activeProblemId: mathematicsPortfolioInput.shape.activeProblemId.nullable().optional(),
    toolchain: mathematicsPortfolioInput.shape.toolchain.optional(),
    problems: mathematicsPortfolioInput.shape.problems.optional(),
    attempts: mathematicsPortfolioInput.shape.attempts.optional(),
    examples: mathematicsPortfolioInput.shape.examples.optional(),
    evidence: mathematicsPortfolioInput.shape.evidence.optional(),
    verifications: mathematicsPortfolioInput.shape.verifications.optional(),
    reviews: mathematicsPortfolioInput.shape.reviews.optional(),
    blockers: mathematicsPortfolioInput.shape.blockers.optional(),
    nextActions: mathematicsPortfolioInput.shape.nextActions.optional(),
  })
  .strict();
