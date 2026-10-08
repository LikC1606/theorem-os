import { z } from 'zod';
import {
  assertResearchTeamToolActionAuthorized,
  readResearchTeamToolPolicy,
} from "../common/types/team/researchTeamToolPolicy";

const portfolioActions = [
  'schema',
  'validate',
  'get',
  'submit',
  'patch',
  'request_review',
  'submit_review',
  'bootstrap',
  'official_gate',
] as const;
type PortfolioAction = (typeof portfolioActions)[number];

export function mathPortfolioToolActions(lite: boolean): PortfolioAction[] {
  if (!lite) return [...portfolioActions];
  readResearchTeamToolPolicy();
  return portfolioActions.filter((action) => {
    try {
      assertResearchTeamToolActionAuthorized('math_portfolio', action);
      return true;
    } catch {
      return false;
    }
  });
}

export async function createMathPortfolioToolInput(actions: readonly PortfolioAction[]) {
  if (!actions.length) throw new Error('math_portfolio requires at least one authorized action.');
  const mutations = actions.some((action) => action !== 'get' && action !== 'bootstrap')
    ? await import("./mathPortfolioMutationInput")
    : undefined;
  const input = {
    action: z.enum([actions[0]!, ...actions.slice(1)], {
      errorMap: () => ({ message: 'This action is not authorized for math_portfolio in the current role.' }),
    }),
    runId: z.string().optional(),
    conversationId: z.string().optional(),
    messageId: z.string().optional(),
    toolCallId: z.string().optional(),
    projectRoot: z.string().optional(),
    /** Optional read-only Lean-Eval checkout used for automatic candidate intake. */
    leanEvalRepositoryRoot: z.string().optional(),
    leanEvalCredits: z.array(z.record(z.unknown())).max(4096).optional(),
    leanEvalProblemId: z.string().trim().min(1).max(128).optional(),
    leanEvalBootstrapReceiptPath: z.string().optional(),
    leanEvalPage: z.number().int().min(1).max(128).optional(),
    leanEvalPageSize: z.number().int().min(1).max(32).optional(),
    artifactId: z.string().optional(),
    artifactVersion: z.number().optional(),
    baseRevision: z.string().optional(),
    title: z.string().optional(),
    changeSummary: z.string().optional(),
    portfolio: mutations?.mathematicsPortfolioInput.optional() ?? z.never().optional(),
    portfolioPatch: mutations?.mathematicsPortfolioPatchInput.optional() ?? z.never().optional(),
    review: mutations
      ? z
          .object({
            id: z.string().optional(),
            problemId: z.string().optional(),
            status: z
              .enum([
                'not_requested',
                'queued',
                'running',
                'passed',
                'changes_requested',
                'refuted',
                'inconclusive',
                'stale',
              ])
              .optional(),
            targetCommit: z.string().optional(),
            statementHash: z.string().optional(),
            reviewerSessionId: z.string().optional(),
            verdict: z.enum(['passed', 'changes_requested', 'refuted', 'inconclusive']).optional(),
            summary: z.string().optional(),
            issueIds: z.array(z.string()).optional(),
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
            updatedAt: z.number().optional(),
          })
          .passthrough()
          .optional()
      : z.never().optional(),
    targetCommit: z.string().optional(),
    statementHash: z.string().optional(),
    promptQuery: z
      .object({
        problemId: z.string(),
        routeFingerprint: z.string(),
        planNodeId: z.string().optional(),
        goal: z.string().max(4000).optional(),
        targetGoal: z.string().max(12000).optional(),
        targetProbeMode: z.enum(['exact', 'apply']).optional(),
        proofStateFingerprint: z.string().trim().min(1).max(256).optional(),
        failureKind: z
          .enum(['unknown_identifier', 'type_mismatch', 'instance_synthesis_failed', 'unsolved_goals', 'tactic_failed'])
          .optional(),
        failureDiagnostic: z.string().trim().min(1).max(4000).optional(),
        routeCoverage: z.boolean().optional(),
        routeNodeLimit: z.number().int().min(1).max(4).optional(),
        importModules: z.array(z.string()).max(16).optional(),
        sourceFile: z.string().trim().min(1).max(1024).optional(),
        upstreamQueries: z
          .object({
            leansearch: z.string().trim().min(1).max(2000).optional(),
            loogle: z.string().trim().min(1).max(2000).optional(),
          })
          .strict()
          .optional(),
        packageQueries: z.array(z.string().trim().min(1).max(256)).max(3).optional(),
        installedPackageScopes: z.array(z.string().trim().min(1).max(128)).max(2).optional(),
        installedPackageQuery: z.string().trim().min(1).max(1000).optional(),
        installedPackageOffset: z.number().int().nonnegative().max(Number.MAX_SAFE_INTEGER).optional(),
        installedPackageCheckTypes: z.boolean().optional(),
        premiseLimit: z.number().int().min(1).max(6).optional(),
        lessonLimit: z.number().int().min(1).max(2).optional(),
      })
      .strict()
      .optional(),
    displayIntent: z.enum(['background', 'open', 'focus']).optional(),
  };
  if (mutations) return input;
  // These optional fields are absent, so read/bootstrap handlers receive undefined.
  // No mutation schema or review workflow is constructed for this surface.
  const { portfolio: _portfolio, portfolioPatch: _portfolioPatch, review: _review, ...readInput } = input;
  return readInput as typeof input;
}
