/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

import type { MathematicsPortfolio } from "../common/chat/mathematics";
import { isMathFoundationalLeanAxiom } from "../common/types/team/mathematicsTeam";
import { hashMathFormalSourceDeclaration, type MathematicsVerifierResult } from "./verifier";

/** Check the full response surface, including notes outside individual attempts. */
export function assertMathRunPortfolioOrigin(portfolio: MathematicsPortfolio, runIdentity: string): void {
  if (
    portfolio.runIdentity !== runIdentity ||
    portfolio.attempts.some((attempt) => attempt.runIdentity !== runIdentity)
  ) {
    throw new Error('Mathematics portfolio memory is not bound to the active run. Use a fresh run workspace.');
  }
  const problemId = portfolio.activeProblemId;
  if (
    portfolio.problems.length > 1 ||
    (portfolio.problems.length === 1 && portfolio.problems[0].id !== problemId) ||
    [
      ...portfolio.attempts,
      ...portfolio.examples,
      ...portfolio.evidence,
      ...portfolio.verifications,
      ...portfolio.reviews,
    ].some((entry) => entry.problemId !== problemId)
  )
    throw new Error('Managed mathematics memory requires a portfolio confined to the active problem.');
}

/** Only the mutation boundary may assign provenance to newly submitted records. */
export function bindMathRunPortfolio(portfolio: MathematicsPortfolio, runIdentity: string): MathematicsPortfolio {
  if (
    (portfolio.runIdentity !== undefined && portfolio.runIdentity !== runIdentity) ||
    portfolio.attempts.some((attempt) => attempt.runIdentity !== undefined && attempt.runIdentity !== runIdentity)
  )
    throw new Error('Cannot import mathematics memory from another run.');
  const bound = {
    ...portfolio,
    runIdentity,
    attempts: portfolio.attempts.map((attempt) => Object.assign({}, attempt, { runIdentity })),
  };
  assertMathRunPortfolioOrigin(bound, runIdentity);
  return bound;
}

/** A checkpoint's claimed lemma is not a receipt. Only this run's verifier results can support it. */
export function assertMathRunPortfolioPremises(
  portfolio: MathematicsPortfolio,
  receipts: readonly MathematicsVerifierResult[]
): void {
  for (const attempt of portfolio.attempts) {
    const ledger = attempt.recoveryCheckpoint?.ledger;
    const checkpoint = ledger?.semiProofCheckpoint;
    if (!checkpoint) continue;
    for (const lemma of checkpoint.verifiedLemmas) {
      // Checkpoint statements are headers; the source parser needs a body delimiter.
      const declarationHash = hashMathFormalSourceDeclaration(
        `${lemma.theoremStatement} := by sorry`,
        lemma.theoremName
      );
      if (
        !declarationHash ||
        !receipts.some(
          (receipt) =>
            receipt.status === 'kernel_verified' &&
            receipt.verifier === 'lean-kernel' &&
            receipt.claim === 'statement' &&
            receipt.targetCommit === checkpoint.targetCommit &&
            receipt.statementHash === ledger.statementHash &&
            receipt.proofHash === lemma.proofHash &&
            receipt.proofPath === lemma.sourceFile &&
            receipt.theoremName === lemma.theoremName &&
            receipt.sourceDeclarationHash === declarationHash &&
            Boolean(receipt.theoremDeclarationHash) &&
            receipt.goalsRemaining === 0 &&
            receipt.sorryCount === 0 &&
            receipt.admitCount === 0 &&
            !receipt.cleanupError &&
            receipt.axioms.every(isMathFoundationalLeanAxiom)
        )
      )
        throw new Error('Mathematics reusable lemma is not backed by a matching verifier receipt in this run.');
    }
  }
}
