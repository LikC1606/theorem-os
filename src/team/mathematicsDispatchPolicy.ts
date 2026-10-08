/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

import type {
  ResearchTeamAssignment,
  ResearchTeamMathAssignment,
} from "../common/types/team/researchTeamContracts";

export type MathematicsWaveValidationPhase = 'dispatch' | 'integration';

/** Reject FORMALIZE objectives that decide failure before the Worker produces evidence. */
export function mathematicsFormalizationPrejudgesFailure(
  assignment: Pick<ResearchTeamAssignment, 'title' | 'objective' | 'acceptanceCriteria' | 'doNotRepeat'>
): boolean {
  const text = [assignment.title, assignment.objective, ...assignment.acceptanceCriteria, ...assignment.doNotRepeat]
    .join('\n')
    .replaceAll(/\s+/gu, ' ');
  return [
    /\b(?:this|the|original|full|whole)\s+(?:theorem|statement|goal|biconditional)\b[^.!?]{0,160}\b(?:far|well)\s+beyond\b[^.!?]{0,120}\b(?:mathlib|formaliz|library|support)/iu,
    /\b(?:do not|don't|never|avoid)\s+(?:attempt(?:ing)?\s+to\s+)?(?:prove|close|solve|formalize)\b[^.!?]{0,100}\b(?:full|whole|complete|original|target|biconditional|theorem)\b/iu,
    /\b(?:primary|main|expected)\s+deliverable\b[^.!?]{0,160}\b(?:reconnaissance|inventory|blocked|inconclusive|obstruction|gap report)\b/iu,
  ].some((pattern) => pattern.test(text));
}

/**
 * Pure limits and ownership checks shared by dispatch and integration.
 * Keeping this policy free of Git/Core state makes it safe to test and reuse
 * when a later wave is resumed from a durable receipt.
 */
export function validateMathematicsWaveLimits(
  input: Readonly<{
    stage: ResearchTeamMathAssignment['stage'];
    count: number;
    reasoningConcurrency: number;
    routes: readonly (string | undefined)[];
    artifactPaths: readonly string[];
    requireDistinctRoutes: boolean;
    phase: MathematicsWaveValidationPhase;
  }>
): void {
  const maximum =
    input.stage === 'diversify'
      ? input.reasoningConcurrency
      : input.stage === 'formalize'
        ? input.reasoningConcurrency
        : input.stage === 'replan'
          ? input.reasoningConcurrency
          : 1;
  const limitMessage =
    input.phase === 'dispatch'
      ? `permits at most ${maximum} Worker assignments`
      : `integration permits at most ${maximum} results`;
  if (input.count > maximum) throw new Error(`Mathematics ${input.stage.toUpperCase()} ${limitMessage}`);
  if (new Set(input.artifactPaths).size !== input.artifactPaths.length) {
    throw new Error(
      input.phase === 'dispatch'
        ? 'Parallel Mathematics assignments must own disjoint proof/artifact paths'
        : 'Parallel Mathematics integration detected overlapping artifact/proof paths'
    );
  }
  if (input.requireDistinctRoutes && new Set(input.routes).size !== input.routes.length) {
    throw new Error(
      input.phase === 'dispatch'
        ? 'Parallel Mathematics assignments must use distinct route fingerprints'
        : 'Parallel Mathematics results must use distinct route fingerprints'
    );
  }
}
