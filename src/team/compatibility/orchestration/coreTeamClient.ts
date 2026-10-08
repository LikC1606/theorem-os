/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

import {
  createResearchCoreTeamClient,
  type ResearchCoreRunState,
  type ResearchCoreSlotState,
  type ResearchCoreTeamClient,
} from "../../coreTeamClient";

/** @deprecated Use ResearchCoreSlotState from resources/research-team. */
export type ChallengeCoreSlotState = ResearchCoreSlotState;
/** @deprecated Use ResearchCoreRunState from resources/research-team. */
export type ChallengeCoreRunState = ResearchCoreRunState;
/** @deprecated Use ResearchCoreTeamClient from resources/research-team. */
export type ChallengeCoreTeamClient = ResearchCoreTeamClient;

/** @deprecated Use createResearchCoreTeamClient from resources/research-team. */
export const createChallengeCoreTeamClient = createResearchCoreTeamClient;
