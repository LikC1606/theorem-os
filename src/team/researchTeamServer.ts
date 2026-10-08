/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 *
 * Dedicated Research Team MCP entrypoint. The implementation is shared with
 * the legacy competition bundle for compatibility, but this source has its
 * own runtime name and build artifact so new Teams never select the IOAI
 * Challenge source.
 */

import { RESEARCH_TEAM_RUNTIME_ENV } from "../common/config/builtinMcpConstants";

process.env[RESEARCH_TEAM_RUNTIME_ENV] = '1';

// Load after setting the marker: competitionServer's startup branch then
// requires a Research Team role capability and cannot silently become a
// Challenge runtime when this dedicated source is selected.
void import("./compatibility/competitionServer").catch((error) => {
  console.error(
    '[ResearchTeamMCP] Failed to load the Core-backed Research Team server:',
    error instanceof Error ? error.stack || error.message : String(error)
  );
  // No MCP server was successfully started. Exit explicitly so partially
  // loaded dependencies cannot keep the stdio process alive indefinitely.
  process.exit(1);
});
