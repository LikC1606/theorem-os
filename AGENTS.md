# Standalone mathematics runtime

This project has no Electron, React, renderer, WebUI, or desktop build. Keep the CLI and mathematics proof behavior independent of the original DeepScientist checkout.

`src/math` owns mathematics services. `src/team` owns Team/MCP orchestration. `src/project-git` owns committed source and assignment records. `src/mcp` and `src/shared` retain compatibility helpers needed by these entrypoints; do not expose unrelated domain tools from the standalone CLI.

Preserve frozen problem/source identities, isolated Worker worktrees, Lean receipts, independent evaluation, and resumable assignments. A model's completed message is never proof acceptance.

New runs use `gpt-6.1-sol` with `xhigh` reasoning and the isolated existing `my_codex` profile unless the user chooses otherwise. Do not copy credentials, alter global Codex configuration, or call real models merely to validate a local extraction.

Make the smallest requested change. Run focused tests and the headless bundle build when modifying runtime boundaries. Do not commit, publish, or modify the original checkout without an explicit request.
