# Standalone mathematics runtime

This project has no Electron, React, renderer, WebUI, or desktop build. Keep the CLI and mathematics proof behavior independent of the original DeepScientist checkout.

`src/math` owns mathematics services. `src/solver/modules` separates M1–M5 research decisions; `src/solver/run.ts` prepares and evaluates runs, and `src/solver/research.ts` executes cooperative role sessions with shared budgets and run-local checkpoints. `src/solver/lemma.ts` checks conditional connections and helper proofs in disposable source projections without relaxing the strict verifier. `src/solver/archive.ts` owns S1 records; `src/solver/evaluation.ts` owns fixed S3 final acceptance. `src/runtime/codexSession.ts` connects to Codex through stdio. Do not reintroduce Core, Team services, HTTP services, role queues, or MCP orchestration. M3 selects ready tasks, M5 assigns Lead, Researcher, Engineer and fixed-version Reviewer responsibilities; `cooperation.ts` runs the asynchronous task and integration loop, and `cooperativeProof.ts` checks and merges partial declarations; S2 learning remains a future extension.

Preserve frozen problem/source identities, isolated solver worktrees, Lean receipts, independent evaluation, and resumable runs. A model's completed message is never proof acceptance.

New runs use `gpt-6.1-sol` with `xhigh` reasoning and the isolated existing `my_codex` profile unless the user chooses otherwise. Do not copy credentials, alter global Codex configuration, or call real models merely to validate a local extraction.

Make the smallest requested change. Run focused tests and the headless bundle build when modifying runtime boundaries. Do not commit, publish, or modify the original checkout without an explicit request.
