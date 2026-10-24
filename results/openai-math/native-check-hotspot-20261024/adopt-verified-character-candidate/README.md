# Character V2: continue the fresh native chain

Final decision: continue the existing fresh native attempt `1f3bb9c1-c99f-4fad-b656-8010a82c265b`. Preserve the old Character run `be2c8bbd-71c7-4dc5-aa21-1c3a7550a2c6` unchanged: do not stop it, resume it, or queue another edit. Old-run adoption remains a validated, unqueued proposal only. The fresh attempt is the selected route; its existing controller handles continuation.

The complete [V2 candidate](../character-sync-def-v2-candidate/Submission.lean) genuinely compiled with exit `0` in **635.028 seconds** and passed its permitted-axiom audit (`propext`, `Classical.choice`, `Quot.sound`). Its unchanged SHA256 is `5c0cbc35bd6335ab7c6d8d57bdece22a3065c6fdc7dee871d2577826b50396d3` and its length is 795,645 bytes. The [build receipt](../character-sync-def-v2-candidate/build-receipt.json) and [axiom-audit receipt](../character-sync-def-v2-candidate/audit-receipt.json) establish independent preparation evidence. Native acceptance requires the separate native verification, review, integration and publisher checks.

The [dry-run script](prepare-dry-run.ts) constructs the old run's complete current plan. It changes only `initial_goal_1`'s owner, objective and revision (`1` → `2`), preserving all other tasks, groups, proof routes, dependencies, target and mathematical contract. The unchanged frozen parser, 64,000-byte reader and supported `queueRunEdit(run, proposal, true)` validated the actual **47,231-byte** normalized edit. The [receipt](dry-run.json) records status `validated`, proposal ID `character-verified-v2-5c0cbc35bd63`, base version `2c9b0b615bb3d89086d92ccc5f9ea804cb84de31c2e036502ce2b92aa52137fc`, and `candidateQueued: false`. Source guards and exact sandbox transport reuse the existing [guard receipt](../guard-preflight-v2/receipt.json) and [transport evidence](../native-sync-def-attempt/transport-preparation.json).

Directly terminating only the old Lean child cannot safely advance this frozen task-check path:

1. `mathProcess.ts:140` records a signalled child with a null exit code, or a wrapper exposes `137`/`143`.
2. `verifier.ts:2040` returns `failed`, with `Lean exited with status unknown/137/143.`.
3. `proofReuse.ts:41` requires genuine Lean error diagnostics and status `1` for deterministic failure. A signal-only failure does not qualify.
4. `modules/evidence.ts:71` therefore leaves the result unattributable.
5. `cooperationTaskProofs.ts:427` throws `math_verifier_unavailable` before the later stale-assignment branch can supersede the old delivery.
6. `research.ts:765` aborts the whole cooperative run for that error.

The [control-flow evidence](failure-control-flow.json) exercises real frozen attribution functions using explicitly synthetic fixtures. No actual signal test was performed and these fixtures are not formal verification receipts.

Gracefully stopping the whole solver and using the exact frozen launch with `--resume` is supported by the inspected code. The top-level handler aborts coherently, cleanup retains the archive, and `run.ts` saves `limit_reached` / `math_run_stopped`. Resume accepts this stopped outcome after immutable-identity checks. In the inspected old archive, the sole goal is running with no saved proof, integrated check, pending validation, conditional task or pending-sync edit; restore would return it to pending. Normal stopping would still update state/result metadata, and the existing `resume-followup.py` supervisor rejects the current phase receipt unless adapted. This route was **not executed** and is **not selected**, because it does not eliminate the preparation wait below.

The corrected [cache replay](old-resume-cache-audit.json) and [native environment identity](old-resume-native-environment-identity.json) use actual `campaign.environment()` startup values resolved through frozen `math.env`. The diagnostic environment is `b6cbd3acabb5efd8739f63e449d5b498c5b28877e44926cbd33c0ef245d03766`; the native tool identity is `21df37a7a514a2c66258155422ec0a1101355dbb3c8fd7c50f3dfa67185a7d4e`. All **228 module output groups** and **228 raw diagnostic artifacts** pass their byte hashes. Same-path regenerated overrides remain byte-identical. The report contains the individual module keys, match reasons and timings behind these totals:

| Old worker | Full-key matches with existing outputs | Guaranteed cached prefix | Work requiring compilation, using real reference timings |
| --- | --- | --- | --- |
| solver | Modules 1–57: 57/57 | 57 | 0 |
| researcher-1 | None: 0/57 | 0 | All 57: 1,741.351 s (29.02 min) |
| researcher-2 | Modules 41–57: 17/57, conditional | 0 | First 40: 284.828 s (4.75 min) |
| engineer | Modules 1–57: 57/57 | 57 | 0 |

Researcher-2's final 17 matches depend on the first 40 recompilations producing the same existing output bytes; they are potential later hits. This audit performed no compilation. The frozen `run.ts:264–277,327` always reruns support-module preflight on resume.

The timings come from the genuinely completed fresh solver's [native preparation diagnostics](../native-sync-def-attempt/native-followup/result.json.runtime/preparation-diagnostics.json), whose 57 module durations sum to **1,741,351 ms**. This receipt's SHA256 at audit time is `63c940840d9f4d4cf8a59e7e92739a92a51cc8cf9a6c5456df8334d1f42c968d`. Peer times can differ under concurrency, and environment/retrieval overhead is additional. Thus the old resume still has an estimated parallel peer critical path of about **29 minutes**, while the fresh attempt has already completed solver preparation and entered parallel peer preparation.

Copying genuine old caches into fresh worktrees does not avoid this wait: `.lake/package-overrides.json` contains worktree-specific absolute paths, `prepareLeanDiagnosticOverrides` rewrites those paths, and `leanDiagnostics.ts:173` hashes the raw config into every source key. Cross-worktree reuse therefore misses from the first module under normal preparation. No caches were copied and no keys were rewritten.

The [preliminary projection-environment diagnostic](old-resume-cache-audit.projection-environment-error.json) is retained only as a correction record. Model projections add empty `LEAN_PATH`/`LEAN_SYSROOT` strings, while actual native startup leaves them absent; the frozen identity distinguishes empty strings from null. Use the corrected report's `reports` and native environment identity for this decision. Its retained top-level `diagnosticError` / `projectionDifference` text describes that superseded preliminary calculation.

The adoption audit sent no signal, queued no edit and launched no Lean or model process. All active source, cache, runtime and state remain untouched by this audit; only its documentation and audit artifacts were produced. Both existing chains remain under their existing controllers, and the selected continuation is the fresh native attempt.
