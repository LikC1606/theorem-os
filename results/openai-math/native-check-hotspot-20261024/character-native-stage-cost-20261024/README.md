# Character native stage cost: existing frozen run

Update **2026-10-24T09:02:33Z**: the ordinary native original-target check passed, without conditions; receipt `lean-adc266b0e003d64e5ebdf91b`, source SHA256 `5c0cbc35bd6335ab7c6d8d57bdece22a3065c6fdc7dee871d2577826b50396d3`. The complete batch took 2375.071 seconds and its original-goal axiom list is only `propext`, `Classical.choice`, `Quot.sound`. Integration started normally. The remaining analysis below is the earlier timestamped snapshot; final native acceptance is still pending. [Original native verification](native-task-verification-20261024T090233Z.json).

**No supported immediate cache action was found that skips a remaining stage or imports the current compiled project outputs.** Continue the existing native process. This audit changed no active source, checkpoint, runtime, cache or affinity, launched no Lean/model run, and repeated neither the V2 fixedpoint checks nor the successful independent original comparator.

Run `1f3bb9c1-c99f-4fad-b656-8010a82c265b`, snapshot **2026-10-24T08:58:38.211811Z**: all **57 support `.olean` files exist** in `/tmp/deepscientist-lean-Xqjuxr/checkout`. Lean **PID 2514282**, parent shell **2365103**, is now compiling **Submission.lean**. `Submission.olean` does not yet exist at this snapshot. These are progress observations; mathematical acceptance remains pending.

| Stage | Existing supported reuse | Expected compilation on the ordinary successful path |
| --- | --- | --- |
| Current task acceptance | Current native check already running | Supports complete; Submission and declaration export remain |
| Canonical integration | Run-owned TaskProofCache, but actual environment digests differ | 57 supports + Submission + declaration export |
| Lead all-target check | Full formal cache; no matching existing project root | 57 supports + Submission + declaration export |
| Final original-workspace check | Full formal cache; distinct root, no matching existing entry | 57 supports + Submission + declaration export |
| Fixed publisher command | Copies pinned dependency packages; omits project build outputs | Cold Lake build of supports, Challenge and Submission, then comparator |

Thus, after the current task check, code inspection predicts **three more cold host batches plus the publisher build**. This is a stage count, not a time estimate or success guarantee. Review, changed inputs or repairs can add work.

The integration miss is concrete. Calling the **actual frozen `proofReuseEnvironment`** on existing projects with the same resolved solver access environment gives `reusable=true` for both, but:

- Delivery source project: digest `3336373af58fcc70d25216b2fb4741c243d67b34213bdd7b826af12593ac1139`; generated `.lake/package-overrides.json` is present with hash `a3eeb1bd82bb91ba9e4f24d2ae7296370743bebbb162812669f1dbf4c1e0b142`.
- Existing clean projection, representing the fresh integration checkout's configuration: digest `e7d8bb593a02d613eed3ff293ca14dfcd6a69ca47958579069843cdb19f67056`; that generated file is absent. All other configuration hashes match.

`withSolverWorktree` creates a clean Git checkout. `proofReuse.ts:25–31` hashes that generated file alongside the tracked configuration, and `cooperativeProof.ts:324–344` includes the resulting environment digest in the task cache key. Therefore the already-established source/merge fixedpoint alone cannot produce this cache hit. The [helper and measured digests](reuse-environments.json) are read-only evidence; no new integration checkout was created for this audit.

The [existing full-cache scan](existing-formal-cache.json) examined 256 successful formal-cache records (6 unexpired): **zero match** the current task request root, future lead all-target root, or final-workspace root. The full key binds projectRootHash, targetCommit, statement identities, source hash, tools and environment (`verifier.ts:2835–2855`). Task statements use digest `0a7945b3864e77f995020b9e39dee6639011fcd0fcc2da7cf7d136bae5f8cacf`; original all-target requests use the separate frozen contract statement identities. `checkSolverProof` does not consult TaskProofCache.

At a full-verifier miss, `verifier.ts:2196–2202` emits direct Lean commands for every local dependency and Submission. It does not consult the startup diagnostic cache or skip existing local `.olean` files. `seedDetachedLakeCache` explicitly seeds only validated packages and excludes generated project build outputs (`verifier.ts:447–487`). The eventual temporary checkout is cleaned up. The current genuine outputs therefore have no supported publication/import interface for the next stages.

The native final evaluator first checks the integrated proof again in the original workspace (`evaluation.ts:34–39`), then executes the exact fixed `--evaluator-command` (`evaluation.ts:40–43`). That command skips `.lake` when copying sources, copies `.lake/packages` separately, and calls `lake build Challenge Submission` before comparator. Its unchanged SHA256 is `8fc5775ca184697301d273e82692d3df19afb9f4442b431c894fe5b0458c0b0f`. The independent comparator result already obtained does not supply a cache lookup to this mandatory command; this audit did not rerun it.

For a future reviewed runtime, the smallest identified integration-cache fix is in `proofReuse.ts:25–31`: **after a sealed environment has validated the pinned package and project configuration, exclude or normalize generated `.lake/package-overrides.json` in this reuse digest**, while preserving tracked configuration, sealed package identity and tool bindings. The existing task cache can then reuse genuine identical projections when every other key agrees. This suggestion is not applied here; it would save integration work only, and does not skip original all-target checks or the publisher build. Editing the bundled frozen runtime or rewriting its existing cache keys is not a supported action for the current run.

[Full stage observation](stage-cost.json) includes current process/namespace information and native artifact metadata. [Frozen code evidence](code-evidence.json) preserves the relevant excerpts and file hashes. [Read-only helper source](read-reuse-environments.ts) records the exact environment-digest query and contains no compiler invocation.
