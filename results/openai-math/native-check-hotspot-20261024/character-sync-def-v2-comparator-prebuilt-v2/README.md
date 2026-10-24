# V2 standalone original-comparator pass

The unchanged pinned comparator binary exited **0** in **41.153 seconds** at
2026-10-24 08:06:06 UTC. Its output includes both
`Lean default kernel accepts the solution` and `Your solution is okay!`.
The original target and permitted axioms are unchanged. Only the two module names
in the original comparator JSON are adapted to `Challenge` and `Submission`.

This standalone check uses the genuine completed V2 `Submission.olean` from the
635.03-second full-source compile. Its source SHA256 is
`5c0cbc35bd6335ab7c6d8d57bdece22a3065c6fdc7dee871d2577826b50396d3`;
its artifact SHA256 is
`11e1303a4cfc4153461ef42b62b5a1aaa03b437024a95d379253824bdefe62dc`.
The original challenge was separately compiled with the same pinned Lean in
1.542 seconds, with exit code 0.

The isolated Lake project registers these two precompiled modules with empty
`defaultFacets`. Thus the comparator's Lake build steps register existing modules;
they do not rebuild Submission. `lake update` genuinely creates the empty local
dependency manifest before the comparator's read-only project sandbox is entered.
The comparator still exports both declarations, compares their types and
definitions, checks permitted axioms, and replays the solution in Lean's default
kernel. Its mathematical checking code and binary are unchanged.

This is independent comparator evidence. The active native launch, full-build
evaluator command, source guards, cache and receipts are unchanged; this check does
not set native acceptance or increase the final native pass count. The fresh
native attempt continues its complete original pipeline.

The two earlier entry-point failures are retained in
`../character-sync-def-v2-comparator/` and
`../character-sync-def-v2-comparator-prebuilt/`: respectively missing Lake project
configuration and missing precreated manifest. Neither reached mathematical
comparison. No proof artifact or trace was invented for any of these attempts.
