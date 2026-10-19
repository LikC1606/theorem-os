# Compare single, independent and cooperative solving

For module-plan comparisons with fixed cooperative workers, including optional
context and custom-rule treatments, see [module experiments](../components/EXPERIMENTS.md).

Use the same pinned public problem, task, model, effort, method, dependency
environment and final host evaluator in three arms:

| Arm | Workers | Information sharing |
| --- | --- | --- |
| `single` | 1 | One iterative solver with Lean feedback |
| `independent` | 4 by default | Separate complete attempts; no messages or proof merging |
| `cooperative` | 4 by default | Lead planning, task assignment, checked helper reuse and review |

Each arm has the **same total turn limit and shared solving time limit**.
Planning, reviews, restarts and retries use that total; independent workers
share it too. These are limits on turns and time, not equal token expenditure.
The single arm uses the same strong model, retrieval tools and Lean feedback.

For a provider-observed token allowance, pass the same `--max-total-tokens N`
through preparation. To isolate this allowance from time and dispatch limits,
also pass `--max-run-seconds 0 --max-turn-seconds 0 --max-turns 0`. The allowance
includes all roles and stops new requests after reported consumption reaches N.
Already running requests may exceed it. Reports retain that overrun and missing
usage; this is not an exact token-matched or billed-cost comparison. The default
is `--max-total-tokens 0`, with no token limit.

Complete the [example setup](README.md) first. Configure a compatible trusted
`.lake/packages` cache in your math environment: the comparison bootstraps fresh
workspaces without downloading dependencies again. From the project root:

```bash
bun run math compare --phase prepare \
  --repo /absolute/path/to/imo2026 --problem imo2026_q1 \
  --task-file /absolute/path/to/imo-q1-case/task.md \
  --build-manifest /absolute/path/to/manifest.json \
  --repetitions 3 --max-turns 20 --max-run-seconds 1800 \
  --proof-environment-cache-dir /absolute/private/proof-environments \
  --directory /absolute/new/comparison
```

Preparation invokes no model. Use a new absolute directory outside both source
checkouts. `comparison.json` records the common task, build and environment
digests, and all launch hashes. Every arm and repetition starts independently
from unfinished statements. Arm order rotates between repetitions; repetition
labels are not controlled provider sampling seeds.

The optional host-private proof environment cache reuses a verified dependency
image. Each run still mounts and checks its own immutable environment; the cache
contains no candidate proofs. Its path is frozen in each launch file.

Inspect the plan before running. The following `run` command invokes the
configured provider for **all planned attempts**. Three repetitions produce
nine runs, each with a 30-minute solving limit above. Dependency preparation and
final evaluation take additional time; a run may finish earlier.

```bash
bun run math compare --phase run --directory /absolute/new/comparison
bun run math compare --phase report --directory /absolute/new/comparison
```

Runs execute sequentially; each arm controls its own worker parallelism. Every
attempt has a separate workspace, checkpoint, result and event log. Failed,
incomplete and missing attempts stay in the planned denominator. An incomplete
run makes the batch return nonzero, while the report is still written. Existing
batches are preserved. To resume an individual run, use its saved launch
arguments with `--resume`, preserve the source build and environment, then
regenerate the comparison report. Batch wall time covers the original launch;
it does not include manual resumes.

`report.json` contains per-arm acceptance counts, per-repetition outcomes,
turns, provider usage, worker errors, exit codes and wall time including
preparation and evaluation. This is recorded evidence without replaying Lean.
Only a matched completed result with a passed final evaluator and checked
solution counts as accepted. The IMO evaluator is local (`official: false`).

Usage aggregates provider-reported counters across workers and sessions,
including planning, review, failed turns and restarts. It cannot certify billed
usage when a provider omits events. If an active worker lacks counters, `totalTokens` is `null`;
partial raw usage and `missingUsageWorkers` remain visible. `reportedTokens`
sums runs with complete counters: always read `missingTokenRuns` alongside it.
Missing counters or timings are not zero-cost attempts. Monetary costs are not
estimated.

For a component replacement experiment, prepare another comparison with
`--scheduler goals-first` or `--scheduler continuation`. Default `plan` preserves plan order; `goals-first`
changes only M3's ordering of ready tasks to prefer original goals. Dependency,
route and ownership checks still apply. Module versions are saved, and resume
rejects a changed policy. This is an ablation to measure, with no claimed
improvement. Use multiple problems and repetitions under the same configuration
before drawing conclusions.

`continuation` prioritizes consumers of checked lemmas on unfinished original-goal
paths and preserves an exploration opportunity alongside two active main-path
tasks. The inspection report separates planned use from recorded Lean proof use.
The comparison harness currently supports the pinned IMO problem set; it does
not launch these arms for arbitrary LeanEval campaigns.

Next, identify recurrent failures in the reports and logs, then change one M3
search rule or M4 context policy at a time, holding tasks, budget and evaluator
fixed and reporting failures alongside successes.
