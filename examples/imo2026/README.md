# Reproduce the public IMO2026 Q1 example

For paired single-agent, independent-parallel and cooperative experiments, see
the [comparison protocol](COMPARISON.md).

This example runs the ordinary solver on all five public Q1 targets from
`humanfia/imo2026` at commit `834c01f2ecac89b648759b1c95bc6180b0ede149`.
The adapter copies public statements and project metadata. It starts with
unfinished proofs and does not seed answers from previous runs.

The case uses `gpt-6.1-sol`, `xhigh`, four agents, the direct method, a shared
30-minute solving limit and 20 total turns. A completed run is accepted only if
all original targets pass host Lean verification after integration. This is a
local evaluation (`official: false`). A demonstration run can remain incomplete
within its budget; the example does not promise a solved task.

## Requirements

Use Linux with Git, Bun 1.2+, Node.js 22+, `/usr/bin/python3`, Elan and Bubblewrap.
Preparing the immutable dependency environment also needs `mksquashfs`,
`squashfuse` (or `snapfuse`), `fusermount3` (or `fusermount`), and permission to
mount FUSE filesystems. `lake exe cache get` downloads the pinned dependencies
and requires network access and enough disk space for Mathlib.

Install dependencies with `bun install --frozen-lockfile` from the project root.
Authenticate your existing Codex profile separately. The default profile is
`~/.config/deepscientist/math-sol-codex`; `CODEX_HOME` can select another existing
profile with access to the configured model.

The [environment template](math.env.example) describes tool and cache settings.
Copy it to a local file, replace the paths, and set
`DEEPSCIENTIST_MATH_ENV_FILE` to that file. Keep Lean/Elan on your shell's PATH
for the dependency download step.

Run the complete `import Mathlib` check on a host with enough memory for Lean
and the other processes sharing its account limit. The first Q1 investigation
found a 12 GiB account limit on the login node, despite much more available host
memory. Moving only the toolchain to local disk did not resolve the timeout.
Use a compute allocation when the login node is constrained; a CPU allocation
does not require a GPU. Check the account or job cgroup limit as well as host RAM.

If the pinned toolchain lives on shared storage, copy its `bin` and `lib` trees
to local disk, preserve relative symlinks, and compare every file using SHA-256
before selecting the copy through the environment template. Keep the same
`lean-toolchain`, package versions, imports, and source constraints. Frozen
environment paths must remain available on the selected host when resuming.

## Prepare, check, and run

From the source checkout, use a **new absolute directory outside the checkout**:

```bash
bash examples/imo2026/reproduce.sh prepare /absolute/new/imo-q1-case
bash examples/imo2026/reproduce.sh check /absolute/new/imo-q1-case
```

`prepare` builds and freezes the runtime, checks out the pinned public source,
creates a fresh solver workspace and task file, and downloads Lean dependencies.
It writes `case.json`, `build.json`, and `bootstrap.json` with the exact problem,
build, model, budget and task digest. It does not invoke a model.

`check` prepares the actual runtime and writes `status: prepared`; it does not
invoke a model or prove any target. Since it creates a checkpoint, use `resume`
to start solving afterwards:

```bash
bash examples/imo2026/reproduce.sh resume /absolute/new/imo-q1-case
```

Use `solve` for a fresh model run when skipping `check`. Solve and resume invoke
your configured provider. Progress is emitted as JSON events; the final outcome
is stored in `result.json`. Only `evaluated_passed` records a successful final
evaluation. Timeouts, errors and incomplete outcomes remain visible.

For an existing pinned benchmark checkout, set `MATH_EXAMPLE_REPO` before
`prepare`. With an already prepared compatible cache, set
`MATH_EXAMPLE_SKIP_CACHE=1` and configure its trusted root in your math environment
file. These options reuse local resources; the task and target identities stay
pinned. Preserve the original build and environment to resume a run.

## Inspect and intervene

```bash
bun run math inspect --run /absolute/new/imo-q1-case/result.json
bun run math inspect --run /absolute/new/imo-q1-case/result.json \
  --format plan --output /absolute/new/imo-q1-case/plan.json
```

The report separates recorded proof checks, open conditions, review, and final
evaluation. It can inspect a running checkpoint before `result.json` exists.
It reads stored evidence and does not rerun Lean.

Once the Lead has created a plan, edit the exported task objectives, helper
types, dependencies or route settings. Retain `baseVersion`, all original goals,
and an acyclic dependency graph. Then validate and queue the edit:

```bash
bun run math edit --run /absolute/new/imo-q1-case/result.json \
  --plan /absolute/new/imo-q1-case/plan.json --dry-run
bun run math edit --run /absolute/new/imo-q1-case/result.json \
  --plan /absolute/new/imo-q1-case/plan.json
```

`queued` means the request was appended to the existing edit protocol. The live
or resumed solver checks the plan version, applies the edit and separately
rechecks affected proofs. Inspect again to distinguish `received`, `applied`,
`rejected` and the proof recheck outcome. Stale plans must be re-exported against
the current plan version. Fully accepted terminal runs are not new experiments;
prepare a fresh case to measure a different method.
