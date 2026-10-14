#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'HELP'
Usage: bash examples/imo2026/reproduce.sh prepare|check|solve|resume /absolute/case-directory

prepare  Build the CLI, bootstrap pinned public IMO2026 Q1, and fetch Lean caches.
check    Prepare the proof environment without invoking a model.
solve    Start a fresh model run; use resume after check or an interrupted run.
resume   Resume with the same case, model, worker count, and build manifest.

Optional environment:
  MATH_EXAMPLE_REPO        Existing Humanfia checkout at the pinned commit.
  MATH_EXAMPLE_SKIP_CACHE  Set to 1 only when a compatible trusted cache is ready.
  CODEX_HOME / DEEPSCIENTIST_MATH_ENV_FILE select existing local configuration.
HELP
}

if [[ ${1:-} == --help || ${1:-} == -h ]]; then usage; exit 0; fi
if [[ $# != 2 || ! $1 =~ ^(prepare|check|solve|resume)$ || $2 != /* ]]; then usage >&2; exit 1; fi
mode=$1
project_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd -P)
case_root=$(/usr/bin/python3 -c 'import os,sys; print(os.path.realpath(sys.argv[1]))' "$2")
case "$case_root/" in "$project_root/"*) echo 'Case directory must be outside the source checkout.' >&2; exit 1;; esac
cd -- "$project_root"

if [[ $mode == prepare ]]; then
  if [[ -e $case_root ]]; then
    echo 'Use a new case directory; existing files are preserved.' >&2
    exit 1
  fi
  mkdir -p -- "$case_root"
  if [[ -n ${MATH_EXAMPLE_REPO:-} ]]; then
    benchmark=$MATH_EXAMPLE_REPO
  else
    benchmark=$case_root/benchmark
    git clone https://github.com/humanfia/imo2026.git "$benchmark"
    git -C "$benchmark" checkout --detach 834c01f2ecac89b648759b1c95bc6180b0ede149
  fi
  bun run build --state-root "$case_root/builds" > "$case_root/build.json"
  bun run math bootstrap-imo --repo "$benchmark" --problem imo2026_q1 \
    --workspace "$case_root/workspace" > "$case_root/bootstrap.json"
  cat > "$case_root/task.md" <<'TASK'
Prove all five targets in the frozen public IMO2026 Q1 statement.
Preserve the original declarations, definitions, assumptions, and protected files.
Write complete Lean proofs in Submission.lean and use compiler feedback to repair them.
TASK
  bun -e '
    const root = process.argv[1];
    const bootstrap = await Bun.file(root + "/bootstrap.json").json();
    const build = await Bun.file(root + "/build.json").json();
    await Bun.write(root + "/case.json", JSON.stringify({
      schema: "deepscientist.math.public-example.v1", problem: bootstrap.problemId,
      sourceCommit: bootstrap.sourceCommit, buildManifestRef: build.buildManifestRef,
      model: "gpt-6.1-sol", effort: "xhigh", workers: 4,
      method: "direct", maxRunSeconds: 1800, maxTurns: 20,
      taskSha256: new Bun.CryptoHasher("sha256").update(await Bun.file(root + "/task.md").arrayBuffer()).digest("hex"),
      evaluator: "host-lean-kernel-all-targets", official: false
    }, null, 2) + "\n");
  ' "$case_root"
  if [[ ${MATH_EXAMPLE_SKIP_CACHE:-0} != 1 ]]; then
    (
      cd -- "$case_root/workspace/generated/imo2026_q1"
      lake exe cache get
    )
  fi
  echo "Prepared public case: $case_root/case.json"
  exit 0
fi

bun -e '
  const { resolveMathematicsLakePackagesCache } = await import("./src/math/verifier.ts");
  const { resolveMathematicsRuntimeEnvironment } = await import("./src/math/mathRuntimeEnvironment.ts");
  if (!resolveMathematicsLakePackagesCache(process.argv[1] + "/workspace/generated/imo2026_q1", resolveMathematicsRuntimeEnvironment())) {
    throw new Error("No compatible package cache. Run lake exe cache get in the prepared project, or configure its .lake/packages directory as a trusted cache.");
  }
' "$case_root"

manifest=$(bun -e 'console.log((await Bun.file(process.argv[1]).json()).buildManifestRef)' "$case_root/case.json")
args=(run --build-manifest "$manifest" --workspace "$case_root/workspace"
  --task-file "$case_root/task.md" --workers 4 --method direct
  --model gpt-6.1-sol --effort xhigh --max-run-seconds 1800 --max-turns 20
  --output "$case_root/result.json")
if [[ $mode == check ]]; then
  args+=(--startup-only)
  if [[ -f $case_root/result.json.runtime/state.json ]]; then args+=(--resume); fi
elif [[ $mode == resume ]]; then
  args+=(--resume)
fi
bun run math "${args[@]}"
