# Upstream Lean Packages

Use package discovery only when the missing capability is not present in the
target project's pinned Mathlib checkout. It is metadata discovery, not a
license to copy source, import a proof corpus, or mutate Lake dependencies.

## Authoritative metadata

- **Reservoir** (`https://reservoir.lean-lang.org`) is Lean and Lake's package
  registry. Its read-only v1 endpoints expose package metadata, registered
  versions, Lean toolchains, dependency revisions, and build results. The
  implementation was inspected at `leanprover/reservoir` commit
  `e097550bb4dcc37284e4e4e6cf9b683b0aeace1e` (Apache-2.0).
- **GitHub repository search** supplies discovery metadata only when
  `packageQueries` contains a domain query. Prefer an exact `owner/repository`
  query when the package is known. Query text is sent to GitHub; do not send a
  private statement or protected task content.
- **The target project** remains compatibility authority. Its `lean-toolchain`
  and the Mathlib revision in `lake-manifest.json` are compared with registered
  package versions. Discovery prefers the project's installed revision when it
  is registered; otherwise it selects a successfully built exact match before
  considering newer but incompatible revisions.

Remote discovery reads metadata only. It does not fetch Lean files or README
proof examples, and `dependencyMutationAllowed` is always `false`.

## Candidate states

- `eligible`: toolchain and available Mathlib revision match, a license is
  declared, and Reservoir built the registered revision on its own toolchain.
- `incompatible`: the target Lean toolchain or Mathlib revision differs.
- `license_review_required`: no usable license identifier is registered.
- `build_unverified`: the matching registered version has no successful
  Reservoir build.
- `compatibility_review_required`: the target or package lacks enough revision
  metadata for an exact comparison.

Even `eligible` means recommendation only. Adding a package requires explicit
authorization, an exact commit pin, review of imports and license, regeneration
of `lake-manifest.json`, and a clean target-project build.

Each candidate also reports local use state:

- `installed_exact` + `search_installed_package`: search its pinned local source.
- `installed_different_revision` + `keep_pinned_local_revision`: use the local
  revision and do not silently upgrade to the newer Registry candidate.
- `not_installed` + `request_dependency_approval`: request permission before
  changing Lake dependencies.
- Review or compatibility actions must be resolved before dependency changes.

## Using an installed package

After selecting an already-installed package, call `math_portfolio(get)` again
with its exact package or repository name in `installedPackageScopes` and one
narrow `installedPackageQuery`. Use a likely declaration name, type fragment,
constant, or short mathematical concept rather than the whole private problem.

The runtime verifies that the scope is present in `lake-manifest.json`, ranks
local source paths against the narrow query before applying its file and byte
budgets, reads `.lean` files under `.lake/packages`, and returns only declaration
headers. It uses a structured `lakefile.toml` `srcDir` when present and qualifies
ordinary declarations with their namespace. It excludes symlinks and paths
named tests, examples, benchmarks, Challenge, Solution, or Submission. Each
result supplies:

- the installed package revision;
- declaration name and header;
- `sourceModule`, which is the candidate import;
- project-relative source path;
- `importRequired: true` and `targetValidationRequired: true`.

Add only the candidate module import in an authorized solver file, then run
`#check` and a targeted build. If the search returns no lexical match, refine
the local query once; do not broaden it into an unbounded source dump.

## Maintained ecosystem snapshot

The following snapshot was checked against Reservoir on 2026-09-02. Treat it
as routing guidance; runtime metadata is newer and takes precedence.

| Area                   | Package                            | Registered toolchain | Reservoir state                       | Use                                                                              |
| ---------------------- | ---------------------------------- | -------------------- | ------------------------------------- | -------------------------------------------------------------------------------- |
| General mathematics    | `leanprover-community/mathlib`     | `v4.34.0-rc2`        | built and tested                      | First choice; search the pinned local revision before external packages.         |
| Automation             | `leanprover-community/aesop`       | `v4.34.0-rc2`        | built and tested                      | White-box proof search; normally already inherited through Mathlib.              |
| Automation             | `leanprover-community/Duper`       | `v4.33.0`            | matching version built                | First-order prover; require exact target compatibility.                          |
| Additive combinatorics | `leanprover-community/AddCombi`    | `v4.34.0-rc2`        | built                                 | Reusable Mathlib-aligned sublibrary.                                             |
| Additive combinatorics | `teorth/PFR`                       | `v4.34.0-rc2`        | built                                 | Deep PFR formalization; use only if its specialized API is needed.               |
| Additive combinatorics | `YaelDillies/APAP`                 | `v4.34.0-rc2`        | built                                 | Kelley-Meka/Roth-number results.                                                 |
| Combinatorics          | `YaelDillies/CamCombi`             | `v4.34.0-rc2`        | built                                 | Graph, extremal, and probabilistic combinatorics.                                |
| Harmonic analysis      | `fpvandoorn/carleson`              | `v4.34.0-rc2`        | built                                 | Carleson's theorem formalization.                                                |
| Physics                | `leanprover-community/Physlib`     | `v4.33.0`            | no matching successful build recorded | Current successor to PhysLean; inspect but do not auto-adopt.                    |
| Probability/statistics | `Lean-MoDS/StatsMLlib`             | `v4.33.0`            | built                                 | Probability, statistics, and learning theory.                                    |
| Mathematical logic     | `FormalizedFormalLogic/Foundation` | `v4.33.0`            | no matching successful build recorded | Broad logic formalization; compatibility review required.                        |
| Cryptography           | `Verified-zkEVM/VCVio`             | `v4.33.1`            | built                                 | Machine-checked cryptographic proof infrastructure.                              |
| Scientific computing   | `lecopivo/scilean`                 | `v4.28.0-rc1`        | matching build failed                 | Valuable scope, but its registered revision is not a current drop-in dependency. |
| Quantum information    | `Timeroot/quantumInfo`             | `v4.28.0`            | matching build failed                 | Inspect as a future candidate, not a current compatible default.                 |
| Mathematical finance   | `formal-applied-math/MathFin`      | `v4.32.0`            | no matching successful build recorded | Specialized candidate requiring manual compatibility work.                       |

`lean-dojo/LeanDojo-v2` and `ruc-ai4math/LeanStateSearch` are retrieval or
training infrastructure, not theorem libraries registered for direct Lake use.
They may inform a future local index adapter, but never present them as theorem
dependencies.

## Protected-source boundary

Do not use `packageQueries` or `installedPackageScopes` for LeanEval or another
protected benchmark. General repository search or whole-package local scanning
can expose benchmark mirrors, prior solutions, and evaluator material. The
runtime excludes obvious benchmark and solution-corpus metadata and risky local
paths, but those filters are defense in depth, not authorization. Protected
tasks remain limited to the approved Mathlib-only LeanSearch and Loogle indexes.

For ordinary projects, also reject benchmark datasets and statement corpora as
dependency sources. In particular, formal-conjecture collections, formal IMO
statement collections, miniF2F-derived corpora, LeanEuclid, evaluator artifacts,
and prior submissions are not reusable libraries.
