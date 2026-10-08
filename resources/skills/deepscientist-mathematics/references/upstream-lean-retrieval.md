# Upstream Lean Retrieval

Use upstream retrieval only after the current project's import-closure search
misses. The runtime sends a query only when `upstreamQueries` explicitly names
a provider. This sends the exact query text to that public service; LeanSearch
states that it collects search terms. Do not send private statements or any
protected benchmark content that the runtime has not explicitly authorized.

## Sources

- **LeanSearch** (`https://leansearch.net/search`): natural-language retrieval
  over Mathlib declarations. The public API returns declaration metadata and
  may also return proof bodies; DeepScientist deliberately discards the proof
  body. The community client is
  `leanprover-community/LeanSearchClient` (Apache-2.0; inspected at commit
  `ba67e212be1197b84c1f1f6299488a10a3002713`).
- **Loogle** (`https://loogle.lean-lang.org/json`): structural retrieval by
  constant, declaration-name substring, type pattern, or conclusion pattern.
  Its upstream project is `nomeata/loogle` (Apache-2.0).
- **Mathlib source and docs**: declaration authority comes from the target
  project's pinned Mathlib checkout. Live documentation may describe a newer
  revision and is navigation only.

LeanSearch is appropriate for a mathematical description such as "a continuous
function on a compact set is bounded". Loogle is appropriate when the goal
already exposes a useful shape, constant, or probable name, for example
`ContinuousOn`, `"boundedVariation"`, or `|- _ < _ -> tsum _ < tsum _`.

## Acceptance Boundary

Treat every remote hit as an unverified premise candidate. Confirm its module is
available, add only an authorized import, run `#check` for the exact declaration,
and compile the target file. A remote rank, type string, documentation page, or
successful result in another Mathlib revision is not proof evidence.

For protected benchmarks, obey the runtime `remoteScope`. Query only these
Mathlib indexes. Never use general Web search, benchmark repositories, prior
submissions, evaluator artifacts, or reference solutions.
