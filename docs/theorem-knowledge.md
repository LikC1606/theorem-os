# Saved Theorem Knowledge

`theorem-os knowledge` makes previously checked proof work searchable without a
model, a running campaign, or an embedding service. Its JSON interface is callable
from an agent or a shell.

## Build a Catalog

```bash
bun bin/math.ts knowledge build \
  --state /PATH/previous-run/result.json.runtime/state.json \
  --state /PATH/another-run/result.json.runtime/state.json \
  --accepted-manifest accepted/accepted.json \
  --submitted-manifest submitted/submitted.json \
  --output /PATH/knowledge/catalog.json \
  --report /PATH/knowledge/import.json
```

Inputs are explicit. Run imports include both current tasks and historical task
versions; only recorded, unconditional kernel checks with matching task versions,
receipts and committed source bytes are eligible. Conditional, failed, stale,
unavailable and mismatched records are reported as skipped. Archived accepted and
locally verified submissions must match their recorded source hashes. Their
theorem/lemma declarations retain the submission's evidence category; each helper
is not a separate official result.

Declaration lookup prefers an exact qualified name over a colliding raw name.
An unqualified alias is usable only when it identifies one declaration; `_root_.`
requires the exact root name. Run imports bind receipts to that precise header.

The catalog retains complete types, explicit premises, available statement/proof
references, source and checked-projection commits, environment identities and
provenance. Closed helper task types are distinguished from source headers whose
variables and scopes require the complete archived file. Missing dependency
reports remain explicitly unavailable. Full allowed source files and Lean project
manifests are stored by content hash. `Solution.lean`, journals, sessions,
environment files and credentials are excluded.

Names alone do not identify a theorem. Different source contexts and environments
remain distinct versions. Identical source bytes are stored once. An incremental
build uses a new output path:

```bash
bun bin/math.ts knowledge build \
  --merge /PATH/knowledge/catalog-v1.json \
  --state /PATH/new-run/result.json.runtime/state.json \
  --output /PATH/knowledge/catalog-v2.json
```

Existing catalogs are never overwritten. The build result reports a SHA-256
digest, counts and an optional detailed skip report.

New builds default to the V2 format: a pinned metadata manifest and a sibling
`CATALOG_FILENAME.objects` directory containing complete source files by SHA-256.
Search and statistics validate metadata identities without opening every proof
file. A theorem lookup checks its declaration against the source; requested source
objects are checked by hash and byte count whenever read. Keep the manifest and
object directory together when moving a catalog. `originSha256` records ancestry;
the new manifest's own SHA-256 is the identity to pin.

V1 catalogs remain readable. Convert one without changing theorem IDs, contexts,
provenance or its original files:

```bash
bun bin/math.ts knowledge pack \
  --catalog /PATH/knowledge/catalog-v1.json \
  --sha256 ORIGINAL_CATALOG_SHA256 \
  --output /PATH/knowledge/catalog-v2.json
```

Packing fully verifies the old catalog before writing. `build --format v1` is
available for consumers that need the original single-file format.

## Search and Read

```bash
bun bin/math.ts knowledge stats --catalog /PATH/knowledge/catalog-v1.json

bun bin/math.ts knowledge search \
  --catalog /PATH/knowledge/catalog-v1.json \
  --sha256 CATALOG_SHA256 \
  --query 'density arithmetic progression' \
  --goal 'THE_EXACT_LEAN_GOAL_AND_LOCAL_CONTEXT' \
  --limit 5

bun bin/math.ts knowledge search \
  --catalog /PATH/knowledge/catalog-v2.json \
  --goal 'THE_EXACT_LEAN_GOAL_AND_LOCAL_CONTEXT' \
  --environment TARGET_ENVIRONMENT_DIGEST \
  --problem-receipt TARGET_PROBLEM_RECEIPT_DIGEST

bun bin/math.ts knowledge get \
  --catalog /PATH/knowledge/catalog-v1.json \
  --sha256 CATALOG_SHA256 --id THEOREM_ID

bun bin/math.ts knowledge get \
  --catalog /PATH/knowledge/catalog-v1.json \
  --sha256 CATALOG_SHA256 --id THEOREM_ID \
  --source Submission/Helpers.lean
```

Search ranks names, types, descriptions and recorded dependencies using lexical
matches and goal shape. Familiar mathematical notation is normalized to Lean type
names, and common namespace prefixes do not create broad matches. English request
and function words are excluded from lexical evidence. A small vocabulary bridge
also matches Lean's `pderiv` to `partial derivative` and `partial derivatives`,
while retaining the original identifier tokens, types and declarations. A goal may be
used without a keyword query. Up to eight `--query` arguments share
one loaded catalog and one prepared search index within the command. Within that
call, identical raw field text shares tokenization, with separate binder modes;
dependency fields and contextual versions remain distinct. No mutable index is
reused between separate calls. `--problem ID` restricts provenance. Results contain bounded
previews and stable IDs; `get` returns the exact type and declaration. Its file
list identifies complete archived context retrievable with `--source`.

`--environment` and `--problem-receipt` prefer matching contextual versions of an
already relevant theorem. Each version reports `match`, `different`, `unknown` or
`not-requested`. These labels describe recorded identities, not Lean applicability.
All versions remain accessible by ID, including versions with different premises
or dependency coverage.

Supported typed binders may receive an additional variable-independent surface
shape bonus. This is a ranking hint, not a claim of Lean equivalence or successful
application. Unsupported syntax falls back to lexical ranking; the original type
and source are always preserved.

## Read Bounded Source Excerpts

```bash
bun bin/math.ts knowledge source \
  --catalog /PATH/knowledge/catalog-v2.json \
  --sha256 CATALOG_SHA256 --id THEOREM_ID \
  --file Submission/Helpers.lean --name QUALIFIED_DECLARATION \
  --lines 80 --max-bytes 16000

bun bin/math.ts knowledge source \
  --catalog /PATH/knowledge/catalog-v2.json \
  --sha256 CATALOG_SHA256 --id THEOREM_ID \
  --file Submission/Helpers.lean --start-line 1 --lines 80

bun bin/math.ts knowledge source \
  --catalog /PATH/knowledge/catalog-v2.json \
  --sha256 CATALOG_SHA256 --id THEOREM_ID \
  --file Submission/Helpers.lean --offset NEXT_OFFSET
```

The source navigator reads any allowed file in the selected theorem's exact
archived context. Named lookup also locates definitions and helper declarations
that have no separate knowledge entry. It verifies the root declaration and
selected file bytes, and returns the source SHA, precise positions and truncation.
It does not search a different context when a declaration is missing.

Choose one of `--name`, `--start-line` or `--offset`. Line numbers start at one;
offsets count UTF-16 code units, with an exclusive end offset. All modes default to
80 lines and 16,000 output bytes, with limits of 200 lines and 65,536 bytes. The
byte budget includes the complete JSON response and its trailing newline.

Continue a truncated response with `--offset nextOffset` for exact, lossless
continuation, including very long Unicode lines. `nextStartLine` is only a location
hint and may repeat part of the last line. Named declaration completeness is
reported independently of context completeness. Every excerpt remains
`source-excerpt-not-complete-context`: namespaces, section variables, local
instances, definitions, attributes and notation may occur elsewhere in the file.
Inspect those ranges or retrieve the complete file with `get --source` before
adapting a source-header declaration.

## Inspect Recorded Dependencies

```bash
bun bin/math.ts knowledge dependencies \
  --catalog /PATH/knowledge/catalog-v2.json \
  --sha256 CATALOG_SHA256 --id THEOREM_ID --depth 2
```

The graph follows recorded statement/proof references only when the full source
context and environment agree. It never connects a different proof snapshot merely
because its theorem name matches. `indexed` references point to an unambiguous
entry; `source-available` references identify a complete archived file accessible
through `get --id SOURCE_THEOREM_ID --source FILE`. That label does not claim the
referenced definition was independently resolved. `ambiguous` and `missing-source`
remain explicit. Unavailable dependency reports mean unknown coverage.

Depth is 0..8; node, reference and version limits bound tool output and report
truncation. These are output limits, not solving time limits.

A search miss does not establish that no relevant theorem exists. These sources
are not automatically installed Lean declarations or standalone modules. Reuse
requires the matching namespace, definitions, instances, imports and hypotheses.
Adapt only the needed code into owned sources; do not replace the target problem
with an archived submission.

## Attach to a Future Run

Add `--knowledge-base /PATH/knowledge/catalog-v1.json` to an otherwise configured
`theorem-os run` command. Each worker receives the same read-only snapshot and
search/get/dependency instructions. V2 snapshots include independent read-only
copies of all source objects, retaining the exact manifest SHA. The run records its catalog digest; resume requires the
same digest. A changed catalog belongs to a new run.

Knowledge remains `recorded-not-replayed` with `requiresFreshCheck: true`.
Neither lookup nor import marks a task accepted, installs old receipts, or closes
an original goal. The existing independent Lean checks and official evaluator
remain responsible for acceptance. Building or searching a catalog never starts
or resumes a solving task.
