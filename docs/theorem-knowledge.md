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

## Enrich Archived Interfaces

Only an explicit enrichment operation invokes Lean. It uses a disposable copy of
the complete archived proofs and an already installed, matching pinned toolchain:

```bash
bun bin/math.ts knowledge enrich \
  --accepted-manifest accepted/accepted.json --problem PROBLEM_ID \
  --output /PATH/knowledge/accepted-enrichment.json

bun bin/math.ts knowledge build \
  --accepted-manifest accepted/accepted.json \
  --accepted-enrichment /PATH/knowledge/accepted-enrichment.json \
  --output /PATH/knowledge/enriched-catalog.json
```

Use `--submitted-manifest` and `--submitted-enrichment` for locally verified
archives whose official result remains pending. An enrichment snapshot may cover
one problem in a larger manifest. Other problems and missing roots retain unknown
coverage. Enrichment has no time limit and responds to cancellation. It does not
install toolchains, replace unavailable versions, invoke a model or run a solver.
External package dependencies require the existing frozen proof environment;
mutable packages cannot establish a reusable environment identity.

The independent, immutable sidecar binds the original manifest bytes, archive
record, source commit, every source and configuration file, actual tools and
environment, collector version and complete query templates. It embeds the exact
queries, full type exports, statement contexts and diagnostic artifacts with
their hashes. Explicit mismatches are rejected. Ordinary builds and searches do
not compile archives, and importing a sidecar does not need its old compiler.

Successful collection adds an `elaboration` field with the full Lean type,
universe parameters, available statement context, explicit omissions and
collection identities. The proof-aware full type is checked by elaborating it
back in the recorded environment. The original `type` and `source-header` remain
intact. Inspect the complete addition with `get --metadata --field elaboration`,
following `nextOffset` until `truncated:false` and parsing the joined JSON. A
failed or unavailable collection never becomes an empty dependency report.
This information remains historical and advisory; it creates no M2 or S3 receipt.

Collector v3 exports fully explicit proof-aware types up to 2,000,000 bytes with
the same Lean round-trip equivalence check. This is an offline storage limit;
search previews and model context budgets keep their existing bounds. Collector
v1 and v2 retain their exact generators and 24,000 / 256,000 byte limits. The readable statement
context keeps its existing limits; an oversized readable type is recorded as an
omission without discarding a successfully round-tripped full type or references.
Other Lean compilation and type-export errors still fail collection. Explicit reference collection allows up to
4,096 references per closure, 256,000 report bytes and 2,000,000 distinct visited
constants. Unavailable references retain their specific traversal, count, byte or
missing-proof reason. These limits apply to archive enrichment; ordinary solver
diagnostics keep their existing bounds. Readers validate each known collector's
exact generator identity, so existing v1 and v2 sidecars remain readable without Lean.

Retry only failed, unavailable or missing roots in a validated earlier snapshot:

```bash
bun bin/math.ts knowledge enrich \
  --accepted-manifest accepted/accepted.json --problem PROBLEM_ID \
  --retry-enrichment /PATH/knowledge/accepted-enrichment.json \
  --output /PATH/knowledge/retry-enrichment.json
```

The retry validates the previous manifest, complete record binding and toolchain
before invoking Lean. It preserves the original query indices and writes a new
sidecar containing only the selected collection results. Successful roots in the
previous snapshot are skipped. A retry with no remaining roots fails before Lean.
Both sidecars remain independent historical evidence; the retry snapshot alone
does not include successful results from the previous snapshot.

If a published proof snapshot omits an official baseline dependency, reconstruct
an independent archive and manifest from the pinned official bytes before
collecting. Retain the original manifest, source hashes and baseline provenance
alongside the restored projection. Adding an unverified earlier workspace copy
does not establish its identity as an accepted dependency.

## Inspect Historical Consumers

```bash
bun bin/math.ts knowledge consumers \
  --catalog /PATH/knowledge/enriched-catalog.json --sha256 CATALOG_SHA256 \
  --id THEOREM_ID --limit 8 --max-bytes 16000
```

Search hits include this reading handle. Consumers reverse recorded references
only within the same complete source context and a known, identical environment,
matching the exact file and qualified declaration name. Statement and proof uses
are reported separately. These edges describe local transitive reference closures;
they do not record direct application arguments or establish applicability in a
new problem. An empty list is not evidence that no useful consumer exists.

Each row includes complete small interfaces or explicit previews, hashes and
metadata continuations for its type, premises and elaboration. Source and context
handles locate the corresponding proof and project files. The complete JSON
response, including its newline, respects `--max-bytes`; `nextOffset` continues
with `--offset N`. Offsets count consumer rows in this command, rather than text
code units. Read the consumer's complete premises and source before adapting the
application, then check its remaining goals in the current problem with Lean.

## Advisory Route Memory

Import recorded research separately from checked theorems with an explicit option:

```bash
bun bin/math.ts knowledge build \
  --include-findings --state /PATH/old-run/result.json.runtime/state.json \
  --output /PATH/knowledge/catalog-with-findings.json

bun bin/math.ts knowledge search \
  --catalog /PATH/knowledge/catalog-with-findings.json --sha256 CATALOG_SHA256 \
  --include-findings --query 'density counterexample' --goal 'EXACT_LEAN_TYPE'

bun bin/math.ts knowledge finding \
  --catalog /PATH/knowledge/catalog-with-findings.json --sha256 CATALOG_SHA256 \
  --id FINDING_ID --max-bytes 16000
```

The importer verifies task and dependency versions, the finding digest and the
complete journal at its fixed delivery commit. Private sources and dependencies
are excluded by default. Records preserve exact contracts, assumptions, blockers,
remaining inputs, evidence and reconsideration conditions. Task names do not enter
the mathematical scope digest. Lexical recall never establishes equal hypotheses;
even a recorded claim of a Lean counterexample remains advisory until rechecked.

Finding reads return exact JSON text pages. Continue with `--offset nextOffset`,
join the text and verify its digest before parsing the full record. V1 and V2
catalogs preserve these records without adding them to checked theorem entries or
installing their historical sources. A finding cannot grant acceptance or park a
current task. Attached catalogs may contribute at most two finding hints per
target, sharing the existing 4 KiB context allowance.

Within one context build, route searches for distinct goals prepare the recorded
statements and summary terms once. Each request keeps its complete raw goal and
independent ranking; exact matches include source and dependency statements.
Environment and receipt matches remain annotations. Repeated requests return
independent result objects, and later calls read the metadata again.

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

Prepare a new run with a new result path instead of changing an existing run's
checkpoint. Given an already prepared problem workspace and task file:

```bash
bun bin/math.ts run \
  --build-manifest /PATH/current-build/manifest.json \
  --workspace /PATH/problem-workspace \
  --task-file /PATH/task.md \
  --knowledge-base /PATH/knowledge/catalog-v2.json \
  --workers 4 \
  --max-run-seconds 0 --max-turns 0 --max-turn-seconds 0 \
  --evaluator-timeout-seconds 0 \
  --output /PATH/new-run-with-knowledge/result.json \
  --startup-only

bun bin/math.ts inspect \
  --run /PATH/new-run-with-knowledge/result.json --format json
```

`--startup-only` validates preparation and creates pinned worker snapshots without
calling the model or starting proof search. Inspection exposes the pinned catalog
SHA as `configuration.knowledgeDigest`. Starting proof search is a separate step
using the same arguments with `--resume` and without `--startup-only`.

Inspection also exposes `knowledge.status`, retrieval coverage and the exact
candidate / finding IDs selected for each consumer, including sections omitted
by the context budget. The checkpoint retains 128 retrieval observations and a
dropped count; full observations are emitted as events. Old checkpoints without
these observations have unknown coverage, rather than zero inferred lookups.

`compare --phase prepare` and `sample-putnam --phase prepare` also accept
`--knowledge-base FILE`. They freeze the catalog, its source objects, digest and
`--knowledge-mode transfer|recovery` in the experiment plan and pass the frozen
snapshot to every launch. The default `transfer` mode rejects recorded target
problem provenance, target entry names, target declarations in archived source
payloads and same-problem findings. This checks recorded identities, not
mathematical equivalence. Use `recovery` for intentionally reusing the target's
own history. Resume and report use the saved plan and reject changed snapshots.

Each matching, knowledge-enabled comparison run reports a `knowledgeFunnel`:
returned search hits, rendered candidates, included context, model selections,
application checks and exact original-consumer closure. Checked references and
elaborated applications remain separate; a completed helper does not close an
original goal. Missing, truncated and legacy observations retain their coverage
limits; unavailable search counts are `null`, while a recorded empty hit list is
zero. Disabled or identity-mismatched runs have no funnel. These observations do
not establish that knowledge caused a proof or cost improvement.

A worker may report a saved theorem it tried in its normal RESEARCH.md JSON:

```json
{"knowledgeUses":[{"id":"THEOREM_ID","catalogDigest":"PINNED_SHA256","declaration":{"name":"Current.adaptedHelper","file":"Submission.lean"}}]}
```

Valid claims are `reported-attempt`. A successful fixed check upgrades a claim to
`checked-reference` only when that consumer's proof actually references the exact
current declaration and file. The origin remains `model-reported-origin`; this
does not prove historical authorship or current proof acceptance. Invalid claims
are rejected telemetry and cannot reject an otherwise valid proof. Original-goal
observations retain at most 256 records; task deliveries keep their own observations.

For a specific adaptation, add an optional `application` to that same use:

```json
{"knowledgeUses":[{"id":"THEOREM_ID","catalogDigest":"PINNED_SHA256","declaration":{"name":"Current.adaptedHelper","file":"Submission.lean"},"application":{"expression":"Current.adaptedHelper","expectedType":"forall (n : Nat), n + 0 = 0 + n","context":{"file":"Submission.lean","declaration":"Current.consumer"},"adaptationSteps":["Instantiate the saved result for the current variables"],"remainingGoals":[],"reconsiderWhen":["The current premises or source change"]}}]}
```

Use the actual closed expression, expected type and assigned context. Optional
`arguments` entries have `parameter` and `value`; `additionalPremises`,
`typeclassIssues`, `adaptationSteps`, `remainingGoals` and `reconsiderWhen` are
lists of notes. The host checks at most four new selected applications per
publication in a proof-erased disposable context, recording `elaborated`,
`failed` or `unavailable` and whether the selected declaration was actually used.
The model cannot supply the host's `check`. Invalid optional reports do not
reject a legitimate proof or reference claim.

Application elaboration has authority `advisory-application-elaboration`: local
declared results may be assumptions, so success checks the reported application
under those interfaces. It does not prove them or close the consumer. Reuse
requires the exact catalog, report, consumer contract, submitted sources, complete
import/configuration closure, tools, frozen environment and intact diagnostic
artifacts. Changed inputs require a new check. M4 can recall up to four scoped
experiences with bounded previews and full local
`.lake/knowledge-applications/<digest>.json` handles. Failures retain their scope
and retry conditions instead of excluding a theorem permanently. Historical
`knowledge consumers` reference closures remain a separate source of evidence.

Knowledge remains `recorded-not-replayed` with `requiresFreshCheck: true`.
Neither lookup nor import marks a task accepted, installs old receipts, or closes
an original goal. The existing independent Lean checks and official evaluator
remain responsible for acceptance. Building or searching a catalog never starts
or resumes a solving task.

## Candidates for the Current Assignment

When a run attaches a catalog, M4 also searches its already validated metadata
before dispatching proof work. A lemma assignment uses its complete closed Lean
type. An original goal uses its frozen source header, including declared binders,
instead of a type supplied by the planner. Research assignments search their
objective. Lead planning searches unresolved original-goal frontier tasks, placing
the evidence-ranked preferred route first and using the current environment when
reading recorded checks. Other active frontiers retain their existing order in
the remaining slots. Residual diagnostic consumers use the same target selection.
Initial planning uses the frozen original targets.

If the current worker has complete Lean JSON diagnostics for one of those exact
consumers, M4 first searches its full residual goal, including local hypotheses.
It rechecks the complete local import closure, project configuration, sealed
dependency identity and actual Lean tools before reading a goal. Only normal
compiler exits with complete, hash-matched raw output are eligible. File positions
must identify a unique qualified declaration and current task version. Missing,
stale, interrupted, truncated or ambiguous diagnostics fall back to the task type,
frozen source header or research objective above.

Each accepted diagnostic is at most 16,000 bytes. Independent residuals and cases
form separate queries; supported local declarations are closed with binders only
for retrieval, while the original diagnostic stays intact. Unsupported syntax
uses an explicit fallback. Stable ordering and round-robin allocation across
consumers share at most eight search requests. The diagnostic reader retains at
most eight matching messages and records how many additional messages it omitted.
Candidate packets retain their existing 4 KiB limit. Retrieval observations
record `searchSource: residual-goal`, each case's searched/omitted status, reader
omissions and exact diagnostic, source, environment and tool identities, even
when prompt budget omits the hint. `searchCandidateIds` records returned hits
before packet limits; `candidateIds` records those actually rendered.
The worker-writable `.lake/lean-diagnostics-latest.json` and its raw artifacts
remain advisory and cannot supply proof acceptance or reopen a closed obligation.

The host considers at most three targets and three candidates per target. Each
target's hint section is at most 4 KiB; excess candidates are removed whole and
counted. An oversized query is explicitly reported as not searched, rather than
truncating its mathematical input. These are retrieval and context limits, not
solving deadlines. The normal context manifest records sections omitted for prompt
budget, while exact current interfaces and assumptions remain mandatory.

The theorem searches in one context build share catalog preparation. Each target
keeps its complete query and goal, including local hypotheses, and receives the
same ranking as an independent search. Repeated requests return independent
result objects. The prepared corpus is discarded after the call, so later calls
observe current metadata; empty and oversized targets retain their own explicit
not-searched records.

Hints bind the catalog digest, current consumer and search-input digest. They show
bounded type previews, dependency coverage and recorded environment compatibility.
Retrieve the full type, all premises and archived context using the pinned
`knowledge get`, `source` and `dependencies` commands before adapting a candidate.
The host reuses catalog metadata already loaded for the run; constructing hints
does not read archived source objects or include historical proof bodies or receipts.

Fixed-candidate review, blind translation and statement comparison receive no such
candidate hints. All matches remain advisory and require fresh checking in the
current problem. A search miss is not evidence that no useful theorem exists.

## Bounded Metadata Reads

Use `knowledge get --metadata --max-bytes 16000` with the same pinned catalog,
SHA and theorem ID. The response omits the proof body and fits the complete JSON
and trailing newline within the requested byte allowance. Each metadata field is
either complete or has an exact continuation handle. The original `get` and
`get --source` outputs remain available for explicit full reads.

For a deferred field, add `--field type --offset 0` (or the field named in its
handle), then continue at `nextOffset`. Offsets use UTF-16 code units and never
split a surrogate pair. Concatenate field pages and check their SHA; JSON fields,
including premises, dependencies, provenance, related versions and file lists,
can then be parsed without losing entries. A type preview never replaces its
complete mathematical interface. Source-header types additionally need their
archived Lean context; use the existing bounded `knowledge source` excerpts.

Exact-interface search uses the same name, type and type-kind identity for its
IDF corpus and displayed groups. Adding proof variants of an unchanged interface
does not increase its document count or dilute other interfaces' keyword scores.
Declaration, context, version and environment identities remain distinct, and
all reuse still requires a fresh Lean check.
