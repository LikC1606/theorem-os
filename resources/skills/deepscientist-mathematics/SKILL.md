---
name: deepscientist-mathematics
description: Evidence-first mathematics research for conjecture discovery, formalization, proof search, counterexample construction, Lean verification, independent review, and Git-backed recovery. Use as the mathematics extension inside Science Mode when a result must be supported or refuted with reproducible evidence before it is reported as proved.
---

# DeepScientist Mathematics

This skill is an optional extension of Science Mode. It keeps the existing
Science Artifact, Science Report, project Git workspace, `math_portfolio`, and
Lean verification contracts. It does not introduce a second chat, memory
database, project repository, or MCP protocol.

The runtime id is `deepscientist-mathematics`; `deepscientist_math` is only the
human-facing shorthand.

## Non-negotiable contract

Treat a mathematical result as a scoped claim, not as a piece of persuasive
text. A conjecture is not proved or refuted because a model says so, because a
Lean file happens to compile, or because a search did not find a counterexample.

Keep these layers separate:

1. **Informal claim**: the user's question and intended meaning.
2. **Formal statement**: definitions, domains, quantifiers, assumptions, and
   the exact proposition checked by a proof assistant.
3. **Supporting evidence**: reproducible examples, calculations, literature,
   retrieved lemmas, experiments, or independent human/agent arguments.
4. **Refuting evidence**: a reproducible counterexample, failed obligation,
   inconsistent assumption, or a negation checked by the formal verifier within
   a declared scope.
5. **Kernel result**: a proof or refutation replayed from a frozen project
   revision with the declared toolchain.

Only a result whose scope, evidence, and verification boundary are explicit may
advance. Never silently turn bounded evidence into a universal claim.

## Canonical memory: Git first

Git is the only durable memory for mathematics work. Resume from the bound
project's committed tree, commit graph, and replay files, not from chat text,
an MCP process, a UI cache, or an Artifact projection alone.

- **Canonical**: committed project files, commit SHA, branch, checkpoint
  metadata, and replay manifests.
- **Projection**: `math_portfolio`, Science Artifact, Preview state, and
  conversation status rows. These must be rebuildable from canonical files.
- **Ephemeral**: model context, in-memory runs, uncommitted files, temporary
  stdout, and interrupted streams. Treat them as provisional or lost after a
  restart.

An uncommitted fact cannot support `Verified`, `Refuted`, or a final report.
The hidden Artifact Git ledger is provenance for Artifact state; it is not a
replacement for the source-project Git memory.

## Existing tool boundary

Use these tools only; do not invent another memory or orchestration tool.

- `project_workspace`: inspect status/frontier, manage approved branches, and
  create explicit checkpoints.
- `math_portfolio`: read its schema/starter template, validate without writing,
  and maintain the typed problem, attempt, example, verification, and review
  projection.
- `lean_workspace`: optional final-proof interface. Use it only after a
  discovery candidate enters formalization. Use one `execute` pipeline for
  public formula/Goal events plus certification, or one `certify` call with all
  independent theorem items. It is the only source of Lean kernel facts.
- `formal_verifier`: one-item Lean compatibility facade and the only trusted
  `official_compare` signer. Do not use it for new multi-theorem Lean work and
  never hand-author an official comparator receipt.
- `research_evidence`: retrieve external literature and source records.
- `science_artifact`: persist evidence, files, reports, and presentation;
  `research_roadmap`: validate and persist the typed goal/stage projection.
- `science_artifact(query_many|transact)`: read two or more independent records
  in one snapshot or atomically create/patch/replace a related batch. Reuse its
  receipts; do not follow it with status/get unless a conflict occurs.
- `user_input`: ask only a small, material scope or route question. In Codex,
  call `mcp__deepscientist_user_input__user_input` through the deferred tool
  namespace; never call native `request_user_input`.
- `report_chart`: validate and render a runtime-listed, evidence-bound native
  chart for the Science Report. Read `deepscientist-report-chart` first, use
  `describe` as the authority for available grammars, and normally call render
  once.
- Existing bounded command/file capabilities: run calculations, finite searches, or
  finite checks; save their command, scope, result, and Artifact links.

If a required capability is unavailable, return `blocked` or `unavailable`;
do not emulate it with prose.

## Runtime and routing preflight

Before intake:

1. Confirm the runtime prompt contains `Mathematical Research Extension` and
   the active skills contain `deepscientist-mathematics` and
   `deepscientist-report-chart`.
2. Confirm `project_workspace` and `math_portfolio` are discoverable before
   discovery. Confirm `lean_workspace` only when a candidate enters formal
   proof, and `report_chart` only before chart work. `formal_verifier` alone
   indicates an older compatible runtime, not the preferred batch surface.
3. Treat the authorized project as already created and bound by the runtime.
   Call `project_workspace` directly and normally omit identity arguments. A
   missing or mismatched binding is a runtime fault; do not create, initialize,
   reopen, migrate, guess, or replace a project, path, or id to bypass it.
4. Classify the entry state from actual project results. A retry envelope, Git
   repository, or initializer commit alone does not mean the task is a resume.
   Use `intake-audit` only when meaningful prior baselines, results, drafts,
   reviews, portfolio entries, or research checkpoints exist; otherwise begin
   fresh mathematical intake.
5. If Discovery Mode is active, treat it as the sole continuation controller.
   Do not call Codex `create_goal`, `get_goal`, or `update_goal`, and do not
   create a second Goal. If it is absent, do not infer one merely because the
   conjecture is difficult; only the user or runtime may enable it.

If preflight fails, name the missing mode, skill, or tool; do not silently route
mathematics into generic intake or baseline work.

## Durable state and evidence

For an ordinary solution, persist only facts needed to resume: the problem,
active candidate, eliminated routes, open bottleneck, and next action. Use the
existing `mathematics/portfolio.json`, problem, example, attempt, and formal
proof paths; never create every optional directory or file up front. Publication
compatibility paths remain `reports/<problem-id>.manifest.json` and
`figures/<figure-id>/{spec.json,caption.md,qa.json}`.

Bind evidence to the exact problem and, after formalization, `statementHash`.
Record scope, method, result, reproducibility, source or command, durable output,
and commit. Examples, calculations, literature, failed searches, and external
solvers are scoped evidence, never a universal proof. A reproducible witness
refutes its exact candidate; “no counterexample found” remains inconclusive.

For executable Lean attempts, call `math_research` with `action=record_search`
after each bounded compiler/probe result. Include the unchanged statement hash,
route fingerprint and revision, proof-state fingerprint, open goals, bounded
diagnostic, goal-count delta, and evidence references. The host computes the
diagnosis and `continue`/`pivot` decision; never claim a closed proof from a
local lemma, a model response, or a theorem card. A repeated route/proof-state
pair without progress is handed to a fresh critic and then requires a materially
different route proposal.

Before terminal verification or formal disproof, read
[references/formal-proving-evidence.md](references/formal-proving-evidence.md)
for the detailed evidence fields, replay boundary, and proof/negation rules.

## Two-lane model

Discovery and proof use the same project Git workspace but have different
acceptance rules.

The default solving path is intentionally short:

```text
UNDERSTAND -> SOLVE_LOOP -> ANSWER
                         -> optional FORMALIZE -> REVIEW -> OFFICIAL_VERIFY
```

Keep exactly one mainline bottleneck. Queue useful side findings without letting
them replace it. When the route is uncertain, ask fresh, independent
Researchers for structurally different route-candidate episodes, sized to the
available independent work.
Each episode proposes and runs its own cheapest decisive probe before returning
one survivor. Discard a refuted or structurally wrong route. Carry only the
strongest supported route or closest actionable gap into the next round, and
repair that same candidate instead of restarting the workflow. Formalization is
an optional terminal lane, not a prerequisite for solving or mathematical
discovery.

### Discovery lane

`understand -> propose/probe -> repair | discard -> answer`

- Write the problem brief, objects, domain, quantifiers, and source
  provenance before generating candidates.
- Maintain one minimal natural-language research contract: objective, known
  results, failed approaches, open obligations, the active bottleneck, and one
  next action. Do not require a Lean statement or proof DAG in this lane.
- Treat literature retrieval, examples, computation, counterexamples,
  natural-language proof steps, conjecture revision, and adversarial critique
  as peer discovery actions. Reuse one researcher when a route is already
  dominant; for a new or high-uncertainty problem, use a parallel Worker wave
  with distinct research functions, then synthesize once. Such actions
  may share the active route identity; require distinct route fingerprints
  only when the wave is explicitly comparing candidate routes.
- After a parallel research wave, synthesize the findings into one mainline
  decision and one next objective. Keep the individual evidence for audit,
  but do not launch one follow-up action per finding.
- Reuse the same Team Worker slot while repairing one candidate so its local
  reasoning context survives. Use a different slot for an adversarial Critic
  or an alternate route. Copy the runtime `session_continuation` contract into
  the next assignment and obey its required or forbidden target slots.
- Keep generated conjectures, numerical experiments, program candidates, and
  literature observations under `discovery/`, `examples/`, or an attempt
  directory. They are not proofs.
- Keep unpromoted ideas as lightweight conjecture or route text in the active
  research contract. Do not assign `candidateId` or `candidateHash` while they
  are still disposable discovery ideas.
- Run boundary, adversarial, finite, randomized, and negation checks before
  promoting a candidate.
- A reproducible witness immediately refutes that candidate. An unsuccessful
  search records `not_refuted_within_scope` and remains inconclusive.
- Promote only an explicitly selected candidate. At that boundary assign its
  stable `candidateId` and normalized `candidateHash`, retaining its assumptions.
  A localized gap stays on that candidate; a refutation or structural error
  starts a new route.

### Proof lane

`formalization -> attempt/compiler feedback/repair -> review -> official verification`

- Compare informal and formal statements side by side.
- Mark their relation `equivalent`, `stronger`, `weaker`, or `unknown`.
- If the relation is not `equivalent`, ask a choice-based user question or
  explicitly report the narrower scope; do not silently proceed.
- Keep each distinct proof strategy in a separate attempt. Within one strategy,
  use Lean/compiler feedback to repair the same candidate while the runtime
  returns `continue_node`; do not rebuild the route for a local gap.
- Count a stall only when a whole solver episode returns without progress, not
  for each compiler action inside it. Preserve the same candidate while a
  repair remains plausible; use a fresh adversarial Critic or an alternate
  route whenever the evidence shows that it can change the next action.
- Keep a route as one whole candidate or the shortest useful linear plan. Build
  a branching lemma DAG only when multiple independent obligations can actually
  be worked in parallel.
- Only a matching named-theorem
  `claim + targetCommit + statementHash + proofHash + theoremDeclarationHash`
  receipt generated by `lean_workspace` certification can support kernel
  verification. `statementHash` is the portfolio's caller-supplied statement
  identity; the declaration hash comes from the committed Lean source. The
  independent review must confirm that the named declaration formalizes that
  statement or its normalized negation.
  Use `claim=statement` for proof and `claim=negation` for formal disproof.
- Reviewers work from a frozen commit. Any changed assumption, import,
  statement, or toolchain invalidates downstream verification and review. The
  independent Reviewer reads `math_portfolio(get)`, audits the existing kernel
  receipt, statement meaning, assumptions, and proof gaps, but does not rerun
  Lean. The official comparator owns the final independent machine execution.

## Own missing formal infrastructure

Treat a missing library theorem, high-level API, construction, endpoint lemma,
or domain abstraction as an open proof dependency whenever Lean runs and the
authorized proof files are writable. Do not return `blocked` or `inconclusive`
merely because Mathlib does not already expose the desired result or because
the dependency chain is large.

For an explicit formalization task:

1. Inspect the local goal, imports, and relevant local library source.
2. Query `math_portfolio(get)` with the live goal, source file, and imports.
   If local retrieval misses and the runtime authorizes it, add an explicit
   `upstreamQueries.leansearch` natural-language query or
   `upstreamQueries.loogle` type/name pattern. Read
   [references/upstream-lean-retrieval.md](references/upstream-lean-retrieval.md)
   for source scope and compatibility rules.
3. If a project has a genuine dependency-level gap,
   add one to three explicit `packageQueries`. Prefer exact
   `owner/repository` identifiers; use a domain query only for discovery. Read
   [references/upstream-lean-packages.md](references/upstream-lean-packages.md)
   before acting on the returned Reservoir metadata. For LeanEval or another
   protected benchmark, package search is reference-only and must exclude the
   benchmark repository, submissions, solution branches, competition pull
   requests, answer repositories, comparator output, and evaluator material.
   Public papers and unrelated Lean packages remain available through this
   source firewall.
   Follow the returned `usageAction`. If it names an already-installed package,
   issue one later `get` with that exact `installedPackageScopes` entry and a
   narrow `installedPackageQuery` built from the live type, constant, or likely
   declaration name. The Registry lookup prefers the project's pinned revision
   when registered and otherwise prefers a built exact-compatible historical
   version over an incompatible latest version. Keep an installed different
   revision pinned; do not replace it with the Registry head. If it requests
   dependency approval, stop before editing Lake files and obtain explicit
   authorization.
4. For an installed-package hit, add only the returned `sourceModule` import in
   an authorized solver file, then `#check` the returned fully qualified
   `declarationName` and compile the target. An explicit installed-package or
   upstream lookup reserves one slot in the compact premise pack, so inspect it
   even when retained local premises also appear. The local index discards proof
   bodies and does not prove that an import is sufficient.
   If an installed-package search reports `status: ok` with zero results, refine
   at most twice: first query the exact identifier or type head, then use two or
   three domain and conclusion tokens likely to occur in a module path or
   declaration header. A bounded zero-result scan is not evidence that the
   package lacks the theorem.
5. Validate every remote declaration against the current imports and toolchain;
   never reuse a proof body returned by a premise search or treat a search rank
   as evidence. Source from a public Lean package may be ported only when its
   exact repository, commit, license, compatibility class, and minimal adopted
   declarations are recorded. A fixed-dependency benchmark must vendor that
   minimal source under solver-owned paths and replay it with the pinned
   toolchain.
   Treat package status as a recommendation only: do not edit Lake dependencies
   without explicit authorization, and require an exact commit pin plus a clean
   target build after any authorized addition.
6. Turn the remaining gap into a hierarchical dependency graph rooted at the
   requested declaration. Keep the top-level route stable; expand an oversized
   milestone into child nodes instead of pretending the whole foundation is one
   lemma or abandoning the route.
7. Select the dependency-ready helper with the best expected return:
   downstream value times next-episode success probability divided by estimated
   effort.
8. Implement it without placeholders in the authorized solver files and run a
   targeted compile at that semantic boundary.
9. Retain every compatible compiling helper, record the exact command and first
   remaining error or goal, and continue from the next dependency.
10. Re-decompose when the missing layer is genuinely independent or too large
    for the current hierarchy. Use in-place node expansion for a large but
    route-preserving dependency; do not replace construction with a blocker report.

An unfinished solver episode must leave a compiled helper, a strictly smaller
goal or later compiler error, a formal route refutation, or an exact external
runtime failure. A list of absent APIs is diagnosis only and cannot be the
episode result. Classify only a toolchain or required verifier service that
cannot run, an unwritable or unauthorized proof workspace, or an enforced
kernel policy that makes the required construction impossible as infrastructure
failure.

Every compiled helper must receive a runtime-bound helper receipt containing
its parent plan node, declaration identity and type, source file, imports,
proof/declaration hashes, pinned commit, source provenance, and kernel result.
The next assignment must reconstruct the expanded frontier and retain the helper
without asking a Worker to repeat it.

## Formal task feasibility preflight

Before committing a long-horizon run to one formal benchmark task, build a
feasibility profile from accepted-credit status, import-closure coverage,
available literature, related public formalizations, definition surface,
estimated missing-foundation depth, formal-degeneracy probes, and the cost of
the first compilable milestone. Rank candidates by calibrated solve score, not
hole count or statement length. A zero-credit task with no reachable first
milestone remains low probability even when its public statement is short.

The shared intake helpers `buildMathFeasibilityProfile` and
`rankMathFeasibilityCandidates` are deterministic and do not persist a second
task index. `acceptedCreditCount` and `holeCount` are non-negative integer
counts; `importCoverage`, `literatureAvailability`,
`relatedFormalizationAvailability`, `definitionSurface`,
`missingFoundationDepth`, `formalDegeneracyPotential`, `firstMilestoneCost`,
and `toolchainCompatibility` are calibrated values in `[0,1]`. The profile
returns a bounded solve probability, an explicit `zeroCredit` flag, major risk
codes, and one reachable first milestone. Credit and hole counts are deliberately
low-weight signals so a short statement cannot outrank a task with no viable
formal foundation.

When several candidates are being tracked in `math_portfolio`, store these
signals under each problem's optional `feasibility` field and call `get` to
receive the derived `feasibilityRanking`. The ranking is advisory intake state;
it never replaces the frozen problem contract, Lean receipt, review, or official
benchmark gate.

For protected benchmarks, never inspect a reference solution or evaluator-only
artifact. Work only in the declared solver-owned paths, use targeted local
builds during construction, and leave the official comparator to the final
unchanged reviewed revision. Avoid interactive commands that wait on standard
input; compile named files or targets instead.

## Resume and persistence

Use the injected project summary when current; otherwise read project status
once. On a real resume, load only the active problem, candidate, latest result,
relevant negative evidence, and next action. Reuse matching completed work and
never poll or rebuild a fresh initializer repository.

Write the factual result first, then update `math_portfolio` once. Checkpoint
only a decision-changing result or a long-running recovery boundary, never each
proof turn. A dirty or hash-mismatched tree is provisional and must not be reset,
cleaned, force-switched, or silently repaired.

## Long-horizon stage loop

For an explicitly long-running investigation, use one `research_roadmap` with a
global evidence-backed `completionContract`. Ordinary problem solving needs only
the active research contract and one bottleneck; do not create roadmap nodes,
stage artifacts, or checkpoints merely to advance a short proof round.

Close each stage as `supported`, `refuted`, `exhausted`, `inconclusive`, or
`runtime_failed`. Record supporting/refuting evidence ids, the changed belief,
reflection, and the next objective in both the route outcome and checkpoint
receipt. A rigorous negative result is progress; tool/runtime failure is not
mathematical refutation and does not require a fabricated source checkpoint. If
no evidence changed, change the premise, region, strategy, tool, or verification
condition before retrying.

Before ending the overall task, audit every requirement of the persistent
objective against current authoritative evidence. Continue while the next stage
still has information gain; pause only for an explicit user request, a verified
result, or an external runtime blocker after solver-owned construction routes
have been exhausted. Missing formal library infrastructure is not such a
blocker.

### Mathematics Team runtime boundary

When Mathematics Team Mode is active, obey its runtime-injected role profile and
the result contract returned by `research_team(action="describe")`; do not
reconstruct Team stages, dispatch, result fields, recovery, or review protocol
from this Skill. This Skill governs only the shared evidence, Git/portfolio/Lean,
formal-verification, and publication boundaries.

## Formalization gate

Formalize only a mature candidate or an explicit user request. Record objects,
domains, quantifiers, assumptions, edge cases, and whether the task is proof,
construction, classification, value, or disproof. Compare the informal and Lean
statements before proof work. Ambiguous readings require a user choice; never
silently prove a narrower claim. Compute identity from the normalized formal
statement.

Start with a direct whole-problem candidate even when `FAST_CHECK` does not
recommend it; that field is advisory. Expand a route DAG only after the direct
candidate fails structurally or runtime progress control requests replanning.

## Supporting and refuting evidence SOP

Before expensive proof search:

1. Test the smallest legal values and all boundary cases that can change the
   truth value.
2. Test equality, zero/one/negative, repeated, extremal, limiting, symmetric,
   and degenerate cases where meaningful.
3. Run bounded exhaustive checks for finite domains with explicit bounds, then
   seeded random or adversarial generation with a saved seed and generator revision.
4. Preserve both positive observations and failed tests; the latter help
   future Agents avoid repeating the same search.

When a witness is found, minimize it, rerun it independently, record the exact
assumptions and command, and stop searching for a proof of the same statement.
If the witness violates a hidden assumption, update the statement hash and
start a new candidate rather than silently deleting the witness.

## Proof search SOP

When the route is uncertain, generate short plans in fresh independent sessions
before expanding one:

- direct library lemma or simplification;
- induction or strong induction;
- contradiction or contrapositive;
- invariant, monovariant, or extremal principle;
- algebraic normalization, arithmetic automation, or finite decision;
- construction plus uniqueness, or a domain-specific geometry/combinatorics route.

Probe the decisive step of each route in parallel. Keep a supported route or the
closest route with an actionable gap; discard a refuted or structurally wrong
route. Search cheap tactics before model expansion. Retrieve existing
declarations and record names, namespaces, imports, query, and source revision
in the attempt. Use compiler errors as structured feedback and repair the same
candidate with a new action or premise. Stronger premises or a simpler verified
connection can justify revising local decomposition before the old route is
refuted. Propose main-route changes to the Lead and retain the current route
until the exact proposal is accepted by the bound assignment adapter. Continue
in the same Worker and worktree when that adapter supports in-place revision;
an unsupported adapter must report the limitation instead of changing bindings.

Literature search is supporting evidence, not an intake prerequisite. Run
targeted searches, inspect results, and narrow the query as the evidence changes.
For PaperClip full text, search the relevant source first and read the returned
`virtualPath` or an explicit `cat` command. Do not pass an external URL to the
PaperClip read action; keep that URL only as citation metadata.
Multi-Agent work may parallelize intake and literature search when tasks are
partitioned by source set, theorem family, or audit question. Assign one
coordinator to deduplicate claims, reconcile assumptions, and write canonical
portfolio state. Require source refs and scope; do not launch duplicate broad queries.
Use an independent reviewer at the verification gate when available. Every
handoff includes problem and attempt ids, hashes, commit, paths, evidence refs,
and the requested action.

Before any proof-producing `FORMALIZE` or `REVIEW` wave, run the typed
mathematics workflow preflight: immutable problem contract, completed FAST_CHECK,
exact statement alignment, frozen route (or an explicitly direct attempt), and
the active proof node/LOCAL_GATE receipt required by the stage. A failed
preflight is a blocker, not a prompt to infer missing state from prose.

## Verification and replay SOP

The formalizer produces one local kernel receipt for the frozen candidate; the
Reviewer audits it without Lean execution. After a sound review, read
[references/formal-proving-evidence.md](references/formal-proving-evidence.md),
then run the official comparator once on the unchanged commit. Do not add a
Reviewer replay or a second local certification. Only verifier-generated events
may claim `kernel_verified`. Missing toolchain, identity, clean boundary, or
receipt means `blocked` or `unavailable`.

## Independent review SOP

The reviewer must:

1. Re-read the informal and formal statements without trusting the proposer.
2. Check assumptions, quantifier order, vacuity, coercions, and definitions.
3. Try to refute using the saved examples and new boundary cases; require either
   a replayable witness checker or a `claim=negation` kernel receipt.
4. Audit the existing local kernel receipt, imports, generated files, axioms,
   stale paths, and replay metadata without rerunning Lean.
5. Return one verdict: `passed`, `changes_requested`, `refuted`, or
   `inconclusive`.

For a review that can advance, bind `mathReview` to the supplied LOCAL_GATE
receipt. A diagnostic replay is optional, never required. Every `evidenceRefs`
entry must resolve to the frozen receipt, a committed portfolio evidence id, or
a Science evidence id.

Record concise findings, evidence ids, commands, and file/line anchors. Do not
record hidden chain-of-thought. If any formal input changes, mark the review
stale and return to formalization.

Return material findings in machine-readable form with `severity` (`blocker`,
`major`, `minor`, or `note`), a mathematics-specific `kind`, concise message,
optional repair target, and evidence refs. `blocker` and `major` findings must
keep the candidate from advancing. This adapts Humanize's severity-driven
repair loop while preserving the Lean kernel, statement, commit, and official
verification gates above.

The reviewer must also reconcile the evidence balance: confirm that supporting
and refuting records refer to the same normalized statement, distinguish “not
found” from “false”, and ensure the terminal disposition names the decisive
lane. A review that checks only the proof file but not the counterexample search
is incomplete.

## Failure codes and recovery

Resume from the last matching candidate and reuse valid results. A local gap
repairs the same candidate; a refuted or structurally wrong route starts a child
attempt; infrastructure failures retry the environment without counting as
mathematical failure. Avoid repeating identical input, action, or proof state
unless it is part of a meaningful repair. Changed statements, assumptions, imports, or toolchains invalidate
downstream verification and review.

## Report assembly and publication gate

For an ordinary solution, answer directly with the argument, limitations, and
next unresolved obligation. Read
[references/reporting-and-figures.md](references/reporting-and-figures.md) only
before drafting a publication-style report, contest submission, mathematical
paper, or evidence-bearing figure.
It defines the report matrix, task-specific visuals, figure QA, manifest, and
publication sequence.

The reference owns report structure, `artifact_embed`, evidence balance, figure
QA, and publication sequencing. Use `report_chart(action="render")` only for a
decision-bearing standard chart. A report may be terminal only when its
`reports/<problem-id>.manifest.json`, applicable
`figures/<figure-id>/{spec.json,caption.md,qa.json}`, portfolio, receipt, review,
statement hash, and commit agree; otherwise publish it as provisional.

## Search continuity

Do not impose a small global deadline, attempt count, validation count, or
repeated-diagnostic cutoff on an explicitly multi-hour investigation. At every
meaningful route change, checkpoint the evidence delta and reflection, then
continue with the best available premise set, search lane, counterexample
region, proof strategy, or verification condition. Repeating a diagnostic is
allowed when it is part of a mathematically meaningful repair.

## Final status contract

Use exactly one final disposition:

- **Verified**: formal statement, supporting proof, exact hashes, replay, and
  passed review are present.
- **Refuted**: the immutable contract's canonical negation has matching Lean
  kernel and signed official-comparator receipts. Counterexamples alone remain
  scoped evidence.
- **Candidate**: a scoped supporting result or incomplete proof exists.
- **Inconclusive**: evidence is mixed, bounded, unavailable, or review disagrees.

Never call an informal argument proved without matching verifier and evidence gates.
