# In-Progress LeanEval Proofs

**Historical research snapshots captured on 2026-10-15 (UTC).** Each snapshot includes four agent worktrees. Dimitrov and Hopf–Rinow subsequently received official acceptance on 2026-10-16; their final proof packages are archived separately under [accepted](../accepted/). The files and capture-time metadata here remain unchanged. The public catalog displays their accepted proofs instead of these earlier drafts.

| Problem | Area | Snapshot status | Sources and research |
| --- | --- | --- | --- |
| Dimitrov lower bound for the house of an algebraic number | Algebraic number theory | In progress at capture; [final proof accepted](../accepted/dimitrov/) | [dimitrov](dimitrov/) |
| Hopf–Rinow theorem | Riemannian geometry | In progress at capture; [final proof accepted](../accepted/hopf_rinow/) | [hopf_rinow](hopf_rinow/) |
| Szemerédi's theorem | Additive combinatorics | In progress; not officially accepted | [szemeredi](szemeredi/) |

[snapshot.json](snapshot.json) records the original capture times and progress, rather than current solver status. Each problem contains:

- `workers/<agent>/`: current Lean sources, dependency pins, research notes, cooperation state, and delivery journals.
- `state.json`: the runtime checkpoint, including task states, existing verification receipts, failures, and cumulative usage.
- `manifest.json`: source provenance, worker metadata, and SHA-256 hashes of all archived files.
- `history.fast-export.gz`: historical proof and research revisions from the run's Git repository, filtered to these source files. The export includes `original-oid` metadata; importing it creates new commit IDs.
- `task*.md`: the original task and continuation instructions when present.

These drafts may contain `sorry`, failed approaches, and unchecked changes. Only the separately archived accepted packages have official acceptance. A local helper check does not establish that an entire problem is solved.

Solvers continued running during capture. Files are individually stable snapshots, but the checkpoint and worktrees can reflect nearby instants. Absolute paths in records refer to the original host. Runtime binaries, model conversations, credentials, environment files, and Lean caches are omitted.

To inspect the filtered history in a separate directory:

```sh
git init recovered
gzip -dc dimitrov/history.fast-export.gz | git -C recovered fast-import --force
git -C recovered branch -a
```

For Lean checks, use the matching original generated workspace and the dependency pins under each agent's project directory. The snapshots preserve research progress; they are not complete machine-independent runtime backups.
