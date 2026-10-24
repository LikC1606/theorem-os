# Human edit queue recovery candidate

This isolated runtime preserves the existing 1 MiB human edit writer contract, including the newline, and makes oversized queue records recoverable. A rejected record is reported once; the durable discard cursor advances through its remaining bytes until the next newline. A JSON-looking trailing fragment cannot become a separate edit.

The selected baseline and the inspected Honeycomb runtime had byte-identical human edit intake, writer, and bounded delivery reader implementations. Both used a 16,000,000-byte delivery reader default; neither supplied human recovery state. This candidate reuses the existing worker discard implementation with a human-only byte bound. It does not reproduce or attribute the historical Snaky 64,000-byte incident to this baseline. Worker delivery limits remain 16,000,000 bytes and research notes remain 1,000,000 bytes.

Changed product files: `src/solver/deliveries.ts`, `src/solver/cooperationInputs.ts`, and `src/solver/humanEdit.ts`. The existing `tests/solverHumanEditRecovery.test.ts` adds seven behavior cases. `changes.patch` contains the complete source and test diff.

Validation passed: 85 focused tests in four files, TypeScript typecheck, the headless three-bundle build, and the actual `readMathBuildManifest` verifier. Legal 65,155-, 66,237-, and 1,048,576-byte records pass through the real writer and cooperative intake while retaining the unrelated assignment and recorded receipt. Oversized complete and partial records are rejected once, survive state resume, and permit the next complete edit. Receipt preservation uses mocked fixture receipts and is not a new Lean or mathematical acceptance result.

Build ID: `57d42932-8fa4-422c-9445-684ef0eb7a09`. Solver SHA256: `73b949a6b2b9a06880110ad56f5a862320e17cf8426577d4172809cdc8d5dd7d`.

The copied runtime uses independent ordinary files: 6,226 regular files checked, no shared inodes, symlinks, or multiple-link files. All 1,312 inventoried frozen baseline files remain unchanged. The new runtime is not active; this work made no model calls, Lean calls, SSE changes, active-chain changes, global configuration writes, commits, or pushes.

`delivery-files.json` lists the exact reviewable delivery. `SHA256SUMS` covers those files and the delivery manifest; run `sha256sum --check SHA256SUMS` from this directory. The complete runtime and dependencies are intentionally outside that explicit delivery list.
