# CharacterVarieties fresh native attempt

This directory prepares the original frozen `CharacterVarietiesAllSeamsSupport` challenge for V2 in `../character-sync-def-v2-candidate/Submission.lean` (SHA256 `5c0cbc35bd6335ab7c6d8d57bdece22a3065c6fdc7dee871d2577826b50396d3`, 795,645 bytes). V2 keeps `external_positive_ne_input` and `external_negative_ne_output` as theorems, and changes the other 166 added theorem declarations to definitions. Preparation does not start Lean, a model, or the native runtime, and does not append any native edit.

The build is the same frozen `d3369e50-0985-4155-804e-baba6801c575` used by the active chain. The launch copies its argument array and changes only the fresh workspace, task-file and output values. It preserves all four workers, the model/effort, the original publisher command, the pinned toolchain, trusted support files and resource settings. The five run/turn/token/evaluator budgets and preparation timeout remain `0`.

`preparation.json` records source, comparator, launch and build identities. Its source/bootstrap environment digest and the active native run's environment digest describe different layers and are recorded separately. The prepared workspace retains the original placeholder Submission; the candidate must enter through the supported queue protocol.

Preparation already performed:

```sh
/home/lzh/.venvs/deepscientist-finance/.bun/bin/bun prepare.ts
/home/lzh/.venvs/deepscientist-finance/.bun/bin/bun queue-candidate.ts --offline
```

`prepare.ts` is one-shot. `transport-preparation.json` records the disposable sandbox source roundtrip, frozen plan parser and 64,000-byte delivery-reader check. Offline validation is not native queue validation or mathematical acceptance.

The full V2 source compile completed with exit code 0 in 635.03 seconds, and its supervised axiom audit also passed. Native startup is running. `continue-native.py` is already running as a persistent controller: it waits for the actual successful startup receipt, starts native resume, validates the fresh plan, submits the candidate through `queueRunEdit`, and records the actual terminal result. It imposes no time limit. `continuation-started.json` and `continuation-receipt.json` identify the controller and its current phase; inspect these and the startup/resume receipts before taking any manual recovery action. Do not launch a second controller or duplicate resume while they are active.

The original manual launch sequence, now handled by that controller, is:

1. Inspect the exact launch without executing it: `/usr/bin/python3 run-native.py startup --print`.
2. Start fresh native preparation: `/usr/bin/python3 run-native.py startup`.
3. After startup exits `0`, begin native solving in a separate supervised process: `/usr/bin/python3 run-native.py resume`.
4. Once this fresh run has a cooperation plan, run `/home/lzh/.venvs/deepscientist-finance/.bun/bin/bun queue-candidate.ts` for a fresh-state dry run, then use the same command with `--queue` to deliver normally.

Run these commands with this directory as the working directory. The runner uses `campaign.environment()` and the campaign root as the native process cwd. Each startup/resume phase writes its own log and receipt, and refuses to overwrite an existing phase receipt. Inspect any uncertain or failed launch before retrying.

The queue script reads only this attempt's state and current plan version; it does not use an active selector or the old hardcoded queue. It dynamically preserves the original goal target/proof path, sets `ownerId: engineer`, increments the goal revision and validates with frozen `queueRunEdit`. Only explicit `--queue` appends an edit; the script never edits a checkpoint.

The model is instructed to execute the exact source loader once and submit an ordinary completed delivery. The host still performs the mandatory source guards, kernel checks, integration, fixed review, permitted-axiom audit and unchanged publisher comparator. No success is claimed until those genuine receipts exist. Existing active native/fullV12 processes and their supervisors remain untouched.
