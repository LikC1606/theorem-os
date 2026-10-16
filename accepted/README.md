# Accepted LeanEval proofs

Six proof packages with passing results from the official LeanEval evaluation. Open a title to inspect the source package, or the result link to read the official response.

| Proof | Area | System / model | Official acceptance |
| --- | --- | --- | --- |
| [Unit conjecture: a nontrivial group-ring unit](annals_unit_conjecture/) | Algebra | DeepScientist + GPT-5.6 | [#1246 · pass](https://github.com/leanprover/lean-eval-submissions/issues/1246#issuecomment-5380977645) |
| [Rademacher type and Enflo type coincide](annals_rademacher_enflo_type/) | Functional analysis | DeepScientist Math + GPT-6.1 (gpt-6.1-sol) | [#2115 · pass](https://github.com/leanprover/lean-eval-submissions/issues/2115#issuecomment-6161355838) |
| [Equiangular lines with a fixed angle](annals_equiangular_lines_fixed_angle/) | Combinatorics | DeepScientist Math + GPT-6.1 (gpt-6.1-sol) | [#2135 · pass](https://github.com/leanprover/lean-eval-submissions/issues/2135#issuecomment-6186332699) |
| [Fractional expectation thresholds](annals_fractional_expectation_thresholds/) | Probabilistic combinatorics | DeepScientist Math + GPT-6.1 (gpt-6.1-sol) | [#2141 · pass](https://github.com/leanprover/lean-eval-submissions/issues/2141#issuecomment-6197783762) |
| [Dimitrov's lower bound](dimitrov/) | Algebraic number theory | DeepScientist Math + GPT-6.1 (gpt-6.1-sol) | [#2143 · pass](https://github.com/leanprover/lean-eval-submissions/issues/2143#issuecomment-6215093969) |
| [Hopf–Rinow theorem](hopf_rinow/) | Riemannian geometry | DeepScientist Math + GPT-6.1 (gpt-6.1-sol) | [#2143 · pass](https://github.com/leanprover/lean-eval-submissions/issues/2143#issuecomment-6215093969) |

These are archived outcomes from TheoremOS's predecessor systems and subsequent work. They are not a success-rate evaluation of the current release. The GPT-6.1 packages document continuation runs; the equiangular-lines package also includes a compatibility port. See each package's provenance and submission discussion before comparing budgets or attributing autonomy.

Official acceptance is identified by the linked LeanEval response. A local `verification.json` records checks for a particular source and environment; `compatibility-verification.json` records the port's validation at its capture time. Neither file alone replaces the official response.

[accepted.json](accepted.json) records the statement revisions, original source commits, model attribution, official acceptance responses, and SHA-256 checksums. All files inside each problem directory are preserved byte for byte from the archived submission package.

Four further proofs have passed the local official comparator and are archived in [submitted](../submitted/) while hosted official evaluation is pending. They are excluded from the six official acceptances above. Historical research snapshots are preserved in [in-progress](../in-progress/).
