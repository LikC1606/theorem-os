"""Freeze this new package after its final check. Does not run Lean or read runtime state."""

import datetime
import hashlib
import json
from pathlib import Path
import re

stage = Path(__file__).resolve().parent
assert not (stage / 'manifest.json').exists(), 'Package already frozen'
label = 'explicit-types-04'
result = json.loads((stage / f'{label}-result.json').read_text())
launch = json.loads((stage / f'{label}-launch.json').read_text())
source = (stage / 'WidthFive.lean').read_bytes()
snapshot = (stage / f'{label}-source.lean').read_bytes()
sha = lambda data: hashlib.sha256(data).hexdigest()
assert result['actualExitCode'] == 0 and not result['timedOut']
assert source == snapshot
assert sha(source) == result['sourceSHA256'] == launch['sourceSHA256']
assert '-Dpp.explicit=true' in result['command']
assert not (stage / f'{label}.stderr.log').read_bytes()
stdout = (stage / f'{label}.stdout.log').read_text()
assert not re.search(r'\berror(?:\(|:)', stdout)
prefix = (stage / 'CurrentPrefix.lean.inc').read_bytes()
assert sha(prefix) == 'f55c042e447b853d775f3f6f164d94ab175cc328eabf324588117d8d436f0c45'

names = ['WidthFive.table_checked', 'WidthFive.count_weighted',
         'WidthFive.path_mem_allPaths', 'WidthFive.path_card_real',
         'WidthFive.stripGrowthAtFive', 'width_five_summability_diagnostic']
qualified = ['OAI.PolynomialVacuumBridge.Corridor.' + n for n in names]
axioms = dict(re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", stdout))
assert set(axioms) == set(qualified)
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
for name, values in axioms.items():
    assert set(re.findall(r'[A-Za-z_][A-Za-z_.]*', values)) == allowed, (name, values)
assert '@weight (@OfNat.ofNat Nat (nat_lit 5)' in stdout
assert '@firstLengthWeight (@OfNat.ofNat Nat (nat_lit 5)' in stdout

parts = ['Basic.lean.inc', 'PotentialTable.lean.inc', 'FiniteCertificate.lean.inc',
         'CertificateChecks.lean.inc', 'Proof.lean.inc']
body = '\n'.join((stage / name).read_text() for name in parts)
final = (stage / 'Final.lean.inc').read_text()
expected = prefix.decode() + '\n' + body + '\nend WidthFive\n' + final
expected += '\nend PolynomialVacuumBridge.Corridor\nend OAI\n'
assert expected.encode() == source
increment = body + '\nend WidthFive\n' + final.split('\n#check', 1)[0] + '\n'
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b', increment)
(stage / 'WidthFive.lean.inc').write_text(increment)
increment_sha = sha(increment.encode())

target = 'OAI.PolynomialVacuumBridge.Corridor.width_five_summability_diagnostic'
target_type = ('Summable (OAI.PolynomialVacuumBridge.Corridor.weight (h := 5)) ∧ '
               'Summable (OAI.PolynomialVacuumBridge.Corridor.firstLengthWeight (h := 5))')
summary = (
    'Prove and deliver the exact unconditional height-five pair of summabilities as a typed '
    'auxiliary lemma. The complete insertion-ready increment below has passed an independent '
    'Lean 4.34.1 kernel check; normal host typed verification and canonical integration are '
    'still required. The proof uses a six-vertex sliding window: each extension is a genuine '
    'frozen-adjacency strip neighbor and avoids every vertex in the current window. Horizontal '
    'translation preserves neighbors, candidates, sliding and the continuation count. The '
    'finite table contains the 336 normalized six-point states plus 25 reachable shorter '
    'windows from the source. Ordinary kernel decide checks all 361 rows in 31 blocks: '
    'each row is nonempty with a positive integer potential, every genuine successor '
    'normalizes to a listed state, and 1000*sum(successor potentials) <=1847*current potential. '
    'An induction bounds the true window continuation count by P(normalize w)*(1847/1000)^n. '
    'A proved finite-list enumerator contains every canonical BridgePath 5: full Nodup '
    'implies avoidance of the six-vertex window. Injectivity of vertices gives the required '
    'path count, and an exact square-root/cosine argument proves 1847/1000<2*cos(pi/8). '
    'The integrated unconditional helpers from sums_reduction then prove the two summabilities. '
    'Python only generated the finite integer witness; Lean recomputes every actual local '
    'neighbor, membership, normalization, lookup and inequality. No diagnostic Python count '
    'is used as a proof or an axiom. There is no strip_growth_below_mu antecedent, and the '
    'original all-height theorem is not invoked.\n\n'
    'Insert the following complete WidthFive.lean.inc once inside namespace '
    'OAI.PolynomialVacuumBridge.Corridor in generated/problem/Submission.lean, after '
    'bridgeSummable_firstLengthWeight_of_mu_bound and '
    'bridgeSummable_weight_of_summable_firstLengthWeight. It opens and closes nested '
    'namespace WidthFive, then proves the target in the outer namespace. Preserve existing '
    'declarations, tasks, and the unresolved all-height theorem. Check declaration-name '
    'collisions. Do not replace Submission.lean with the standalone WidthFive.lean harness. '
    'Keep ordinary decide and its proofs; do not replace them by native_decide, placeholders '
    'or additional axioms.\n\n'
    f'Local evidence: source SHA256 {sha(source)}, increment SHA256 {increment_sha}; '
    f'actual final exit 0 in {result["durationSeconds"]} seconds. The source also passed '
    'summability-03; the final run changes only the pretty-printer flag to expose implicit '
    'types including the explicit height-five arguments of weight and firstLengthWeight. All six key declarations print '
    'only [propext, Classical.choice, Quot.sound]. Lean 4.34.1, Mathlib '
    'd13f23b723b8a846827a245b89c10fc7d3f11612, sealed environment '
    '2d808da67c8ab8ad74458d8a53ecc2ee8da9c63a825e0429439ebf56a9a78c87; '
    'one CPU/thread, 32 GiB, maxHeartbeats=0 and no wall/CPU/invocation cap. '
    'This proves height five only. Host native acceptance, all-height resolution, and '
    'OpenAI-hosted certification are not claimed.\n\n'
)
objective = summary + '```lean\n' + increment + '```\n'
task = {
    'id': f'width_five_summability_{sha(source)[:8]}', 'kind': 'lemma',
    'objective': objective, 'dependsOn': ['sums_reduction'], 'revision': 0,
    'proofPath': 'Submission.lean', 'theoremName': target, 'type': target_type,
    'groupId': 'main',
}


def write_json(name, value):
    (stage / name).write_text(json.dumps(value, indent=2, ensure_ascii=False) + '\n')


(stage / 'task-objective.md').write_text(objective)
write_json('native-task-proposal.json', task)
write_json('native-task-handoff.json', task)
write_json('delivery-contract.json', {
    'theoremName': target, 'type': target_type, 'dependsOn': ['sums_reduction'],
    'source': 'WidthFive.lean', 'sourceSHA256': sha(source),
    'increment': 'WidthFive.lean.inc', 'incrementSHA256': increment_sha,
    'validatedPrefixSHA256': sha(prefix), 'finalValidation': f'{label}-result.json',
    'localKernelProved': True, 'nativeTaskProofAcceptance': False,
    'canonicalIntegration': False, 'allHeightsProved': False,
    'insertionNamespace': 'OAI.PolynomialVacuumBridge.Corridor',
    'standaloneHarnessMustNotReplaceSubmission': True,
    'activeSourceReinspectedDuringArchival': False,
})
write_json('key-theorems.json', {
    'printedTypesAndAxioms': f'{label}.stdout.log', 'prettyPrinterExplicit': True,
    'target': {'name': target, 'type': target_type},
    'declarations': [{'name': name, 'axioms': sorted(allowed)} for name in qualified],
})
write_json('verification-audit.json', {
    'actualExitCode': 0, 'sourceMatchesSavedSnapshot': True,
    'sourceMatchesLaunchAndResultSHA256': True, 'sourceMatchesComponents': True,
    'canonicalPrefixSHA256': sha(prefix), 'sourceSHA256': sha(source),
    'incrementSHA256': increment_sha, 'allSixAxiomListsWhitelisted': True,
    'heightExplicitInFinalPrintedType': True, 'placeholderFreeIncrement': True,
    'noLeanRerunDuringArchival': True, 'failuresPreserved': [
        'local-certificate-01', 'summability-02'],
    'passedRuns': ['summability-03', label],
    'finalPrettyPrinterOnlyRerunReason': 'Expose implicit height and all six exact types',
    'pythonIsProofOracle': False, 'nativeTaskProofAcceptance': False,
})
provenance = json.loads((stage / 'provenance.json').read_text())
provenance.update({
    'archivedAt': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'sourceSHA256': sha(source), 'incrementSHA256': increment_sha,
    'diagnosticSourceSHA256': sha((stage / 'certificate-diagnostic.json').read_bytes()),
    'newProofRoute': 'Six-vertex window; checked positive integer potential; canonical Nodup coverage',
    'noPlaceholderProofs': True, 'noLeanRerunDuringArchival': True,
})
write_json('provenance.json', provenance)

(stage / 'README.md').write_text(f'''# Honeycomb height-five kernel proof

The unconditional theorem `{target}` proves `Summable (weight (h := 5)) ∧ Summable (firstLengthWeight (h := 5))` for the frozen canonical `BridgePath 5`. [Final Lean evidence]({label}-result.json) records actual exit 0 in {result['durationSeconds']} seconds. The all-height original theorem remains open.

[WidthFive.lean.inc](WidthFive.lean.inc) is the complete insertion-ready proof. Insert it once inside `OAI.PolynomialVacuumBridge.Corridor` after the unconditional helpers from integrated `sums_reduction`. It opens/closes its own `WidthFive` namespace and proves the target in the outer namespace. [WidthFive.lean](WidthFive.lean) is a standalone validation harness and must not replace an active submission. [CurrentPrefix.lean.inc](CurrentPrefix.lean.inc) is the unchanged validated helper prefix.

The proof remembers the last six vertices and excludes all of them from each genuine strip-neighbor extension. The finite table has 336 six-point states and 25 shorter windows reachable from the source. [CertificateChecks.lean.inc](CertificateChecks.lean.inc) checks all 361 rows with ordinary kernel `decide` in 31 blocks: nonemptiness, positive integer potential, closure under every actual candidate, and `1000 * sum(P(successor)) ≤ 1847 * P(state)`. The proof of `count_weighted` transports these facts by horizontal translation and inducts on length. `path_mem_allPaths` proves coverage of every original canonical self-avoiding path, using full `Nodup` to justify the window exclusion. Finite-set injection yields the geometric count bound, and an exact cosine identity gives `1847/1000 < 2*cos(pi/8)`. The canonical counting-to-summability helpers finish both targets without a growth assumption.

[generate_certificate.py](generate_certificate.py) and [certificate-diagnostic.json](certificate-diagnostic.json) retain the exact witness construction. Python suggested the route by finding maximum ten-step count 450; that diagnostic count is not claimed as a separate Lean theorem. Lean independently checks the actual local one-step potential certificate, including every lookup and membership. No Python output is imported as an axiom or trusted oracle.

[task-objective.md](task-objective.md) directly inlines the entire increment. [native-task-proposal.json](native-task-proposal.json) and its identical [handoff object](native-task-handoff.json) contain the exact typed task. [delivery-contract.json](delivery-contract.json) and [HANDOFF.txt](HANDOFF.txt) record the type, insertion point and hashes. Normal host native typed acceptance and canonical integration are still required; neither is claimed here.

[Final stdout]({label}.stdout.log) prints all six key theorem types with implicit arguments exposed, including height five on both `weight` and `firstLengthWeight`, and their exact axiom lists. Each uses only `propext`, `Classical.choice`, and `Quot.sound`. [verification-audit.json](verification-audit.json) confirms identical source, snapshot, launch/result hashes, and an increment free of placeholders, additional axioms, unsafe definitions or native evaluation tactics.

Four real runs are preserved with exact source snapshots, stdout/stderr, launch and result JSON. The first failed on computability, a translation proof and whole-table recursion depth. The second verified every small certificate block and the canonical path-coverage lemma, but failed to assemble the left-associated conjunction and to mark the real constant noncomputable. `summability-03` passed the complete proof. The final run kept that proof source byte-identical and enabled only explicit type printing. No Lean check was repeated during archival.

Validation used Lean 4.34.1, Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, sealed environment `2d808da67c8ab8ad74458d8a53ecc2ee8da9c63a825e0429439ebf56a9a78c87`, one CPU/thread, 32 GiB, `maxHeartbeats=0`, and no wall, CPU, token or invocation cap. No active runtime, source, state, queue, old evidence, cache or global configuration was modified. No publisher solution, hidden reasoning or credentials were read; no model, commit or push was invoked. This is local kernel evidence, with no claim of OpenAI-hosted certification or an all-height solution.
''')
(stage / 'HANDOFF.txt').write_text(
    'UNCONDITIONAL HEIGHT-FIVE LOCAL KERNEL PROOF\n\n'
    f'Theorem: {target}\nType: {target_type}\n'
    f'Task ID: {task["id"]}\nDepends on: sums_reduction\n\n'
    'Insert WidthFive.lean.inc once in namespace OAI.PolynomialVacuumBridge.Corridor, '
    'after bridgeSummable_firstLengthWeight_of_mu_bound and '
    'bridgeSummable_weight_of_summable_firstLengthWeight. Do not replace Submission '
    'with the standalone harness. Preserve existing tasks/declarations and the open '
    'all-height original theorem. Check collisions before normal native submission.\n\n'
    f'Source SHA256: {sha(source)}\nIncrement SHA256: {increment_sha}\n'
    f'Final actual exit: 0; duration: {result["durationSeconds"]} seconds\n'
    f'Final launch/result: {label}-launch.json / {label}-result.json\n'
    'Six exact types/axiom lists are in the final stdout with pp.explicit=true. '
    'Allowed axioms only: propext, Classical.choice, Quot.sound.\n\n'
    'Python witness generation is not mathematical proof; Lean checks every finite '
    'certificate row and the full canonical path connection. Height five only. '
    'Native host acceptance and integration remain with the parent; no active chain '
    'or results repository was modified here.\n')

files = sorted(p for p in stage.iterdir() if p.is_file() and p.name not in {
    'manifest.json', 'SHA256SUMS'})
manifest = {
    'scope': 'Frozen unconditional height-five local kernel proof package',
    'sourceSHA256': sha(source), 'incrementSHA256': increment_sha,
    'finalResult': f'{label}-result.json', 'theoremName': target, 'type': target_type,
    'nativeTaskProofAcceptance': False, 'allHeightsProved': False,
    'fileCount': len(files),
    'files': [{'path': p.name, 'bytes': p.stat().st_size,
               'sha256': sha(p.read_bytes())} for p in files],
}
write_json('manifest.json', manifest)
files.append(stage / 'manifest.json')
(stage / 'SHA256SUMS').write_text(''.join(
    f'{sha(p.read_bytes())}  {p.name}\n' for p in sorted(files)))
print(json.dumps({'fileCountIncludingManifest': len(files),
                  'sourceSHA256': sha(source), 'incrementSHA256': increment_sha,
                  'taskId': task['id'], 'manifestSHA256': sha((stage/'manifest.json').read_bytes())}))
