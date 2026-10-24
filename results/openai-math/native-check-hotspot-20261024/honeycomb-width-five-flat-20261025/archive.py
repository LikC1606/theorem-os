"""Freeze an explicit source/evidence allowlist, excluding every build artifact."""
import datetime
import difflib
import hashlib
import json
from pathlib import Path
import re

stage = Path(__file__).resolve().parent
assert not (stage/'manifest.json').exists(), 'Package already frozen'
sha = lambda b: hashlib.sha256(b).hexdigest()
load = lambda name: json.loads((stage/name).read_text())
compile_result = load('kernel-compile-01-result.json')
probe = load('exact-types-02-result.json')
guard = load('source-preflight-02-result.json')
source = (stage/'project/Submission.lean').read_bytes()
inc = (stage/'WidthFiveFlat.lean.inc').read_text()
assert guard['results'][-1]['passed']
assert compile_result['actualExitCode'] == probe['actualExitCode'] == 0
assert sha(source) == compile_result['sourceSHA256'] == probe['candidateSHA256']
assert sha(source) == guard['results'][-1]['sourceSHA256']
assert source == (stage/'kernel-compile-01-source.lean').read_bytes()
assert (stage/'project/Probe.lean').read_bytes() == (stage/'exact-types-02-source.lean').read_bytes()
assert compile_result['outputModuleSHA256'] == probe['importedModuleSHA256']
assert sha((stage/'project/Submission.olean').read_bytes()) == probe['importedModuleSHA256']
base = (stage/'BaseSubmission.lean').read_text()
anchor = 'theorem finite_bridge_sums : FiniteBridgeSums := by\n'
assert source.decode() == base.replace(anchor, inc+'\n'+anchor)
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b', inc)
assert not re.search(r'(?m)^\s*(namespace|end|section|open|set_option|attribute)\b', inc)
assert not re.search(r'(?m)^\]$', inc)
assert not (stage/'exact-types-02.stderr.log').read_bytes()
output = (stage/'exact-types-02.stdout.log').read_text()
assert not re.search(r'\berror(?:\(|:)', output)
names = ['widthFiveTable_checked', 'widthFiveCount_weighted',
         'widthFivePath_mem_allPaths', 'widthFivePath_card_real',
         'widthFiveStripGrowthAtFive', 'width_five_summability_diagnostic']
qualified = ['OAI.PolynomialVacuumBridge.Corridor.'+name for name in names]
axioms = dict(re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", output))
assert set(axioms) == set(qualified)
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
for name, values in axioms.items():
    assert set(re.findall(r'[A-Za-z_][A-Za-z_.]*', values)) == allowed
for function in ['weight', 'firstLengthWeight']:
    assert '@OAI.PolynomialVacuumBridge.Corridor.'+function+' (@OfNat.ofNat Nat (nat_lit 5)' in output


def save(name, value):
    (stage/name).write_text(json.dumps(value, indent=2, ensure_ascii=False)+'\n')


old_task = json.loads((stage.parent/'honeycomb-width-five-20261025/native-task-proposal.json').read_text())
task_id, target, target_type = old_task['id'], old_task['theoremName'], old_task['type']
description = (
    'Deliver the same unconditional height-five theorem for the existing task '
    f'{task_id}, with the exact target type unchanged. The previous namespaced delivery '
    'was rejected before Lean by math_original_context_changed. Use the complete flat '
    'increment below, which passed the active fixed assertSolverProjectSources using the '
    'exact four-field SolverSourceConstraints snapshot, then passed a new full Lean '
    f'compile in {compile_result["durationSeconds"]} seconds. A short Probe imported only '
    'the newly compiled module and printed six exact theorem types and their axiom lists; '
    'each list contains only propext, Classical.choice and Quot.sound. The explicit target '
    'has height 5 for both weight and firstLengthWeight.\n\n'
    'Insert this exact block once inside the already existing '
    'OAI.PolynomialVacuumBridge.Corridor namespace before the original finite_bridge_sums '
    'declaration. It adds no namespace/end/section/open/global option commands. '
    'All 102 helpers have unique widthFive-prefixed names, and both Decidable instances '
    'are explicitly named. Preserve indentation of the 31 table-closing brackets; '
    'top-level closing brackets and added documentation comments were also left in the '
    'sourceStructure context by the fixed parser and caused the old rejection. Do not '
    'add comments or wrappers outside declarations. If a previous rejected h5 block '
    'remains in the assigned worktree, replace only that added h5 block and h5 target '
    'with this exact flat block; preserve all canonical declarations and the open '
    'all-height original theorem. Check collisions and reuse exact matching flat '
    'helpers. Do not replace the full Submission with this block or the diagnostic '
    'baseline, and do not insert Probe queries into the guarded Submission.\n\n'
    'The mathematics is unchanged: a six-vertex window over genuine frozen-adjacency '
    'strip neighbors, 361 checked positive integer potential rows, translation '
    'invariance, an unconditional weighted count, full canonical Nodup-path coverage, '
    'finite-set injection, beta=1847/1000<2*cos(pi/8), and the integrated unconditional '
    'counting-to-summability helpers from sums_reduction. Ordinary kernel decide '
    'rechecks all local row inequalities; Python is not a proof oracle. No growth '
    'hypothesis or original all-height theorem is used. No new mathematics or height-six '
    'work is requested. Complete ordinary typed delivery so the independent host '
    'performs native acceptance and integration. Local preflight and kernel success '
    'do not themselves constitute a native TaskProof or OpenAI-hosted certification.\n\n'
    f'New full-source SHA256 {sha(source)}; exact increment SHA256 {sha(inc.encode())}; '
    f'Probe import module SHA256 {probe["importedModuleSHA256"]}. Lean 4.34.1, fixed '
    'Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612, one CPU/thread, 32 GiB, '
    'maxHeartbeats=0; no wall/CPU/invocation cap. Do not rerun standalone checks '
    'on this byte-identical passed source for formatting or linter warnings.\n\n'
)
objective = description+'```lean\n'+inc+'```\n'
(stage/'task-objective.md').write_text(objective)
task = {**old_task, 'objective': objective}
save('native-task-proposal.json', task)
save('native-task-handoff.json', task)
save('delivery-contract.json', {
    'existingTaskId': task_id, 'theoremName': target, 'type': target_type,
    'dependsOn': old_task['dependsOn'], 'targetContractUnchanged': True,
    'increment': 'WidthFiveFlat.lean.inc', 'incrementSHA256': sha(inc.encode()),
    'fullCandidate': 'project/Submission.lean', 'sourceSHA256': sha(source),
    'guardPreflight': 'source-preflight-02-result.json',
    'compileResult': 'kernel-compile-01-result.json',
    'probeResult': 'exact-types-02-result.json', 'probeOutput': 'exact-types-02.stdout.log',
    'localGuardPassed': True, 'localKernelPassed': True,
    'nativeTaskProofAcceptance': False, 'canonicalIntegration': False,
    'allHeightsProved': False, 'doNotCopyBuildArtifacts': True,
})
save('verification-audit.json', {
    'sourceSHA256': sha(source), 'incrementSHA256': sha(inc.encode()),
    'guardSameSourceAsCompiled': True, 'compileSnapshotMatches': True,
    'probeImportsExactNewModule': True, 'allSixAxiomListsWhitelisted': True,
    'heightFiveExplicitInPrintedTypes': True, 'originalBaseBytesPreserved': True,
    'incrementPlaceholderFree': True, 'oldSuccessfulSourceRerun': False,
    'newCandidateFullCompileCount': 1, 'noLeanRerunDuringArchival': True,
    'oldFormalRejectedCandidateNotAvailable': True,
    'failedGuardReproductionIsReconstructed': True,
    'guardFailureEvidence': 'source-preflight-result.json',
    'guardPassEvidence': 'source-preflight-02-result.json',
    'firstFlatFailureSource': 'project-guard-01-source.lean',
    'firstFlatFailureContext': 'project-context-diagnostic.txt',
    'originalAllHeightTheoremStillContainsItsPreexistingPlaceholder': True,
    'heightFiveAxiomsContainNoSorryAx': True,
})
save('key-theorems.json', {'exactTypesAndAxioms': 'exact-types-02.stdout.log',
    'declarations': [{'name': name, 'axioms': sorted(allowed)} for name in qualified],
    'target': {'name': target, 'type': target_type}})
provenance = load('provenance.json')
provenance.update({'archivedAt': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'sourceSHA256': sha(source), 'incrementSHA256': sha(inc.encode()),
    'guardModuleSHA256': guard['guardModuleSHA256'],
    'noLeanRerunDuringArchival': True, 'originalBaseBytesPreserved': True})
save('provenance.json', provenance)
(stage/'context-guard-01.diff').write_text(''.join(difflib.unified_diff(
    (stage/'baseline-context-diagnostic.txt').read_text().splitlines(keepends=True),
    (stage/'project-context-diagnostic.txt').read_text().splitlines(keepends=True),
    fromfile='baseline residual context', tofile='first flat candidate residual context')))

(stage/'README.md').write_text(f'''# Height-five source-context compatibility repair

The exact unconditional height-five theorem `{target}` now has a flat proof increment compatible with the active fixed source guard. The [actual preflight](source-preflight-02-result.json) passed, the [new complete source compile](kernel-compile-01-result.json) exited 0 in {compile_result['durationSeconds']} seconds, and the [short module Probe](exact-types-02-result.json) exited 0 in {probe['durationSeconds']} seconds. All [six exact type/axiom queries](exact-types-02.stdout.log) use only `propext`, `Classical.choice`, and `Quot.sound`; both summands explicitly have height 5.

Deliver [WidthFiveFlat.lean.inc](WidthFiveFlat.lean.inc), whose SHA256 is `{sha(inc.encode())}`. Insert it once in the existing `OAI.PolynomialVacuumBridge.Corridor` namespace before the original `finite_bridge_sums`, without adding another namespace. [task-objective.md](task-objective.md) inlines the full block. The identical [proposal](native-task-proposal.json) and [handoff object](native-task-handoff.json) preserve the existing task `{task_id}`, exact type and dependency on `sums_reduction`; the parent handles the normal objective update and native queue.

The rejection occurred before Lean. The guard hashes the residual text outside recognized named declarations. A reconstruction from the frozen public h3 baseline and original h5 increment reproduced `math_original_context_changed`; it is not an archived original failed delivery. Removing only the namespace was insufficient. The two unnamed instances and 31 top-level `]` lines from finite-table definitions also remained as context. After naming both instances and prefixing all 102 helpers, the [context diff](context-guard-01.diff) still showed exactly 31 closing brackets plus a new theorem doc comment. Indenting those brackets and removing that new comment fixed the guard. A helper simp attribute was also removed; the actual diff did not show it as a residual cause. The guard implementation was neither edited nor bypassed.

[project/Submission.lean](project/Submission.lean) is the full candidate actually preflighted and compiled, SHA256 `{sha(source)}`. It preserves the frozen baseline byte-for-byte except for inserting the h5 block. The original all-height theorem retains its existing `sorry`; the six h5 declarations do not depend on it, as demonstrated by their axiom lists. The h5 increment has no placeholder, native evaluation tactic or added axiom. The mathematical proof and finite certificate are unchanged by the naming/formatting repair.

[source-preflight-result.json](source-preflight-result.json) retains the first real guard failures, [project-guard-01-source.lean](project-guard-01-source.lean) the first flat candidate, and [context-diagnostic.ts](context-diagnostic.ts) the bounded residual-context comparison. [source-preflight-02-result.json](source-preflight-02-result.json) records the final pass against the exact [fixed constraints snapshot](fixed-source-constraints.json), using the active fixed `assertSolverProjectSources`. The original namespaced source was not recompiled.

The new full candidate was compiled once into a module local to this isolated directory. [project/Probe.lean](project/Probe.lean) then imported that exact module, whose SHA256 is recorded in both compile and Probe receipts. Query commands were kept out of the guarded submission. No passed source was recompiled for printing or archival. Lean 4.34.1, fixed Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, one CPU/thread, 32 GiB and `maxHeartbeats=0` were used without wall, CPU or invocation caps.

[delivery-files.json](delivery-files.json) is the explicit copy allowlist. It contains only source, scripts, fixed public metadata and logs; the local `.olean`, build products, caches and symlinks are excluded. Copy only its `files` entries into the results repository. No active runtime, source, state, cache, receipt, old frozen package or results repository was modified. No queue operation, model call, commit or push was performed. Native TaskProof acceptance and canonical integration remain pending with the parent; the all-height original theorem remains open.
''')
(stage/'HANDOFF.txt').write_text(
    f'EXISTING TASK: {task_id}\nTHEOREM: {target}\nTYPE: {target_type}\n\n'
    f'INCREMENT: WidthFiveFlat.lean.inc\nINCREMENT SHA256: {sha(inc.encode())}\n'
    f'FULL CANDIDATE: project/Submission.lean\nSOURCE SHA256: {sha(source)}\n\n'
    'Actual guard pass: source-preflight-02-result.json\n'
    'New compile pass: kernel-compile-01-result.json\n'
    'Six exact types/axioms: exact-types-02.stdout.log\n'
    'Probe result: exact-types-02-result.json\n\n'
    'Insert the flat increment in the existing outer namespace before finite_bridge_sums; '
    'preserve bracket indentation and named instances. Do not add new namespace wrappers '
    'or top-level comments, and do not insert Probe commands into Submission. '
    'Preserve all current declarations and the unresolved all-height target.\n'
    'Update only the existing h5 objective through the normal queue; the type and other '
    'task contracts are unchanged. Local verification does not grant native acceptance.\n'
    'Copy only delivery-files.json entries. Never copy project/Submission.olean, '
    'other build products or links. No more Lean run is needed for archival.\n')

files = [
    'BaseSubmission.lean', 'OriginalWidthFive.lean.inc', 'WidthFiveFlat.lean.inc',
    'WidthFiveFlat-guard-01.lean.inc', 'fixed-source-constraints.json',
    'prepare.py', 'preflight.ts', 'context-diagnostic.ts', 'validate.py', 'archive.py',
    'rename-map.json', 'provenance.json', 'source-preflight-result.json',
    'source-preflight-02-result.json', 'project-guard-01-source.lean',
    'README.md', 'HANDOFF.txt', 'task-objective.md', 'native-task-proposal.json',
    'native-task-handoff.json', 'delivery-contract.json', 'verification-audit.json',
    'key-theorems.json', 'project/Probe.lean',
    'context-guard-01.diff',
]
variants = ['baseline', 'namespaced', 'flat-anonymous', 'flat-named-simp', 'project']
trusted = list(load('fixed-source-constraints.json')['constraints']['trustedFiles'])
for name in variants:
    files += [name+'/Submission.lean']+[name+'/'+p for p in trusted]
    files += [name+'-context-diagnostic.txt']
for label in ['kernel-compile-01', 'exact-types-02']:
    files += [label+suffix for suffix in ['-launch.json', '-result.json', '-source.lean',
                                        '.stdout.log', '.stderr.log']]
files = sorted(set(files))
for name in files:
    p = stage/name
    assert p.is_file() and not p.is_symlink(), name
    assert not re.search(r'\.(olean|ilean|c|ir)(?:\.|$)', name), name
save('delivery-files.json', {
    'schema': 'theorem-os.local-proof-delivery-allowlist.v1',
    'files': sorted(files+['delivery-files.json', 'manifest.json', 'SHA256SUMS']),
    'excludedLocalBuildArtifact': 'project/Submission.olean',
    'copyOnlyListedRegularFiles': True,
})
files.append('delivery-files.json')
save('manifest.json', {
    'scope': 'Frozen flat height-five compatibility repair', 'sourceSHA256': sha(source),
    'incrementSHA256': sha(inc.encode()), 'existingTaskId': task_id,
    'guardPassed': True, 'localKernelPassed': True, 'nativeTaskProofAcceptance': False,
    'files': [{'path': name, 'bytes': (stage/name).stat().st_size,
               'sha256': sha((stage/name).read_bytes())} for name in sorted(files)],
})
files.append('manifest.json')
(stage/'SHA256SUMS').write_text(''.join(
    f'{sha((stage/name).read_bytes())}  {name}\n' for name in sorted(files)))
print(json.dumps({'deliveryFileCount': len(files)+1, 'sourceSHA256': sha(source),
    'incrementSHA256': sha(inc.encode()), 'manifestSHA256': sha((stage/'manifest.json').read_bytes()),
    'taskId': task_id, 'buildArtifactsExcluded': True}))
