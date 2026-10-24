from pathlib import Path
import datetime, hashlib, json, re

s=Path(__file__).resolve().parent
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
ns='OAI.PolynomialVacuumBridge.Corridor.'
inc=(s/'WidthThree.lean.inc').read_text(); source=(s/'WidthThree.lean').read_text(); prefix=(s/'CurrentPrefix.lean.inc').read_text()
launch=json.loads((s/'summability-01-launch.json').read_text()); result=json.loads((s/'summability-01-result.json').read_text()); prov=json.loads((s/'provenance.json').read_text())
assert sha(s/'WidthThree.lean')==sha(s/'summability-01-source.lean')==launch['sourceSHA256']==result['sourceSHA256']
assert result['actualExitCode']==0 and result['timedOut'] is False
assert all(result[k]==v for k,v in launch.items())
assert (s/'summability-01.stderr.log').stat().st_size==0
checked=['WidthThree.count_five','WidthThree.count_block_bound','WidthThree.path_mem_allPaths','WidthThree.path_card','WidthThree.stripGrowthAtThree','width_three_summability_diagnostic']
assert source==prefix+'\n'+inc+'\n'+'\n'.join('#check @'+n+'\n#print axioms '+n for n in checked)+'\nend PolynomialVacuumBridge.Corridor\nend OAI\n'
stdout=(s/'summability-01.stdout.log').read_text()
axioms={n:re.findall(r'[A-Za-z_.]+',b) for n,b in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]+)\]",stdout)}
assert set(axioms)=={ns+n for n in checked}
assert all(set(a)=={'propext','Classical.choice','Quot.sound'} for a in axioms.values())
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',source)
root=Path('/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/tasks/HoneycombBridgeFiniteness/attempts/workflow-20261024/result.json.runtime')
state=json.loads((root/'state.json').read_text()); coop=state['cooperation']
dep=next(e for e in coop['tasks'] if e.get('task',{}).get('id')=='sums_reduction')
canonical=root/'worktree/generated/problem/Submission.lean'
assert canonical.read_text().startswith(prefix)
names=[]; localns=''
for line in inc.splitlines():
    if line=='namespace WidthThree':localns='WidthThree.'
    if line=='end WidthThree':localns=''
    m=re.match(r'(?:(?:noncomputable )?def|lemma|theorem)\s+([^\s:{]+)',line)
    if m:names.append(localns+m.group(1))
collisions=[n for n in names if re.search(r'^(?:(?:noncomputable )?def|lemma|theorem)\s+'+re.escape(n.rsplit('.',1)[-1])+r'(?=[\s:{])',canonical.read_text(),re.M)]
assert not collisions
history=[]
for p in sorted(s.glob('*-result.json')):
    r=json.loads(p.read_text())
    history.append({'label':p.name.removesuffix('-result.json'),'actualExitCode':r['actualExitCode'],'durationSeconds':r['durationSeconds'],'sourceSHA256':r['sourceSHA256'],'resultFile':p.name,'stdoutLog':Path(r['stdoutLog']).name})
assert len(history)==3
(s/'dependency-snapshot.json').write_text(json.dumps({'inspectedAt':now,'runId':state['runId'],'canonicalCommit':coop['canonicalCommit'],'planVersion':coop['planVersion'],'canonicalSource':str(canonical),'canonicalSourceSHA256':sha(canonical),'canonicalStartsWithValidatedPrefix':True,'validatedPrefixSHA256':sha(s/'CurrentPrefix.lean.inc'),'canonicalSourceDependency':{k:dep['task'].get(k) for k in ['id','kind','revision','theoremName','type']},'canonicalSourceDependencyStatus':dep['status'],'canonicalSourceDependencyIntegratedCheckPassed':dep.get('integratedCheck',{}).get('passed'),'canonicalSourceDependencyIntegratedCheckCommit':dep.get('integratedCheck',{}).get('commit'),'existingUnconditionalHelperDeclarations':[ns+'bridgeSummable_firstLengthWeight_of_mu_bound',ns+'bridgeSummable_weight_of_summable_firstLengthWeight'],'newDeclarationNameCollisions':collisions,'activeStateChanged':False},ensure_ascii=False,indent=2)+'\n')
objective=('Prove and deliver the exact unconditional fixed-height-three pair of summabilities as a typed auxiliary lemma. A complete insertion-ready proof increment is included below and has passed an independent local Lean 4.34.1 kernel check; normal host typed verification and canonical integration are still required. '
'The proof enumerates the six width-three vertex kinds, proves the translation invariance of non-backtracking continuation counts, and kernel-checks the at-most-20 count for five steps after each possible incoming edge using ordinary decide. A block induction bounds all continuation counts by 16*20^(n/5); a finite vertex-list enumerator contains every canonical BridgePath 3 and yields the cardinality bound 32*20^(n/5) <= 32*(11/6)^n. Pure rational arithmetic proves 20 <= (11/6)^5, and the exact cosine/square-root identity proves 11/6 < 2*cos(pi/8). '
'Use the already integrated unconditional counting-to-summability helpers from sums_reduction. The task has no strip_growth_below_mu antecedent and does not invoke the original finite_bridge_sums proof. '
'Insert the following complete WidthThree.lean.inc increment once inside namespace OAI.PolynomialVacuumBridge.Corridor in generated/problem/Submission.lean, after bridgeSummable_firstLengthWeight_of_mu_bound and bridgeSummable_weight_of_summable_firstLengthWeight. The increment opens and closes nested namespace WidthThree and then proves width_three_summability_diagnostic in the outer namespace. Check for declaration-name collisions and reuse exact compatible helpers if a previous delivery has inserted them. Preserve all existing declarations, all current tasks, the original theorem and its unresolved higher-width frontier. Do not replace Submission.lean with the standalone WidthThree.lean validation harness. '
'The finite enumeration is proved directly from frozen definitions; it imports no Python count or external certificate as an axiom. Ordinary decide reduces a finite proposition in the kernel. The source has no placeholder, native_decide, additional axiom or weakened conclusion. Height three alone is proved; this auxiliary task does not resolve all heights.\n\n'
'Local evidence: source SHA256 '+sha(s/'WidthThree.lean')+', increment SHA256 '+sha(s/'WidthThree.lean.inc')+', Mathlib '+prov['mathlibCommit']+', sealed environment '+prov['sealedEnvironmentIdentity']+', actual exit 0 in '+str(result['durationSeconds'])+' seconds, one thread/core, 32 GiB, maxHeartbeats=0, no wall/CPU/invocation cap. All six printed key declarations, including the exact target, depend only on [propext, Classical.choice, Quot.sound]. This package does not itself grant native host task acceptance or OpenAI-hosted certification.\n\n```lean\n'+inc+'```\n')
(s/'task-objective.md').write_text(objective)
task={'id':'width_three_summability_e0dd3d96','kind':'lemma','objective':objective,'dependsOn':['sums_reduction'],'revision':0,'proofPath':'Submission.lean','theoremName':ns+'width_three_summability_diagnostic','type':'Summable ('+ns+'weight (h := 3)) ∧ Summable ('+ns+'firstLengthWeight (h := 3))','groupId':'main'}
(s/'native-task-proposal.json').write_text(json.dumps(task,ensure_ascii=False,indent=2)+'\n')
contract={'schema':'honeycomb-width-three-delivery.v1','createdAt':now,'task':task,'sourceFile':'WidthThree.lean.inc','sourceSHA256':sha(s/'WidthThree.lean.inc'),'sourceBytes':(s/'WidthThree.lean.inc').stat().st_size,'sourceInsertionNamespace':ns[:-1],'harnessFile':'WidthThree.lean','harnessSHA256':sha(s/'WidthThree.lean'),'canonicalSourceDependencies':[ns+'bridgeSummable_firstLengthWeight_of_mu_bound',ns+'bridgeSummable_weight_of_summable_firstLengthWeight'],'canonicalSourceDependencyTask':'sums_reduction','newDeclarations':[ns+n for n in names],'noNewMathematicalAssumptions':True,'originalAllWidthsTargetProved':False,'nativeTaskProofAccepted':False,'openAIHostedCertification':False,'activeRuntimeSourceStateQueueChanged':False,'modelCalled':False}
(s/'delivery-contract.json').write_text(json.dumps(contract,ensure_ascii=False,indent=2)+'\n')
audit={'checkedAt':now,'validationWasRerunDuringArchival':False,'sourceLaunchResultSnapshotSHA256Equal':True,'sourceSHA256':sha(s/'WidthThree.lean'),'incrementSHA256':sha(s/'WidthThree.lean.inc'),'prefixSHA256':sha(s/'CurrentPrefix.lean.inc'),'resultSHA256':sha(s/'summability-01-result.json'),'launchSHA256':sha(s/'summability-01-launch.json'),'stdoutSHA256':sha(s/'summability-01.stdout.log'),'stderrBytes':0,'actualExitCode':0,'durationSeconds':result['durationSeconds'],'toolchain':result['leanToolchain'],'mathlibCommit':result['mathlibCommit'],'sealedEnvironmentIdentity':result['sealedEnvironmentIdentity'],'sourceContainsForbiddenProofKeywords':False,'ordinaryDecideIsKernelReduction':True,'pythonDiagnosticImportedAsProof':False,'checkedDeclarationAxioms':axioms,'axiomsExactlyWhitelist':True,'currentCanonicalStartsWithValidatedPrefix':True,'newDeclarationNameCollisions':collisions,'validationHistory':history,'nativeTaskProofAccepted':False}
(s/'verification-audit.json').write_text(json.dumps(audit,ensure_ascii=False,indent=2)+'\n')
prov.update({'archivedAt':now,'sourceSHA256':sha(s/'WidthThree.lean'),'incrementSHA256':sha(s/'WidthThree.lean.inc'),'prefixSHA256':sha(s/'CurrentPrefix.lean.inc'),'newProofRoute':'Translation invariant non-backtracking continuation count; five steps <=20; finite-list injection; rational beta11/6.','widthTwoReuse':'Canonical prefix and the finite path-list coverage/cardinality pattern only. The height-three local neighbor/count proof is new.','priorPublishedSolutionsRead':False,'noPlaceholderProofs':True,'nativeTaskProofAcceptance':False,'activeStateQueueChanged':False,'noModelCalled':True,'noLeanRerunDuringArchival':True})
(s/'provenance.json').write_text(json.dumps(prov,ensure_ascii=False,indent=2)+'\n')
(s/'assemble.py').write_text("from pathlib import Path\ns = Path(__file__).resolve().parent\nnames = "+repr(checked)+"\nsource = (s / 'CurrentPrefix.lean.inc').read_text() + '\\n' + (s / 'WidthThree.lean.inc').read_text() + '\\n' + '\\n'.join('#check @' + n + '\\n#print axioms ' + n for n in names) + '\\nend PolynomialVacuumBridge.Corridor\\nend OAI\\n'\n(s / 'WidthThree.lean').write_text(source)\n")
(s/'README.md').write_text('''# Honeycomb height-three diagnostic

The unconditional theorem `OAI.PolynomialVacuumBridge.Corridor.width_three_summability_diagnostic` is proved here: `weight` and `firstLengthWeight` are summable on the frozen `BridgePath 3` type. The [final Lean result](summability-01-result.json) records actual exit 0 in 10.050331623060629 seconds. This package proves a fixed-height auxiliary result; the original theorem over all positive heights remains open.

For each of the six vertex kinds, `neighbors` is proved equivalent to frozen adjacency inside the strip. Horizontal translation preserves these finite neighbor sets and the non-backtracking continuation count. The 16 possible normalized incoming edges have at most 20 continuations over the next five steps; `count_five` proves this with ordinary kernel `decide`, independently of Python output. A block induction gives `count a b n <= 16 * 20^(n/5)`. A finite enumerator contains every canonical `BridgePath 3` vertex list, because `Nodup` excludes immediate reversal, and yields cardinality at most `32 * 20^(n/5) <= 32 * (11/6)^n`. The strict bound `11/6 < 2*cos(pi/8)` then lets the existing unconditional counting-to-summability helpers finish the target.

[WidthThree.lean.inc](WidthThree.lean.inc) is the complete insertion-ready increment. Insert it once inside `OAI.PolynomialVacuumBridge.Corridor`, after the existing helpers from integrated `sums_reduction`. It opens and closes its own nested `WidthThree` namespace and proves the target in the outer namespace. [WidthThree.lean](WidthThree.lean) is the standalone validation harness, [CurrentPrefix.lean.inc](CurrentPrefix.lean.inc) is the exact current helper prefix used for validation, and [assemble.py](assemble.py) reproduces the harness. The standalone harness must not replace an active submission.

[task-objective.md](task-objective.md) inlines the complete increment. [native-task-proposal.json](native-task-proposal.json) and [delivery-contract.json](delivery-contract.json) provide the exact new auxiliary task, with `sums_reduction` as an already integrated source dependency. [HANDOFF.txt](HANDOFF.txt) records the insertion point and exact type. [dependency-snapshot.json](dependency-snapshot.json) confirms that the inspected canonical source starts with the validated prefix and has no collision with the proposed new declaration names. This package does not edit the active task plan or queue.

The [final stdout](summability-01.stdout.log) prints types and axioms for six key declarations, including the exact summability target. Every one uses exactly `propext`, `Classical.choice` and `Quot.sound`. The source contains no `sorry`, `admit`, `axiom`, `unsafe` or `native_decide`. [verification-audit.json](verification-audit.json) confirms identical source, saved snapshot, launch and result hashes. Validation used Lean 4.34.1, fixed Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, sealed environment `2d808da67c8ab8ad74458d8a53ecc2ee8da9c63a825e0429439ebf56a9a78c87`, one CPU/thread, 32 GiB and `maxHeartbeats=0`, without wall/CPU/invocation caps. The final passed source was not rerun during archival.

Three real local checks are preserved. The first failed while distributing a finite-set image through conditional neighbor definitions and trying to infer two unbound placeholders in a normalization helper. The second had already verified the exact five-step count but failed to fold `2^4` to `16` in the short-tail bound. The final complete source passed after those elaboration fixes. Every failure retains its exact source snapshot, stdout/stderr, launch and result. `CountBounds.lean.inc` and `Coverage.lean.inc` are intermediate drafting history; `WidthThree.lean.inc` is the sole delivery increment.

The earlier Python block-count diagnostic suggested this route. It is recorded by hash in [provenance.json](provenance.json) and was not imported as a proof, axiom or external oracle. The proof reuses the width-two finite-list enumeration pattern and the unchanged canonical counting-to-summability prefix; it proves the new height-three neighbor, normalization and five-step facts directly.

Normal host native typed acceptance and integration are still required. No all-height proof or OpenAI-hosted certification is claimed. No active runtime, source, state, queue, old cache, frozen package or global configuration was changed. No publisher solution, hidden reasoning or credentials were read; no model was called, and no commit or push was made.
''')
(s/'HANDOFF.txt').write_text(f'''New auxiliary task: {task['id']}
Theorem: {task['theoremName']}
Proof path: Submission.lean
Depends on existing integrated source task: sums_reduction
Exact type:
{task['type']}

Normal delivery:
Parent may add native-task-proposal.json through its normal task-plan queue edit and prioritize it at a natural assignment boundary. task-objective.md / native-task-proposal.json["objective"] inlines the full passed WidthThree.lean.inc code. No queue mutation was performed by this package. Use ordinary native proof delivery/check/integration; this independent local check is not itself a TaskProof receipt.

Insertion:
Insert WidthThree.lean.inc exactly once inside namespace OAI.PolynomialVacuumBridge.Corridor, after these already integrated unconditional helpers:
- {ns}bridgeSummable_firstLengthWeight_of_mu_bound
- {ns}bridgeSummable_weight_of_summable_firstLengthWeight
The increment opens/closes WidthThree and then defines width_three_summability_diagnostic in the outer namespace. All {len(names)} new declaration names were absent at inspection. Preserve existing declarations and the original finite_bridge_sums target. Do not replace Submission.lean with standalone WidthThree.lean.

Mathematics:
Exact width-three neighbors and horizontal-shift invariance are proved from frozen adjacency. Each normalized incoming edge has <=20 five-step non-backtracking continuations, proved by ordinary decide. count_add_bound and strong induction give count a b n<=16*20^(n/5). The canonical BridgePath 3 lists inject into a finite enumerator whose card<=32*20^(n/5). Since 20<=(11/6)^5, the real count is <=32*(11/6)^n. beta_lt_mu proves 11/6<2*cos(pi/8). The two summabilities follow from existing unconditional helpers. No all-width growth assumption or original sorry is used. Height three alone is settled here.

Local verification:
Actual Lean exit0, {result['durationSeconds']} seconds, no timeout.
Source SHA256 {sha(s/'WidthThree.lean')}
Increment SHA256 {sha(s/'WidthThree.lean.inc')}
All six printed key declarations have exactly propext, Classical.choice, Quot.sound; no sorryAx.
No sorry/admit/axiom/unsafe/native_decide in the complete source. All three actual checks and both failed exact source histories are preserved. The final source was not recompiled during archival.

Scope:
Host native TaskProof acceptance and integration remain pending. The all-height original theorem is not proved. No active runtime/source/state/queue/cache/frozen package change, model call, commit or push.
''')
files=sorted(p for p in s.iterdir() if p.is_file() and p.name not in {'delivery-files.json','SHA256SUMS'})
manifest={'schema':'honeycomb-width-three-files.v1','createdAt':now,'files':[{'path':p.name,'bytes':p.stat().st_size,'sha256':sha(p)} for p in files],'excludedSelfFiles':['delivery-files.json','SHA256SUMS'],'fileCountIncludingManifestAndChecksums':len(files)+2}
(s/'delivery-files.json').write_text(json.dumps(manifest,ensure_ascii=False,indent=2)+'\n')
allhashed=sorted([*files,s/'delivery-files.json'],key=lambda p:p.name)
(s/'SHA256SUMS').write_text(''.join(sha(p)+'  '+p.name+'\n' for p in allhashed))
for p in s.glob('*.json'):json.loads(p.read_text())
for f in manifest['files']:
    p=s/f['path']; assert sha(p)==f['sha256'] and p.stat().st_size==f['bytes']
for link in re.findall(r'\]\(([^)]+)\)',(s/'README.md').read_text()):assert (s/link).is_file(),link
assert task['objective'].split('```lean\n',1)[1].removesuffix('```\n')==inc
print(json.dumps({'stage':str(s),'files':len(files)+2,'newDeclarations':len(names),'incrementBytes':len(inc.encode()),'sourceSHA256':sha(s/'WidthThree.lean'),'incrementSHA256':sha(s/'WidthThree.lean.inc'),'deliveryContractSHA256':sha(s/'delivery-contract.json'),'manifestSHA256':sha(s/'delivery-files.json'),'failureCount':sum(h['actualExitCode']!=0 for h in history),'finalActualExitCode':0},indent=2))
