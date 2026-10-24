from pathlib import Path
import datetime, hashlib, json, re

s=Path(__file__).resolve().parent
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
inc=(s/'WidthTwo.lean.inc').read_text(); source=(s/'WidthTwo.lean').read_text(); prefix=(s/'CurrentPrefix.lean.inc').read_text()
launch=json.loads((s/'summability-01-launch.json').read_text()); result=json.loads((s/'summability-01-result.json').read_text())
assert sha(s/'WidthTwo.lean')==sha(s/'summability-01-source.lean')==launch['sourceSHA256']==result['sourceSHA256']
assert result['actualExitCode']==0 and result['timedOut'] is False
assert all(result[k]==v for k,v in launch.items())
assert (s/'summability-01.stderr.log').stat().st_size==0
prov=json.loads((s/'provenance.json').read_text())
checked=['WidthTwo.nextPairs_card','WidthTwo.continuations_card','WidthTwo.path_mem_allPaths','WidthTwo.path_card','WidthTwo.stripGrowthAtTwo','width_two_summability_diagnostic']
ns='OAI.PolynomialVacuumBridge.Corridor.'
assert source==prefix+'\n'+inc+'\n'+'\n'.join('#check @'+n+'\n#print axioms '+n for n in checked)+'\nend PolynomialVacuumBridge.Corridor\nend OAI\n'
stdout=(s/'summability-01.stdout.log').read_text()
axioms={n:re.findall(r'[A-Za-z_.]+',b) for n,b in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]+)\]",stdout)}
assert set(axioms)=={ns+n for n in checked}
assert all(set(a)=={'propext','Classical.choice','Quot.sound'} for a in axioms.values())
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',source)
root=Path('/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/tasks/HoneycombBridgeFiniteness/attempts/workflow-20261024/result.json.runtime')
state=json.loads((root/'state.json').read_text()); coop=state['cooperation']
oldtask=next(e for e in coop['tasks'] if e.get('task',{}).get('id')=='width_two_summability_diagnostic')
dep=next(e for e in coop['tasks'] if e.get('task',{}).get('id')=='sums_reduction')
canonical=root/'worktree/generated/problem/Submission.lean'
assert canonical.read_text().startswith(prefix)
names=[]; localns=''
for line in inc.splitlines():
    if line=='namespace WidthTwo':localns='WidthTwo.'
    if line=='end WidthTwo':localns=''
    m=re.match(r'(?:(?:noncomputable )?def|lemma|theorem)\s+([^\s:{]+)',line)
    if m:names.append(localns+m.group(1))
assert len(names)==20
collisions=[n for n in names if re.search(r'^(?:(?:noncomputable )?def|lemma|theorem)\s+'+re.escape(n.rsplit('.',1)[-1])+r'(?=[\s:{])',canonical.read_text(),re.M)]
assert not collisions
history=[]
for p in sorted(s.glob('*-result.json')):
    r=json.loads(p.read_text())
    history.append({'label':p.name.removesuffix('-result.json'),'actualExitCode':r['actualExitCode'],'durationSeconds':r['durationSeconds'],'sourceSHA256':r['sourceSHA256'],'resultFile':p.name,'stdoutLog':Path(r['stdoutLog']).name})
assert len(history)==7
(s/'dependency-snapshot.json').write_text(json.dumps({'inspectedAt':now,'runId':state['runId'],'canonicalCommit':coop['canonicalCommit'],'planVersion':coop['planVersion'],'canonicalSource':str(canonical),'canonicalSourceSHA256':sha(canonical),'canonicalStartsWithValidatedPrefix':True,'validatedPrefixSHA256':sha(s/'CurrentPrefix.lean.inc'),'existingTask':{k:oldtask['task'].get(k) for k in ['id','kind','revision','proofPath','theoremName','type','dependsOn']},'existingTaskStatus':oldtask['status'],'canonicalSourceDependency':{k:dep['task'].get(k) for k in ['id','kind','revision','theoremName','type']},'canonicalSourceDependencyStatus':dep['status'],'canonicalSourceDependencyIntegratedCheckPassed':dep.get('integratedCheck',{}).get('passed'),'canonicalSourceDependencyIntegratedCheckCommit':dep.get('integratedCheck',{}).get('commit'),'existingUnconditionalHelperDeclarations':[ns+'bridgeSummable_firstLengthWeight_of_mu_bound',ns+'bridgeSummable_weight_of_summable_firstLengthWeight'],'newDeclarationNameCollisions':collisions,'activeStateChanged':False},ensure_ascii=False,indent=2)+'\n')
objective=('Prove the existing exact fixed-width-two summability diagnostic and deliver it through the ordinary assignment proof protocol. A complete unconditional proof increment is included below and has passed an independent local Lean 4.34.1 kernel check; normal host typed verification and canonical integration are still required. '
'This is the same pending task and same conclusion, not a new or conditional task. Preserve its current theoremName, type, dependencies, and all other tasks; no all-width strip-growth hypothesis is assumed. '
'The proof explicitly enumerates neighbors of the four width-two vertex kinds, proves at most three non-backtracking two-step extensions after any incoming edge, recursively bounds continuation counts by 2*3^(n/2), injects each canonical BridgePath 2 vertex list into the finite enumerator, and derives the count bound 4*3^(n/2) <= 4*(sqrt 3)^n. It proves sqrt 3 < 2*cos(pi/8) and uses the existing canonical unconditional counting-to-summability helpers from integrated sums_reduction. '
'Insert the following entire WidthTwo.lean.inc increment once inside namespace OAI.PolynomialVacuumBridge.Corridor in generated/problem/Submission.lean, after bridgeSummable_firstLengthWeight_of_mu_bound and bridgeSummable_weight_of_summable_firstLengthWeight. The increment itself opens and closes the nested WidthTwo namespace and then proves width_two_summability_diagnostic in the outer namespace. '
'Check for declaration-name collisions and reuse exact compatible existing helpers if a prior delivery has already inserted them. Preserve all existing declarations, including finite_bridge_sums and all-width tasks. Do not replace Submission.lean with the standalone WidthTwo.lean validation harness. '
'The complete proof and finite enumeration use no placeholder, imported solution, extra axiom or native_decide. Widths h>=3 remain outside this fixed-width diagnostic.\n\n'
'Local evidence: source SHA256 '+sha(s/'WidthTwo.lean')+', increment SHA256 '+sha(s/'WidthTwo.lean.inc')+', Mathlib '+prov['mathlibCommit']+', sealed environment '+prov['sealedEnvironmentIdentity']+', actual Lean exit 0 in '+str(result['durationSeconds'])+' seconds, one thread/core, 32 GiB, maxHeartbeats=0, no wall/CPU/call cap. All six printed key declarations, including the exact target, depend only on [propext, Classical.choice, Quot.sound]. This evidence does not itself constitute native host task acceptance or OpenAI-hosted certification.\n\n```lean\n'+inc+'```\n')
(s/'task-objective.md').write_text(objective)
proposal=dict(oldtask['task']);proposal['objective']=objective
(s/'native-task-handoff.json').write_text(json.dumps(proposal,ensure_ascii=False,indent=2)+'\n')
contract={'schema':'honeycomb-width-two-delivery.v1','createdAt':now,'existingTaskId':'width_two_summability_diagnostic','existingTaskStatus':oldtask['status'],'requestedMutation':'Parent may update only the existing task objective and priority through its normal queue edit. This package performs no queue mutation.','task':proposal,'theoremName':proposal['theoremName'],'type':proposal['type'],'sourceFile':'WidthTwo.lean.inc','sourceSHA256':sha(s/'WidthTwo.lean.inc'),'sourceBytes':(s/'WidthTwo.lean.inc').stat().st_size,'sourceInsertionNamespace':ns[:-1],'harnessFile':'WidthTwo.lean','harnessSHA256':sha(s/'WidthTwo.lean'),'canonicalSourceDependencies':[ns+'bridgeSummable_firstLengthWeight_of_mu_bound',ns+'bridgeSummable_weight_of_summable_firstLengthWeight'],'canonicalSourceDependencyTask':'sums_reduction','newDeclarations':[ns+n for n in names],'noNewMathematicalAssumptions':True,'originalAllWidthsTargetProved':False,'nativeTaskProofAccepted':False,'openAIHostedCertification':False,'activeRuntimeSourceStateQueueChanged':False,'modelCalled':False}
(s/'delivery-contract.json').write_text(json.dumps(contract,ensure_ascii=False,indent=2)+'\n')
audit={'checkedAt':now,'validationWasRerunDuringArchival':False,'sourceLaunchResultSnapshotSHA256Equal':True,'sourceSHA256':sha(s/'WidthTwo.lean'),'incrementSHA256':sha(s/'WidthTwo.lean.inc'),'prefixSHA256':sha(s/'CurrentPrefix.lean.inc'),'resultSHA256':sha(s/'summability-01-result.json'),'launchSHA256':sha(s/'summability-01-launch.json'),'stdoutSHA256':sha(s/'summability-01.stdout.log'),'stderrBytes':0,'actualExitCode':0,'durationSeconds':result['durationSeconds'],'toolchain':result['leanToolchain'],'mathlibCommit':result['mathlibCommit'],'sealedEnvironmentIdentity':result['sealedEnvironmentIdentity'],'sourceContainsForbiddenProofKeywords':False,'checkedDeclarationAxioms':axioms,'axiomsExactlyWhitelist':True,'currentCanonicalStartsWithValidatedPrefix':True,'newDeclarationNameCollisions':collisions,'validationHistory':history,'nativeTaskProofAccepted':False}
(s/'verification-audit.json').write_text(json.dumps(audit,ensure_ascii=False,indent=2)+'\n')
prov.update({'archivedAt':now,'sourceSHA256':sha(s/'WidthTwo.lean'),'incrementSHA256':sha(s/'WidthTwo.lean.inc'),'prefixSHA256':sha(s/'CurrentPrefix.lean.inc'),'newProofRoute':'Explicit width-two neighbor enumeration and two-step non-backtracking continuation bound. Counting includes an overapproximation of all simple paths.','inheritedResearchProofReused':False,'priorPublishedSolutionsRead':False,'noPlaceholderProofs':True,'nativeTaskProofAcceptance':False,'activeStateQueueChanged':False,'noModelCalled':True,'noLeanRerunDuringArchival':True})
(s/'provenance.json').write_text(json.dumps(prov,ensure_ascii=False,indent=2)+'\n')
(s/'assemble.py').write_text("from pathlib import Path\ns = Path(__file__).resolve().parent\nnames = "+repr(checked)+"\nsource = (s / 'CurrentPrefix.lean.inc').read_text() + '\\n' + (s / 'WidthTwo.lean.inc').read_text() + '\\n' + '\\n'.join('#check @' + n + '\\n#print axioms ' + n for n in names) + '\\nend PolynomialVacuumBridge.Corridor\\nend OAI\\n'\n(s / 'WidthTwo.lean').write_text(source)\n")
(s/'README.md').write_text('''# Honeycomb width-two diagnostic

The unconditional theorem `OAI.PolynomialVacuumBridge.Corridor.width_two_summability_diagnostic` is proved here: both `weight` and `firstLengthWeight` are summable on the frozen `BridgePath 2` type. The [final Lean result](summability-01-result.json) has actual exit 0 in 21.30641626403667 seconds. This closes the fixed-width diagnostic, while the original all-width theorem remains open.

The proof enumerates the exact neighbors of the four width-two vertex kinds. After any incoming edge, at most three two-step continuations avoid immediate reversal (`WidthTwo.nextPairs_card`). A recursive finite enumerator has at most `2 * 3^(n/2)` continuations; every canonical `BridgePath 2` is included because its `Nodup` condition prevents immediate reversal. Thus any finite set of length-`n` paths has cardinality at most `4 * 3^(n/2)`, and hence at most `4 * (sqrt 3)^n`. The strict inequality `sqrt 3 < 2*cos(pi/8)` makes the current canonical counting-to-summability helpers applicable.

[WidthTwo.lean.inc](WidthTwo.lean.inc) contains the complete insertion-ready increment. Insert it once inside `OAI.PolynomialVacuumBridge.Corridor`, after the existing unconditional helpers from integrated `sums_reduction`. It defines a nested `WidthTwo` namespace and proves the selected diagnostic theorem in the outer namespace. [WidthTwo.lean](WidthTwo.lean) is the standalone validation harness; do not use it to replace an active submission. [CurrentPrefix.lean.inc](CurrentPrefix.lean.inc) is the exact existing declaration prefix used for validation, and [assemble.py](assemble.py) reproduces the harness.

[task-objective.md](task-objective.md) inlines the entire increment for the existing pending task, and [native-task-handoff.json](native-task-handoff.json) preserves its exact task fields with only the objective replaced. [delivery-contract.json](delivery-contract.json) records the exact type, names, source dependencies and intended normal host delivery. [HANDOFF.txt](HANDOFF.txt) gives the insertion instructions. [dependency-snapshot.json](dependency-snapshot.json) records that the current canonical source starts with the validated prefix and has no declaration-name collision at inspection.

The [final stdout](summability-01.stdout.log) prints exact types and axioms for six key declarations, including the target. All have exactly `propext`, `Classical.choice` and `Quot.sound`; the source contains no `sorry`, `admit`, `axiom`, `unsafe` or `native_decide`. [verification-audit.json](verification-audit.json) checks the source/launch/result/snapshot hashes and the axiom output. Validation used Lean 4.34.1, fixed Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, sealed environment `2d808da67c8ab8ad74458d8a53ecc2ee8da9c63a825e0429439ebf56a9a78c87`, one CPU/thread, 32 GiB, and `maxHeartbeats=0`, without wall/CPU/invocation caps. The final result was not rerun during archival.

Seven real local checks are retained: five failed elaboration attempts, a passing local neighbor lemma check, and the final passing complete theorem. The failures concerned finite-set simplification, a shadowed membership name, an unavailable arithmetic lemma name, and list-length/finite-set coercion normalization. Their exact source snapshots, stdout/stderr and result metadata remain in the package. The route did not require a mathematical assumption, change of target, counterexample exclusion, or alteration of the frozen definitions. The three intermediate `.lean.inc` drafting files are retained only as development history; `WidthTwo.lean.inc` is the sole delivery increment.

This package supplies independent local kernel evidence. Normal host native task verification and integration remain pending. It does not certify the original all-width theorem or OpenAI-hosted acceptance. No active runtime, source, state, queue, existing cache or global configuration was changed. No publisher solution, hidden reasoning or credentials were read; no model was called, and no commit or push was made.
''')
(s/'HANDOFF.txt').write_text(f'''Existing task: width_two_summability_diagnostic
Theorem: {proposal['theoremName']}
Proof path: {proposal['proofPath']}
Exact existing type (unchanged):
{proposal['type']}

Normal delivery:
The existing task was pending at inspection. Parent may update only its objective to task-objective.md / native-task-handoff.json["objective"] and adjust priority through normal queueRunEdit. The full validated increment is inlined in that objective. Do not create a duplicate diagnostic, rewrite its conclusion, replace Submission.lean, or treat this local package as a native TaskProof receipt. This package did not edit the queue.

Insert WidthTwo.lean.inc once inside namespace OAI.PolynomialVacuumBridge.Corridor, after these existing canonical unconditional declarations supplied by integrated sums_reduction:
- {ns}bridgeSummable_firstLengthWeight_of_mu_bound
- {ns}bridgeSummable_weight_of_summable_firstLengthWeight
The increment opens and closes WidthTwo itself, then defines the target in the outer namespace. All 20 declaration names were absent from inspected canonical source. Preserve all existing declarations and the original finite_bridge_sums target. Existing task dependencies are unchanged; mentioning sums_reduction identifies the already integrated source helpers, not a new antecedent.

Proof facts:
Every width-two vertex has the explicitly enumerated neighbors; each incoming edge has at most 3 non-backtracking two-step extensions. continuations_card proves <=2*3^(m/2) by two-step induction. path_mem_allPaths proves inclusion of each frozen BridgePath 2. path_card proves <=4*3^(n/2), path_card_real upgrades to <=4*(sqrt3)^n. sqrt_three_lt_mu proves sqrt3<2*cos(pi/8), and stripGrowthAtTwo selects C=4, beta=sqrt3. The final diagnostic uses the existing counting-to-summability helper and its weight corollary. No strip_growth_below_mu assumption or original sorry is used.

Final local verification:
Actual Lean exit 0, {result['durationSeconds']} seconds; no timeout.
Source SHA256 {sha(s/'WidthTwo.lean')}
Increment SHA256 {sha(s/'WidthTwo.lean.inc')}
All 6 printed key declaration axioms exactly propext, Classical.choice, Quot.sound; no sorryAx.
Source contains no sorry/admit/axiom/unsafe/native_decide. Exact source, result, launch, stdout/stderr and 5 failed elaboration histories retained. See verification-audit.json, provenance.json and SHA256SUMS. No unchanged Lean rerun during archival.

Scope:
Both summabilities at width 2 only. Widths h>=3 and the original all-width acceptance remain open here. No host task acceptance, hosted certification, activity mutation, model call, commit or push.
''')
files=sorted(p for p in s.iterdir() if p.is_file() and p.name not in {'delivery-files.json','SHA256SUMS'})
manifest={'schema':'honeycomb-width-two-files.v1','createdAt':now,'files':[{'path':p.name,'bytes':p.stat().st_size,'sha256':sha(p)} for p in files],'excludedSelfFiles':['delivery-files.json','SHA256SUMS'],'fileCountIncludingManifestAndChecksums':len(files)+2}
(s/'delivery-files.json').write_text(json.dumps(manifest,ensure_ascii=False,indent=2)+'\n')
allhashed=sorted([*files,s/'delivery-files.json'],key=lambda p:p.name)
(s/'SHA256SUMS').write_text(''.join(sha(p)+'  '+p.name+'\n' for p in allhashed))
for p in s.glob('*.json'):json.loads(p.read_text())
for f in manifest['files']:
    p=s/f['path'];assert sha(p)==f['sha256'] and p.stat().st_size==f['bytes']
for link in re.findall(r'\]\(([^)]+)\)',(s/'README.md').read_text()):assert (s/link).is_file(),link
assert proposal['objective'].split('```lean\n',1)[1].removesuffix('```\n')==inc
print(json.dumps({'stage':str(s),'files':len(files)+2,'incrementBytes':len(inc.encode()),'sourceSHA256':sha(s/'WidthTwo.lean'),'incrementSHA256':sha(s/'WidthTwo.lean.inc'),'deliveryContractSHA256':sha(s/'delivery-contract.json'),'manifestSHA256':sha(s/'delivery-files.json'),'failureCount':sum(h['actualExitCode']!=0 for h in history),'finalActualExitCode':0},indent=2))
