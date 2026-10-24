from pathlib import Path
import json, hashlib, datetime, subprocess, re
B = Path('/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/native-check-hotspot-20261024')
O = Path(__file__).resolve().parent
R = Path('/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/tasks/HoneycombBridgeFiniteness/attempts/workflow-20261024/result.json.runtime')
raw = (R/'state.json').read_bytes(); state = json.loads(raw)
tid = 'width_one_bridge_sums_b433299a'
node = next(n for n in state['cooperation']['tasks'] if n['task']['id']==tid)
goal = next(n for n in state['cooperation']['tasks'] if n['task']['id']=='initial_goal_1')
confined = next(n for n in state['cooperation']['tasks'] if n['task']['id']=='confined_bridge_sums_all_heights_9dd59d27')
assert node['status']=='integrated'
assert node['proof']['commit']=='3c08cbf9e691e7156540ed075ffc3de20edb6652'
assert node['integratedCheck']['commit']=='78602bd19dc2708c16543e3fe55edfe8407a8824'
sha = lambda x: hashlib.sha256(x).hexdigest()
def save(name, obj):
    (O/name).write_text(json.dumps(obj,ensure_ascii=False,indent=2)+'\n')
def norm(text):
    return re.sub(r'\s+','',re.sub(r'/\-.*?\-/','',text,flags=re.S))
now = datetime.datetime.now(datetime.timezone.utc).isoformat()
save('task-record.json',node)
canonical = (B/'honeycomb-confined-finiteness-20261024/CanonicalDefinitions.lean.inc').read_text()
known = {'proof':'lean-b1c75a2ef3a0363767a6edd9','integratedCheck':'lean-909381d19f6680c1615fba09'}
rows, captures = [], []
for key,label in [('proof','proof-source'),('integratedCheck','integrated-source')]:
    proof = node[key]; batch = proof['verification']
    assert proof['passed'] is True and batch['status']=='kernel_verified' and len(batch['results'])==1
    result = batch['results'][0]
    assert result['receiptId']==known[key] and result['theoremName']==node['task']['theoremName']
    assert result['status']=='kernel_verified' and result['sorryCount']==result['admitCount']==result['goalsRemaining']==0
    assert set(result['axioms'])=={'propext','Classical.choice','Quot.sound'}
    assert proof.get('conditions',[])==[]
    assert result['statementHash']==node['assignment']['taskDigest']==proof['taskDigest']==result['leanStatementHash']
    assert result['statementBinding']=='caller-bound-to-committed-declaration'
    command=['git','-C',str(R/'worktree'),'show',proof['commit']+':generated/problem/Submission.lean']
    proc=subprocess.run(command,check=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    assert not proc.stderr
    directory=O/label; directory.mkdir(exist_ok=True)
    (directory/'Submission.lean').write_bytes(proc.stdout)
    text=proc.stdout.decode(); filehash=sha(proc.stdout)
    defs=text[text.index('inductive Vertex where'):text.index('\n\nlemma bridgeCriticalActivity_pos')]
    assert norm(defs)==norm(canonical)
    matches=list(re.finditer(r'(?m)^theorem finite_bridge_sums_at_one\b',text)); assert len(matches)==1
    off=matches[0].start(); declaration=text[off:text.index('theorem finite_bridge_sums :',off)].strip()
    (directory/'target-declaration.lean.txt').write_text(declaration+'\n')
    for change in node['proof']['changes']:
        assert change['after'] in text
    added='\n'.join(c['after'] for c in node['proof']['changes'])
    assert not re.search(r'\b(sorry|admit|finite_bridge_sums)\b',added)
    save(label+'-verification.json',batch)
    stdout=result['stdoutPreview']; start=stdout.index('DEEPSCIENTIST_AXIOMS_BEGIN_')
    (directory/'axioms-output.txt').write_text(stdout[start:]+'\n')
    kernel=next(e['payload'] for e in batch['events'] if e['kind']=='check.kernel_checked')
    opened=next(e['payload'] for e in batch['events'] if e['kind']=='file.opened')
    assert kernel['status']=='kernel_verified' and kernel['exitCode']==0 and kernel['timedOut'] is False and kernel['aborted'] is False
    assert opened['proofHash']==result['proofHash']
    rows.append({'stage':key,'passed':True,'commit':proof['commit'],'seedCommit':proof['seedCommit'],'sourceDigest':proof['sourceDigest'],'sourceFile':str(Path(label)/'Submission.lean'),'sourceFileSHA256':filehash,'sourceFileBytes':len(proc.stdout),'canonicalDefinitionsMatch':True,'all22NewDeclarationsPresentInGitSource':True,'conditions':proof.get('conditions',[]),'receiptId':result['receiptId'],'sessionId':result['sessionId'],'verificationTargetCommit':batch['targetCommit'],'receiptTargetCommit':result['targetCommit'],'status':batch['status'],'startedAt':batch['startedAt'],'checkedAt':batch['checkedAt'],'durationMs':batch['durationMs'],'kernelDurationMs':kernel['durationMs'],'kernelExitCode':kernel['exitCode'],'timedOut':False,'aborted':False,'axioms':result['axioms'],'sorryCount':0,'admitCount':0,'goalsRemaining':0,'proofHash':result['proofHash'],'hostOpenedBytes':opened['bytes'],'sourceDeclarationHash':result['sourceDeclarationHash'],'theoremDeclarationHash':result['theoremDeclarationHash'],'statementHash':result['statementHash'],'statementBinding':result['statementBinding'],'elaboratedDeclarationType':result['elaboratedDeclarationType'],'changedDeclarationsInThisRecord':len(proof['changes']),'originalGoalReferencedInNewDeclarations':False,'referenceCoverage':{'taskRecordReferencesPresent':'references' in proof,'resultDeclarationReferencesPresent':'declarationReferences' in result,'stdoutReferenceMarkerIsNull':bool(re.search(r'DS_DECL_REFERENCES_[^:]+:null',stdout)),'rootReferenceSHACrosscheckAvailable':False},'identityNote':'Public committed source SHA, complete-source digest, host proofHash and sandbox targetCommit are separate identities. No equality between full-source SHA and host proofHash is asserted.'})
    captures.append({'command':command,'exitCode':0,'stdoutBytes':len(proc.stdout),'stdoutSHA256':filehash,'stderrBytes':0})
log=R.parents[2]/'solve.log'; rawlog=log.read_bytes(); selected=[]; index=[]
for number,line in enumerate(rawlog.splitlines(),1):
    try: event=json.loads(line)
    except (ValueError,TypeError): continue
    if event.get('runId')==state['runId'] and event.get('taskId')==tid and event.get('event') in {'delivery_published','task_checked','task_integrated'}:
        assert all(k not in event for k in ['reasoning','messages','command','output','content'])
        selected.append(line); index.append({'line':number,'at':event['at'],'event':event['event'],'commit':event.get('commit'),'receiptIds':event.get('receiptIds',[])})
assert any(e['event']=='task_checked' for e in index)
assert any(e['event']=='task_integrated' and e['commit']==node['integratedCheck']['commit'] for e in index)
(O/'events-safe-raw.jsonl').write_bytes(b'\n'.join(selected)+b'\n')
save('events-index.json',index); save('verification-summary.json',rows); save('git-source-capture.json',captures)
save('confined-status-only.json',{'taskId':confined['task']['id'],'status':confined['status'],'proofPassed':confined.get('proof',{}).get('passed'),'integratedPassed':confined.get('integratedCheck',{}).get('passed'),'integratedCommit':confined.get('integratedCheck',{}).get('commit'),'note':'State only. Full native confined evidence remains in the prior separate frozen package.'})
save('identity.json',{'capturedAt':now,'runId':state['runId'],'phase':state['phase'],'model':state['model'],'buildDigest':state['buildDigest'],'environmentDigest':state['environmentDigest'],'taskDigest':state['taskDigest'],'methodDigest':state['methodDigest'],'evaluatorDigest':state['evaluatorDigest'],'providerProfileDigest':state['providerProfileDigest'],'canonicalCommitAtSnapshot':state['cooperation']['canonicalCommit'],'integratedTaskCanonicalCommit':node['integratedCheck']['commit'],'taskId':tid,'nativeTaskDigest':node['assignment']['taskDigest'],'assignmentId':node['assignment']['assignmentId'],'dependencies':node['assignment']['dependencies'],'stateFile':str(R/'state.json'),'stateBytes':len(raw),'stateSHA256':sha(raw),'rawEventLog':str(log),'rawEventLogBytes':len(rawlog),'rawEventLogSHA256':sha(rawlog),'auxiliaryStatement':node['task']['type'],'proofPath':node['task']['proofPath'],'leanToolchain':'leanprover/lean4:v4.34.1','mathlibCommit':'d13f23b723b8a846827a245b89c10fc7d3f11612','toolchainIdentitySource':'Inherited fixed run environment; independently checked width-one package provenance corroborates versions.'})
save('result.json',{'schema':'honeycomb-native-width-one.v1','frozenAt':now,'status':'native-task-integrated','taskId':tid,'theoremName':node['task']['theoremName'],'type':node['task']['type'],'scope':'All six canonical summability clauses at height one only.','nativeProofPassed':True,'nativeIntegratedCheckPassed':True,'canonicalCommit':node['integratedCheck']['commit'],'proofCommit':node['proof']['commit'],'conditions':[],'axioms':['propext','Classical.choice','Quot.sound'],'sorryCount':0,'admitCount':0,'goalsRemaining':0,'proofDurationMs':node['proof']['verification']['durationMs'],'integratedCheckDurationMs':node['integratedCheck']['verification']['durationMs'],'referenceCoverage':'Host reports no declarationReferences and null stdout reference marker; no root-reference SHA equality claimed. Exact git source and committed-declaration binding are preserved.','originalGoal':{'taskId':goal['task']['id'],'status':goal['status'],'conditions':goal.get('proof',{}).get('conditions',[])},'originalTheoremAccepted':False,'openAIHostedCertification':False,'activeChainChangedByArchive':False,'leanRerun':False,'queueEdited':False,'gitMutation':False,'previousPackagesModified':False,'topLevelResultsReadmeOrManifestChanged':False})
(O/'README.md').write_text('''# Honeycomb 高度一的六项正式集成回执

`width_one_bridge_sums_b433299a` 已通过独立原生 TaskProof 检查与 canonical 集成检查。正式定理 `OAI.PolynomialVacuumBridge.Corridor.finite_bridge_sums_at_one` 在高度 1 证明完整 BridgePath 与 ConfinedBridgePath 的 weight、firstLengthWeight 和归一化 firstLengthWeight 六项可求和。

原生证明回执为 `lean-b1c75a2ef3a0363767a6edd9`，耗时 21.382 秒；集成回执为 `lean-909381d19f6680c1615fba09`，耗时 18.179 秒。两项均 kernel_verified、exit 0、无 timeout/abort，sorry/admit/goals 全为 0，无 conditions，仅依赖 propext、Classical.choice、Quot.sound。

proof commit 为 `3c08cbf9e691e7156540ed075ffc3de20edb6652`，集成 canonical commit 为 `78602bd19dc2708c16543e3fe55edfe8407a8824`。[proof 公开源码](proof-source/Submission.lean) 与 [集成公开源码](integrated-source/Submission.lean) 由对应精确 commit 的 git show 只读取出，22 个新增声明均存在，官方定义未改变。

本次两份宿主回执未提供 references/declarationReferences，stdout 的 DS_DECL_REFERENCES 标记为 null；因此不能像 prior confined 包一样核对根 reference SHA。两份源码 SHA、sourceDigest、proofHash 与验证 targetCommit 分别保存在 [verification-summary.json](verification-summary.json)，不混称它们相等。正式回执仍具有 caller-bound-to-committed-declaration 绑定、精确 statementHash 和原生内核通过状态。

[task-record.json](task-record.json) 冻结完整对应任务记录。两份原始 verification JSON、原生公理输出、[raw 安全宿主事件](events-safe-raw.jsonl)、[事件索引](events-index.json) 和 [身份摘要](identity.json) 提供可复查证据。该任务只依赖已集成的 sums_reduction，没有假设未证的全高度 strip_growth_below_mu，也未在新增声明中调用原目标。

本结果只证明高度 1 的六项结论。全高度 confined 三项已有集成状态仅记录于 [confined-status-only.json](confined-status-only.json)，完整证据保留于先前冻结包。完整原题 initial_goal_1 仍 conditional/未解，一般高度完整 BridgePath 的前三个子句缺口仍在；此结果不属于 OpenAI 托管认证。

本次只在这个新包冻结已有正式证据与公开 git 源码，没有重编 Lean、修改活动源码/runtime/state/队列/缓存/配置或旧包，没有编辑结果库顶层 README/manifest，也没有 commit/push。[delivery-files.json](delivery-files.json) 与 [SHA256SUMS](SHA256SUMS) 列出精确交付。
''')
payload=sorted(p for p in O.rglob('*') if p.is_file() and p.name not in {'delivery-files.json','SHA256SUMS'})
save('delivery-files.json',{'schema':'honeycomb-native-width-one-delivery.v1','frozenAt':now,'files':[{'name':str(p.relative_to(O)),'bytes':p.stat().st_size,'sha256':sha(p.read_bytes())} for p in payload]})
(O/'SHA256SUMS').write_text(''.join(sha(p.read_bytes())+'  '+str(p.relative_to(O))+'\n' for p in sorted(O.rglob('*')) if p.is_file() and p.name!='SHA256SUMS'))
print(json.dumps({'directory':str(O),'files':len([p for p in O.rglob('*') if p.is_file()]),'status':'native-task-integrated','proofReceipt':rows[0]['receiptId'],'integrationReceipt':rows[1]['receiptId'],'original':goal['status']},ensure_ascii=False))
