from pathlib import Path
import datetime, hashlib, json, re, subprocess, sys, shutil
H=Path('/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/native-check-hotspot-20261024')
R=Path('/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/tasks/HoneycombBridgeFiniteness/attempts/workflow-20261024/result.json.runtime')
width=int(sys.argv[1]); assert width in (3,4,5)
word={3:'three',4:'four',5:'five'}[width]
tid={3:'width_three_summability_e0dd3d96',4:'width_four_summability_a8462a19',5:'width_five_summability_ba0a1c09'}[width]
raw=(R/'state.json').read_bytes();state=json.loads(raw);node=next(n for n in state['cooperation']['tasks'] if n['task']['id']==tid)
assert node['status']=='integrated', 'Task has not integrated; no archive is created.'
assert node['proof']['passed'] is True and node['integratedCheck']['passed'] is True
O=H/f'honeycomb-native-width-{word}-20261025';O.mkdir()
shutil.copyfile(Path(__file__),O/'freeze.py')
sha=lambda x:hashlib.sha256(x).hexdigest()
def save(n,x):(O/n).write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def git(commit,relative):
 cmd=['git','-C',str(R/'worktree'),'show',commit+':'+relative];p=subprocess.run(cmd,check=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE);assert not p.stderr
 return p.stdout,{'command':cmd,'exitCode':p.returncode,'stdoutBytes':len(p.stdout),'stdoutSHA256':sha(p.stdout),'stderrBytes':0}
def norm(s):return re.sub(r'\s+','',re.sub(r'/\-.*?\-/','',s,flags=re.S))
now=datetime.datetime.now(datetime.timezone.utc).isoformat();goal=next(n for n in state['cooperation']['tasks'] if n['task']['id']=='initial_goal_1')
assert goal['status']=='conditional'
canonical=(H/'honeycomb-confined-finiteness-20261024/CanonicalDefinitions.lean.inc').read_text()
short=node['task']['theoremName'].split('.')[-1];changes=node['proof']['changes'];nchanges=len(changes)
target=next(c['after'] for c in changes if c['name'].split('.')[-1]==short)
assert not re.search(r'\b(sorry|admit|finite_bridge_sums|axiom|unsafe|native_decide)\b','\n'.join(c['after'] for c in changes))
save('task-record.json',node);rows=[];captures=[]
for key,label in [('proof','proof-source'),('integratedCheck','integrated-source')]:
 p=node[key];v=p['verification'];assert p['passed'] is True and v['status']=='kernel_verified' and len(v['results'])==1
 r=v['results'][0];assert r['status']=='kernel_verified' and r['theoremName']==node['task']['theoremName']
 assert r['sorryCount']==r['admitCount']==r['goalsRemaining']==0 and set(r['axioms'])=={'propext','Classical.choice','Quot.sound'}
 assert not p.get('conditions',[]) and r['statementHash']==r['leanStatementHash']==p['taskDigest']==node['assignment']['taskDigest']
 assert r['statementBinding']=='caller-bound-to-committed-declaration' and r['targetCommit']==v['targetCommit']
 source,cap=git(p['commit'],'generated/problem/Submission.lean');captures.append(cap);d=O/label;d.mkdir();(d/'Submission.lean').write_bytes(source);text=source.decode()
 defs=text[text.index('inductive Vertex where'):text.index('\n\nlemma bridgeCriticalActivity_pos')];assert norm(defs)==norm(canonical)
 for c in changes:assert c['after'] in text
 assert text.count(target)==1
 (d/'target-declaration.lean.txt').write_text(target.strip()+'\n');save(label+'-verification.json',v)
 stdout=r['stdoutPreview'];a=stdout.index('DEEPSCIENTIST_AXIOMS_BEGIN_');m=re.search(r'DEEPSCIENTIST_AXIOMS_END_[^\n]+',stdout[a:]);assert m
 (d/'axioms-output.txt').write_text(stdout[a:a+m.end()]+'\n')
 kernel=next(e['payload'] for e in v['events'] if e['kind']=='check.kernel_checked');opened=next(e['payload'] for e in v['events'] if e['kind']=='file.opened')
 assert kernel['exitCode']==0 and kernel['timedOut'] is False and kernel['aborted'] is False and opened['proofHash']==r['proofHash']
 rows.append({'stage':key,'passed':True,'commit':p['commit'],'seedCommit':p['seedCommit'],'sourceDigest':p['sourceDigest'],'sourceFile':str(Path(label)/'Submission.lean'),'sourceFileSHA256':sha(source),'sourceFileBytes':len(source),'canonicalDefinitionsMatch':True,'allNewDeclarationsPresentInGitSource':True,'newDeclarationCount':nchanges,'conditions':p.get('conditions',[]),'receiptId':r['receiptId'],'sessionId':r['sessionId'],'verificationTargetCommit':v['targetCommit'],'receiptTargetCommit':r['targetCommit'],'status':v['status'],'startedAt':v['startedAt'],'checkedAt':v['checkedAt'],'durationMs':v['durationMs'],'kernelDurationMs':kernel['durationMs'],'kernelExitCode':0,'timedOut':False,'aborted':False,'axioms':r['axioms'],'sorryCount':0,'admitCount':0,'goalsRemaining':0,'proofHash':r['proofHash'],'hostOpenedBytes':opened['bytes'],'sourceDeclarationHash':r['sourceDeclarationHash'],'theoremDeclarationHash':r['theoremDeclarationHash'],'statementHash':r['statementHash'],'statementBinding':r['statementBinding'],'elaboratedDeclarationType':r['elaboratedDeclarationType'],'originalGoalReferencedInNewDeclarations':False,'referenceCoverage':{'taskRecordReferencesPresent':'references' in p,'resultDeclarationReferencesPresent':'declarationReferences' in r,'stdoutReferenceMarkerIsNull':bool(re.search(r'DS_DECL_REFERENCES_[^:]+:null',stdout)),'rootReferenceSHACrosscheckPerformed':False},'identityNote':'Public full-source SHA, sourceDigest, host proofHash and sandbox targetCommit are separate identities. No full-source SHA / proofHash equality or root-reference SHA binding is asserted.'})
tool,cap=git(node['integratedCheck']['commit'],'generated/problem/lean-toolchain');captures.append(cap);manifest,cap=git(node['integratedCheck']['commit'],'generated/problem/lake-manifest.json');captures.append(cap);mathlib=next(p for p in json.loads(manifest)['packages'] if p['name']=='mathlib')
assert tool.decode().strip()=='leanprover/lean4:v4.34.1' and mathlib['rev']=='d13f23b723b8a846827a245b89c10fc7d3f11612'
save('toolchain-provenance.json',{'commit':node['integratedCheck']['commit'],'leanToolchain':tool.decode().strip(),'leanToolchainFileSHA256':sha(tool),'lakeManifestSHA256':sha(manifest),'mathlibPackage':mathlib,'captureMethod':'Read-only git show of exact integration commit; no Lean invocation.'})
log=R.parents[2]/'solve.log';rawlog=log.read_bytes();selected=[];index=[];offset=0
for i,line in enumerate(rawlog.splitlines(keepends=True),1):
 try:e=json.loads(line)
 except (ValueError,TypeError):offset+=len(line);continue
 if e.get('runId')==state['runId'] and e.get('taskId')==tid and e.get('event') in {'delivery_published','task_checked','task_integrated'}:
  assert all(k not in e for k in ['reasoning','messages','command','output','content']);selected.append(line);index.append({'line':i,'byteOffset':offset,'lineBytes':len(line),'rawLineSHA256':sha(line),'at':e['at'],'event':e['event'],'commit':e.get('commit'),'receiptIds':e.get('receiptIds',[])})
 offset+=len(line)
assert any(x['event']=='task_checked' for x in index) and any(x['event']=='task_integrated' and x['commit']==node['integratedCheck']['commit'] for x in index)
(O/'events-safe-raw.jsonl').write_bytes(b''.join(selected));save('events-index.json',index);save('verification-summary.json',rows);save('git-source-capture.json',captures)
save('identity.json',{'capturedAt':now,'runId':state['runId'],'phase':state['phase'],'turns':state['turns'],'model':state['model'],'buildDigest':state['buildDigest'],'environmentDigest':state['environmentDigest'],'taskDigest':state['taskDigest'],'methodDigest':state['methodDigest'],'evaluatorDigest':state['evaluatorDigest'],'providerProfileDigest':state['providerProfileDigest'],'canonicalCommitAtSnapshot':state['cooperation']['canonicalCommit'],'integratedTaskCanonicalCommit':node['integratedCheck']['commit'],'taskId':tid,'nativeTaskDigest':node['assignment']['taskDigest'],'assignmentId':node['assignment']['assignmentId'],'dependencies':node['assignment']['dependencies'],'stateFile':str(R/'state.json'),'stateBytes':len(raw),'stateSHA256':sha(raw),'rawEventLog':str(log),'rawEventLogBytes':len(rawlog),'rawEventLogSHA256':sha(rawlog),'auxiliaryStatement':node['task']['type'],'proofPath':node['task']['proofPath'],'leanToolchain':tool.decode().strip(),'mathlibCommit':mathlib['rev']})
result={'schema':f'honeycomb-native-width-{word}.v1','frozenAt':now,'status':'native-task-integrated','taskId':tid,'theoremName':node['task']['theoremName'],'type':node['task']['type'],'scope':f'Only width {width} full BridgePath weight and firstLengthWeight summability.','nativeProofPassed':True,'nativeIntegratedCheckPassed':True,'canonicalCommit':node['integratedCheck']['commit'],'proofCommit':node['proof']['commit'],'conditions':[],'axioms':rows[0]['axioms'],'sorryCount':0,'admitCount':0,'goalsRemaining':0,'proofDurationMs':rows[0]['durationMs'],'integratedCheckDurationMs':rows[1]['durationMs'],'referenceCoverage':rows[0]['referenceCoverage'],'originalGoal':{'taskId':goal['task']['id'],'status':goal['status'],'conditions':goal.get('proof',{}).get('conditions',[])},'originalTheoremAccepted':False,'openAIHostedCertification':False,'activeChainChangedByArchive':False,'leanRerun':False,'queueEdited':False,'gitMutation':False,'previousPackagesModified':False,'topLevelResultsReadmeOrManifestChanged':False};save('result.json',result)
refs='两份回执均未提供 references/declarationReferences，stdout 的引用标记均为 null。' if all(not x['referenceCoverage']['taskRecordReferencesPresent'] and not x['referenceCoverage']['resultDeclarationReferencesPresent'] and x['referenceCoverage']['stdoutReferenceMarkerIsNull'] for x in rows) else '引用字段的实际存在情况逐阶段保存在 verification-summary.json；原始 verification 保留实际内容。'
(O/'README.md').write_text(f'''# Honeycomb 宽度 {width} 原生集成回执\n\n`{tid}` 已通过原生 TaskProof 和 canonical 集成检查，无条件证明宽度 {width} 的完整 BridgePath weight 与 firstLengthWeight 两项可求和。\n\n证明回执 `{rows[0]['receiptId']}` 耗时 {rows[0]['durationMs']/1000:.3f} 秒，集成回执 `{rows[1]['receiptId']}` 耗时 {rows[1]['durationMs']/1000:.3f} 秒。两项均 kernel_verified、exit 0、无 timeout/abort，目标 sorry/admit/goals 全为 0，无 conditions，仅有 propext、Classical.choice、Quot.sound。\n\nproof commit 为 `{node['proof']['commit']}`，integration commit 为 `{node['integratedCheck']['commit']}`。精确 commit 的 [证明源码](proof-source/Submission.lean) 和 [集成源码](integrated-source/Submission.lean) 只读取自 git show。{nchanges} 个新增声明全部存在，canonical 定义与前一冻结基准相同，新增声明未调用未证原目标。\n\n{refs} 不宣称公开整文件 SHA 等于 host proofHash，也不宣称已核对根 reference SHA。[verification-summary.json](verification-summary.json) 分别记录公开源 SHA、sourceDigest、proofHash、sandbox targetCommit、精确 statementHash 与 caller-bound-to-committed-declaration 绑定。\n\n本结论只覆盖固定宽度 {width}。原题 initial_goal_1 仍 conditional/未解，公开整文件仍保留原题 sorry；零 sorry 仅指本辅助目标及其实际依赖闭包。本结果不是 OpenAI 托管认证。\n\n[任务记录](task-record.json)、原始 verification JSON、公理输出、[安全原生日志](events-safe-raw.jsonl)、[事件索引](events-index.json)、[身份](identity.json) 与 [工具链身份](toolchain-provenance.json) 保留完整证据。本次未重跑 Lean、未改活动 state/source/runtime/cache/队列/配置、旧包或结果库顶层 README/manifest，未 commit/push。[delivery-files.json](delivery-files.json) 与 [SHA256SUMS](SHA256SUMS) 提供精确交付清单。\n''')
payload=sorted(p for p in O.rglob('*') if p.is_file() and p.name not in {'delivery-files.json','SHA256SUMS'});save('delivery-files.json',{'schema':f'honeycomb-native-width-{word}-delivery.v1','frozenAt':now,'files':[{'name':str(p.relative_to(O)),'bytes':p.stat().st_size,'sha256':sha(p.read_bytes())} for p in payload]})
(O/'SHA256SUMS').write_text(''.join(sha(p.read_bytes())+'  '+str(p.relative_to(O))+'\n' for p in sorted(O.rglob('*')) if p.is_file() and p.name!='SHA256SUMS'))
for p in O.rglob('*.json'):json.loads(p.read_text())
for line in (O/'SHA256SUMS').read_text().splitlines():
 expected,name=line.split('  ',1);assert sha((O/name).read_bytes())==expected
for f in json.loads((O/'delivery-files.json').read_text())['files']:assert (O/f['name']).stat().st_size==f['bytes'] and sha((O/f['name']).read_bytes())==f['sha256']
for _,target in re.findall(r'\[([^\]]+)\]\(([^)]+)\)',(O/'README.md').read_text()):assert (O/target).is_file()
print(json.dumps({'directory':str(O),'status':'native-task-integrated','files':len([p for p in O.rglob('*') if p.is_file()]),'proofReceipt':rows[0]['receiptId'],'integrationReceipt':rows[1]['receiptId'],'original':goal['status'],'resultSHA256':sha((O/'result.json').read_bytes()),'deliveryFilesSHA256':sha((O/'delivery-files.json').read_bytes())},ensure_ascii=False))
