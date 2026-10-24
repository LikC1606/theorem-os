from pathlib import Path
import datetime, hashlib, json, re, collections, difflib
B = Path('/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/native-check-hotspot-20261024')
O = Path(__file__).resolve().parent
R = Path('/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/tasks/HoneycombBridgeFiniteness/attempts/workflow-20261024/result.json.runtime')
sha = lambda x: hashlib.sha256(x).hexdigest()
def save(name, value):
    (O / name).write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n')
def norm(text):
    text = re.sub(r'/\-.*?\-/', '', text, flags=re.S)
    text = re.sub(r'(?m)^\s*open scoped BigOperators\s*$', '', text)
    return re.sub(r'\s+', '', text)
def warning_normalized(text):
    return norm(text.replace(', Prod.fst', '').replace('letI :=', 'let _ :=').replace('summable_of_finite_support', 'summable_of_hasFiniteSupport'))
configs = [
 ('confined_bridge_sums_all_heights_9dd59d27', 'researcher-1', 'worktree-2', 'bridgeConfined_sums', 'def bridgeBoxColumn :', [B/'honeycomb-confined-finiteness-20261024/ExistingColumnCode.lean.inc', B/'honeycomb-confined-finiteness-20261024/ConfinedFiniteness.lean.inc']),
 ('width_one_bridge_sums_b433299a', 'researcher-2', 'worktree-3', 'finite_bridge_sums_at_one', 'def hexX :', [B/'honeycomb-width-one-20261024/WidthOne.lean.inc']),
]
now = datetime.datetime.now(datetime.timezone.utc).isoformat()
state_raw = (R/'state.json').read_bytes()
s = json.loads(state_raw)
nodes = {n['task']['id']: n for n in s['cooperation']['tasks']}
workers = {w['id']: w for w in s['workers']}
rows, sources, artifacts = [], [], []
canonical = (B/'honeycomb-confined-finiteness-20261024/CanonicalDefinitions.lean.inc').read_text()
for tid, wid, tree, theorem, start, fragments in configs:
    n, w = nodes[tid], workers[wid]
    sp = R/tree/'generated/problem/Submission.lean'
    raw = sp.read_bytes(); text = raw.decode()
    expected = '\n'.join(f.read_text() for f in fragments)
    expected = expected[expected.index(start):]
    actual = text[text.index(start):text.index('theorem finite_bridge_sums :')]
    unchanged_math = norm(expected) == norm(actual)
    warning_only = warning_normalized(expected) == warning_normalized(actual)
    assert warning_only
    ds = [m.group(1) for m in re.finditer(r'(?m)^\s*(?:(?:noncomputable|private|protected)\s+)*(?:def|lemma|theorem|structure|inductive)\s+([^\s(:]+)', text)]
    assert ds.count(theorem) == 1 and len(ds) == len(set(ds))
    definitions = text[text.index('inductive Vertex where'):text.index('\n\nlemma bridgeCriticalActivity_pos')]
    assert norm(definitions) == norm(canonical)
    off = re.search(r'(?m)^theorem '+re.escape(theorem)+r'\b', text).start()
    declaration = text[off:text.index('theorem finite_bridge_sums :', off)].strip()
    dn = wid+'-target-declaration.lean.txt'
    (O/dn).write_text(declaration+'\n')
    diff_name = wid+'-public-proof-vs-verified.diff'
    (O/diff_name).write_text(''.join(difflib.unified_diff(expected.splitlines(True), actual.splitlines(True), fromfile='verified increment', tofile='public worker source')))
    rows.append({'taskId':tid, 'status':n['status'], 'attempts':n['attempts'], 'assignment':n['assignment'], 'typePreflight':n.get('typePreflight'), 'theoremName':n['task']['theoremName'], 'type':n['task']['type'], 'proofPath':n['task']['proofPath'], 'dependsOn':n['task']['dependsOn'], 'dependenciesStatus':{d:nodes[d]['status'] for d in n['task']['dependsOn']}, 'feedback':n.get('feedback'), 'proof':n.get('proof'), 'receipts':{k:[x for x in s['cooperation'][k] if x.get('taskId')==tid] for k in ['proofReadyRecords','deliveryReceipts','deliveries']}, 'worker':{k:w.get(k) for k in ['id','phase','sessionTaskId','sessionAssignmentId','scheduling','lastActivity']}})
    sources.append({'taskId':tid, 'workerId':wid, 'sourcePath':str(sp), 'sourceBytes':len(raw), 'sourceSHA256':sha(raw), 'sourceMtimeUTC':datetime.datetime.fromtimestamp(sp.stat().st_mtime,datetime.timezone.utc).isoformat(), 'targetNamePresentOnce':True, 'duplicateDeclarationNames':[], 'matchModuloCommentsWhitespaceUnusedScopedOpen':unchanged_math, 'matchAlsoAllowingThreeKnownWarningCleanups':warning_only, 'knownWarningCleanups':[] if unchanged_math else ['unused Prod.fst simp argument removed', 'letI replaced by let _', 'deprecated summable_of_finite_support replaced by summable_of_hasFiniteSupport'], 'verifiedFragments':[{'path':str(p),'sha256':sha(p.read_bytes())} for p in fragments], 'canonicalDefinitionsMatch':True, 'incrementContainsSorryOrAdmit':bool(re.search(r'\b(sorry|admit)\b',actual)), 'originalGoalPlaceholderRemains':True, 'incrementReferencesOriginalGoal':bool(re.search(r'\bfinite_bridge_sums\b',actual)), 'targetExcerpt':dn, 'sourceDifference':diff_name, 'assignedTypeMatchesTargetHeader':True, 'checkScope':'Read-only header and source comparison; no new kernel proof check.'})
    cp = R/tree/'COOPERATION.json'; cr = cp.read_bytes(); coop=json.loads(cr)
    peer = next(p for p in coop['peers'] if p['id']==tid)
    assert all(p.read_text() in peer['objective'] for p in fragments)
    rp = R/tree/'RESEARCH.md'; rr=rp.read_bytes()
    artifacts.append({'workerId':wid, 'research':{'path':str(rp),'bytes':len(rr),'sha256':sha(rr)}, 'cooperation':{'path':str(cp),'bytes':len(cr),'sha256':sha(cr)}, 'peer':{k:peer[k] for k in ['id','owner','status','taskDigest','dependsOn']}, 'fullVerifiedInputInObjective':True, 'objectiveDigest':peer.get('objectiveDigest')})
log = R.parents[2]/'solve.log'; raw_log=log.read_bytes()
start_at = min(workers[c[1]]['scheduling']['since'] for c in configs)
allow = {'event','at','workerId','taskId','taskDigest','activity','itemType','status','kind','evidence','proofAcceptance','reason','assignmentKey','seedCommit','runId','operation','turn','totalTurns','turnId','compiledContentDigest','messageDigest','messageBytes','contentDigest','requiredTaskIds','included','omitted','usedBytes','mandatoryBytes','optionalBytes','maxOptionalBytes','maxBytes','id','affectedTasks'}
event_allow = {'worker_activity','task_assigned','task_type_preflight','task_checked','task_integrated','proof_ready','proof_ready_recorded','proof_ready_requested','delivery_received','delivery_published','turn_started','context_compiled','context_dispatched','context_restarted','context_compaction_started','context_compaction_completed','research_action','edit_received','edit_applied','edit_rejected'}
metadata=[]; counts=collections.Counter(); activity=collections.defaultdict(collections.Counter)
for line_no,line in enumerate(raw_log.splitlines(),1):
    try: event=json.loads(line)
    except (ValueError,TypeError): continue
    if event.get('runId')!=s['runId'] or event.get('at',0)<start_at: continue
    if event.get('workerId') not in [c[1] for c in configs] and event.get('taskId') not in [c[0] for c in configs]: continue
    counts[event.get('event')]+=1
    if event.get('event')=='worker_activity': activity[event['workerId']][event.get('activity','')+':'+event.get('itemType','')]+=1
    if event.get('event') in event_allow: metadata.append({'line':line_no,**{k:v for k,v in event.items() if k in allow}})
(O/'events-metadata.jsonl').write_text(''.join(json.dumps(e,ensure_ascii=False)+'\n' for e in metadata))
save('capture.json', {'capturedAt':now,'runId':s['runId'],'stateFile':str(R/'state.json'),'stateBytes':len(state_raw),'stateSHA256':sha(state_raw),'phase':s['phase'],'canonicalCommit':s['cooperation']['canonicalCommit'],'planVersion':s['cooperation']['planVersion'],'eventLog':str(log),'eventLogBytes':len(raw_log),'eventLogSHA256':sha(raw_log),'captureStartAt':start_at,'captureLastEventAt':max(e['at'] for e in metadata),'policy':'Only public source/RESEARCH/COOPERATION and selected state metadata. Top-level event whitelist excludes command/model item/reasoning bodies. No full state/objective copied.'})
save('task-state-summary.json',rows); save('source-adoption-check.json',sources); save('public-worker-artifacts.json',artifacts)
proof_events=[e for e in metadata if e.get('taskId') in [c[0] for c in configs] and e['event'] in ['task_checked','task_integrated','proof_ready','proof_ready_recorded','proof_ready_requested','delivery_received','delivery_published']]
save('event-summary.json',{'eventCounts':dict(counts),'activityCounts':{k:dict(v) for k,v in activity.items()},'targetHostProofEvents':proof_events,'compilationInterpretation':'CommandExecution activity cannot identify Lean invocations; no duplicate compilation established from allowed metadata.'})
save('result.json',{'schema':'honeycomb-summability-adoption-health.v1','capturedAt':now,'status':'no-concrete-adoption-error-observed','conclusion':'Both complete proof increments are saved in the assigned public source files. Targets and canonical definitions match. Width-one code differs only in comments/whitespace/unused scope openings; confined code additionally cleans three documented warnings. Both tasks remain in model execution without proof delivery/acceptance at this snapshot.','concreteErrors':[],'repairRequired':False,'mathematicalCodeSaved':True,'duplicateDeclarationsObserved':False,'missingDependenciesObserved':False,'deliveryProtocolErrorObserved':False,'formalAcceptanceObserved':False,'unnecessaryCompilationObserved':'not-established','limitations':['Read-only source audit does not replace native kernel acceptance.','Allowed metadata cannot establish the count or necessity of worker Lean invocations.','Existing original goal placeholder remains unresolved and is not called by either increment.'],'actions':{'activeFilesModified':False,'queueEdited':False,'leanInvoked':False,'verifiedPackageRerun':False,'gitUsed':False},'nextStep':'Let existing assignments finish normal proof-ready, TaskProof and integration; no repair justified by this snapshot.'})
(O/'README.md').write_text('''# Honeycomb summability adoption health

没有发现需要修复的正式采用错误。两份完整证明都已保存到对应 worker 的公开 `generated/problem/Submission.lean`：researcher-1 保存全高度 confined 三项合取，researcher-2 保存高度 1 的六项合取。目标声明各出现一次，无重复声明，官方定义未变，精确目标类型匹配。两项类型预检均已 closed-type-elaborated；width-one 的 sums_reduction 依赖已 integrated。

width-one 证明只删了注释、空白和未使用的 scoped-open。confined 证明还按原提示删除 unused Prod.fst、把 letI 改为 let _、把废弃的 summable_of_finite_support 改成 summable_of_hasFiniteSupport。这些精确差异保存在公开源码 diff 中；没有发现数学缺口，但当前源码仍须由原生宿主独立检查，不能沿用旧 SHA 声称已验收。

截点中两项仍为 running，当前 assignment 没有 proof-ready、正式交付回执或 TaskProof。两个 RESEARCH.md 仍为空；完整输入和实际目标代码已分别出现在 COOPERATION 与源文件中。此时属于模型执行中，没有证据证明交付协议错误。

公开事件表明 worker 持续有 commandExecution 和模型活动元数据。允许读取的字段没有命令正文，无法据此推断 Lean 编译次数或证明多余编译。原目标 finite_bridge_sums 的既有占位仍在，两个新增增量均未调用它。

证据见 [任务与回执](task-state-summary.json)、[源码比对](source-adoption-check.json)、[公开产物](public-worker-artifacts.json)、[事件摘要](event-summary.json)、[安全事件元数据](events-metadata.jsonl) 和 [精确截点](capture.json)。两份目标声明和源码 diff 也是公开产物的小型摘录。

本任务只写入此新证据目录；未改活动文件、队列或配置，未运行 Lean、重检已通过包、读取隐藏推理或 ProducedSolution，也未 commit/push。本检查没有产生修复项；下一步等待原任务完成正常 proof-ready、TaskProof 与 integration。
''')
payload=sorted(p for p in O.iterdir() if p.is_file() and p.name not in {'delivery-files.json','SHA256SUMS'})
save('delivery-files.json',{'schema':'honeycomb-summability-adoption-health-delivery.v1','files':[{'name':p.name,'bytes':p.stat().st_size,'sha256':sha(p.read_bytes())} for p in payload]})
(O/'SHA256SUMS').write_text(''.join(sha(p.read_bytes())+'  '+p.name+'\n' for p in sorted(O.iterdir()) if p.is_file() and p.name!='SHA256SUMS'))
print(json.dumps({'directory':str(O),'files':len(list(O.iterdir())),'status':'no-concrete-adoption-error-observed','formalAcceptance':False},ensure_ascii=False))
