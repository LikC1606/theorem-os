from pathlib import Path
import datetime
import hashlib
import json
import re
import subprocess


H = Path('/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/native-check-hotspot-20261024')
O = Path(__file__).resolve().parent
R = Path('/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/tasks/HoneycombBridgeFiniteness/attempts/workflow-20261024/result.json.runtime')
TID = 'width_two_summability_diagnostic'
EXPECTED = {
    'proof': ('a862efb5ee31eaf58ca174b79730f960a7b89302', 'lean-30a9b8d0f88ea68d0cdfffd7'),
    'integratedCheck': ('0d4bd1c55e8dff31f375e1d5dbe243c799489133', 'lean-280acb880d3c011f61e534da'),
}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def save(name, value):
    (O / name).write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n')


def norm(text):
    return re.sub(r'\s+', '', re.sub(r'/\-.*?\-/', '', text, flags=re.S))


def git_source(commit, relative):
    command = ['git', '-C', str(R / 'worktree'), 'show', commit + ':' + relative]
    result = subprocess.run(command, check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    assert not result.stderr
    return result.stdout, {
        'command': command, 'exitCode': result.returncode,
        'stdoutBytes': len(result.stdout), 'stdoutSHA256': sha(result.stdout), 'stderrBytes': 0,
    }


state_bytes = (R / 'state.json').read_bytes()
state = json.loads(state_bytes)
node = next(n for n in state['cooperation']['tasks'] if n['task']['id'] == TID)
goal = next(n for n in state['cooperation']['tasks'] if n['task']['id'] == 'initial_goal_1')
assert node['status'] == 'integrated'
assert node['task']['type'] == 'Summable (OAI.PolynomialVacuumBridge.Corridor.weight (h := 2)) ∧ Summable (OAI.PolynomialVacuumBridge.Corridor.firstLengthWeight (h := 2))'
assert goal['status'] == 'conditional'
now = datetime.datetime.now(datetime.timezone.utc).isoformat()
save('task-record.json', node)
canonical = (H / 'honeycomb-confined-finiteness-20261024/CanonicalDefinitions.lean.inc').read_text()
changes = node['proof']['changes']
assert len(changes) == 20
added = '\n'.join(change['after'] for change in changes)
assert not re.search(r'\b(sorry|admit|finite_bridge_sums|axiom|unsafe|native_decide)\b', added)

summaries = []
captures = []
for key, label in [('proof', 'proof-source'), ('integratedCheck', 'integrated-source')]:
    proof = node[key]
    batch = proof['verification']
    assert proof['commit'] == EXPECTED[key][0]
    assert proof['passed'] is True and batch['status'] == 'kernel_verified'
    assert len(batch['results']) == 1
    receipt = batch['results'][0]
    assert receipt['receiptId'] == EXPECTED[key][1]
    assert receipt['theoremName'] == node['task']['theoremName']
    assert receipt['status'] == 'kernel_verified'
    assert receipt['sorryCount'] == receipt['admitCount'] == receipt['goalsRemaining'] == 0
    assert set(receipt['axioms']) == {'propext', 'Classical.choice', 'Quot.sound'}
    assert proof.get('conditions', []) == []
    assert receipt['statementHash'] == node['assignment']['taskDigest'] == proof['taskDigest'] == receipt['leanStatementHash']
    assert receipt['statementBinding'] == 'caller-bound-to-committed-declaration'
    source, capture = git_source(proof['commit'], 'generated/problem/Submission.lean')
    captures.append(capture)
    directory = O / label
    directory.mkdir()
    (directory / 'Submission.lean').write_bytes(source)
    text = source.decode()
    definitions = text[text.index('inductive Vertex where'):text.index('\n\nlemma bridgeCriticalActivity_pos')]
    assert norm(definitions) == norm(canonical)
    for change in changes:
        assert change['after'] in text
    matches = list(re.finditer(r'(?m)^theorem width_two_summability_diagnostic\b', text))
    assert len(matches) == 1
    start = matches[0].start()
    declaration = text[start:text.index('theorem finite_bridge_sums :', start)].strip()
    (directory / 'target-declaration.lean.txt').write_text(declaration + '\n')
    save(label + '-verification.json', batch)
    stdout = receipt['stdoutPreview']
    axiom_start = stdout.index('DEEPSCIENTIST_AXIOMS_BEGIN_')
    axiom_end = stdout.index('\nDEEPSCIENTIST_AXIOMS_END_', axiom_start)
    axiom_end = stdout.find('\n', axiom_end + 1) if '\n' in stdout[axiom_end + 1:] else len(stdout)
    (directory / 'axioms-output.txt').write_text(stdout[axiom_start:axiom_end] + '\n')
    kernel = next(e['payload'] for e in batch['events'] if e['kind'] == 'check.kernel_checked')
    opened = next(e['payload'] for e in batch['events'] if e['kind'] == 'file.opened')
    assert kernel['status'] == 'kernel_verified' and kernel['exitCode'] == 0
    assert kernel['timedOut'] is False and kernel['aborted'] is False
    assert opened['proofHash'] == receipt['proofHash']
    assert receipt['targetCommit'] == batch['targetCommit']
    summary = {
        'stage': key, 'passed': True, 'commit': proof['commit'], 'seedCommit': proof['seedCommit'],
        'sourceDigest': proof['sourceDigest'], 'sourceFile': str(Path(label) / 'Submission.lean'),
        'sourceFileSHA256': sha(source), 'sourceFileBytes': len(source),
        'canonicalDefinitionsMatch': True, 'all20NewDeclarationsPresentInGitSource': True,
        'conditions': proof.get('conditions', []), 'receiptId': receipt['receiptId'],
        'sessionId': receipt['sessionId'], 'verificationTargetCommit': batch['targetCommit'],
        'receiptTargetCommit': receipt['targetCommit'], 'status': batch['status'],
        'startedAt': batch['startedAt'], 'checkedAt': batch['checkedAt'], 'durationMs': batch['durationMs'],
        'kernelDurationMs': kernel['durationMs'], 'kernelExitCode': kernel['exitCode'],
        'timedOut': False, 'aborted': False, 'axioms': receipt['axioms'],
        'sorryCount': 0, 'admitCount': 0, 'goalsRemaining': 0,
        'proofHash': receipt['proofHash'], 'hostOpenedBytes': opened['bytes'],
        'sourceDeclarationHash': receipt['sourceDeclarationHash'],
        'theoremDeclarationHash': receipt['theoremDeclarationHash'],
        'statementHash': receipt['statementHash'], 'statementBinding': receipt['statementBinding'],
        'elaboratedDeclarationType': receipt['elaboratedDeclarationType'],
        'changedDeclarationsInThisRecord': len(proof['changes']),
        'originalGoalReferencedInNewDeclarations': False,
        'referenceCoverage': {
            'taskRecordReferencesPresent': 'references' in proof,
            'resultDeclarationReferencesPresent': 'declarationReferences' in receipt,
            'stdoutReferenceMarkerIsNull': bool(re.search(r'DS_DECL_REFERENCES_[^:]+:null', stdout)),
            'rootReferenceSHACrosscheckAvailable': False,
        },
        'identityNote': 'Public full-source SHA, complete-source digest, host proofHash and sandbox targetCommit are separate identities. No full-source SHA / host proofHash equality is asserted.',
    }
    assert summary['referenceCoverage']['taskRecordReferencesPresent'] is False
    assert summary['referenceCoverage']['resultDeclarationReferencesPresent'] is False
    assert summary['referenceCoverage']['stdoutReferenceMarkerIsNull'] is True
    summaries.append(summary)

toolchain, toolchain_capture = git_source(node['integratedCheck']['commit'], 'generated/problem/lean-toolchain')
manifest_bytes, manifest_capture = git_source(node['integratedCheck']['commit'], 'generated/problem/lake-manifest.json')
captures.extend([toolchain_capture, manifest_capture])
manifest = json.loads(manifest_bytes)
mathlib = next(p for p in manifest['packages'] if p['name'] == 'mathlib')
assert toolchain.decode().strip() == 'leanprover/lean4:v4.34.1'
assert mathlib['rev'] == 'd13f23b723b8a846827a245b89c10fc7d3f11612'
save('toolchain-provenance.json', {
    'commit': node['integratedCheck']['commit'], 'leanToolchain': toolchain.decode().strip(),
    'leanToolchainFileSHA256': sha(toolchain), 'lakeManifestSHA256': sha(manifest_bytes),
    'mathlibPackage': mathlib, 'captureMethod': 'Read-only git show of exact integration commit; no Lean invocation.',
})

log = R.parents[2] / 'solve.log'
rawlog = log.read_bytes()
selected = []
event_index = []
offset = 0
for number, line in enumerate(rawlog.splitlines(keepends=True), 1):
    try:
        event = json.loads(line)
    except (ValueError, TypeError):
        offset += len(line)
        continue
    if event.get('runId') == state['runId'] and event.get('taskId') == TID and event.get('event') in {'delivery_published', 'task_checked', 'task_integrated'}:
        assert all(k not in event for k in ['reasoning', 'messages', 'command', 'output', 'content'])
        selected.append(line)
        event_index.append({
            'line': number, 'byteOffset': offset, 'lineBytes': len(line), 'rawLineSHA256': sha(line),
            'at': event['at'], 'event': event['event'], 'commit': event.get('commit'),
            'receiptIds': event.get('receiptIds', []),
        })
    offset += len(line)
assert any(e['event'] == 'task_checked' for e in event_index)
assert any(e['event'] == 'task_integrated' and e['commit'] == node['integratedCheck']['commit'] for e in event_index)
(O / 'events-safe-raw.jsonl').write_bytes(b''.join(selected))
save('events-index.json', event_index)
save('verification-summary.json', summaries)
save('git-source-capture.json', captures)
save('identity.json', {
    'capturedAt': now, 'runId': state['runId'], 'phase': state['phase'], 'turns': state['turns'],
    'model': state['model'], 'buildDigest': state['buildDigest'], 'environmentDigest': state['environmentDigest'],
    'taskDigest': state['taskDigest'], 'methodDigest': state['methodDigest'], 'evaluatorDigest': state['evaluatorDigest'],
    'providerProfileDigest': state['providerProfileDigest'], 'canonicalCommitAtSnapshot': state['cooperation']['canonicalCommit'],
    'integratedTaskCanonicalCommit': node['integratedCheck']['commit'], 'taskId': TID,
    'nativeTaskDigest': node['assignment']['taskDigest'], 'assignmentId': node['assignment']['assignmentId'],
    'dependencies': node['assignment']['dependencies'], 'stateFile': str(R / 'state.json'),
    'stateBytes': len(state_bytes), 'stateSHA256': sha(state_bytes), 'rawEventLog': str(log),
    'rawEventLogBytes': len(rawlog), 'rawEventLogSHA256': sha(rawlog),
    'auxiliaryStatement': node['task']['type'], 'proofPath': node['task']['proofPath'],
    'leanToolchain': toolchain.decode().strip(), 'mathlibCommit': mathlib['rev'],
    'toolchainIdentitySource': 'Exact integration commit lean-toolchain and lake-manifest.json.',
})
save('result.json', {
    'schema': 'honeycomb-native-width-two.v1', 'frozenAt': now, 'status': 'native-task-integrated',
    'taskId': TID, 'theoremName': node['task']['theoremName'], 'type': node['task']['type'],
    'scope': 'Only width-two full BridgePath weight and firstLengthWeight summability; helper supplies the explicit bound 4*(sqrt(3))^n.',
    'nativeProofPassed': True, 'nativeIntegratedCheckPassed': True,
    'canonicalCommit': node['integratedCheck']['commit'], 'proofCommit': node['proof']['commit'],
    'conditions': [], 'axioms': summaries[0]['axioms'], 'sorryCount': 0, 'admitCount': 0, 'goalsRemaining': 0,
    'proofDurationMs': node['proof']['verification']['durationMs'],
    'integratedCheckDurationMs': node['integratedCheck']['verification']['durationMs'],
    'referenceCoverage': 'No references/declarationReferences in either host receipt; stdout DS_DECL_REFERENCES is null. No root-reference SHA equality claimed. Exact git source and committed-declaration binding are preserved.',
    'originalGoal': {'taskId': goal['task']['id'], 'status': goal['status'], 'conditions': goal.get('proof', {}).get('conditions', [])},
    'originalTheoremAccepted': False, 'openAIHostedCertification': False,
    'activeChainChangedByArchive': False, 'leanRerun': False, 'queueEdited': False, 'gitMutation': False,
    'previousPackagesModified': False, 'topLevelResultsReadmeOrManifestChanged': False,
})
(O / 'README.md').write_text('''# Honeycomb 宽度二的原生集成回执

`width_two_summability_diagnostic` 已通过原生 TaskProof 与 canonical 集成检查。定理 `OAI.PolynomialVacuumBridge.Corridor.width_two_summability_diagnostic` 无条件证明宽度 2 的完整 BridgePath 的 weight 与 firstLengthWeight 两项可求和。20 个新增声明还给出有限路径计数上界 `4 * (sqrt 3)^n`，并证明 `sqrt 3 < 2 * cos (pi / 8)`，供既有可求和约化使用。

原生证明回执为 `lean-30a9b8d0f88ea68d0cdfffd7`，耗时 23.908 秒；集成回执为 `lean-280acb880d3c011f61e534da`，耗时 24.130 秒。两项均 kernel_verified、exit 0、无 timeout/abort，目标的 sorry/admit/goals 全为 0，无 conditions，只依赖 propext、Classical.choice、Quot.sound。

proof commit 为 `a862efb5ee31eaf58ca174b79730f960a7b89302`，集成 commit 为 `0d4bd1c55e8dff31f375e1d5dbe243c799489133`。[proof 公开源码](proof-source/Submission.lean) 与 [集成公开源码](integrated-source/Submission.lean) 来自对应精确 commit 的只读 git show。20 个新增声明均存在，canonical 定义与前一冻结基准一致，新增声明没有调用未证原目标。

两份宿主回执均没有 references/declarationReferences，stdout 的 DS_DECL_REFERENCES 标记为 null。因此不能独立核对根 reference SHA，也不宣称公开整文件 SHA 等于宿主 proofHash。两种 SHA、sourceDigest、验证 sandbox targetCommit、statementHash 与 caller-bound-to-committed-declaration 绑定分别保存在 [verification-summary.json](verification-summary.json)。精确 integration commit 的 Lean 4.34.1 和 Mathlib revision 保存在 [toolchain-provenance.json](toolchain-provenance.json)。

任务依赖数组为空；其公开证明使用 canonical 中既有的两个可求和约化辅助定理。该结论只覆盖宽度 2 的两项可求和，尚未证明所有宽度的增长界或完整原题。`initial_goal_1` 仍 conditional/未解，归档的整文件中仍保留该原目标的 sorry；零 sorry 的说法仅针对本辅助任务的实际验证目标及依赖闭包。本结果不是 OpenAI 托管认证。

[task-record.json](task-record.json) 冻结对应任务记录；两份原始 verification JSON、公理输出、[安全原生日志](events-safe-raw.jsonl)、[事件索引](events-index.json) 与 [身份摘要](identity.json) 保留核查证据。本次未调用 Lean、修改活动 state/source/runtime/cache/队列/配置、旧包或结果库顶层 README/manifest，未 commit/push。[delivery-files.json](delivery-files.json) 与 [SHA256SUMS](SHA256SUMS) 提供精确交付清单。
''')

payload = sorted(p for p in O.rglob('*') if p.is_file() and p.name not in {'delivery-files.json', 'SHA256SUMS'})
save('delivery-files.json', {
    'schema': 'honeycomb-native-width-two-delivery.v1', 'frozenAt': now,
    'files': [{'name': str(p.relative_to(O)), 'bytes': p.stat().st_size, 'sha256': sha(p.read_bytes())} for p in payload],
})
(O / 'SHA256SUMS').write_text(''.join(
    sha(p.read_bytes()) + '  ' + str(p.relative_to(O)) + '\n'
    for p in sorted(O.rglob('*')) if p.is_file() and p.name != 'SHA256SUMS'
))
print(json.dumps({
    'directory': str(O), 'files': len([p for p in O.rglob('*') if p.is_file()]),
    'status': 'native-task-integrated', 'proofReceipt': summaries[0]['receiptId'],
    'integrationReceipt': summaries[1]['receiptId'], 'original': goal['status'],
}, ensure_ascii=False))
