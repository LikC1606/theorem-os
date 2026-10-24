"""Local scheduling experiment for two already-running native Lean checks."""
from pathlib import Path
import datetime
import hashlib
import json
import os
import sys
import time

stage = Path(__file__).resolve().parent
receipt_path = stage / 'locality-receipt.json'
targets = [
    (169941, 'SnakyConditional', '712ecd4ee1a6cf29e5dc08a07510910addc1870b4039327836646b7a0f16daab', list(range(80, 88))),
    (1179438, 'CharacterVarieties', '0ec8e7e2fbe9ff7f2d4c849c7558c152e24d707d79943d6f7ac08d0b27fa98c9', list(range(16, 24))),
]


def stamp():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def snapshot(pid):
    root = Path('/proc') / str(pid)
    raw = (root / 'stat').read_text()
    fields = raw[raw.rfind(')') + 2:].split()
    threads = []
    for task in sorted((root / 'task').iterdir()):
        try:
            raw = (task / 'stat').read_text()
            values = raw[raw.rfind(')') + 2:].split()
            sched = dict(line.split(':', 1) for line in (task / 'sched').read_text().splitlines() if ':' in line)
            sched = {key.strip(): value.strip() for key, value in sched.items()}
            run_ns, wait_ns, slices = map(int, (task / 'schedstat').read_text().split())
            threads.append({
                'tid': int(task.name), 'startTicks': values[19], 'cpu': int(values[36]),
                'runtimeNs': run_ns, 'waitNs': wait_ns, 'slices': slices,
                'migrations': int(sched['se.nr_migrations']),
                'affinity': sorted(os.sched_getaffinity(int(task.name))),
            })
        except (FileNotFoundError, ProcessLookupError):
            pass
    return {'pid': pid, 'startTicks': fields[19], 'at': stamp(), 'monotonic': time.monotonic(), 'threads': threads}


def save(receipt):
    temporary = receipt_path.with_suffix('.tmp')
    temporary.write_text(json.dumps(receipt, indent=2) + '\n')
    temporary.replace(receipt_path)


def restore(entry):
    pid = entry['pid']
    try:
        current = snapshot(pid)
    except FileNotFoundError:
        return 'process_exited'
    if current['startTicks'] != entry['before']['startTicks']:
        return 'pid_reused_not_modified'
    originals = {item['tid']: item for item in entry['before']['threads']}
    fallback = originals[pid]['affinity']
    for item in current['threads']:
        previous = originals.get(item['tid'])
        mask = previous['affinity'] if previous and previous['startTicks'] == item['startTicks'] else fallback
        try:
            os.sched_setaffinity(item['tid'], mask)
        except ProcessLookupError:
            pass
    return 'restored'


if sys.argv[1:] == ['restore']:
    receipt = json.loads(receipt_path.read_text())
    for entry in receipt['targets']:
        entry['restoration'] = restore(entry)
    receipt['restoredAt'] = stamp()
    save(receipt)
    print(json.dumps({'restored': [entry['restoration'] for entry in receipt['targets']]}), flush=True)
    raise SystemExit(0)

assert not sys.argv[1:]
assert not receipt_path.exists(), 'Do not repeat a completed scheduling action.'
receipt = {'startedAt': stamp(), 'targets': [], 'formalAcceptance': False}
for pid, name, expected_sha, mask in targets:
    root = Path('/proc') / str(pid)
    source_sha = hashlib.sha256((root / 'cwd/Submission.lean').read_bytes()).hexdigest()
    assert source_sha == expected_sha, (name, source_sha)
    limits = (root / 'limits').read_text()
    assert any('Max address space' in line and line.split()[3:5] == ['34359738368', '34359738368'] for line in limits.splitlines())
    before = snapshot(pid)
    assert all(set(mask) <= set(item['affinity']) for item in before['threads'])
    cache = Path('/sys/devices/system/cpu') / f'cpu{mask[0]}/cache/index3/shared_cpu_list'
    assert cache.read_text().strip() == f'{mask[0]}-{mask[-1]}'
    receipt['targets'].append({'pid': pid, 'name': name, 'sourceSHA256': source_sha, 'requestedAffinity': mask,
                               'limitsBefore': limits, 'before': before})
save(receipt)
print(json.dumps({'event': 'baseline_started', 'seconds': 20}), flush=True)
time.sleep(20)
for entry in receipt['targets']:
    entry['baselineEnd'] = snapshot(entry['pid'])
    assert entry['baselineEnd']['startTicks'] == entry['before']['startTicks']
save(receipt)
try:
    for entry in receipt['targets']:
        for item in entry['baselineEnd']['threads']:
            try:
                os.sched_setaffinity(item['tid'], entry['requestedAffinity'])
            except ProcessLookupError:
                pass
        entry['applied'] = snapshot(entry['pid'])
        assert all(item['affinity'] == entry['requestedAffinity'] for item in entry['applied']['threads'])
    receipt['appliedAt'] = stamp()
    save(receipt)
    print(json.dumps({'event': 'affinity_applied', 'targets': [{k: entry[k] for k in ('pid', 'name', 'requestedAffinity')} for entry in receipt['targets']]}), flush=True)
    time.sleep(20)
    for entry in receipt['targets']:
        entry['after'] = snapshot(entry['pid'])
        assert entry['after']['startTicks'] == entry['before']['startTicks']
        assert all(item['affinity'] == entry['requestedAffinity'] for item in entry['after']['threads'])
        assert (Path('/proc') / str(entry['pid']) / 'limits').read_text() == entry['limitsBefore']
        summaries = {}
        for label, first, last in [('baseline', entry['before'], entry['baselineEnd']), ('locality', entry['applied'], entry['after'])]:
            previous = {item['tid']: item for item in first['threads']}
            elapsed = last['monotonic'] - first['monotonic']
            pairs = [(previous[item['tid']], item) for item in last['threads'] if item['tid'] in previous and previous[item['tid']]['startTicks'] == item['startTicks']]
            summaries[label] = {
                'wallSeconds': elapsed,
                'cpuSeconds': sum(b['runtimeNs'] - a['runtimeNs'] for a, b in pairs) / 1e9,
                'waitSeconds': sum(b['waitNs'] - a['waitNs'] for a, b in pairs) / 1e9,
                'migrations': sum(b['migrations'] - a['migrations'] for a, b in pairs),
            }
        entry['measurement'] = summaries
    receipt['finishedAt'] = stamp()
    receipt['verified'] = True
    receipt['interpretation'] = 'Scheduling locality only. CPU time and migrations do not establish proof throughput or a speedup factor.'
    save(receipt)
    print(json.dumps({'event': 'verified', 'targets': [{k: entry[k] for k in ('pid', 'name', 'measurement')} for entry in receipt['targets']]}), flush=True)
except BaseException:
    for entry in receipt['targets']:
        entry['restoration'] = restore(entry)
    receipt['failedAt'] = stamp()
    save(receipt)
    raise
