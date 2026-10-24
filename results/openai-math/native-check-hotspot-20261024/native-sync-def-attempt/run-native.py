#!/usr/bin/python3
"""Explicit startup/resume entry point for this fresh, isolated native attempt."""
from pathlib import Path
import argparse
import datetime
import fcntl
import hashlib
import importlib.util
import json
import os
import subprocess
import sys
import time


def digest(file):
    return hashlib.sha256(Path(file).read_bytes()).hexdigest()


stage = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('phase', choices=('startup', 'resume'))
parser.add_argument('--print', action='store_true', dest='print_only', help='inspect the launch without executing it')
options = parser.parse_args()
info = json.loads((stage / 'preparation.json').read_text())
root = Path(info['campaign'])
sys.path.insert(0, str(root))
spec = importlib.util.spec_from_file_location('sync_def_campaign', root / 'campaign.py')
campaign = importlib.util.module_from_spec(spec)
spec.loader.exec_module(campaign)
launch_file = Path(info['launchFile'])
assert digest(launch_file) == info['launchSHA256']
assert digest(info['frozenLaunchFile']) == info['frozenLaunchSHA256']
assert digest(info['build']['buildManifestRef']) == info['buildManifestSHA256']
assert digest(info['taskFile']) == info['taskSHA256']
assert digest(info['sourceFile']) == info['originalChallengeSHA256']
launch = json.loads(launch_file.read_text())
original = json.loads(Path(info['frozenLaunchFile']).read_text())
expected = list(original['args'])
for flag, value in (('--workspace', info['workspace']), ('--task-file', info['taskFile']), ('--output', info['output'])):
    expected[expected.index(flag) + 1] = value
assert launch['args'] == expected
assert {k: v for k, v in launch.items() if k != 'args'} == {k: v for k, v in original.items() if k != 'args'}
assert all(launch['args'][launch['args'].index(flag) + 1] == '0' for flag in campaign.BUDGET_FLAGS)
assert launch['args'][launch['args'].index('--prepare-timeout-seconds') + 1] == '0'
assert all(campaign.load(root / 'campaign-state.json')['policy'][key] == 0 for key in campaign.UNLIMITED_BUDGET)
assert hashlib.sha256(launch['args'][launch['args'].index('--evaluator-command') + 1].encode()).hexdigest() == info['publisherCommandSHA256']
args = launch['args'] + (['--startup-only'] if options.phase == 'startup' else ['--resume'])
if options.print_only:
    print(json.dumps({'phase': options.phase, 'args': args, 'cwd': launch['cwd'], 'executed': False}, indent=2))
    raise SystemExit(0)

run = stage / 'native-followup'
receipt_file = stage / (options.phase + '-receipt.json')
with (stage / 'native-run.lock').open('a') as lock:
    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    assert not receipt_file.exists(), 'Inspect the existing phase receipt before retrying a native process.'
    if options.phase == 'startup':
        assert not Path(info['output'] + '.runtime/state.json').exists(), 'Fresh startup must not overwrite a native state.'
    else:
        startup = json.loads((stage / 'startup-receipt.json').read_text())
        assert startup.get('phase') == 'startup_finished' and startup.get('exitCode') == 0

    record = {
        'observedAt': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'target': info['id'], 'phase': options.phase + '_starting',
        'buildId': info['build']['buildId'], 'output': info['output'],
        'unlimitedBudgets': campaign.UNLIMITED_BUDGET, 'prepareTimeoutSeconds': 0,
        'modelInvocationPossible': options.phase == 'resume', 'nativeAccepted': False,
        'originalCampaignChanged': False,
    }

    def save():
        temporary = receipt_file.with_suffix('.tmp')
        temporary.write_text(json.dumps(record, indent=2) + '\n')
        os.replace(temporary, receipt_file)

    save()
    started = time.monotonic()
    with (run / (options.phase + '.log')).open('a') as output:
        process = subprocess.Popen(args, cwd=launch['cwd'], env=campaign.environment(),
                                   stdin=subprocess.DEVNULL, stdout=output,
                                   stderr=subprocess.STDOUT, start_new_session=True)
        record.update(phase=options.phase + '_running', childPid=process.pid)
        save()
        code = process.wait()
    record.update(phase=options.phase + '_finished', exitCode=code,
                  durationSeconds=time.monotonic() - started,
                  observedAt=datetime.datetime.now(datetime.timezone.utc).isoformat())
    if options.phase == 'resume':
        result_file = Path(info['output'])
        result = json.loads(result_file.read_text()) if result_file.exists() else {}
        record.update(nativeAccepted=campaign.accepted_result(result),
                      resultStatus=result.get('status'), resultReason=result.get('reason'),
                      runId=result.get('runId'))
    save()
    print(json.dumps(record), flush=True)
    raise SystemExit(code)
