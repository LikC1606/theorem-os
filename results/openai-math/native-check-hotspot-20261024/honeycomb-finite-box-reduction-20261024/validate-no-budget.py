import datetime
import hashlib
import json
import os
from pathlib import Path
import resource
import subprocess
import time

stage = Path(__file__).resolve().parent
lean = Path('/home/lzh/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean')
sealed = json.loads((stage / 'environment-readability.json').read_text())
sealed_root = Path(sealed['sealedPackagesRoot'])
roots = sorted(sealed_root.glob('*/.lake/build/lib/lean'))
assert (sealed_root / 'mathlib/.lake/build/lib/lean/Mathlib.olean').is_file()
cpus = sorted(os.sched_getaffinity(0))[:1]
assert resource.getrlimit(resource.RLIMIT_CPU) == (resource.RLIM_INFINITY, resource.RLIM_INFINITY)
command = [str(lean), '--threads=1', '--memory=32768', '-DautoImplicit=false',
           '-DmaxHeartbeats=0', '-DmaxRecDepth=1000', 'Submission.lean']
launch = {
    'startedAt': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'command': command,
    'cwd': str(stage),
    'sourceSHA256': hashlib.sha256((stage / 'Submission.lean').read_bytes()).hexdigest(),
    'leanToolchain': 'leanprover/lean4:v4.34.1',
    'mathlibCommit': 'd13f23b723b8a846827a245b89c10fc7d3f11612',
    'leanPath': [str(p) for p in roots],
    'resourceLimits': {
        'wallSeconds': None,
        'cpuSoftSeconds': None,
        'cpuHardSeconds': None,
        'maxHeartbeats': 0,
        'addressSpaceGiB': 32,
        'leanMemoryMiB': 32768,
        'threads': 1,
        'cpus': cpus,
    },
    'activeRuntimeChanged': False,
    'sealedEnvironmentIdentity': sealed['sealedIdentity'],
    'priorBudgetedSuccessResult': str(stage / 'validation-final-result.json'),
    'reasonForRerun': 'Remove inherited helper-entry wall, CPU and heartbeat budgets to honor the authorized unlimited-time policy; source and environment are unchanged.',
}
with (stage / 'validation-no-budget-launch.json').open('x') as handle:
    json.dump(launch, handle, indent=2)
    handle.write('\n')
environment = os.environ.copy()
environment['LEAN_PATH'] = ':'.join([str(stage), *(str(p) for p in roots)])


def limits():
    os.sched_setaffinity(0, cpus)
    resource.setrlimit(resource.RLIMIT_AS, (32 * 1024**3, 32 * 1024**3))


started = time.monotonic()
with (stage / 'validation-no-budget.stdout.log').open('xb') as stdout, \
        (stage / 'validation-no-budget.stderr.log').open('xb') as stderr:
    process = subprocess.Popen(command, cwd=stage, env=environment, preexec_fn=limits,
                               stdin=subprocess.DEVNULL, stdout=stdout, stderr=stderr)
    returncode = process.wait()
usage = resource.getrusage(resource.RUSAGE_CHILDREN)
result = {
    **launch,
    'finishedAt': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'durationSeconds': time.monotonic() - started,
    'actualExitCode': returncode,
    'timedOut': False,
    'maxResidentSetKiB': usage.ru_maxrss,
    'userCPUSeconds': usage.ru_utime,
    'systemCPUSeconds': usage.ru_stime,
    'stdoutLog': str(stage / 'validation-no-budget.stdout.log'),
    'stderrLog': str(stage / 'validation-no-budget.stderr.log'),
    'hostTaskProofAcceptance': False,
}
with (stage / 'validation-no-budget-result.json').open('x') as handle:
    json.dump(result, handle, indent=2)
    handle.write('\n')
print(json.dumps(result))
