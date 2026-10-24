import datetime
import hashlib
import json
import os
from pathlib import Path
import resource
import subprocess
import sys
import time

stage = Path(__file__).resolve().parent
label = sys.argv[1]
assert label.replace('-', '').isalnum()
source = stage / 'WidthOne.lean'
provenance = json.loads((stage / 'provenance.json').read_text())
sealed_root = Path(provenance['sealedPackagesRoot'])
roots = sorted(sealed_root.glob('*/.lake/build/lib/lean'))
assert (sealed_root / 'mathlib/.lake/build/lib/lean/Mathlib.olean').is_file()
assert resource.getrlimit(resource.RLIMIT_CPU) == (resource.RLIM_INFINITY, resource.RLIM_INFINITY)
cpus = sorted(os.sched_getaffinity(0))[:1]
command = ['/home/lzh/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean',
           '--threads=1', '--memory=32768', '-DautoImplicit=false',
           '-DmaxHeartbeats=0', '-DmaxRecDepth=1000', source.name]
launch = {
    'startedAt': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'command': command,
    'cwd': str(stage),
    'sourceSHA256': hashlib.sha256(source.read_bytes()).hexdigest(),
    'sourceBytes': source.stat().st_size,
    'leanToolchain': provenance['leanToolchain'],
    'mathlibCommit': provenance['mathlibCommit'],
    'leanPath': [str(p) for p in roots],
    'sealedEnvironmentIdentity': provenance['sealedEnvironmentIdentity'],
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
    'activeSourceChanged': False,
    'hostTaskProofAcceptance': False,
}
with (stage / (label + '-launch.json')).open('x') as handle:
    json.dump(launch, handle, indent=2)
    handle.write('\n')
with (stage / (label + '-source.lean')).open('xb') as handle:
    handle.write(source.read_bytes())
environment = os.environ.copy()
environment['LEAN_PATH'] = ':'.join([str(stage), *(str(p) for p in roots)])


def limits():
    os.sched_setaffinity(0, cpus)
    resource.setrlimit(resource.RLIMIT_AS, (32 * 1024**3, 32 * 1024**3))


started = time.monotonic()
with (stage / (label + '.stdout.log')).open('xb') as stdout, \
        (stage / (label + '.stderr.log')).open('xb') as stderr:
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
    'stdoutLog': str(stage / (label + '.stdout.log')),
    'stderrLog': str(stage / (label + '.stderr.log')),
}
with (stage / (label + '-result.json')).open('x') as handle:
    json.dump(result, handle, indent=2)
    handle.write('\n')
print(json.dumps(result))
