import datetime
import hashlib
import json
import os
from pathlib import Path
import resource
import subprocess
import time

stage = Path(__file__).resolve().parent
project = Path('/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/environment/project')
lean = Path('/home/lzh/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean')
sealed = json.loads((stage / 'environment-readability.json').read_text())
sealed_root = Path(sealed['sealedPackagesRoot'])
roots = sorted(sealed_root.glob('*/.lake/build/lib/lean'))
assert (sealed_root / 'mathlib/.lake/build/lib/lean/Mathlib.olean').is_file()
cpus = sorted(os.sched_getaffinity(0))[:1]
command = [str(lean), '--threads=1', '--memory=32768', '-DautoImplicit=false',
           '-DmaxHeartbeats=800000', '-DmaxRecDepth=1000', 'Submission.lean']
launch = {
    'startedAt': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'command': command,
    'cwd': str(stage),
    'sourceSHA256': hashlib.sha256((stage / 'Submission.lean').read_bytes()).hexdigest(),
    'leanToolchain': 'leanprover/lean4:v4.34.1',
    'mathlibCommit': 'd13f23b723b8a846827a245b89c10fc7d3f11612',
    'leanPath': [str(p) for p in roots],
    'resourceLimits': {'wallSeconds': 180, 'cpuSoftSeconds': 120, 'cpuHardSeconds': 125,
                       'addressSpaceGiB': 32, 'leanMemoryMiB': 32768, 'threads': 1, 'cpus': cpus},
    'invocationLimit': 1,
    'activeRuntimeChanged': False,
    'sealedEnvironmentIdentity': sealed['sealedIdentity'],
    'priorImportFailureResult': str(stage / 'validation-result.json'),
}
with (stage / 'validation-kernel-32g-launch.json').open('x') as handle:
    json.dump(launch, handle, indent=2)
    handle.write('\n')
environment = os.environ.copy()
environment['LEAN_PATH'] = ':'.join([str(stage), *(str(p) for p in roots)])

def limits():
    os.sched_setaffinity(0, cpus)
    resource.setrlimit(resource.RLIMIT_AS, (32 * 1024**3, 32 * 1024**3))
    resource.setrlimit(resource.RLIMIT_CPU, (120, 125))

started = time.monotonic()
timed_out = False
with (stage / 'validation.stdout.log').open('wb') as stdout, \
        (stage / 'validation.stderr.log').open('wb') as stderr:
    process = subprocess.Popen(command, cwd=stage, env=environment, preexec_fn=limits,
                               stdin=subprocess.DEVNULL, stdout=stdout, stderr=stderr)
    try:
        returncode = process.wait(timeout=180)
    except subprocess.TimeoutExpired:
        timed_out = True
        process.kill()
        returncode = process.wait()
usage = resource.getrusage(resource.RUSAGE_CHILDREN)
result = {
    **launch,
    'finishedAt': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'durationSeconds': time.monotonic() - started,
    'actualExitCode': returncode,
    'timedOut': timed_out,
    'maxResidentSetKiB': usage.ru_maxrss,
    'userCPUSeconds': usage.ru_utime,
    'systemCPUSeconds': usage.ru_stime,
    'stdoutLog': str(stage / 'validation.stdout.log'),
    'stderrLog': str(stage / 'validation.stderr.log'),
    'hostTaskProofAcceptance': False,
}
(stage / 'validation-kernel-32g-result.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result))
