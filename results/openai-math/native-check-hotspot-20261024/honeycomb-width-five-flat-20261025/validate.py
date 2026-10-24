"""Compile only the new guard-compatible candidate, then query its exact module."""
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
mode, label = sys.argv[1:3]
assert mode in {'compile', 'query'} and label.replace('-', '').isalnum()
project = stage / 'project'
provenance = json.loads((stage / 'provenance.json').read_text())
sealed_root = Path(provenance['sealedPackagesRoot'])
roots = sorted(sealed_root.glob('*/.lake/build/lib/lean'))
assert (sealed_root/'mathlib/.lake/build/lib/lean/Mathlib.olean').is_file()
assert resource.getrlimit(resource.RLIMIT_CPU) == (resource.RLIM_INFINITY, resource.RLIM_INFINITY)
sha = lambda b: hashlib.sha256(b).hexdigest()
candidate_sha = sha((project/'Submission.lean').read_bytes())
guard = json.loads((stage/'source-preflight-02-result.json').read_text())
assert guard['results'][-1]['passed']
assert guard['results'][-1]['sourceSHA256'] == candidate_sha
source = project / ('Submission.lean' if mode == 'compile' else 'Probe.lean')
module = project / 'Submission.olean'
command = ['/home/lzh/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean',
           '--threads=1', '--memory=32768', '-DautoImplicit=false',
           '-DmaxHeartbeats=0', '-DmaxRecDepth=1000']
if mode == 'compile':
    assert not module.exists()
    command += ['-o', module.name, source.name]
else:
    prior = json.loads((stage/'kernel-compile-01-result.json').read_text())
    assert prior['actualExitCode'] == 0
    assert prior['sourceSHA256'] == candidate_sha
    assert sha(module.read_bytes()) == prior['outputModuleSHA256']
    command += ['-Dpp.explicit=true', source.name]
cpus = sorted(os.sched_getaffinity(0))[:1]
launch = {
    'startedAt': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'mode': mode, 'command': command, 'cwd': str(project),
    'sourcePath': str(source), 'sourceSHA256': sha(source.read_bytes()),
    'sourceBytes': source.stat().st_size, 'candidateSHA256': candidate_sha,
    'guardPreflight': 'source-preflight-02-result.json',
    'leanToolchain': provenance['leanToolchain'],
    'mathlibCommit': provenance['mathlibCommit'],
    'sealedEnvironmentIdentity': provenance['sealedEnvironmentIdentity'],
    'leanPath': [str(project), *(str(r) for r in roots)],
    'resourceLimits': {'wallSeconds': None, 'cpuSoftSeconds': None,
        'cpuHardSeconds': None, 'maxHeartbeats': 0, 'addressSpaceGiB': 32,
        'leanMemoryMiB': 32768, 'threads': 1, 'cpus': cpus},
    'activeRuntimeChanged': False, 'activeSourceChanged': False,
    'nativeTaskProofAcceptance': False,
}
if mode == 'query':
    launch['importedModuleSHA256'] = sha(module.read_bytes())
with (stage/(label+'-launch.json')).open('x') as out:
    json.dump(launch, out, indent=2)
    out.write('\n')
with (stage/(label+'-source.lean')).open('xb') as out:
    out.write(source.read_bytes())
environment = os.environ.copy()
environment['LEAN_PATH'] = ':'.join(launch['leanPath'])


def limits():
    os.sched_setaffinity(0, cpus)
    resource.setrlimit(resource.RLIMIT_AS, (32*1024**3, 32*1024**3))


start = time.monotonic()
with (stage/(label+'.stdout.log')).open('xb') as stdout, \
        (stage/(label+'.stderr.log')).open('xb') as stderr:
    process = subprocess.Popen(command, cwd=project, env=environment, preexec_fn=limits,
        stdin=subprocess.DEVNULL, stdout=stdout, stderr=stderr)
    code = process.wait()
usage = resource.getrusage(resource.RUSAGE_CHILDREN)
result = {**launch,
    'finishedAt': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'durationSeconds': time.monotonic()-start, 'actualExitCode': code,
    'timedOut': False, 'maxResidentSetKiB': usage.ru_maxrss,
    'userCPUSeconds': usage.ru_utime, 'systemCPUSeconds': usage.ru_stime,
    'stdoutLog': str(stage/(label+'.stdout.log')),
    'stderrLog': str(stage/(label+'.stderr.log')),
}
if mode == 'compile' and code == 0:
    result['outputModuleSHA256'] = sha(module.read_bytes())
assert sha(source.read_bytes()) == launch['sourceSHA256']
with (stage/(label+'-result.json')).open('x') as out:
    json.dump(result, out, indent=2)
    out.write('\n')
print(json.dumps(result))
