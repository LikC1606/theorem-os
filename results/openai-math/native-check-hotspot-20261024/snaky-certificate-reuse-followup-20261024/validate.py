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
label, filename = sys.argv[1:3]
assert label.replace('-', '').isalnum()
assert filename in ['CertificateContext.lean', 'BaselineCertificate.lean', 'ReuseCertificate.lean']
source = stage / filename
provenance = json.loads((stage / 'provenance.json').read_text())
base = Path(provenance['sourceRoot'])
sealed = Path(provenance['sealedPackagesRoot'])
roots = sorted(sealed.glob('*/.lake/build/lib/lean'))
assert (sealed / 'mathlib/.lake/build/lib/lean/Mathlib.olean').is_file()
assert resource.getrlimit(resource.RLIMIT_CPU) == (resource.RLIM_INFINITY, resource.RLIM_INFINITY)
if filename != 'CertificateContext.lean':
    assert (stage / 'CertificateContext.olean').is_file()
output = stage / (source.stem + '.olean')
assert not output.exists()
cpus = sorted(os.sched_getaffinity(0))[:1]
command = ['/home/lzh/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean',
           '-j1', '--memory=32768', '-DmaxHeartbeats=0', '-DmaxRecDepth=100000',
           '-DElab.async=false', '-o', output.name, source.name]
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
for entry in provenance['compiledDependencies']:
    assert entry['sourceSHA256'] == sha(base / (entry['module'] + '.lean'))
    assert entry['oleanSHA256'] == sha(base / (entry['module'] + '.olean'))
launch = {
    'startedAt': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'command': command, 'cwd': str(stage), 'sourceSHA256': sha(source),
    'sourceBytes': source.stat().st_size,
    'leanToolchain': provenance['leanToolchain'], 'mathlibCommit': provenance['mathlibCommit'],
    'sealedEnvironmentIdentity': provenance['sealedEnvironmentIdentity'],
    'leanPath': [str(stage), str(base), *(str(p) for p in roots)],
    'compiledDependenciesReused': provenance['compiledDependencies'],
    'resourceLimits': {'wallSeconds': None, 'cpuSeconds': None, 'invocations': None,
                       'maxHeartbeats': 0, 'maxRecDepth': 100000,
                       'addressSpaceGiB': 32, 'leanMemoryMiB': 32768,
                       'threads': 1, 'cpus': cpus},
    'originalGoalCompiled': False, 'nativeAcceptance': False,
    'activeProcessSourceRuntimeStateQueueModified': False,
}
if filename != 'CertificateContext.lean':
    launch['contextOleanSHA256'] = sha(stage / 'CertificateContext.olean')
with (stage / (label + '-launch.json')).open('x') as handle:
    json.dump(launch, handle, indent=2)
    handle.write('\n')
with (stage / (label + '-source.lean')).open('xb') as handle:
    handle.write(source.read_bytes())
env = os.environ.copy()
env['LEAN_PATH'] = ':'.join(launch['leanPath'])


def limits():
    os.sched_setaffinity(0, cpus)
    resource.setrlimit(resource.RLIMIT_AS, (32 * 1024**3, 32 * 1024**3))


started = time.monotonic()
with (stage / (label + '.stdout.log')).open('xb') as stdout, \
        (stage / (label + '.stderr.log')).open('xb') as stderr:
    process = subprocess.Popen(command, cwd=stage, env=env, preexec_fn=limits,
                               stdin=subprocess.DEVNULL, stdout=stdout, stderr=stderr)
    actual_exit = process.wait()
usage = resource.getrusage(resource.RUSAGE_CHILDREN)
result = {**launch,
          'finishedAt': datetime.datetime.now(datetime.timezone.utc).isoformat(),
          'durationSeconds': time.monotonic() - started, 'actualExitCode': actual_exit,
          'timedOut': False, 'userCPUSeconds': usage.ru_utime,
          'systemCPUSeconds': usage.ru_stime, 'maxResidentSetKiB': usage.ru_maxrss,
          'stdoutLog': str(stage / (label + '.stdout.log')),
          'stderrLog': str(stage / (label + '.stderr.log'))}
if output.is_file():
    result['outputOleanSHA256'] = sha(output)
    result['outputOleanBytes'] = output.stat().st_size
with (stage / (label + '-result.json')).open('x') as handle:
    json.dump(result, handle, indent=2)
    handle.write('\n')
print(json.dumps(result))
