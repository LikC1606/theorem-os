from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
import time

root = Path(__file__).resolve().parent
for entry in json.loads((root / 'manifest.json').read_text())['files']:
    source = root / entry['path']
    if hashlib.sha256(source.read_bytes()).hexdigest() != entry['sha256']:
        raise SystemExit('Archived file changed: ' + entry['path'])

lean_path = subprocess.check_output(
    ['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=root, text=True).strip()
lean = subprocess.check_output(['elan', 'which', 'lean'], cwd=root, text=True).strip()
if 'version 4.34.1' not in subprocess.check_output([lean, '--version'], text=True):
    raise SystemExit('The pinned Lean 4.34.1 compiler is required.')
build = root / '.build'
build.mkdir(exist_ok=True)
env = dict(os.environ, LEAN_PATH=str(build) + ':' + lean_path,
           LEAN_NUM_THREADS='1', MALLOC_ARENA_MAX='2')
results = []
order = json.loads((root / 'module-order.json').read_text())
for module in order:
    relative = module.replace('.', '/')
    source = root / (relative + '.lean')
    output = build / (relative + '.olean')
    log = build / (relative + '.log')
    output.parent.mkdir(parents=True, exist_ok=True)
    command = [lean, '-j1', '-DElab.async=false', '-o', str(output), str(source)]
    started = time.monotonic()
    with log.open('w') as stream:
        result = subprocess.run(command, cwd=root, env=env,
                                stdout=stream, stderr=subprocess.STDOUT)
    row = {'module': module, 'exitCode': result.returncode,
           'sourceSHA256': hashlib.sha256(source.read_bytes()).hexdigest(),
           'durationSeconds': time.monotonic() - started}
    results.append(row)
    (build / 'recheck.json').write_text(json.dumps(results, indent=2) + '\n')
    print(json.dumps(row), flush=True)
    if result.returncode:
        raise SystemExit(result.returncode)

final_log = (build / (order[-1].replace('.', '/') + '.log')).read_text()
target = 'OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram.producedMarkedValues_allSeams'
audit = re.search(re.escape("'" + target + "'") +
                  r'\s+depends on axioms:\s*\[([^\]]*)\]', final_log)
if not audit or set(map(str.strip, audit.group(1).split(','))) != {
        'propext', 'Classical.choice', 'Quot.sound'}:
    raise SystemExit('The exact original target axiom audit did not pass.')
print(final_log)
