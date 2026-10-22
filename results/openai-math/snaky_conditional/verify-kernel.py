from pathlib import Path
import json, os, subprocess, time, hashlib
root = Path(__file__).resolve().parent
lean_path = subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=root,text=True).strip()
build=root/'.build';build.mkdir(exist_ok=True)
env=dict(os.environ,LEAN_PATH=str(build)+':'+lean_path,LEAN_NUM_THREADS='1',MALLOC_ARENA_MAX='2')
lean=subprocess.check_output(['elan','which','lean'],cwd=root,text=True).strip()
assert 'version 4.34.1' in subprocess.check_output([lean,'--version'],text=True)
results=[]
for module in json.loads((root/'module-order.json').read_text()):
 source=root/(module+'.lean');command=[lean,'-j1','-DElab.async=false','-o',str(build/(module+'.olean')),str(source)]
 started=time.monotonic()
 with (build/(module+'.log')).open('w') as log:
  result=subprocess.run(command,cwd=root,env=env,stdout=log,stderr=subprocess.STDOUT)
 row={'module':module,'sourceSHA256':hashlib.sha256(source.read_bytes()).hexdigest(),'exitCode':result.returncode,'durationSeconds':time.monotonic()-started}
 results.append(row);print(json.dumps(row),flush=True)
 (build/'recheck.json').write_text(json.dumps(results,indent=2)+'\n')
 if result.returncode:raise SystemExit(result.returncode)
print((build/(json.loads((root/'module-order.json').read_text())[-1]+'.log')).read_text())
