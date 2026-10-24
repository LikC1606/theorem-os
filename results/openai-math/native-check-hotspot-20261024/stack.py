import gdb
import json
import datetime
from pathlib import Path
thread_id = int(gdb.convenience_variable('target_tid'))
for thread in gdb.selected_inferior().threads():
    if thread.ptid[1] == thread_id:
        thread.switch()
        break
else:
    raise RuntimeError('target thread absent')
frame = gdb.newest_frame()
groups = []
frames = []
depth = 0
while frame is not None and depth < 8192:
    name = frame.name() or hex(frame.pc())
    frames.append({'depth': depth, 'function': name, 'pc': hex(frame.pc())})
    if groups and groups[-1][2] == name:
        groups[-1][1] = depth
    else:
        groups.append([depth, depth, name])
    depth += 1
    frame = frame.older()
output = {'observedAt': datetime.datetime.now(datetime.timezone.utc).isoformat(),
          'pid': gdb.selected_inferior().pid, 'tid': thread_id, 'frames': frames,
          'truncated': frame is not None}
target = Path('/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/native-check-hotspot-20261024') / ('stack-%d.json' % output['pid'])
target.write_text(json.dumps(output, indent=2) + '\n')
seen = set()
for first, last, name in groups:
    if name not in seen:
        print('%d..%d %s' % (first, last, name))
        seen.add(name)
print('FRAME_COUNT', depth, 'TRUNCATED', frame is not None)
