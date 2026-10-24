import gdb,json,time,datetime
from pathlib import Path
out=Path('/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/native-check-hotspot-20261024/snaky-integration-cost-20261024')
report={'observedAt':datetime.datetime.now(datetime.timezone.utc).isoformat(),'pid':1659442,'threads':[],'maxFrameDepth':8192,'maxAttachedSeconds':8}
attached=False
started=None
try:
    gdb.execute('attach 1659442',to_string=True)
    attached=True
    started=time.monotonic()
    report['attachedAt']=datetime.datetime.now(datetime.timezone.utc).isoformat()
    priorities=[]
    for thread in gdb.selected_inferior().threads():
        tid=thread.ptid[1]
        try:
            stat=Path('/proc/1659442/task/%d/stat'%tid).read_text().split()
            state=stat[2];ticks=int(stat[13])+int(stat[14])
        except Exception:state='?';ticks=0
        priorities.append((thread,state,ticks))
    priorities.sort(key=lambda t:(t[1]=='R',t[2]),reverse=True)
    for thread,state,ticks in priorities:
        thread.switch()
        entry={'tid':thread.ptid[1],'name':thread.name,'processStateBeforeRead':state,'cpuTicks':ticks,'frames':[]}
        try:
            frame=gdb.newest_frame()
            depth=0
            while frame is not None and depth<8192 and time.monotonic()-started<8:
                entry['frames'].append({'depth':depth,'function':frame.name() or hex(frame.pc()),'pc':hex(frame.pc())})
                depth+=1;frame=frame.older()
            entry['truncated']=frame is not None
        except Exception as error:entry['error']=str(error)
        report['threads'].append(entry)
        if time.monotonic()-started>=8:
            report['attachedTimeBudgetReached']=True;break
except Exception as error:
    report['error']=str(error)
finally:
    if attached:
        try:
            gdb.execute('detach',to_string=True)
            report['detached']=True
        except Exception as error:report['detachError']=str(error)
    report['attachedSeconds']=None if started is None else time.monotonic()-started
    report['finishedAt']=datetime.datetime.now(datetime.timezone.utc).isoformat()
    (out/'symbolized-stack-sample.json').write_text(json.dumps(report,indent=2)+'\n')
for thread in report['threads']:
    print('TID',thread['tid'],'FRAMES',len(thread['frames']),'TRUNCATED',thread.get('truncated'))
    seen=set()
    for frame in thread['frames']:
        name=frame['function']
        if name not in seen:
            print(frame['depth'],name)
            seen.add(name)
print('ATTACHED_SECONDS',report['attachedSeconds'],'DETACHED',report.get('detached'))
