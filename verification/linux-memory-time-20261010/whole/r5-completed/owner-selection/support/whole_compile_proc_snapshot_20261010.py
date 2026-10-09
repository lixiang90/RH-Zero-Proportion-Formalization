"""One read-only, ownership-checked proc/owned-output-metadata snapshot."""
from pathlib import Path
import json, os, time
run='whole-f40-compile-r5'
group=Path('/sys/fs/cgroup/memory/rh-proportion-memory-20261010')/run
lean=Path('/tmp/rh-proportion-memory-20261010/lean-4.33.0-rc2-linux/bin/lean')
root=Path('/tmp/rh-proportion-memory-20261010/whole-native-20261010-r5')
rows=[]
for value in (group/'cgroup.procs').read_text().split():
    process=Path('/proc')/value
    try:
        assert run in (process/'cgroup').read_text(),'PID does not belong to allocated cgroup'
        exe=(process/'exe').resolve(strict=True)
        if exe!=lean:continue
        cmd=(process/'cmdline').read_bytes().replace(b'\x00',b' ').decode()
        assert str(root/'source/Solution/Candidate.lean') in cmd
        stat=(process/'stat').read_text().rsplit(')',1)[1].split()
        status=dict(x.split(':',1) for x in (process/'status').read_text().splitlines() if ':' in x)
        tasks=[]
        for task in sorted((process/'task').iterdir()):
            try:
                s=(task/'stat').read_text().rsplit(')',1)[1].split()
                tasks.append({'tid':task.name,'state':s[0],'wchan':(task/'wchan').read_text().strip(),'major_faults':int(s[9]),'minor_faults':int(s[7]),'user_ticks':int(s[11]),'system_ticks':int(s[12])})
            except (FileNotFoundError,ProcessLookupError):pass
        rows.append({'pid':int(value),'ownership_verified':True,'exe':str(exe),'command':cmd,'state':stat[0],'main_wchan':(process/'wchan').read_text().strip(),'major_faults':int(stat[9]),'minor_faults':int(stat[7]),'user_ticks':int(stat[11]),'system_ticks':int(stat[12]),'status':{k:status[k].strip() for k in ('State','VmRSS','VmHWM','Threads')},'io':(process/'io').read_text(),'tasks':tasks})
    except (FileNotFoundError,ProcessLookupError):pass
files=[]
for path in sorted((root/'lib/Solution').glob('Candidate*')):
    stat=path.stat();files.append({'path':str(path),'bytes':stat.st_size,'mtime_ns':stat.st_mtime_ns})
result={'observed_unix':time.time(),'run_id':run,'processes':rows,'owned_solution_output_file_metadata':files,'artifact_contents_read':False,'dependency_cache_read':False,'tracing_or_signals_used':False}
print(json.dumps(result,indent=2))
