"""Root-allocated intentional resource cutoff; keep worker/harness for evidence."""
from pathlib import Path
import json, os, signal, time
run='whole-f40-compile-r5'
root=Path('/tmp/rh-proportion-memory-20261010/whole-native-20261010-r5')
group=Path('/sys/fs/cgroup/memory/rh-proportion-memory-20261010')/run
lean=Path('/tmp/rh-proportion-memory-20261010/lean-4.33.0-rc2-linux/bin/lean')
record=root/'phase-ledgers/compile-intentional-resource-cutoff.json'
assert not record.exists(),'Preserve previous cutoff record'
before={k:(group/k).read_text().strip() for k in ('memory.failcnt','memory.oom_control','memory.usage_in_bytes','memory.max_usage_in_bytes')}
assert int(before['memory.failcnt'])>0
targets=[]
for value in (group/'cgroup.procs').read_text().split():
    process=Path('/proc')/value
    try:
        assert run in (process/'cgroup').read_text(),'PID ownership mismatch'
        if (process/'exe').resolve(strict=True)!=lean:continue
        cmd=(process/'cmdline').read_bytes().replace(b'\x00',b' ').decode()
        assert str(root/'source/Solution/Candidate.lean') in cmd
        targets.append({'pid':int(value),'exe':str(lean),'command':cmd,'ownership_verified':True})
    except (FileNotFoundError,ProcessLookupError):pass
result={'classification':'INTENTIONAL_RESOURCE_CUTOFF_BY_ROOT_ALLOCATION','observed_unix':time.time(),'run_id':run,'resource_counters_before':before,'targets':targets,'signal':'SIGTERM only to verified owned Lean; worker and harness remain alive','reason':'Root revised allocation after resource gate failure and persistent read-page pressure. Not a Lean mathematical rejection, an observed OOM, or the external timeout guard.','source_sha256':'f40d0cb3566d4e71a6bb624a4d4375ca3ade977d3850e14e134a8a850f4abd50','root_authorization':'ROOT_GO_20261010_INTENTIONAL_RESOURCE_CUTOFF_THEN_R6','signals_sent':[]}
for target in targets:
    try:os.kill(target['pid'],signal.SIGTERM);result['signals_sent'].append(target['pid'])
    except ProcessLookupError:result.setdefault('exited_before_signal',[]).append(target['pid'])
record.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
