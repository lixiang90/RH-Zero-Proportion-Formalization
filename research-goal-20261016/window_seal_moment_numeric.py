"""Hash-gated index of the 82 point and 403 added q2 ordinary proofs."""
from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sha = lambda raw: hashlib.sha256(raw).hexdigest()
plan = json.loads((HERE/'window_moment_numeric_modules.json').read_bytes())
receipt = json.loads((HERE/'lean_verification.json').read_bytes())
known = {r['module']:r for r in receipt['modules']}
modules = plan['point_modules']+plan['grid_modules']
assert len(modules) == 23
records = []
files = ['research-goal-20261016/window_generate_moment_numeric.py',
         'research-goal-20261016/window_moment_numeric_modules.json',
         'research-goal-20261016/window_seal_moment_numeric.py']
allowed = {'propext','Classical.choice','Quot.sound'}
for module in modules:
    path = module.replace('.','/')+'.lean'
    source = (ROOT/path).read_bytes()
    record = known[module]
    assert record['passed'] and record['exit_code'] == 0 and record['source_unchanged']
    assert record['source_sha256'] == sha(source)
    logpath = 'research-goal-20261016/'+record['log']
    log = (ROOT/logpath).read_bytes()
    assert record['log_sha256'] == sha(log)
    roots = []
    for name,axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log.decode('utf8',errors='replace')):
        names = [a.strip() for a in axioms.split(',') if a.strip()]
        assert set(names) <= allowed, (module,names)
        roots.append({'name':name,'axioms':names})
    data = module.endswith('Data')
    assert data or roots, module
    records.append({'module':module,'source_path':path,'source_bytes':len(source),
                    'source_sha256':sha(source),'log_path':logpath,'log_sha256':sha(log),
                    'olean_sha256':record['olean_sha256'],'whole_process_seconds':record['whole_process_seconds'],
                    'data_only':data,'printed_roots':roots,'ordinary_Lean_passed':True})
    files.extend([path,logpath])
out = {'scope':'Complete ordinary proofs for new two-cell moment point/q2 inputs. No actual moment exclusion or global cover is asserted.',
       'script_sha256':sha(Path(__file__).read_bytes()),'friendly_packet_sha256':plan['source_sha256'],
       'generator_sha256':sha((HERE/'window_generate_moment_numeric.py').read_bytes()),
       'compiler_sha256':receipt['compiler_sha256'],'driver_sha256':receipt['driver_sha256'],
       'proof_modules':sum(not r['data_only'] for r in records),
       'data_modules':sum(r['data_only'] for r in records),'point_rows':82,
       'new_q2_rows':403,'old_q2_reused':175,'new_q4_rows':0,'records':records,
       'all_current_sources_and_logs_verified':True,'actual_Lean_exclusions':0,
       'complete_global_cover':False,'new_zero_proportion_proven':False}
path = HERE/'window_moment_numeric_proof_index.json'
path.write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
files.append('research-goal-20261016/'+path.name)
index = {'files':[{'path':p,'sha256':sha((ROOT/p).read_bytes()),'bytes':(ROOT/p).stat().st_size} for p in files],
         'proof_index_sha256':sha(path.read_bytes()),'complete_global_cover':False}
sync = HERE/'window_moment_numeric_sync_files.json'
sync.write_text(json.dumps(index,indent=2)+'\n',encoding='utf8')
print(json.dumps({'proof_modules':out['proof_modules'],'data_modules':out['data_modules'],
                  'proof_index_sha256':sha(path.read_bytes()),'sync_index_sha256':sha(sync.read_bytes()),'files':len(files)}))
