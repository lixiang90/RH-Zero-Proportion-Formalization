"""Freeze the actually passed analytic/numeric inputs of the two moment cells.

The final aggregate coefficient checks and local exclusions are outside this
index until they have their own successful ordinary-kernel receipts.
"""
from pathlib import Path
import hashlib
import json
import re

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
sha=lambda raw:hashlib.sha256(raw).hexdigest()
plans=['window_moment_numeric_modules.json','window_moment_atom_modules.json',
       'window_moment_energy_case_modules.json','window_moment_actual_box_modules.json']
modules=[]
for name in plans:
 p=json.loads((HERE/name).read_bytes())
 ms=p.get('modules',p.get('point_modules',[])+p.get('grid_modules',[]))
 modules.extend(m if isinstance(m,str) else m['module'] for m in ms)
modules+=['StructuralGoal20261016.'+s for s in [
 'WindowMomentLayout','WindowMomentEnergy','WindowMomentRLT',
 'WindowMomentEnergyCertificate','WindowMomentRounding','WindowMomentPolynomial',
 'WindowMomentBox','WindowMomentEnergyPolynomial','WindowMomentGlobalBox','WindowMomentExactInteger']]
modules=list(dict.fromkeys(modules))
receipt=json.loads((HERE/'lean_verification.json').read_bytes())
known={r['module']:r for r in receipt['modules']}
records=[]
files=['research-goal-20261016/'+n for n in plans]
files += ['research-goal-20261016/'+n for n in [
 'window_generate_moment_numeric.py','window_generate_moment_energy_cases.py',
 'window_generate_moment_atoms.py','window_generate_moment_actual_boxes.py',
 'window_seal_moment_inputs.py']]
for module in modules:
 path=module.replace('.','/')+'.lean'
 src=(ROOT/path).read_bytes();r=known[module]
 assert r['passed'] and r['exit_code']==0 and r['source_unchanged']
 assert r['source_sha256']==sha(src)
 logpath='research-goal-20261016/'+r['log'];log=(ROOT/logpath).read_bytes()
 assert r['log_sha256']==sha(log)
 roots=[]
 for name,axs in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log.decode('utf8',errors='replace')):
  axioms=[s.strip()for s in axs.split(',')if s.strip()]
  assert set(axioms)<={'propext','Classical.choice','Quot.sound'}
  roots.append({'name':name,'axioms':axioms})
 data=module.endswith('Data')
 assert data or roots,module
 records.append({'module':module,'source_path':path,'source_sha256':sha(src),'source_bytes':len(src),
                 'log_path':logpath,'log_sha256':sha(log),'olean_sha256':r['olean_sha256'],
                 'duration_seconds':r['whole_process_seconds'],'data_only':data,'roots':roots,
                 'ordinary_Lean_passed':True})
 files.extend([path,logpath])
out={'scope':__doc__,'script_sha256':sha(Path(__file__).read_bytes()),'compiler_sha256':receipt['compiler_sha256'],
     'proof_modules':sum(not r['data_only']for r in records),'data_modules':sum(r['data_only']for r in records),
     'point_rows':82,'new_q2_rows':403,'old_q2_reused':175,'new_q4_rows':0,'actual_old_atoms':[103,106],
     'actual_energy_cells':2,'actual_tight_box_cells':2,'records':records,
     'all_current_sources_and_logs_verified':True,'independently_replayed_here':False,
     'actual_moment_exclusions_in_this_index':0,'complete_global_cover':False,'new_zero_proportion_proven':False}
path=HERE/'window_moment_actual_inputs_index.json'
path.write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
files.append('research-goal-20261016/'+path.name)
idx={'files':[{'path':p,'sha256':sha((ROOT/p).read_bytes()),'bytes':(ROOT/p).stat().st_size}for p in files],
     'proof_index_sha256':sha(path.read_bytes()),'actual_moment_exclusions':0,'complete_global_cover':False}
sync=HERE/'window_moment_actual_inputs_sync_files.json'
sync.write_text(json.dumps(idx,indent=2)+'\n',encoding='utf8')
print(json.dumps({'proof_modules':out['proof_modules'],'data_modules':out['data_modules'],
                  'index_sha256':sha(path.read_bytes()),'sync_sha256':sha(sync.read_bytes()),'files':len(files)}))
