"""Seal the two actual ordinary-kernel moment exclusions only after full PASS.

Input lemmas, coefficient checks, and final two local exclusions are separate
record classes. No complete root cover or new zero proportion is asserted.
"""
from pathlib import Path
import hashlib
import json
import re

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
sha=lambda raw:hashlib.sha256(raw).hexdigest()
base=json.loads((HERE/'window_moment_actual_inputs_index.json').read_bytes())
plan=json.loads((HERE/'window_moment_aggregate_modules.json').read_bytes())
modules=[r['module']for r in base['records']]+plan['modules']+[
 'StructuralGoal20261016.WindowMomentFormSum',
 'StructuralGoal20261016.WindowMomentCollectHDirect',
 'StructuralGoal20261016.WindowMomentAggregateActual',
 'StructuralGoal20261016.WindowMomentExclusionCase00',
 'StructuralGoal20261016.WindowMomentExclusionCase01',
 'StructuralGoal20261016.WindowMomentExclusions']
modules=list(dict.fromkeys(modules))
receipt=json.loads((HERE/'lean_verification.json').read_bytes())
known={r['module']:r for r in receipt['modules']}
records=[]
files=[r['path'] for r in json.loads((HERE/'window_moment_actual_inputs_sync_files.json').read_bytes())['files']]
files+=['research-goal-20261016/'+n for n in [
 'window_generate_moment_aggregate.py','window_generate_moment_exclusions.py',
 'window_moment_frozen_write.py',
 'window_generate_moment_numeric_guarded.py','window_generate_moment_energy_cases_guarded.py',
 'window_generate_moment_atoms_guarded.py','window_generate_moment_actual_boxes_guarded.py',
 'window_moment_chain_recheck_receipt.json',
 'window_moment_aggregate_modules.json','window_seal_moment_exclusions.py',
 'window_moment_actual_inputs_sync_files.json']]
for module in modules:
 path=module.replace('.','/')+'.lean'
 src=(ROOT/path).read_bytes();r=known[module]
 assert r['passed'] and r['exit_code']==0 and r['source_unchanged'],module
 assert r['source_sha256']==sha(src),module
 logpath='research-goal-20261016/'+r['log'];log=(ROOT/logpath).read_bytes()
 assert r['log_sha256']==sha(log),module
 roots=[]
 for name,axs in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log.decode('utf8',errors='replace')):
  axioms=[s.strip()for s in axs.split(',')if s.strip()]
  assert set(axioms)<={'propext','Classical.choice','Quot.sound'},(module,axioms)
  roots.append({'name':name,'axioms':axioms})
 data=module.endswith('Data')
 assert data or roots,module
 kind='final_local_exclusion' if module.endswith('WindowMomentExclusions') else (
      'aggregate_coefficient_or_strict_check' if module in plan['modules'] and not data else
      'untrusted_data' if data else 'proved_input_or_algebra')
 records.append({'module':module,'kind':kind,'source_path':path,'source_sha256':sha(src),'source_bytes':len(src),
                 'log_path':logpath,'log_sha256':sha(log),'olean_sha256':r['olean_sha256'],
                 'duration_seconds':r['whole_process_seconds'],'data_only':data,'roots':roots,
                 'ordinary_Lean_passed':True})
 files.extend([path,logpath])
final=next(r for r in records if r['kind']=='final_local_exclusion')
names={r['name']for r in final['roots']}
expected=['StructuralGoal20261016.WindowMomentExclusions.exclude0',
          'StructuralGoal20261016.WindowMomentExclusions.exclude1']
assert set(expected)<=names
out={'scope':__doc__,'script_sha256':sha(Path(__file__).read_bytes()),'compiler_sha256':receipt['compiler_sha256'],
     'proof_modules':sum(not r['data_only']for r in records),'data_modules':sum(r['data_only']for r in records),
     'point_rows':82,'new_q2_rows':403,'old_q2_reused':175,'actual_old_atoms':[103,106],
     'actual_energy_cells':2,'exact_common_denominator_digits':[51,54],
     'generator_safety':'Current aggregate/exclusion generators and the new *_guarded.py entry points refuse changes to exact PASS-pinned source bytes and to sources marked live; changed proofs require a new module name. Previously published generator files retain their original bytes.',
     'guarded_generation_entry_points':[
       'window_generate_moment_numeric_guarded.py','window_generate_moment_energy_cases_guarded.py',
       'window_generate_moment_atoms_guarded.py','window_generate_moment_actual_boxes_guarded.py',
       'window_generate_moment_aggregate.py','window_generate_moment_exclusions.py'],
     'root_threshold':'11/1250','orthant_separation':'123/128',
     'local_cell_paths':['r001000001000001101011101','r001000001000001110011100'],
     'cell_scope':'The contracted cells stored in the audited input packet at these paths, not the entire uncontracted ancestor cells.',
     'cell_source':'cover-cross-moment-factor-friendly-cases.json: cases[*].cell',
     'ancestral_reachability_Lean_proven_here':False,
     'ancestral_reachability_evidence':'Independent Python replay of the frozen ancestry remains separate from the local Lean exclusion theorem.',
     'formal_root_cover_composition_proven_here':False,
     'actual_ordinary_Lean_local_exclusions':2,'final_roots':expected,'records':records,
     'all_current_sources_and_logs_verified':True,'independent_replay_of_new_exclusions':False,
     'fresh_downstream_recheck_receipt':'window_moment_chain_recheck_receipt.json',
     'complete_global_cover':False,'new_zero_proportion_proven':False}
path=HERE/'window_moment_actual_exclusion_index.json'
path.write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
files.append('research-goal-20261016/'+path.name)
files=list(dict.fromkeys(files))
idx={'files':[{'path':p,'sha256':sha((ROOT/p).read_bytes()),'bytes':(ROOT/p).stat().st_size}for p in files],
     'exclusion_index_sha256':sha(path.read_bytes()),'actual_ordinary_Lean_local_exclusions':2,
     'complete_global_cover':False,'new_zero_proportion_proven':False}
sync=HERE/'window_moment_actual_exclusion_sync_files.json'
sync.write_text(json.dumps(idx,indent=2)+'\n',encoding='utf8')
print(json.dumps({'proof_modules':out['proof_modules'],'data_modules':out['data_modules'],
                  'actual_local_exclusions':2,'index_sha256':sha(path.read_bytes()),'sync_sha256':sha(sync.read_bytes()),'files':len(files)}))
