"""Seal only the eight-leaf W10 pilot after current-source kernel PASS.

The root scaffold retains sixteen sibling coverage hypotheses. This index
does not certify the complete W10 tree or an improved zero proportion.
"""
from pathlib import Path
import hashlib
import json
import re
import statistics

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
sha=lambda raw:hashlib.sha256(raw).hexdigest()
plan=json.loads((HERE/'lean_leaf_pilot_generated.json').read_bytes())
receipt=json.loads((HERE/'lean_verification.json').read_bytes())
known={r['module']:r for r in receipt['modules']}
records=[]
files=['research-goal-20261016/'+s for s in [
 'lean_generate_leaf_pilot.py','lean_leaf_pilot_generated.json',
 'lean_seal_leaf_pilot.py','window_moment_frozen_write.py']]
for entry in plan['modules']:
    module=entry['module']
    r=known[module]
    source=(ROOT/entry['source']).read_bytes()
    assert sha(source)==entry['source_sha256']==r['source_sha256'],module
    assert r['passed'] and r['source_unchanged'] and r['exit_code']==0,module
    logpath='research-goal-20261016/'+r['log']
    raw=(ROOT/logpath).read_bytes()
    assert sha(raw)==r['log_sha256'],module
    roots=[]
    for name,axs in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",raw.decode('utf8',errors='replace')):
        axioms=[s.strip() for s in axs.split(',') if s.strip()]
        assert set(axioms)<={'propext','Classical.choice','Quot.sound'},(module,axioms)
        roots.append({'name':name,'axioms':axioms})
    data=module.endswith('Data')
    assert data or roots,module
    records.append({**entry,'data_only':data,'roots':roots,
      'ordinary_Lean_passed':True,'log':logpath,'log_sha256':sha(raw),
      'olean_sha256':r['olean_sha256'],'whole_process_seconds':r['whole_process_seconds']})
    files += [entry['source'],logpath]
leaf_times=[r['whole_process_seconds'] for r in records if 'LeafPilotLeaf' in r['module']]
assert len(leaf_times)==8
out={'scope':__doc__,'script_sha256':sha(Path(__file__).read_bytes()),
 'compiler_sha256':receipt['compiler_sha256'],'prefix':plan['prefix'],
 'frozen_tree_sha256':plan['tree_sha256'],'frozen_compact_sha256':plan['compact_sha256'],
 'distinct_numeric_leaves':8,'subtree_nodes':15,'subtree_branches':7,'ancestor_branches':16,
 'records':records,'proof_modules':10,'data_modules':1,
 'unconditional_subtree_root':'StructuralGoal20261016.W10LeafPilot.selected_covered',
 'conditional_root_scaffold':'StructuralGoal20261016.W10LeafPilot.root_covered_of_siblings',
 'unproved_sibling_hypotheses':plan['unproved_sibling_hypotheses'],
 'all_current_sources_and_logs_verified':True,
 'performance':{'leaf_whole_process_seconds':leaf_times,
   'warm_leaf_module_median_seconds':statistics.median([v for i,v in enumerate(leaf_times) if i!=1]),
   'cold_leaf_module_seconds':leaf_times[1],
   'compute_only_cost_isolated':False,
   'observed_process_snapshot':{'module':'StructuralGoal20261016.W10LeafPilotLeaf01',
      'linux_pid':619,'RSS_KiB':7194896,'elapsed_seconds':41,'CPU_percent':37.8,
      'maximum_RSS_measured':False},
   'note':'Module durations include import overhead; no whole-tree runtime extrapolation is certified.'},
 'ordinary_Lean_verified':True,'independent_replay':False,
 'complete_W10_cover':False,'source_size_compliant':False,'new_zero_proportion_proven':False}
p=HERE/'lean_leaf_pilot_proof_index.json'
p.write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
files.append('research-goal-20261016/'+p.name)
files=list(dict.fromkeys(files))
sync={'proof_index_sha256':sha(p.read_bytes()),
      'files':[{'path':s,'sha256':sha((ROOT/s).read_bytes()),'bytes':(ROOT/s).stat().st_size}for s in files],
      'distinct_numeric_leaves':8,'complete_W10_cover':False,'new_zero_proportion_proven':False}
q=HERE/'lean_leaf_pilot_sync_files.json'
q.write_text(json.dumps(sync,indent=2)+'\n',encoding='utf8')
print(json.dumps({'proof_modules':10,'data_modules':1,'files':len(files),
                  'proof_index_sha256':sha(p.read_bytes()),'sync_sha256':sha(q.read_bytes()),
                  'warm_module_median_seconds':out['performance']['warm_leaf_module_median_seconds']}))
