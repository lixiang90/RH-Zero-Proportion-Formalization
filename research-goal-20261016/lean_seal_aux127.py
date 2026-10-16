"""Seal actual complete coverage of the fixed 127-leaf W10 subtree.

All internal numerical and geometric obligations are discharged. The
separate original-root scaffold retains four sibling coverage hypotheses.
This is not a complete 95,615-numeric-leaf W10 proof or a new zero bound.
"""
from pathlib import Path
import hashlib
import json
import re

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
sha=lambda raw:hashlib.sha256(raw).hexdigest()
plan=json.loads((HERE/'lean_aux127_generated.json').read_bytes())
receipt=json.loads((HERE/'lean_aux127_verification.json').read_bytes())
known={r['module']:r for r in receipt['modules']}
canonical={r['module']:r for r in json.loads((HERE/'lean_verification.json').read_bytes())['modules']}
assert plan['numeric_leaves']==127 and plan['subtree_branches']==126
records=[]
files=['research-goal-20261016/'+n for n in ['lean_generate_aux127.py','lean_aux127_verify.py',
 'lean_aux127_generated.json','lean_aux127_seed.json.gz','lean_seed_aux127.py',
 'lean_check_aux127_reproduction.py','lean_aux127_reproduction.json',
 'lean_seal_aux127.py','lean_aux127_verification.json','window_moment_frozen_write.py']]


def metric(text,label):
    return re.search(re.escape(label)+r':\s*(\S+)',text).group(1)


for entry in plan['modules']:
    module=entry['module'];r=known[module]
    assert r['passed'] and r['exit_code']==0 and r['source_unchanged'],module
    assert sha((ROOT/entry['source']).read_bytes())==r['source_sha256']==entry['source_sha256']
    assert canonical[module]==r,module
    log='research-goal-20261016/'+r['log'];raw=(ROOT/log).read_bytes()
    assert sha(raw)==r['log_sha256']
    roots=[]
    for name,axs in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",raw.decode('utf8',errors='replace')):
        axioms=[s.strip() for s in axs.split(',') if s.strip()]
        assert set(axioms)<={'propext','Classical.choice','Quot.sound'},(module,axioms)
        roots.append({'name':name,'axioms':axioms})
    for name in re.findall(r"'([^']+)' does not depend on any axioms",raw.decode('utf8',errors='replace')):
        roots.append({'name':name,'axioms':[]})
    assert {p['name']for p in roots}==set(entry['roots']),module
    profile='research-goal-20261016/lean_timed_'+module.rsplit('.',1)[-1]+'_'+r['source_sha256'][:12]+'.txt'
    resource=(ROOT/profile).read_bytes();text=resource.decode()
    parts=[float(v)for v in metric(text,'Elapsed (wall clock) time (h:mm:ss or m:ss)').split(':')]
    wall=sum(v*60**i for i,v in enumerate(reversed(parts)))
    user=float(metric(text,'User time (seconds)'));system=float(metric(text,'System time (seconds)'))
    records.append({**entry,'ordinary_Lean_passed':True,'printed_roots':roots,
      'log':log,'log_sha256':sha(raw),'olean_sha256':r['olean_sha256'],
      'resource':profile,'resource_sha256':sha(resource),
      'whole_process_seconds':r['whole_process_seconds'],'Linux_wall_seconds':wall,
      'user_seconds':user,'system_seconds':system,'CPU_seconds':user+system,
      'max_RSS_KiB':int(metric(text,'Maximum resident set size (kbytes)'))})
    files += [entry['source'],log,profile]
final=next(r for r in records if r['kind']=='composition')
assert 'StructuralGoal20261016.W10Aux127.selected_covered'in {r['name']for r in final['printed_roots']}
reproduction=json.loads((HERE/'lean_aux127_reproduction.json').read_bytes())
assert reproduction['all_source_bytes_and_mtimes_unchanged']
assert reproduction['generator_sha256']==sha((HERE/'lean_generate_aux127.py').read_bytes())
assert reproduction['seed_sha256']==plan['self_contained_seed_sha256']
out={'scope':__doc__,'script_sha256':sha(Path(__file__).read_bytes()),
 'compiler_sha256':receipt['compiler_sha256'],'base_verifier_sha256':receipt['driver_sha256'],
 'timed_runner_sha256':sha((HERE/'lean_aux127_verify.py').read_bytes()),
 'GNU_time_sha256':'7310b9b4c51a8f4d26c1af0da250f03a49ec8a8141033123e79196ad18f6c81b',
 'prefix':'r0010','candidate':'old-W10','candidate_floor':'433/50000',
 'numeric_leaves':127,'internal_subtree_branches':126,'ancestor_branches':4,
 'proof_modules':22,'data_modules':1,'printed_roots':sum(len(r['printed_roots'])for r in records),
 'records':records,'complete_selected_subtree_coverage_Lean_proven':True,
 'selected_subtree_root':'StructuralGoal20261016.W10Aux127.selected_covered',
 'internal_numeric_or_geometry_hypotheses_remaining':0,
 'original_root_scaffold':'StructuralGoal20261016.W10Aux127.root_covered_of_siblings',
 'unproved_original_root_sibling_hypotheses':plan['unproved_root_sibling_hypotheses'],
 'same_frozen_monolithic_cell_literal':True,
 'old_unpassed_monolithic_source_sha256_provenance_only':plan['old_unpassed_monolithic_source_sha256'],
 'tree_sha256_provenance_only':plan['tree_sha256'],'compact_sha256_provenance_only':plan['compact_sha256'],
 'seed_sha256':plan['self_contained_seed_sha256'],'seed_bytes':plan['self_contained_seed_bytes'],
 'seed_mathematical_data_trusted':False,'generator_large_input_dependency':False,
 'cost':{'Linux_wall_seconds_sum':sum(r['Linux_wall_seconds']for r in records),
         'CPU_seconds_sum':sum(r['CPU_seconds']for r in records),
         'max_RSS_KiB':max(r['max_RSS_KiB']for r in records),
         'numeric_groups':[{'leaves':r['leaf_count'],'Linux_wall_seconds':r['Linux_wall_seconds'],
           'CPU_seconds':r['CPU_seconds'],'max_RSS_KiB':r['max_RSS_KiB']}
           for r in records if r['kind']=='numeric_aux'],
         'composition_Linux_wall_seconds':final['Linux_wall_seconds'],
         'note':'Observed costs for this fixed subtree; no certified whole-tree runtime or compression result.'},
 'all_current_sources_logs_resources_verified':True,'complete_W10_cover':False,
 'independent_kernel_replay':False,'source_size_compliant':False,'new_zero_proportion_proven':False}
p=HERE/'lean_aux127_proof_index.json';p.write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
files.append('research-goal-20261016/'+p.name)
sync={'proof_index_sha256':sha(p.read_bytes()),
 'files':[{'path':s,'sha256':sha((ROOT/s).read_bytes()),'bytes':(ROOT/s).stat().st_size}for s in files],
 'proof_modules':22,'data_modules':1,'numeric_leaves':127,
 'complete_selected_subtree_coverage_Lean_proven':True,
 'complete_W10_cover':False,'new_zero_proportion_proven':False}
q=HERE/'lean_aux127_sync_files.json';q.write_text(json.dumps(sync,indent=2)+'\n',encoding='utf8')
print(json.dumps({'proof_modules':22,'data_modules':1,'files':len(files),
 'proof_index_sha256':sha(p.read_bytes()),'sync_sha256':sha(q.read_bytes()),'cost':out['cost']}))
