"""Freeze the same-eight-leaf auxiliary batch and resource measurements.

Only one mathematical module is new; two import controls are diagnostics.
There are no new distinct cells and no complete W10 coverage theorem.
"""
from pathlib import Path
import hashlib
import json
import re

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
sha=lambda raw:hashlib.sha256(raw).hexdigest()
plan=json.loads((HERE/'lean_leaf_batch_generated.json').read_bytes())
receipt=json.loads((HERE/'lean_leaf_batch_benchmark_receipt.json').read_bytes())
known={r['module']:r for r in receipt['modules']}
files=['research-goal-20261016/'+n for n in ['lean_generate_leaf_batch_probe.py',
 'lean_leaf_batch_benchmark.py','lean_leaf_batch_generated.json',
 'lean_leaf_batch_benchmark_receipt.json','lean_seal_leaf_batch.py']]
records=[]


def metric(text,label):
    return re.search(re.escape(label)+r':\s*(\S+)',text).group(1)


for entry in plan['modules']:
    module=entry['module'];r=known[module]
    assert r['passed'] and r['source_unchanged'] and r['exit_code']==0,module
    assert sha((ROOT/entry['source']).read_bytes())==r['source_sha256']==entry['source_sha256']
    log='research-goal-20261016/'+r['log'];raw=(ROOT/log).read_bytes()
    assert sha(raw)==r['log_sha256']
    roots=[]
    for name,axs in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",raw.decode('utf8',errors='replace')):
        axioms=[s.strip() for s in axs.split(',') if s.strip()]
        assert set(axioms)<={'propext','Classical.choice','Quot.sound'},(module,axioms)
        roots.append({'name':name,'axioms':axioms})
    batch=module.endswith('Batch')
    assert len(roots)==(24 if batch else 0)
    profile='research-goal-20261016/lean_timed_'+module.rsplit('.',1)[-1]+'_'+r['source_sha256'][:12]+'.txt'
    rawprofile=(ROOT/profile).read_bytes();text=rawprofile.decode()
    wall=metric(text,'Elapsed (wall clock) time (h:mm:ss or m:ss)')
    parts=[float(v) for v in wall.split(':')];wallsecs=sum(v*60**i for i,v in enumerate(reversed(parts)))
    user=float(metric(text,'User time (seconds)'));system=float(metric(text,'System time (seconds)'))
    records.append({**entry,'ordinary_Lean_passed':True,'diagnostic_control':not batch,'roots':roots,
      'log':log,'log_sha256':sha(raw),'olean_sha256':r['olean_sha256'],
      'whole_process_seconds':r['whole_process_seconds'],'resource':profile,'resource_sha256':sha(rawprofile),
      'Linux_wall_seconds':wallsecs,'user_seconds':user,'system_seconds':system,
      'CPU_seconds':user+system,'max_RSS_KiB':int(metric(text,'Maximum resident set size (kbytes)'))})
    files += [entry['source'],log,profile]
cold,warm,batch=records
delta_wall=batch['Linux_wall_seconds']-warm['Linux_wall_seconds']
delta_cpu=batch['CPU_seconds']-warm['CPU_seconds']
out={'scope':__doc__,'script_sha256':sha(Path(__file__).read_bytes()),
 'compiler_sha256':receipt['compiler_sha256'],'base_verifier_sha256':receipt['driver_sha256'],
 'benchmark_runner_sha256':sha((HERE/'lean_leaf_batch_benchmark.py').read_bytes()),
 'GNU_time_sha256':'7310b9b4c51a8f4d26c1af0da250f03a49ec8a8141033123e79196ad18f6c81b',
 'records':records,'proof_modules':1,'diagnostic_controls':2,'rechecked_numeric_leaves':8,
 'new_distinct_numeric_leaves':0,'batch_printed_roots':24,
 'pilot_proof_index_sha256':sha((HERE/'lean_leaf_pilot_proof_index.json').read_bytes()),
 'pilot_sync_manifest_sha256':sha((HERE/'lean_leaf_pilot_sync_files.json').read_bytes()),
 'comparison':{'warm_import_wall_seconds':warm['Linux_wall_seconds'],
   'batch_wall_seconds':batch['Linux_wall_seconds'],'incremental_wall_seconds':delta_wall,
   'incremental_CPU_seconds':delta_cpu,'incremental_wall_seconds_per_leaf':delta_wall/8,
   'incremental_CPU_seconds_per_leaf':delta_cpu/8,
   'RSS_increase_over_import_control_KiB':batch['max_RSS_KiB']-warm['max_RSS_KiB'],
   'interpretation':'One small paired sample. The difference includes leaf normalization, arithmetic and soundness theorem work; it is not a certified full-tree runtime or 127-leaf memory prediction.'},
 'all_current_sources_logs_resources_verified':True,'independent_kernel_replay':False,
 'complete_W10_cover':False,'source_size_compliant':False,'new_zero_proportion_proven':False,
 'no_127_leaf_aux_source_generated_here':True}
p=HERE/'lean_leaf_batch_proof_index.json';p.write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
files.append('research-goal-20261016/'+p.name)
sync={'proof_index_sha256':sha(p.read_bytes()),
 'files':[{'path':s,'sha256':sha((ROOT/s).read_bytes()),'bytes':(ROOT/s).stat().st_size}for s in files],
 'proof_modules':1,'diagnostic_controls':2,'new_distinct_numeric_leaves':0,
 'complete_W10_cover':False,'new_zero_proportion_proven':False}
q=HERE/'lean_leaf_batch_sync_files.json';q.write_text(json.dumps(sync,indent=2)+'\n',encoding='utf8')
print(json.dumps({'proof_index_sha256':sha(p.read_bytes()),'sync_sha256':sha(q.read_bytes()),
                  'files':len(files),'incremental_CPU_seconds_per_leaf':delta_cpu/8,
                  'max_RSS_KiB':batch['max_RSS_KiB']}))
