"""Freeze three ordinary-kernel analytic bridges; numerical inputs remain hypotheses.

This is not a new local exclusion, a complete cover, or an independent
kernel replay. Existing local exclusion counts are unchanged.
"""
from pathlib import Path
import hashlib
import json
import re

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
sha=lambda raw:hashlib.sha256(raw).hexdigest()
receipt=json.loads((HERE/'lean_verification.json').read_bytes())
known={r['module']:r for r in receipt['modules']}
names=['WindowMomentResidualPSD','WindowScalarBregman','WindowScalarBregmanPacket']
records=[]
files=['research-goal-20261016/'+Path(__file__).name]
for name in names:
    module='StructuralGoal20261016.'+name
    r=known[module]
    path=module.replace('.','/')+'.lean'
    raw=(ROOT/path).read_bytes()
    assert r['source_sha256']==sha(raw) and r['source_unchanged'],module
    assert r['passed'] and r['exit_code']==0,module
    log='research-goal-20261016/'+r['log']
    text=(ROOT/log).read_bytes()
    assert sha(text)==r['log_sha256'],module
    roots=[]
    for root,axs in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",text.decode('utf8',errors='replace')):
        axioms=[s.strip() for s in axs.split(',') if s.strip()]
        assert set(axioms)<={'propext','Classical.choice','Quot.sound'},(module,axioms)
        roots.append({'name':root,'axioms':axioms})
    assert roots,module
    records.append({'module':module,'source':path,'source_sha256':sha(raw),'source_bytes':len(raw),
       'log':log,'log_sha256':sha(text),'olean_sha256':r['olean_sha256'],
       'whole_process_seconds':r['whole_process_seconds'],'roots':roots,
       'ordinary_Lean_passed':True})
    files += [path,log]
out={'scope':__doc__,'script_sha256':sha(Path(__file__).read_bytes()),
     'canonical_receipt':'research-goal-20261016/lean_verification.json',
     'compiler_sha256':receipt['compiler_sha256'],'proof_modules':3,
     'records':records,'all_current_sources_and_logs_verified':True,
     'analytic_hypotheses':{
       'ResidualPSD':'Actual derivative affine enclosure, nonzero normalization radii.',
       'ScalarBregman':'p,x in the certified interval; m<M; m<=actual w-second<=M on the whole interval.',
       'BregmanPacket':'The preceding curvature hypotheses plus actual point value/slope enclosures and a certified |x-p-eta| error radius.'},
     'new_actual_local_exclusions':0,'complete_global_cover':False,
     'new_zero_proportion_proven':False,'independent_Nanoda_replayed':False}
p=HERE/'window_bregman_core_formal_index.json'
p.write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
files.append('research-goal-20261016/'+p.name)
sync={'formal_index_sha256':sha(p.read_bytes()),
      'files':[{'path':s,'sha256':sha((ROOT/s).read_bytes()),'bytes':(ROOT/s).stat().st_size} for s in files],
      'proof_modules':3,'new_actual_local_exclusions':0,'complete_global_cover':False,
      'new_zero_proportion_proven':False,'independent_Nanoda_replayed':False}
q=HERE/'window_bregman_core_sync_files.json'
q.write_text(json.dumps(sync,indent=2)+'\n',encoding='utf8')
print(json.dumps({'proof_modules':3,'roots':sum(len(r['roots']) for r in records),
                  'files':len(files),'index_sha256':sha(p.read_bytes()),'sync_sha256':sha(q.read_bytes())}))
