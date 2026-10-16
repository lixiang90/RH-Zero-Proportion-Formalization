"""Sole serial timed verification of the fixed 127-leaf auxiliary scope.

Each compiler is capped at 13500MB and 180 seconds. No failed stage is
silently skipped. The complete 95,615-leaf W10 tree is never dispatched.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re
import subprocess
import sys
import lean_verify

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
LINUX='/mnt/d/codex-build/Riemann-Zero/RH-Zero-Proportion-Formalization'
sha=lambda raw:hashlib.sha256(raw).hexdigest()
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('stage',choices=['pilot','rest','compose'])
args=ap.parse_args()
plan=json.loads((HERE/'lean_aux127_generated.json').read_bytes())
assert plan['numeric_leaves']==127 and plan['prefix']=='r0010'
assert json.loads((HERE/'lean_priority_queue.json').read_bytes())==[]
entries=plan['modules']
if args.stage=='pilot':
    entries=[r for r in entries if r['kind']=='data' or r.get('leaf_start')==0]
elif args.stage=='rest':
    entries=[r for r in entries if r['kind']=='geometry_aux' or (r['kind']=='numeric_aux' and r['leaf_start']>0)]
else:
    receipt=json.loads((HERE/'lean_aux127_verification.json').read_bytes())
    known={r['module']:r for r in receipt['modules']}
    for r in entries:
        if r['kind']!='composition':
            assert known[r['module']]['passed'] and known[r['module']]['source_sha256']==r['source_sha256'],r['module']
    entries=[r for r in entries if r['kind']=='composition']
targets=[r['module']for r in entries]
for r in entries:
    assert sha((ROOT/r['source']).read_bytes())==r['source_sha256'],r['module']
original_popen=subprocess.Popen
previous_profile=None


def timed_popen(argv,*posargs,**kwargs):
    global previous_profile
    if isinstance(argv,list) and '/usr/bin/prlimit' in argv:
        if previous_profile and previous_profile.exists():
            text=previous_profile.read_text()
            peak=int(re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)',text).group(1))
            if peak>=12*1024*1024:
                raise SystemExit('Stop at checkpoint: previous module RSS reached 12GiB; reduce the next batch.')
        source=Path(argv[-1]).name
        assert source in [m.rsplit('.',1)[-1]+'.lean'for m in targets]
        assert '-M13500' in argv
        raw=(ROOT/'StructuralGoal20261016'/source).read_bytes()
        profile='lean_timed_'+source[:-5]+'_'+sha(raw)[:12]+'.txt'
        previous_profile=HERE/profile
        pos=argv.index('/usr/bin/prlimit')
        argv[pos:pos]=['/usr/bin/time','-v','-o',LINUX+'/research-goal-20261016/'+profile,
                       '/usr/bin/timeout','--signal=TERM','--kill-after=15s','180s']
    return original_popen(argv,*posargs,**kwargs)


subprocess.Popen=timed_popen
sys.argv=[sys.argv[0],'--receipt','lean_aux127_verification.json']+targets
exitcode=0
try:
    lean_verify.main()
except SystemExit as exc:
    exitcode=exc.code or 0
receipt=json.loads((HERE/'lean_aux127_verification.json').read_bytes())
canonical=HERE/'lean_verification.json'
combined=json.loads(canonical.read_bytes())
known={r['module']:r for r in combined['modules']}
for r in receipt['modules']:
    known[r['module']]=r
combined['modules']=list(known.values())
lean_verify.save(canonical,combined)
print(json.dumps({'aux127_stage':args.stage,'stage_exit_code':exitcode,
                  'complete_W10_cover':False}),flush=True)
raise SystemExit(exitcode)
