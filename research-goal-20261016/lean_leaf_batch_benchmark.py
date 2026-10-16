"""Run only the fixed eight-leaf batch probe with GNU time resource logs.

The existing serial verifier constructs the exact pinned Lean invocation.
This wrapper inserts GNU time before prlimit; it mutates the invocation list
so the durable proof receipt records the complete executed command.
"""
from pathlib import Path
import hashlib
import json
import subprocess
import sys
import lean_verify

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
LINUX='/mnt/d/codex-build/Riemann-Zero/RH-Zero-Proportion-Formalization'
plan=json.loads((HERE/'lean_leaf_batch_generated.json').read_bytes())
targets=[r['module'] for r in plan['modules']]
assert len(targets)==3 and plan['distinct_numerical_leaves']==8
original_popen=subprocess.Popen


def timed_popen(argv,*args,**kwargs):
    if isinstance(argv,list) and '/usr/bin/prlimit' in argv:
        source=Path(argv[-1]).name
        assert source in [m.rsplit('.',1)[-1]+'.lean' for m in targets]
        module=source[:-5]
        raw=(ROOT/'StructuralGoal20261016'/source).read_bytes()
        profile='lean_timed_'+module+'_'+hashlib.sha256(raw).hexdigest()[:12]+'.txt'
        pos=argv.index('/usr/bin/prlimit')
        argv[pos:pos]=['/usr/bin/time','-v','-o',LINUX+'/research-goal-20261016/'+profile]
    return original_popen(argv,*args,**kwargs)


subprocess.Popen=timed_popen
sys.argv=[sys.argv[0],'--receipt','lean_leaf_batch_benchmark_receipt.json','--keep-going']+targets
lean_verify.main()
