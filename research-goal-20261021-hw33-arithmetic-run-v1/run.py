"""Root-selected single run of NEW H33 arithmetic only; no full source replay."""
from pathlib import Path
import hashlib, json, os, subprocess, time
ROOT=Path(__file__).resolve().parent.parent
HERE=Path(__file__).resolve().parent
probe=ROOT/'research-goal-20261021-attempt030-h33-arithmetic-probe-preparation-v2/FloorProbe.lean'
data=probe.read_bytes()
assert len(data)==7634 and hashlib.sha256(data).hexdigest()=='2750bae9e75c3b0c030057a90b92fb7cea0d84399112fbba701561d30dc5dbc8'
source=HERE/'FloorProbe.lean'
assert not source.exists() and not (HERE/'terminal.json').exists()
source.write_bytes(data+b'\n#print axioms AMW.floor_numeric\n#print axioms AMW.h33_ratio_exact\n#print axioms AMW.h33_strict_improvement\n')
historical=json.loads((ROOT/'research-goal-20261021-w9a2-v11-resource-pass-v1/work/started.json').read_bytes())
compiler=historical['compiler_argv'][0]
environment=os.environ.copy()
environment['LEAN_PATH']=';'.join(historical['package_libs_reused_without_recursive_data_rehash'])
environment['LEAN_SYSROOT']=historical['compiler_environment']['LEAN_SYSROOT']
args=[compiler,'-j1','-M6500','--tstack=262144','-DrelaxedAutoImplicit=false','-DElab.async=false',
      '-o',str(HERE/'FloorProbe.olean'),'-i',str(HERE/'FloorProbe.ilean'),'-c',str(HERE/'FloorProbe.c'),'--json',str(source)]
receipt={'schema':'new-H33-arithmetic-probe-run-v1','scope':'Only new floor inequality, ratio identity and exact strict improvement. No upstream certificate/full proof/exporter/independent kernels/site acceptance.',
         'source_bytes':len(source.read_bytes()),'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
         'command':args,'LEAN_PATH':environment['LEAN_PATH'],'runtime_reuse':'Historical package overlays only, no new recursive audit and no cached user Core/Candidate or trusted Challenge imported',
         'timeout_seconds':120,'automatic_retries':0,'full_source_passed':False,'official_accepted':False}
(HERE/'started.json').write_bytes((json.dumps(receipt,indent=2)+'\n').encode())
t=time.monotonic()
try:
    with (HERE/'stdout.jsonl').open('xb') as out,(HERE/'stderr.log').open('xb') as err:
        result=subprocess.run(args,env=environment,cwd=HERE,stdout=out,stderr=err,timeout=120)
    receipt['child_exit_code']=result.returncode
    receipt['timed_out']=False
except subprocess.TimeoutExpired:
    receipt['child_exit_code']=None;receipt['timed_out']=True
finally:
    receipt['elapsed_seconds']=time.monotonic()-t
    receipt['outputs']=[]
    for name in ['FloorProbe.olean','FloorProbe.ilean','FloorProbe.c','stdout.jsonl','stderr.log']:
        p=HERE/name
        if p.exists():
            b=p.read_bytes();receipt['outputs'].append({'path':name,'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()})
    receipt['arithmetic_probe_passed']=receipt.get('child_exit_code')==0 and not receipt['timed_out']
    (HERE/'terminal.json').write_bytes((json.dumps(receipt,indent=2)+'\n').encode())
    print(json.dumps({k:receipt[k] for k in ['child_exit_code','timed_out','elapsed_seconds','arithmetic_probe_passed','outputs']}))
raise SystemExit(0 if receipt['arithmetic_probe_passed'] else 1)
