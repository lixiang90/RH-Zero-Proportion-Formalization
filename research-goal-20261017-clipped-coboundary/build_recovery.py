"""Build an output-only recovery fork; never imports/calls an optimizer."""
from pathlib import Path
import ast,hashlib
HERE=Path(__file__).resolve().parent
source=(HERE/'clipped_pilot.py').read_text();dest=HERE/'clipped_recovery.py';assert not dest.exists()
assert hashlib.sha256((HERE/'failure-files.json').read_bytes()).hexdigest()=='776052bad06ca5240e47d58c31e83d0dbb17cbe567125d5787828c80d6b36278'
new=source.replace("OUT=HERE/'clipped-pilot.json';START=HERE/'LP-started.json'", "OUT=HERE/'recovery-pilot.json';START=HERE/'recovery-LP-started.json';RAW=HERE/'raw-result.json'")
new=new.replace('import hashlib, json, math, os, sys, time','import hashlib, json, math, os, sys, time\nfrom types import SimpleNamespace')
helpers='''def native(v):
    if isinstance(v,np.ndarray):return native(v.tolist())
    if isinstance(v,np.generic):return native(v.item())
    if isinstance(v,dict):return {str(k):native(w)for k,w in v.items()}
    if isinstance(v,(list,tuple)):return [native(w)for w in v]
    if isinstance(v,float)and not math.isfinite(v):return 'NaN'if math.isnan(v)else 'Infinity'if v>0 else '-Infinity'
    if v is None or isinstance(v,(str,int,float,bool)):return v
    raise TypeError('Unsupported output type: '+repr(type(v)))
def durable(path,data):
    payload=json.dumps(native(data),indent=2,allow_nan=False)+'\\n';temp=path.with_suffix(path.suffix+'.partial')
    with temp.open('w',encoding='utf8')as handle:handle.write(payload);handle.flush();os.fsync(handle.fileno())
    os.replace(temp,path)
'''
new=new.replace('def main():',helpers+'\ndef main():',1)
new=new.replace('assert not OUT.exists()and not START.exists();began=', 'assert not OUT.exists()and not START.exists()and not RAW.exists();began=')
new=new.replace('    pins={p.relative_to(ROOT)',"    paths.extend([HERE/'failure-files.json',HERE/'failure-receipt.json',HERE/'clipped_pilot.py',HERE/'LP-started.json',HERE/'build_recovery.py'])\n    assert digest(HERE/'failure-files.json')=='776052bad06ca5240e47d58c31e83d0dbb17cbe567125d5787828c80d6b36278'\n    pins={p.relative_to(ROOT)",1)
begin=new.index("    out={**startdoc,'phase':");end=new.index('    for p in paths:assert digest(p)==pins',begin)
body=new[begin:end].replace("'LP_seconds':time.monotonic()-tick", "'LP_seconds':elapsed")
summary='    def summary(result,elapsed):\n'+''.join('    '+line+'\n'for line in body.splitlines())+'        return out\n'
new=new[:begin]+"    elapsed=time.monotonic()-tick\n    durable(RAW,{'source_sha256_start':pins,'actual_total_LP_calls_including_failed_output':2,'this_recovery_LP_calls':1,'LP_seconds':elapsed,'result':dict(result)})\n    out=summary(result,elapsed)\n"+new[end:]
marker="    START.write_text(json.dumps(startdoc,indent=2,allow_nan=False)+'\\n',encoding='utf8');tick=time.monotonic()"
preflight=summary+'''    # Full prospective summary and raw-result type/schema preflight, with
    # a dummy vector only for JSON conversion. No mathematical point is queried.
    mock=SimpleNamespace(status=0,message='serialization preflight only',success=np.bool_(True),nit=np.int64(0),x=np.zeros(9))
    check=summary(mock,0.)
    check.update({'source_sha256_end':pins,'all_sources_unchanged':True,'seconds':0.,'potential_range_proof_instantiated_in_Lean':False,
        'new_G_requires_new_KKT_Newton_and_root_budget':True,'old_F_KKT_or_Newton_leaves_reused':False,
        'global_mean_floor_proven':False,'new_Lean_invocations':0,'cell_exclusion_proven':False,'new_zero_proportion_proven':False})
    json.dumps(native(check),allow_nan=False)
    json.dumps(native({'result':{'status':np.int64(0),'success':np.bool_(True),'x':np.zeros(9),'fun':np.float64(0),
        'ineqlin':{'residual':np.zeros(29180),'marginals':np.zeros(29180)},'lower':{'residual':np.zeros(9),'marginals':np.zeros(9)},
        'upper':{'residual':np.full(9,np.inf),'marginals':np.zeros(9)}}}),allow_nan=False)
    startdoc.update({'complete_JSON_schema_preflight_passed':True,'actual_total_LP_calls_authorized_including_original':2,
        'identical_model_recovery_authorized':True,'prior_result_output_failed':True,'no_further_retry_authorized':True})
    durable(START,startdoc);tick=time.monotonic()'''
assert marker in new;new=new.replace(marker,preflight,1)
new=new.replace("    OUT.write_text(json.dumps(out,indent=2,allow_nan=False)+'\\n',encoding='utf8')", "    out.update({'actual_total_LP_calls_including_failed_output':2,'this_recovery_LP_calls':1,'raw_result_path':RAW.relative_to(ROOT).as_posix(),'raw_result_sha256':digest(RAW),'serialization_preflight_passed':True})\n    durable(OUT,out)")
new=new.replace("'seconds']}),flush=True)","'seconds']}),flush=True)")
old_calls=[ast.dump(n,include_attributes=False)for n in ast.walk(ast.parse(source))if isinstance(n,ast.Call)and isinstance(n.func,ast.Name)and n.func.id=='linprog']
new_calls=[ast.dump(n,include_attributes=False)for n in ast.walk(ast.parse(new))if isinstance(n,ast.Call)and isinstance(n.func,ast.Name)and n.func.id=='linprog']
assert len(old_calls)==len(new_calls)==1 and old_calls==new_calls
start="    rows=[];counts=[];gram=";stop="    startdoc={'scope':"
assert source[source.index(start):source.index(stop)]==new[new.index(start):new.index(stop)]
dest.write_text(new,encoding='utf8')
print('output-only recovery source created; pool/kernel/features/matrix/objective/bounds/linprog AST unchanged')
