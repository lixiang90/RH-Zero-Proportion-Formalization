"""Whole imported Zeta trace-graph literal arithmetic; zero SDK hash/API calls."""
import hashlib
import json
from pathlib import Path
import re
from cache_binding import header_info, TraceHashGraph, mix

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
BASE=ROOT/'research-goal-20261020-w9a2-runtime-closure-preparation/runtime-closure-CANDIDATE-INCOMPLETE.json'
configuration=json.loads(BASE.read_text(encoding='utf-8'))
packages={name:ROOT/'.lake/packages'/name for name in configuration['package_source_revisions']}
SDK_ROOTS={'Lean','Init','Std','Lake'}
nodes={};active=set();file_pins={}

def pin(path):
    raw=path.read_bytes();file_pins[str(path)]=dict(path=str(path),bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest())
    return raw
def find(module):
    rel=Path(*module.split('.')).with_suffix('.lean')
    found=[(p/rel,name) for name,p in packages.items() if (p/rel).is_file()]
    assert len(found)==1,(module,found)
    return found[0]
def visit(module):
    if module in nodes:return
    if module.split('.')[0] in SDK_ROOTS:
        nodes[module]=dict(owner='SDK');return
    assert module not in active;active.add(module)
    source,owner=find(module);raw=pin(source);is_module,details,prelude=header_info(raw)
    for imp in details:visit(imp['module'])
    base=packages[owner]/'.lake/build/lib/lean'/Path(*module.split('.'))
    trace_path=base.with_suffix('.trace');trace=json.loads(pin(trace_path));outputs=trace['outputs']
    assert outputs.get('m',False)==is_module,module
    entries=outputs['o']+[outputs[k] for k in ['rs','r'] if outputs.get(k)]
    hashes={}
    for entry in entries:
        value,suffix=entry.split('.',1);path=base.with_suffix('.'+suffix);sidecar=Path(str(path)+'.hash')
        assert path.is_file(),str(path)
        assert pin(sidecar).decode('utf-8').strip()==value,str(path)
        hashes[suffix]=int(value,16)
    nodes[module]=dict(owner=owner,is_module=is_module,import_details=details,output_hashes=hashes,
                       source=source,trace=trace)
    active.remove(module)

roots=[]
gate=json.loads((HERE/'gate-template.json').read_text(encoding='utf-8'))
for row in gate['candidate_import_source_files']:
    p=ROOT/row['path'];raw=pin(p);assert hashlib.sha256(raw).hexdigest()==row['sha256']
    roots += [imp['module'] for imp in header_info(raw)[1] if imp['module'].startswith('Zeta23.')]
for module in roots:visit(module)
graph=TraceHashGraph(nodes);results=[]
def node_hash(node):
    if isinstance(node[1],str):return int(node[1],16)
    h=1723
    for child in node[1]:h=mix(h,node_hash(child))
    return h
for module,n in nodes.items():
    if n['owner']!='Zeta23':continue
    t=n['trace'];inputs=t['inputs'];assert len(inputs)==9
    extra,imps=inputs[0][1]
    assert inputs[0][0]=='deps'
    assert extra==['Zeta23/Zeta23:extraDep',[['@Zeta23:extraDep','00000000000006bb']]]
    expected=graph.import_inputs(module)
    assert imps==['imports',expected if expected else '00000000000006bb'],module
    assert inputs[1]==['libs',[[s,'00000000000006bb'] for s in ['import dynlibs','package external libraries','module dynlibs','module plugins']]]
    assert inputs[2]==['Lean 4.33.0, commit d8b18978322de05a8f3dba51ef03cf5461676c17','3eca9d16ab6c877d']
    assert Path(inputs[3][0]).resolve()==n['source'].resolve()
    assert re.fullmatch('[0-9a-f]{16}',inputs[3][1])
    assert inputs[4]==['options',[['-DrelaxedAutoImplicit=false','74a2b5546b55be80'],['-Dpp.unicode.fun=true','9b94070140457fab']]]
    assert inputs[5]==['isModule: '+str(n['is_module']).lower(),format(mix(1723,11 if n['is_module'] else 13),'016x')]
    assert inputs[6][0]=='Module.name: '+module and re.fullmatch('[0-9a-f]{16}',inputs[6][1])
    assert inputs[7]==['Package.id?: (some Zeta23)','31803ca4013655a1']
    assert inputs[8]==['Module.leanArgs: #[]','00000000000006bb']
    h=1723
    for node in inputs:h=mix(h,node_hash(node))
    assert format(h,'016x')==t['depHash'],module
    results.append(dict(module=module,is_module=n['is_module'],import_inputs=expected,complete_trace_depHash=t['depHash']))
result=dict(scope='ALL 140 imported Zeta source/trace schemas and complete public/meta/all/legacy import trace arithmetic from existing output hash literals; not actual SDK data-byte hashing or proof validation',
  SDK_hash_API_calls=0,compiler_runs=0,proof_runs=0,result='PASS',Zeta_count=len(results),
  total_nonSDK_graph_nodes=sum(n['owner']!='SDK' for n in nodes.values()),
  modern_modules=[r['module'] for r in results if r['is_module']],modules=results,
  files=list(file_pins.values()),audit_sources=[dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest())
    for p in [HERE/'audit_trace_graph.py',HERE/'cache_binding.py',HERE/'assemble.py']])
with (HERE/'all-imported-zeta-trace-graph.json').open('x',encoding='utf-8',newline='\n') as f:
    json.dump(result,f,indent=2);f.write('\n')
print(json.dumps({k:result[k] for k in ['result','Zeta_count','total_nonSDK_graph_nodes','modern_modules','SDK_hash_API_calls']}))
