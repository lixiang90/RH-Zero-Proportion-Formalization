"""Read-only Zeta source/trace shape audit. No SDKHash instantiation/API/main."""
import hashlib
import json
from pathlib import Path
from collections import Counter
from cache_binding import header

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
PACKAGE=ROOT/'.lake/packages/Zeta23'

def pin(p):
    raw=p.read_bytes()
    return dict(path=str(p),bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest())
def flat(x):
    if isinstance(x,str):yield x
    elif isinstance(x,list):
        for v in x:yield from flat(v)
    elif isinstance(x,dict):
        for v in x.values():yield from flat(v)

rows=[]
for p in sorted((PACKAGE/'Zeta23').rglob('*.lean')):
    raw=p.read_bytes();is_module,deps,prelude=header(raw)
    name=p.relative_to(PACKAGE).with_suffix('').as_posix().replace('/','.')
    base=PACKAGE/'.lake/build/lib/lean'/p.relative_to(PACKAGE).with_suffix('')
    trace_path=base.with_suffix('.trace')
    row=dict(module=name,source=pin(p),header_is_module=is_module,imports=deps,prelude=prelude)
    if trace_path.is_file():
        t=json.loads(trace_path.read_text(encoding='utf-8'));o=t['outputs']
        declared=[s for s in flat(o) if s.endswith(('.olean','.olean.server','.olean.private','.ir','.ir.sig'))]
        data=[]
        for entry in declared:
            lake,suffix=entry.split('.',1);path=base.with_suffix('.'+suffix);sidecar=Path(str(path)+'.hash')
            data.append(dict(suffix=suffix,path=str(path),exists=path.is_file(),
              bytes=path.stat().st_size if path.is_file() else None,
              hash_sidecar_exists=sidecar.is_file(),
              hash_sidecar_matches_trace=sidecar.read_text(encoding='utf-8').strip()==lake if sidecar.is_file() else False))
        row.update(trace=pin(trace_path),trace_is_module=o.get('m',False),
          schema=t.get('schemaVersion'),input_count=len(t.get('inputs',[])),inputs=t.get('inputs'),outputs=o,data=data)
    else:row['trace_missing']=True
    rows.append(row)
summary=dict(source_count=len(rows),modern_modules=[r['module'] for r in rows if r['header_is_module']],
  module_flag_mismatches=[r['module'] for r in rows if 'trace_is_module' in r and r['trace_is_module']!=r['header_is_module']],
  input_counts=dict(Counter(str(r.get('input_count')) for r in rows)),
  schemas=dict(Counter(str(r.get('schema')) for r in rows)),
  missing_traces=[r['module'] for r in rows if r.get('trace_missing')],
  data_shape_failures=[dict(module=r['module'],data=d) for r in rows for d in r.get('data',[])
     if not (d['exists'] and d['hash_sidecar_exists'] and d['hash_sidecar_matches_trace'])])
result=dict(scope='ALL Zeta23/ source and existing trace shapes/output-presence/sidecar-literal consistency only; not an SDK byte hash/proof check',
            SDK_hash_API_calls=0,compiler_runs=0,proof_runs=0,summary=summary,modules=rows)
with (HERE/'all-zeta-shapes-final.json').open('x',encoding='utf-8',newline='\n') as f:
    json.dump(result,f,indent=2);f.write('\n')
print(json.dumps(summary))
