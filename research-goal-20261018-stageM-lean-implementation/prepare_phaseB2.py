"""Repoint the prepared local proof to the versioned quantized component."""
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
HERE=Path(__file__).resolve().parent


def item(p):
    b=p.read_bytes()
    return {'path':p.relative_to(ROOT).as_posix(),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}


def main():
    prior=HERE/'phaseB1-prepared.json'
    assert item(prior)['sha256']=='8a48c0beea62afd99321b4c21a119ffdea100db3f13d9813e3e884fe6cd61ad4'
    old=json.loads(prior.read_text(encoding='utf-8'))
    dst=ROOT/'StructuralS1RM20261018/PhaseB2';dst.mkdir(exist_ok=False)
    rows=[]
    for name in ['LocalData','LocalGeometry','LocalComponents','LocalPair']:
        p=ROOT/'StructuralS1RM20261018/PhaseB1'/(name+'.lean')
        bound=next(x for x in old['files'] if x['path']==p.relative_to(ROOT).as_posix())
        assert item(p)['sha256']==bound['sha256']
        text=p.read_text(encoding='utf-8')
        text=text.replace('import StructuralS1RM20261018.PhaseB1.','import StructuralS1RM20261018.PhaseB2.')
        text=text.replace('import StructuralS1RM20261018.QuantizedComponent\n',
                          'import StructuralS1RM20261018.PhaseA1.QuantizedComponent\n')
        q=dst/(name+'.lean')
        with q.open('x',encoding='utf-8',newline='\n') as f:f.write(text)
        rows.append(item(q))
    result={'schema':'M-local-phaseB2-import-only-prepared-v1','files':rows+[item(Path(__file__))],
        'dependencies':[item(prior),item(HERE/'phaseA1-prepared.json')],
        'change':'Imports only: PhaseB1 to PhaseB2, QuantizedComponent to PhaseA1; no mathematical statement/proof-body change.',
        'phaseA1_must_pass_before_compiling':True,'Lean_runs':0,'separate_compile_gate_required':True,
        'global_cover_proved':False,'source_bytes':sum(x['bytes'] for x in rows)}
    p=HERE/'phaseB2-prepared.json'
    with p.open('x',encoding='utf-8',newline='\n') as f:json.dump(result,f,indent=2);f.write('\n')
    print(json.dumps(item(p)))


if __name__=='__main__':main()
