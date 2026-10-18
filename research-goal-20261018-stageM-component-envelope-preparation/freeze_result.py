"""Byte-only closure of the one M attempt, whether certified or inconclusive."""
from pathlib import Path
from hashlib import sha256
import json
import os

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
def pin(p):return sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text(encoding='utf-8'))
def row(p):return {'path':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':pin(p)}
def main():
    assert not (HERE/'files.json').exists();terminal=load(HERE/'terminal.json')
    assert terminal['child_launches']==1 and terminal['automatic_retry'] is False
    prepared=load(HERE/'prepared-files.json')
    for item in prepared['files']:
        p=ROOT/item['path'];assert pin(p)==item['sha256'] and p.stat().st_size==item['bytes']
    refs={item['path']:item['sha256'] for item in prepared['read_only_dependencies']}
    if (HERE/'started.json').exists():refs.update(load(HERE/'started.json')['inputs_sha256'])
    mismatches={name:{'expected':expected,'current':pin(ROOT/name)} for name,expected in refs.items() if pin(ROOT/name)!=expected}
    result=load(HERE/'result.json') if (HERE/'result.json').exists() else None
    files=sorted(p for p in HERE.iterdir() if p.is_file() and p.name!='files.json')
    manifest={'schema':'M-one-component-envelope-producer-evidence-v1','files':[row(p) for p in files],
        'read_only_dependencies':[row(ROOT/name) for name in sorted(refs) if not (ROOT/name).is_relative_to(HERE)],
        'input_identity_mismatches':mismatches,'terminal_exit_code':terminal['exit_code'],'limit_stop':terminal['limit_stop'],
        'outcome':result['outcome'] if result else 'failed_or_interrupted','producer_exact_certificate_present':bool(result and result['passed']),
        'independent_review_pending':True,'Lean_proven':False,'new_global_floor_or_kappa_proven':False,'website_submission_ready':False}
    with (HERE/'files.json').open('x',encoding='utf-8',newline='\n') as f:
        json.dump(manifest,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
    print(json.dumps({'manifest':row(HERE/'files.json'),'outcome':manifest['outcome']}))

if __name__=='__main__':main()
