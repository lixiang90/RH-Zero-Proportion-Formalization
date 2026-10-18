"""Byte-hash freeze only after one gated J child; no certificate recomputation."""
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
    assert not (HERE/'files.json').exists()
    terminal=load(HERE/'terminal.json');assert terminal['child_launches']==1 and terminal['automatic_retry'] is False
    prepared=load(HERE/'prepared-files.json')
    for item in prepared['files']+prepared['read_only_dependencies']:
        p=ROOT/item['path'];assert pin(p)==item['sha256'] and p.stat().st_size==item['bytes']
    refs={item['path']:item['sha256'] for item in prepared['read_only_dependencies']}
    if (HERE/'started.json').exists():refs.update(load(HERE/'started.json')['inputs_sha256'])
    for name,expected in refs.items():assert pin(ROOT/name)==expected
    paths=sorted(p for p in HERE.iterdir() if p.is_file() and p.name!='files.json')
    result=load(HERE/'result.json') if (HERE/'result.json').exists() else None
    manifest={'schema':'J-one-fixed-basis-producer-evidence-v1','files':[row(p) for p in paths],
        'read_only_dependencies':[row(ROOT/name) for name in sorted(refs) if not (ROOT/name).is_relative_to(HERE)],
        'terminal_exit_code':terminal['exit_code'],'limit_stop':terminal['limit_stop'],
        'producer_complete':bool(result and result['passed']),
        'complete_H_remaining_classified':bool(result and result['complete_H_remaining_classified']),
        'independent_arithmetic_replay_pending':True,'Lean_proven':False,'new_global_floor_proven':False,
        'website_submission_ready':False,'scope':'One fixed-basis candidate family; hashes only, not an independent arithmetic audit.'}
    with (HERE/'files.json').open('x',encoding='utf-8',newline='\n') as f:
        json.dump(manifest,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
    print(json.dumps({'manifest':row(HERE/'files.json'),'producer_complete':manifest['producer_complete']}))

if __name__=='__main__':main()
