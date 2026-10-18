"""Byte-only freeze of the terminated first O bridge compiler run."""
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
HERE=Path(__file__).resolve().parent
JOB=ROOT/'tmp/current-s1r-O-20261018/v0'


def item(p):
    b=p.read_bytes();return {'path':p.relative_to(ROOT).as_posix(),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}


def main():
    assert json.loads((JOB/'terminal.json').read_text())['passed'] is False
    cell=json.loads((JOB/'CellAQuantitative.receipt.json').read_text())
    strong=json.loads((JOB/'StrongQuantized.receipt.json').read_text())
    assert cell['ordinary_compile_passed'] and cell['axiom_audit_passed']
    assert not strong['ordinary_compile_passed'] and strong['exit_code']==1
    for name in ['CellAQuantitative','StrongQuantized']:
        assert (ROOT/'StructuralS1RO20261018'/(name+'.lean')).read_bytes()==(JOB/(name+'.lean')).read_bytes()
    sources=[ROOT/'StructuralS1RO20261018'/(x+'.lean') for x in ['CellAQuantitative','StrongQuantized']]
    olean=ROOT/'tmp/current-s1r-O-20261018/lib/StructuralS1RO20261018/CellAQuantitative.olean'
    r={'schema':'O-actual-thin-bridges-v0-execution-v1','actual_exec_session':63417,'exec_terminal_exit':1,
        'files':[item(p) for p in sorted(JOB.iterdir()) if p.suffix in ['.json','.log']]+[item(Path(__file__))],
        'dependencies':[item(p) for p in sources+[HERE/'prepared-files.json',
          ROOT/'research-goal-20261016/gates/stageO-actual-thin-bridges-20261018.json']],
        'compiled_olean_metadata_only':item(olean),'passed_module':cell,'failed_unverified_module':strong,
        'max_RSS_KiB':{'CellAQuantitative':6830028,'StrongQuantized':6846924},
        'prefix_or_QuantizedComponent_recompiled':False,'automatic_repairs_or_retries':0,
        'finite_data_or_Sparse_or_B2_runs':0,'fixed_pair_actual_floor_proved':False,
        'global_floor_proved':False,'Nano_replayed':False}
    out=HERE/'execution-v0-files.json'
    with out.open('x',encoding='utf-8',newline='\n') as f:json.dump(r,f,indent=2);f.write('\n')
    print(json.dumps(item(out)))


if __name__=='__main__':main()
