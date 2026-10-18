"""Byte-only freeze of completed phaseA v0; never compile or alter old files."""
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
HERE=Path(__file__).resolve().parent
JOB=ROOT/'tmp/current-s1r-M-20261018/v0'


def item(p):
    b=p.read_bytes()
    return {'path':p.relative_to(ROOT).as_posix(),'bytes':len(b),
            'sha256':hashlib.sha256(b).hexdigest()}


def main():
    terminal=json.loads((JOB/'terminal.json').read_text(encoding='utf-8'))
    assert terminal['passed'] is False
    a=json.loads((JOB/'CurrentPrefix.receipt.json').read_text(encoding='utf-8'))
    b=json.loads((JOB/'QuantizedComponent.receipt.json').read_text(encoding='utf-8'))
    assert a['ordinary_compile_passed'] and not b['ordinary_compile_passed']
    assert not (JOB/'Sparse78.receipt.json').exists()
    originals=[]
    for name in ['CurrentPrefix','QuantizedComponent','Sparse78']:
        source=ROOT/'StructuralS1RM20261018'/(name+'.lean')
        copy=JOB/(name+'.lean')
        assert source.read_bytes()==copy.read_bytes()
        originals.append({'current_source':item(source),'immutable_execution_snapshot':item(copy)})
    records=sorted(p for p in JOB.iterdir() if p.suffix in ['.log','.json'])
    deps=[HERE/'compiler-prepared.json',HERE/'phaseA-prepared.json',
          ROOT/'research-goal-20261016/gates/stageM-actual-Lean-phaseA-20261018.json']
    olean=ROOT/'tmp/current-s1r-M-20261018/lib/StructuralS1RM20261018/CurrentPrefix.olean'
    r={'schema':'M-phaseA-v0-ordinary-execution-evidence-v1',
       'actual_exec_session':7986,'exec_terminal_exit':1,
       'files':[item(p) for p in records]+[item(Path(__file__))],
       'dependencies':[item(p) for p in deps],
       'source_identities':originals,
       'olean_metadata_only_not_staging_binary':item(olean),
       'results':{'CurrentPrefix':a,'QuantizedComponent':b,'Sparse78':'not run after predecessor failure'},
       'observed_max_RSS_KiB':{'CurrentPrefix':9037076,'QuantizedComponent':6836528},
       'scope':'one ordinary compiled prefix; failed QuantizedComponent is unverified; no actual local pair, global cover, website runtime, or Nano claim',
       'source_or_v0_log_modified':False,'automatic_repairs_or_retries':0}
    out=HERE/'phaseA-v0-execution-files.json'
    with out.open('x',encoding='utf-8',newline='\n') as f:
        json.dump(r,f,ensure_ascii=False,indent=2);f.write('\n')
    print(json.dumps(item(out)))


if __name__=='__main__':main()
