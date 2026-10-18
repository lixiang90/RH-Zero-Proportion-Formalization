"""Freeze real A1b results; keep successful and failed module scopes separate."""
import hashlib
import json
from pathlib import Path
import re

ROOT=Path(__file__).resolve().parents[1]
HERE=Path(__file__).resolve().parent
JOB=ROOT/'tmp/current-s1r-M-20261018/phaseA1b'


def item(p):
    b=p.read_bytes();return {'path':p.relative_to(ROOT).as_posix(),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}


def main():
    assert json.loads((JOB/'terminal.json').read_text())['passed'] is False
    q=json.loads((JOB/'QuantizedComponent.receipt.json').read_text())
    s=json.loads((JOB/'Sparse78.receipt.json').read_text())
    assert q['ordinary_compile_passed'] and not s['ordinary_compile_passed']
    raw=(JOB/'QuantizedComponent.log').read_bytes().decode('utf-8',errors='replace')
    roots=[]
    for name,axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",raw,re.S):
        aa=[x.strip() for x in axioms.split(',')]
        assert set(aa)<= {'propext','Classical.choice','Quot.sound'}
        roots.append({'name':name,'axioms':aa})
    assert len(roots)==3
    sources=[ROOT/'StructuralS1RM20261018/PhaseA1/QuantizedComponent.lean',
             ROOT/'StructuralS1RM20261018/Sparse78.lean']
    for p in sources:assert p.read_bytes()==(JOB/p.name).read_bytes()
    oleans=[JOB/'lib/StructuralS1RM20261018/CurrentPrefix.olean',
            JOB/'lib/StructuralS1RM20261018/PhaseA1/QuantizedComponent.olean']
    assert item(oleans[0])['sha256']=='8a67fa6cd8dbf293b802471bf39fb2cc160130a263191ce1c854d16fc35db692'
    r={'schema':'M-phaseA1b-ordinary-compile-and-axioms-evidence-v1',
        'actual_exec_session':80357,'exec_terminal_exit':1,
        'files':[item(p) for p in sorted(JOB.iterdir()) if p.suffix in ['.json','.log']]+[item(Path(__file__))],
        'dependencies':[item(p) for p in [HERE/'phaseA1b-prepared.json',HERE/'phaseA1-execution-files.json',
            ROOT/'research-goal-20261016/gates/stageM-actual-Lean-phaseA1b-runtime-20261018.json']+sources],
        'olean_metadata_only':[item(p) for p in oleans],
        'ordinary_compiled_proof_modules':[q['module']], 'printed_axiom_roots':roots,
        'failed_unverified_module':s,'successful_module_receipt':q,
        'max_RSS_KiB':{'QuantizedComponent':6839876,'Sparse78':6751388},
        'CurrentPrefix_recompiled':False,'automatic_retries_or_repairs':0,
        'B2_compiled':False,'actual_pair_theorem_proved':False,'global_cover_proved':False,
        'Nano_replayed':False}
    out=HERE/'phaseA1b-execution-files.json'
    with out.open('x',encoding='utf-8',newline='\n') as f:json.dump(r,f,indent=2);f.write('\n')
    print(json.dumps(item(out)))


if __name__=='__main__':main()
