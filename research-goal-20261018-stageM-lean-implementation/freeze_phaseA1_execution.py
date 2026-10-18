"""Freeze the terminated import-path failure, not a theorem-level check."""
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
HERE=Path(__file__).resolve().parent
JOB=ROOT/'tmp/current-s1r-M-20261018/phaseA1'


def item(p):
    b=p.read_bytes();return {'path':p.relative_to(ROOT).as_posix(),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}


def main():
    terminal=json.loads((JOB/'terminal.json').read_text(encoding='utf-8'))
    assert terminal['passed'] is False
    receipt=json.loads((JOB/'QuantizedComponent.receipt.json').read_text(encoding='utf-8'))
    assert receipt['exit_code']==1 and receipt['source_unchanged']
    log=(JOB/'QuantizedComponent.log').read_bytes()
    assert b'CurrentPrefix.olean' in log and b'does not exist' in log
    assert not (JOB/'Sparse78.receipt.json').exists()
    prefix=ROOT/'tmp/current-s1r-M-20261018/lib/StructuralS1RM20261018/CurrentPrefix.olean'
    assert item(prefix)['sha256']=='8a67fa6cd8dbf293b802471bf39fb2cc160130a263191ce1c854d16fc35db692'
    deps=[HERE/'phaseA1-prepared.json',HERE/'phaseA-v0-execution-files.json',
          ROOT/'research-goal-20261016/gates/stageM-actual-Lean-phaseA1-20261018.json',
          ROOT/'StructuralS1RM20261018/PhaseA1/QuantizedComponent.lean']
    r={'schema':'M-phaseA1-import-failure-execution-v1','actual_exec_session':48921,
       'exec_terminal_exit':1,'files':[item(p) for p in sorted(JOB.iterdir()) if p.suffix in ['.json','.log']]+[item(Path(__file__))],
       'dependencies':[item(p) for p in deps],
       'prefix_metadata_only':item(prefix),'receipt':receipt,
       'failure_stage':'CurrentPrefix import resolution before checking the repaired theorem',
       'theorem_failure_claim':False,'new_Lean_proof_PASS':False,
       'Sparse78_run':False,'automatic_retries':0,
       'diagnosed_minimal_fix':'Copy the already hash-verified CurrentPrefix.olean into the first isolated library under its same module path; no prefix recompilation.'}
    out=HERE/'phaseA1-execution-files.json'
    with out.open('x',encoding='utf-8',newline='\n') as f:json.dump(r,f,indent=2);f.write('\n')
    print(json.dumps(item(out)))


if __name__=='__main__':main()
