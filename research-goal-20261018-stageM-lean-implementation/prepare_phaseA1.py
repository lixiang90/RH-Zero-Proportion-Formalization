"""Create a new source path and pin the single same-theorem tactic repair."""
import ast
import difflib
import hashlib
import json
from pathlib import Path
import sys

ROOT=Path(__file__).resolve().parents[1]
HERE=Path(__file__).resolve().parent


def item(p):
    b=p.read_bytes()
    return {'path':p.relative_to(ROOT).as_posix(),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}


def write(p,text):
    with p.open('x',encoding='utf-8',newline='\n') as f:f.write(text)


def main():
    original=ROOT/'StructuralS1RM20261018/QuantizedComponent.lean'
    assert item(original)['sha256']=='eded1014724685d8fd8d8e1d2b67c1b0d40b9c53ebdf21feac5ec158e1443c64'
    text=original.read_text(encoding='utf-8')
    before='''  convert h using 1 <;>
    simp only [ell, slope, intercept, dLo, dHi, kappa] <;> push_cast <;> ring'''
    after='''  have he : (slope f p : ℝ) * (20 * 32768 * s) + (intercept f L0 p : ℝ) =
      (kappa : ℝ) * ell f L0 p s := by
    unfold slope intercept dLo dHi ell kappa
    push_cast
    ring
  rw [he]
  exact h'''
    assert text.count(before)==1
    repaired=text.replace(before,after)
    newdir=ROOT/'StructuralS1RM20261018/PhaseA1';newdir.mkdir(exist_ok=False)
    new=newdir/'QuantizedComponent.lean';write(new,repaired)
    diff=''.join(difflib.unified_diff(text.splitlines(True),repaired.splitlines(True),
        fromfile=original.relative_to(ROOT).as_posix(),tofile=new.relative_to(ROOT).as_posix()))
    write(HERE/'phaseA1-source.diff',diff)
    for n in ['compile_phaseA1.py','prepare_phaseA1.py']:
        ast.parse((HERE/n).read_text(encoding='utf-8'),filename=n)
    olean=ROOT/'tmp/current-s1r-M-20261018/lib/StructuralS1RM20261018/CurrentPrefix.olean'
    assert item(olean)['sha256']=='8a67fa6cd8dbf293b802471bf39fb2cc160130a263191ce1c854d16fc35db692'
    py=Path(sys.executable)
    dependencies=[original,ROOT/'StructuralS1RM20261018/CurrentPrefix.lean',
        ROOT/'StructuralS1RM20261018/Sparse78.lean',olean,HERE/'compile_phaseA.py',
        HERE/'compiler-runtime-observation.json',HERE/'phaseA-v0-execution-files.json',
        ROOT/'tmp/setup-20261015/runtime.json']
    r={'schema':'M-phaseA1-single-versioned-tactic-repair-prepared-v1',
        'files':[item(p) for p in [new,HERE/'compile_phaseA1.py',HERE/'prepare_phaseA1.py',HERE/'phaseA1-source.diff']],
        'dependencies':[item(p) for p in dependencies],
        'Python_executable':{'path':str(py),'sha256':hashlib.sha256(py.read_bytes()).hexdigest()},
        'reused_prefix_olean_sha256':item(olean)['sha256'],
        'reused_prefix_source_sha256':'ea8e01118d19158ba8313504910645ad467ea86eb2ea65a897859ae98101df21',
        'targets':['StructuralS1RM20261018/PhaseA1/QuantizedComponent','StructuralS1RM20261018/Sparse78'],
        'repeat_CurrentPrefix':False,'automatic_repairs_or_retries':0,
        'same_theorem_statements':True,'original_v0_unchanged':item(original)['sha256']=='eded1014724685d8fd8d8e1d2b67c1b0d40b9c53ebdf21feac5ec158e1443c64',
        'AST_only':True,'Lean_runs':0,'new_immutable_gate_required':True,
        'command_template':[str(py),'research-goal-20261018-stageM-lean-implementation/compile_phaseA1.py','--gate','ROOT_GATE_PATH','--gate-sha256','ROOT_GATE_SHA'],
        'scope':'versioned QuantizedComponent routine tactic repair plus first Sparse78 attempt; no other compiler target'}
    out=HERE/'phaseA1-prepared.json';write(out,json.dumps(r,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps(item(out)))


if __name__=='__main__':main()
