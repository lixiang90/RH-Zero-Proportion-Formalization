"""Prepare a versioned typed-derivative/API repair; never invoke Lean."""
import ast
import difflib
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
HERE=Path(__file__).resolve().parent


def item(p):
    b=p.read_bytes();return {'path':p.relative_to(ROOT).as_posix(),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}


def write(p,text):
    with p.open('x',encoding='utf-8',newline='\n') as f:f.write(text)


def main():
    prep=json.loads((HERE/'prepared-files.json').read_text(encoding='utf-8'))
    original=ROOT/'StructuralS1RO20261018/StrongQuantized.lean'
    assert item(original)['sha256']=='8df384c850d119b5a9328d730506f3117df950d8bb17deea2d40d28a39812ab9'
    old=original.read_text(encoding='utf-8')
    before='''    have hquad := (((hasDerivAt_id x).sub_const q).pow 2).const_mul (m/2)
    convert hw.sub hquad using 1 <;> ring'''
    after='''    have hpow := ((hasDerivAt_id x).sub_const q).pow 2
    have hquad := HasDerivAt.const_mul (m/2) hpow
    change HasDerivAt (fun y : ℝ => (m/2)*(y-q)^2)
      ((m/2)*((2 : ℝ)*(x-q)^(2-1)*1)) x at hquad
    have hcoef : (m/2)*((2 : ℝ)*(x-q)^(2-1)*1) = m*(x-q) := by ring
    rw [hcoef] at hquad
    exact hw.sub hquad'''
    assert old.count(before)==1;new=old.replace(before,after)
    before='''    have hlin := ((hasDerivAt_id x).sub_const q).const_mul m
    convert hw.sub hlin using 1 <;> ring'''
    after='''    have hlin := HasDerivAt.const_mul m ((hasDerivAt_id x).sub_const q)
    change HasDerivAt (fun y : ℝ => m*(y-q)) (m*1) x at hlin
    rw [mul_one] at hlin
    exact hw.sub hlin'''
    assert new.count(before)==1;new=new.replace(before,after)
    new=new.replace('(slope f p : ℝ)','(StructuralS1RM20261018.QuantizedComponent.slope f p : ℝ)')
    new=new.replace('(intercept f L0 p : ℝ)','(StructuralS1RM20261018.QuantizedComponent.intercept f L0 p : ℝ)')
    new=new.replace('unfold slope intercept dLo dHi ell kappa',
        'unfold StructuralS1RM20261018.QuantizedComponent.slope\n      StructuralS1RM20261018.QuantizedComponent.intercept dLo dHi ell kappa')
    folder=ROOT/'StructuralS1RO20261018/PhaseO1';folder.mkdir(exist_ok=False)
    source=folder/'StrongQuantized.lean';write(source,new)
    write(HERE/'phaseO1-source.diff',''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),
        fromfile=original.relative_to(ROOT).as_posix(),tofile=source.relative_to(ROOT).as_posix())))
    oldrunner=(HERE/'compile_bridges.py').read_text(encoding='utf-8')
    runner=oldrunner.replace("'stageO-current-s1R-thin-bridges'","'stageO-current-s1R-strong-bridge-v1'")
    runner=runner.replace("'prepared-files.json'","'phaseO1-prepared.json'")
    runner=runner.replace("'tmp/current-s1r-O-20261018/v0'","'tmp/current-s1r-O-20261018/phaseO1'")
    runner=runner.replace("lib=ROOT/'tmp/current-s1r-O-20261018/lib'","lib=job/'lib'")
    runner=runner.replace("targets=['StructuralS1RO20261018/CellAQuantitative','StructuralS1RO20261018/StrongQuantized']",
        "targets=['StructuralS1RO20261018/PhaseO1/StrongQuantized']")
    rp=HERE/'compile_phaseO1.py';write(rp,runner);ast.parse(runner,filename=str(rp))
    ast.parse(Path(__file__).read_text(encoding='utf-8'),filename=__file__)
    write(HERE/'phaseO1-runner.diff',''.join(difflib.unified_diff(oldrunner.splitlines(True),runner.splitlines(True),
        fromfile='compile_bridges.py',tofile='compile_phaseO1.py')))
    reused=list(prep['reused_oleans'])
    cell=ROOT/'tmp/current-s1r-O-20261018/lib/StructuralS1RO20261018/CellAQuantitative.olean'
    ci=item(cell);assert ci['sha256']=='f063a1ce3926420a27d2fc953cde516ff8f5565b33356dfe77af77f56f001a10'
    reused.append(dict(ci,relative_module_path='StructuralS1RO20261018/CellAQuantitative.olean'))
    deps=prep['dependencies']+[item(p) for p in [HERE/'prepared-files.json',HERE/'execution-v0-files.json',
        original,ROOT/'StructuralS1RO20261018/CellAQuantitative.lean',cell,HERE/'compile_bridges.py']]
    result={'schema':'O-PhaseO1-same-theorem-API-repair-prepared-v1',
        'files':[item(p) for p in [source,rp,Path(__file__),HERE/'phaseO1-source.diff',HERE/'phaseO1-runner.diff']],
        'dependencies':deps,'reused_oleans':reused,'Python_executable':prep['Python_executable'],
        'external_Linux_pins':prep['external_Linux_pins'],
        'Lean_runs':0,'AST_only':True,'mathematical_statement_changes':False,
        'change':'Typed derivative helpers and scalar coefficient equality; fully qualify quantized slope/intercept. No new analytic premise.',
        'prefix_or_Quantized_or_CellA_recompile':False,'automatic_repairs_or_retries':0,
        'new_immutable_gate_required':True,'fixed_data_or_Sparse_or_B2_authorized':False,
        'command_template':[prep['Python_executable']['path'],
            'research-goal-20261018-stageO-actual-bridges-preparation/compile_phaseO1.py',
            '--gate','ROOT_GATE_PATH','--gate-sha256','ROOT_GATE_SHA']}
    p=HERE/'phaseO1-prepared.json';write(p,json.dumps(result,ensure_ascii=False,indent=2)+'\n')
    assert item(original)['sha256']=='8df384c850d119b5a9328d730506f3117df950d8bb17deea2d40d28a39812ab9'
    print(json.dumps(item(p)))


if __name__=='__main__':main()
