"""Byte identities/AST only; no Lean, model import, curvature or matrix call."""
import ast
import hashlib
import json
from pathlib import Path
import sys

ROOT=Path(__file__).resolve().parents[1]
HERE=Path(__file__).resolve().parent


def item(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for chunk in iter(lambda:f.read(1048576),b''):h.update(chunk)
    return {'path':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':h.hexdigest()}


def main():
    sources=[ROOT/'StructuralS1RO20261018'/n for n in ['CellAQuantitative.lean','StrongQuantized.lean']]
    for p in sources:
        text=p.read_text(encoding='utf-8')
        assert not any(x in text for x in ['sorry','native_decide','import StructuralGoal20261016'])
    for n in ['compile_bridges.py','prepare.py']:ast.parse((HERE/n).read_text(encoding='utf-8'),filename=n)
    reused=[]
    for relative,expected in [
        ('StructuralS1RM20261018/CurrentPrefix.olean','8a67fa6cd8dbf293b802471bf39fb2cc160130a263191ce1c854d16fc35db692'),
        ('StructuralS1RM20261018/PhaseA1/QuantizedComponent.olean','b3b098e0b4219ce2b2e400d9117bc6431121a3ff14ae7a8e400713288abf36b9')]:
        p=ROOT/'tmp/current-s1r-M-20261018/phaseA1b/lib'/relative
        data=item(p);assert data['sha256']==expected;reused.append(dict(data,relative_module_path=relative))
    deps=[ROOT/p for p in [
        'StructuralS1RM20261018/CurrentPrefix.lean','StructuralS1RM20261018/PhaseA1/QuantizedComponent.lean',
        'research-goal-20261018-stageM-lean-implementation/phaseA-v0-execution-files.json',
        'research-goal-20261018-stageM-lean-implementation/phaseA1b-execution-files.json',
        'research-goal-20261018-stageN2-curvature-interface-static/files.json',
        'research-goal-20261018-stageO-fixed-curvature-preparation/files.json',
        'tmp/setup-20261015/runtime.json']]
    deps += [ROOT/x['path'] for x in reused]
    py=Path(sys.executable)
    result={'schema':'O-current-s1R-actual-thin-bridges-prepared-v1',
        'files':[item(p) for p in sources+[HERE/'INTERFACE.zh.md',HERE/'compile_bridges.py',Path(__file__)]],
        'dependencies':[item(p) for p in deps],'reused_oleans':reused,
        'Python_executable':{'path':str(py),'sha256':hashlib.sha256(py.read_bytes()).hexdigest()},
        'external_Linux_pins':{
          '/var/tmp/rh-zero-20261015/lean-4.33.0-rc2-linux/bin/lean':'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',
          '/var/tmp/rh-zero-20261015/record-verification/modular/lib/ChallengeDeps.olean':'a9127aa6c9a70793124b7b08c16baac0b205c4d717a44a313de812534aa01542',
          '/var/tmp/rh-zero-20261015/record-verification/modular/lib/ChallengeDeps/CandidateSpec.olean':'670b554a94297575edfeb26036162247539f2168c5f5c1ee657c65d305f3866b'},
        'Lean_runs':0,'Python_AST_only':True,'actual_finite_data_generated':False,
        'new_source_bytes':sum(p.stat().st_size for p in sources),
        'command_template':[str(py),'research-goal-20261018-stageO-actual-bridges-preparation/compile_bridges.py','--gate','ROOT_GATE_PATH','--gate-sha256','ROOT_GATE_SHA'],
        'target_order':['StructuralS1RO20261018/CellAQuantitative','StructuralS1RO20261018/StrongQuantized'],
        'compile_flags':['-j1','-M13500','--tstack=262144','-DrelaxedAutoImplicit=false','-DElab.async=false'],
        'new_isolated_lib':'tmp/current-s1r-O-20261018/lib','prefix_recompile':False,
        'automatic_repairs_or_retries':0,'immutable_future_gate_required':True,
        'fixed_pair_actual_floor_proved':False,'global_floor_or_new_kappa_proved':False}
    p=HERE/'prepared-files.json'
    with p.open('x',encoding='utf-8',newline='\n') as f:json.dump(result,f,ensure_ascii=False,indent=2);f.write('\n')
    print(json.dumps(item(p)))


if __name__=='__main__':main()
