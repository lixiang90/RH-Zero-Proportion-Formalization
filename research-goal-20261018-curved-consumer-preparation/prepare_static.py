"""AST this metadata script and hash existing sources only; no Lean execution."""
import ast
from hashlib import sha256
import json
import os
from pathlib import Path
import re
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
def row(p):return {'path':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':sha256(p.read_bytes()).hexdigest()}
def main():
    assert not (HERE/'prepared-files.json').exists()
    ast.parse(Path(__file__).read_text(encoding='utf8'))
    sources=[ROOT/'StructuralS1RCurvedConsumer20261018'/n for n in ['SparseDual.lean','QuadraticNetwork.lean']]
    roots=[]
    for p in sources:
        text=p.read_text(encoding='utf8')
        assert not re.search(r'\b(sorry|admit|native_decide|unsafe)\b',text)
        assert not re.search(r'(?m)^\s*(axiom|constant)\s+',text)
        assert text.startswith('import Mathlib\n') and 'import Structural' not in text
        found=re.findall(r'(?m)^#print axioms (StructuralS1RCurvedConsumer20261018\.[A-Za-z0-9_.]+)$',text)
        assert len(found)==3;roots.extend(found)
    deps=[
        'AGENTS.md','lean-toolchain','lakefile.toml',
        'StructuralS1RM20261018/Sparse78.lean',
        'tmp/current-s1r-M-20261018/phaseA1b/Sparse78.lean',
        'tmp/current-s1r-M-20261018/phaseA1b/Sparse78.log',
        'tmp/setup-20261015/packages/mathlib/Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean',
        'tmp/setup-20261015/packages/mathlib/Mathlib/Algebra/BigOperators/Ring/Finset.lean',
        'tmp/setup-20261015/packages/mathlib/Mathlib/Data/Int/Cast/Basic.lean',
        'research-goal-20261018-stageO-independent/audit-files.json',
        'research-goal-20261018-stageO-independent/independent-review.json',
        'research-goal-20261018-stageO-fixed-curvature-preparation/files.json',
        'research-goal-20261018-stageO-fixed-curvature-preparation/curvature-packet.json',
        'research-goal-20261018-stageN2-curvature-interface-static/files.json',
        'research-goal-20261018-record-source-audit/snapshot/Solution.lean']
    allfiles=sources+[HERE/'NOTE.zh.md',Path(__file__)]
    out={'schema':'generic-curved-finite-consumer-static-source-prepared-v1',
        'files':[row(p) for p in allfiles],'read_only_dependencies':[row(ROOT/p) for p in deps],
        'fully_qualified_axiom_print_roots':roots,'compile_runs':0,'Lean_execution_runs':0,
        'new_case_data_generated':False,'new_FS_curvature_matrix_LP_evaluations':0,
        'old_failure_sources_unchanged':True,'proof_or_axioms_success_claimed':False,
        'static_only':True,'website_source_runtime_budget':'unknown'}
    with (HERE/'prepared-files.json').open('x',encoding='utf8') as f:json.dump(out,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
    print(json.dumps({'prepared_manifest':row(HERE/'prepared-files.json'),
        'source_bytes':sum(p.stat().st_size for p in sources),'static_only':True,'Lean_runs':0}))
if __name__=='__main__':main()
