"""Freeze the one fixed swap67 common-quartic separation and its audit."""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
AUDIT=ROOT/'research-goal-20261017-swap67-audit'
OUT=HERE/'swap67-quartic-files.json'

def record(p):return {'path':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
def main():
    assert not OUT.exists()
    doc=json.loads((HERE/'swap67-quartic-static.json').read_bytes());audit=json.loads((AUDIT/'independent-replay.json').read_bytes())
    assert audit['passed'] and audit['all_inputs_unchanged']
    assert doc['source_sha256_start']==doc['source_sha256_end'] and audit['source_sha256_start']==audit['source_sha256_end']
    assert doc['exact714_excluded_by_this_necessary_row'] and F(doc['expected_upper_difference_at_exact714'])<F(-17,10000)
    files=[p for p in HERE.iterdir() if p.is_file() and p!=OUT]+[AUDIT/'independent_replay.py',AUDIT/'independent-replay.json']
    names={p.relative_to(ROOT).as_posix() for p in files};deps={}
    for pins in [doc['source_sha256_start'],audit['source_sha256_start']]:
        for name,h in pins.items():
            p=ROOT/name;r=record(p);assert r['sha256']==h
            if name not in names:deps[name]=r
    formalpath=ROOT/'research-goal-20261016/window_global_competitor_formal_index.json'
    formal=json.loads(formalpath.read_bytes());assert formal['receipt_record']['passed'] and formal['receipt_record']['exit_code']==0
    assert formal['source']['sha256']==record(ROOT/formal['source']['path'])['sha256']
    for p in [formalpath,ROOT/formal['source']['path'],ROOT/formal['log']['path']]:deps[p.relative_to(ROOT).as_posix()]=record(p)
    out={'scope':__doc__,'package_files':[record(p) for p in sorted(files,key=lambda p:p.relative_to(ROOT).as_posix())],
        'dependency_files':[deps[k] for k in sorted(deps)],'single_fixed_swap_zero_based':[6,7],
        'changed_nonzero_edges':8,'exactly_cancelled_nonzero_edges':33,'new_necessary_rows':1,
        'old_exact714_point_separated':True,'expected_upper_difference_exact':doc['expected_upper_difference_at_exact714'],
        'exact_short_threshold':'-17/10000','independent_stdlib_replay_passed':True,
        'generic_actual_Fw24_Lean_bridge_passed':True,'concrete_numerical_envelope_newly_Lean_proved':False,
        'solver_calls':0,'Lean_invocations_by_this_package':0,'cell_exclusion_proven':False,'new_zero_proportion_proven':False}
    OUT.write_text(json.dumps(out,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({'manifest_sha256':record(OUT)['sha256'],'files':len(files),'dependencies':len(deps),'bytes':sum(p.stat().st_size for p in files)}))
if __name__=='__main__':main()
