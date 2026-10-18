"""Freeze uncompiled concrete source checkpoint by byte/AST inspection only."""
import ast
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
HERE=Path(__file__).resolve().parent


def entry(p):
    b=p.read_bytes()
    return {'path':p.relative_to(ROOT).as_posix(),'bytes':len(b),
            'sha256':hashlib.sha256(b).hexdigest()}


def main():
    modules=['LocalData','LocalGeometry','LocalComponents','LocalPair']
    generated=[ROOT/'StructuralS1RM20261018'/f'{m}.lean' for m in modules]
    scripts=[HERE/n for n in ['generate_local_data.py','generate_local_pair.py','prepare_local_sources.py']]
    for p in scripts:
        ast.parse(p.read_text(encoding='utf-8'),filename=str(p))
    inputs=ROOT/'research-goal-20261018-stageM-component-envelope-preparation'
    dependencies=[inputs/n for n in ['model.json','certificate.json','original-components.json','files.json']]
    dependencies += [ROOT/'research-goal-20261018-stageM-independent/audit-files.json',
                     HERE/'phaseA-prepared.json',HERE/'local-data-prepared.json',HERE/'local-pair-prepared.json']
    source_bytes=sum(p.stat().st_size for p in generated)
    r={'schema':'M-concrete-local-actual-source-checkpoint-v1',
       'files':[entry(p) for p in generated+scripts],
       'dependencies':[entry(p) for p in dependencies],
       'phaseB_Lean_runs':0,'source_AST_only':True,
       'phaseA_compilation':'separately authorized and currently tracked by original handle',
       'actual_local_theorem':'StructuralS1RM20261018.LocalPair.actual_pair_lower',
       'premises':['literal original cell0 id','literal original cell604 reversed',
                   'all nine physical gaps >=17/20','both original true Ordered inequalities'],
       'conclusion':'current s1R G(left)+G(suffix)>=2*893766123055294719/1e20',
       'global_leaf_reachability_proved':False,'global_product_cover_proved':False,
       'new_kappa_proved':False,'Nano_replayed':False,
       'phaseB_source_bytes':source_bytes,
       'full_accepted_baseline_bytes':1818411,
       'raw_baseline_plus_phaseB_and_generic_bytes':1818411+source_bytes+3065+3772,
       'size_scope':'Engineering sum only, not a standalone submission or runtime guarantee; source imports/closures/deduplication and global product proof are not composed.',
       'frozen_source_policy':'No generator overwrites any existing source (exclusive create).',
       'next_gate':'Separate root review and ordinary Lean gate required for all four local modules.'}
    out=HERE/'local-concrete-prepared.json'
    with out.open('x',encoding='utf-8',newline='\n') as f:
        json.dump(r,f,ensure_ascii=False,indent=2);f.write('\n')
    print(json.dumps(entry(out)))


if __name__=='__main__':
    main()
