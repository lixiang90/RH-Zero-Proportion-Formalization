"""Freeze a reviewed mathematical specification, not a model or proof."""
from pathlib import Path
import hashlib,json

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
OUT=HERE/'plan-files.json'


def main():
    assert not OUT.exists()
    names=[HERE/'PLAN.md',Path(__file__)]
    files=[]
    for p in names:
        raw=p.read_bytes()
        files.append({'path':p.relative_to(ROOT).as_posix(),'bytes':len(raw),
                      'sha256':hashlib.sha256(raw).hexdigest()})
    doc={'scope':__doc__,'files':files,
         'Taylor_formulas_statically_reviewed':True,
         'review_scope':'Orders, signs, factorials, odd-even payment and degree-six scalar/M0 limit only.',
         'new_model_constructed':False,'solver_calls':0,'Lean_invocations':0,
         'new_cell_exclusion':False,'new_zero_proportion_proven':False}
    OUT.write_text(json.dumps(doc,indent=2)+'\n',encoding='utf8')
    print(json.dumps({'manifest':OUT.relative_to(ROOT).as_posix(),
                      'sha256':hashlib.sha256(OUT.read_bytes()).hexdigest()}))


if __name__=='__main__':
    if not __debug__:
        raise RuntimeError('Assertions must remain enabled')
    main()
