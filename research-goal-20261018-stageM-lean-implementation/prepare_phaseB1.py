"""Versioned syntax/API correction, preserving all original prepared sources."""
import ast
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
HERE=Path(__file__).resolve().parent


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def record(p):
    return {'path':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':sha(p)}


def main():
    prior=HERE/'local-concrete-prepared.json'
    assert sha(prior)=='0597f34452e93003369c37a9c3e215b550182feaea777c841777bfd1fc856450'
    manifest=json.loads(prior.read_text(encoding='utf-8'))
    modules=['LocalData','LocalGeometry','LocalComponents','LocalPair']
    source=ROOT/'StructuralS1RM20261018'
    target=source/'PhaseB1'
    target.mkdir(exist_ok=False)
    before=[]; after=[]
    old='  apply of_decide_eq_true\n  exact ⟨by decide, balanced, cost⟩'
    new='  unfold check\n  exact decide_eq_true_eq.mpr ⟨by decide, balanced, cost⟩'
    for mod in modules:
        p=source/(mod+'.lean')
        bound=next(x for x in manifest['files'] if x['path']==p.relative_to(ROOT).as_posix())
        assert sha(p)==bound['sha256']
        before.append(record(p))
        text=p.read_text(encoding='utf-8')
        for name in modules:
            text=text.replace('import StructuralS1RM20261018.'+name+'\n',
                              'import StructuralS1RM20261018.PhaseB1.'+name+'\n')
        if mod=='LocalData':
            assert text.count(old)==1
            text=text.replace(old,new)
        out=target/(mod+'.lean')
        with out.open('x',encoding='utf-8',newline='\n') as f:f.write(text)
        after.append(record(out))
    assert all(sha(ROOT/x['path'])==x['sha256'] for x in before)
    ast.parse(Path(__file__).read_text(encoding='utf-8'))
    result={'schema':'M-local-phaseB1-uncompiled-API-correction-v1',
        'prior_checkpoint_sha256':sha(prior),'original_sources_unchanged':before,
        'files':after+[record(Path(__file__))],
        'change':'LocalData.checked uses decide_eq_true_eq.mpr; imports repointed to PhaseB1. Mathematical definitions and theorem statements unchanged.',
        'theorem_namespace_unchanged':'StructuralS1RM20261018.LocalPair.actual_pair_lower',
        'Lean_runs':0,'separate_compile_gate_required':True,
        'global_cover_proved':False,'phaseB1_source_bytes':sum(x['bytes'] for x in after)}
    out=HERE/'phaseB1-prepared.json'
    with out.open('x',encoding='utf-8',newline='\n') as f:
        json.dump(result,f,ensure_ascii=False,indent=2);f.write('\n')
    print(json.dumps(record(out)))


if __name__=='__main__':main()
