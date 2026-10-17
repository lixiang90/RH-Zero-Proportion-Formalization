"""Static source/monomial audit, not a degree-six model builder or solver."""
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations_with_replacement
import gzip
import hashlib
import json

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent


def row(p):
    b=p.read_bytes()
    return {'path':p.relative_to(ROOT).as_posix(),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}


def freeze(p,v):
    raw=(json.dumps(v,indent=2,allow_nan=False)+'\n').encode('utf8')
    if p.exists():
        assert p.read_bytes()==raw,'Frozen output differs; use a new path.'
    else:
        p.write_bytes(raw)


def add(p,q,scale=F(1)):
    out=p.copy()
    for m,c in q.items():
        out[m]=out.get(m,F(0))+scale*c
        if not out[m]:del out[m]
    return out


def times(p,q):
    out={}
    for m,c in p.items():
        for n,d in q.items():out=add(out,{tuple(sorted(m+n)):c*d})
    return out


def main():
    names=['research-goal-20261017-quartic/quartic-model.json.gz',
           'research-goal-20261017-quartic/quartic_static.py',
           'research-goal-20261017-quartic/quartic-files.json',
           'research-goal-20261017-quartic/quartic_positivity_erratum.txt',
           'research-goal-20261017-swap-family-quartic/swap-family-normalized.json.gz',
           'research-goal-20261017-swap-family-quartic/swap_family_normalized_static.py',
           'research-goal-20261017-swap-family-quartic/swap-family-files.json',
           'research-goal-20261017-stationary-swap/stationary-swap-static.json',
           'research-goal-20261017-stationary-swap/stationary_swap_static.py']
    inputs=[row(ROOT/n) for n in names]
    model=json.loads(gzip.decompress((ROOT/names[0]).read_bytes()))
    family=json.loads(gzip.decompress((ROOT/names[4]).read_bytes()))
    assert family['parent_model_sha256']==inputs[0]['sha256']
    assert model['target']==family['target']=='11/1250'
    old=[tuple(m) for m in model['monomials']]
    new=[m for d in range(7) for m in combinations_with_replacement(range(9),d)]
    b1,b2,b3=new[:10],new[:55],new[:220]
    assert len(old)==715 and old==new[:715] and len(new)==5005
    assert max(map(len,b1))==1 and max(map(len,b2))==2 and max(map(len,b3))==3
    assert new[715]==(0,0,0,0,0)
    assert old==[tuple(m) for m in family['monomials']]
    assert family['old_scalar_rows']==5795 and len(family['additional_linear_rows'])==8
    assert len(model['linear_rows'])==5795 and len(model['PSD_blocks'])==47
    lower=model['cell'][0][:9];margins=[n-31488 for n in lower]
    assert all(n>0 for n in margins)
    assert lower[6]-model['cell'][1][7]==117
    assert all(F(x)>0 for x in model['normalized_gap_radius'])

    def packed(raw):return {old[k]:F(c) for k,c in raw if F(c)}
    def linear(raw):
        out={():F(raw['constant'])} if F(raw['constant']) else {}
        return add(out,{old[k+1]:F(c) for k,c in raw['coefficients'] if F(c)})
    H=list(map(packed,model['KKT_cubic_polynomials']))
    E=list(map(packed,model['KKT_dynamic_error_polynomials']))
    assert all(max(map(len,p),default=0)<=3 for p in H)
    assert all(max(map(len,p),default=0)<=4 for p in E)
    signed=0;slack_uses=[]
    for i,r in enumerate(model['linear_rows']):
        if any(k==714 for k,_ in r['coefficients']):slack_uses.append({'row':i,'meta':r['meta']})
        if r['meta'][0]!='free_KKT_with_dynamic_error':continue
        _,coordinate,test,sign=r['meta']
        hp=H[coordinate] if test==0 else times(H[coordinate],{(test-1,):F(1)})
        expected=add(E[coordinate],hp,F(sign))
        stored={():F(r['bound'])} if F(r['bound']) else {}
        stored=add(stored,{old[k+1]:-F(c) for k,c in r['coefficients'] if F(c)})
        assert stored==expected
        signed+=1
    assert signed==180 and len(slack_uses)==2
    assert all(k<714 for r in family['additional_linear_rows'] for k,_ in r['coefficients'])
    slacks=list(map(packed,model['normalized_geometry_slacks']))
    L2=packed(model['old_quadratic_L2']);c=F(11,1250)
    checked=0
    for k,block in enumerate(model['PSD_blocks']):
        basis=b2 if k==0 else b1
        assert block['size']==len(basis)
        multiplier=packed(block['multiplier_polynomial'])
        if k==0:assert multiplier=={():F(1)}
        elif k==1:assert multiplier=={m:v/c for m,v in add({():c},L2,F(-1)).items()}
        else:
            axis=k-2
            assert multiplier=={m:4*v for m,v in times(slacks[2*axis],slacks[2*axis+1]).items()}
        for i,j,form in block['entries']:
            assert i>=j
            expected=times(multiplier,{tuple(sorted(basis[i]+basis[j])):F(1)})
            assert linear(form)==expected
            assert all(len(m)<=4 and m in new for m in expected)
            checked+=1
    assert checked==4070
    assert [row(ROOT/n) for n in names]==inputs
    newmom=new[715:]
    even=sum(all(m.count(r)%2==0 for r in set(m)) for m in newmom)
    assert len(newmom)==4290 and even==165
    audit={'scope':__doc__,'source_dependencies':inputs,
           'old_KKT_rows_exactly_match_E_plus_or_minus_P':signed,
           'all_nine_coordinates_free_margins_SC_units':margins,
           'old_PSD_entries_checked_against_multiplier_times_monomials':checked,
           'old_monomial_prefix_preserved':True,'new_moment_count_including_constant':5005,
           'new_nonconstant_moments':5004,'old_slack_column':714,'required_new_slack_column':5004,
           'new_meaning_of_column_714':'y0^5','old_slack_occurrences':slack_uses,
           'old_5795_plus_8_rows_referenced_intact':True,
           'new_basis_sizes':[220,55,10],
           'expected_new_blocks':73,'expected_new_lower_triangle_entries':96580,
           'new_degree5_degree6_moments':4290,'new_all_even_moments':165,
           'new_moment_box_rows':8580,'expected_scalar_rows_after_boxes':14383,
           'positive_h_lower_bound':'117/32768',
           'new_model_built_or_implementation_audited':False,'new_points':0,
           'solver_calls':0,'Lean_invocations':0,'old_exact714_extension_decided':False,
           'strict_projection_shrink_proved':False,'new_exclusion':False,'new_zero_proportion_proven':False}
    auditpath=HERE/'static-embedding-audit.json';freeze(auditpath,audit)
    mods=['WindowKKTInstance','WindowMinimizerCover','WindowGapEnergy','WindowDirectionalAffine',
          'WindowGlobalCompetitor','WindowSecondVariation','WindowMomentEnergyCertificate',
          'WindowFixedDerivative','WindowCellDerivative','WindowDerivativeTableArithmetic',
          'WindowTaylorBridge','WindowProfile']
    known={r['module']:r for r in json.loads((ROOT/'research-goal-20261016/lean_verification.json').read_bytes())['modules']}
    actual=[]
    for name in mods:
        p=ROOT/'StructuralGoal20261016'/(name+'.lean');r=known['StructuralGoal20261016.'+name]
        e=row(p);assert r['passed'] and e['sha256']==r['source_sha256']
        e.update(current_ordinary_module_passed=True,ordinary_log_sha256=r['log_sha256'])
        actual.append(e)
    deps=HERE/'actual-api-dependencies.json'
    freeze(deps,{'scope':'Current ordinary-source bindings only; concrete quartic/sextic packets remain uninstantiated.',
                 'sources':actual,'all_new_actual_packet_obligations_remain_visible':True})
    files=[row(p) for p in [HERE/'REVIEW.md',HERE/'CURVATURE_COMPARISON.md',Path(__file__),auditpath,deps]]
    pin=HERE/'degree6-review-files.json'
    freeze(pin,{'scope':'Static degree-six necessity/sign/principal-embedding review and stationary-swap integral theory.',
                'files':files,'external_model_source_index':row(auditpath),'actual_API_source_index':row(deps),
                'new_Lean_invocations':0,'solver_calls':0,'new_points':0,
                'old_exact714_extension_decided':False,'strict_projection_shrink_proved':False,
                'new_exclusion':False,'new_global_cover':False,'new_zero_proportion_proven':False})
    print(json.dumps({'pin':row(pin),'files':len(files),'bytes':sum(x['bytes'] for x in files),
                      'old_entries_checked':checked,'old_KKT_rows_checked':signed,
                      'actual_API_modules':len(actual)}))


if __name__=='__main__':
    if not __debug__:raise RuntimeError('Assertions must remain enabled')
    main()
