"""Independent Fraction gate for the one full-eight rank-one pilot.

No producer import or optimizer. Rationalize saved float coordinates
unchanged, check all5803 rows at energy slack0 and all47 pointwise
q(y)*v(y)*v(y)^T factorizations/necessary nonnegative multipliers.
Default read-only; --write-receipt creates an absent receipt once.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations_with_replacement
import argparse, gzip, hashlib, json, time
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent;OUT=HERE/'independent-replay.json'
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--write-receipt',action='store_true');args=ap.parse_args()
    if args.write_receipt:assert not OUT.exists()
    began=time.monotonic();path=HERE/'rankone-pilot.json';p=json.loads(path.read_bytes())
    inputs={**p['source_sha256_start'],path.relative_to(ROOT).as_posix():digest(path)}
    assert p['source_sha256_start']==p['source_sha256_end']and p['all_sources_unchanged']
    for n,h in inputs.items():assert digest(ROOT/n)==h
    model=json.loads(gzip.decompress((ROOT/'research-goal-20261017-quartic/quartic-model.json.gz').read_bytes()))
    family=json.loads(gzip.decompress((ROOT/'research-goal-20261017-swap-family-quartic/swap-family-normalized.json.gz').read_bytes()))
    proof=json.loads((ROOT/'research-goal-20261017-swap-family-quartic/swap-family-exact-primal.json').read_bytes())
    mon=[m for d in range(5)for m in combinations_with_replacement(range(9),d)];idx={m:k for k,m in enumerate(mon)}
    assert list(map(list,mon))==model['monomials']==family['monomials']and len(mon)==715
    assert p['fixed_seed_rational']==proof['rational_714_moments'][:9]and p['optimizer_calls']==1 and p['method']=='L-BFGS-B'
    y=[F(str(float(v)))for v in p['raw_candidate_float']];assert list(map(str,y))==p['candidate_rationalized_without_repair']and all(-1<=v<=1 for v in y)
    values=[]
    for m in mon:
        v=F(1)
        for j in m:v*=y[j]
        values.append(v)
    point=values[1:]+[F(0)];assert len(point)==715
    rows=model['linear_rows']+family['additional_linear_rows'];assert len(rows)==5803
    violations=[];worst=None;byfamily={}
    for r,row in enumerate(rows):
        slack=F(row['bound'])-sum((F(c)*point[k]for k,c in row['coefficients']),F(0));normalized=slack/F(row['scale'])
        e={'row':r,'meta':row['meta'],'slack':str(slack),'normalized_slack':str(normalized)}
        if worst is None or normalized<F(worst['normalized_slack']):worst=e
        key=row['meta'][0]
        if key not in byfamily or normalized<F(byfamily[key]['normalized_slack']):byfamily[key]=e
        if slack<0:violations.append(e)
    blocks=[];entry_count=0
    for block in model['PSD_blocks']:
        q={mon[k]:F(v)for k,v in block['multiplier_polynomial']};multiplier=sum((v*values[idx[m]]for m,v in q.items()),F(0))
        basis=mon[:block['size']];assert block['size']in(10,55)
        for i,j,form in block['entries']:
            # Check the exact polynomial identity, as well as its value at this point.
            expected={}
            for m,v in q.items():
                key=tuple(sorted(m+basis[i]+basis[j]));assert len(key)<=4;expected[key]=expected.get(key,F(0))+v
            expected={m:v for m,v in expected.items()if v}
            actual={mon[k+1]:F(v)for k,v in form['coefficients']if F(v)}
            if F(form['constant']):actual[()]=F(form['constant'])
            assert expected==actual
            value=F(form['constant'])+sum((F(v)*point[k]for k,v in form['coefficients']),F(0))
            assert value==multiplier*values[idx[basis[i]]]*values[idx[basis[j]]];entry_count+=1
        blocks.append({'name':block['name'],'size':block['size'],'multiplier':str(multiplier),'nonnegative_at_rank_one':multiplier>=0})
    passed=not violations and all(b['nonnegative_at_rank_one']for b in blocks)
    for n,h in inputs.items():assert digest(ROOT/n)==h
    out={'scope':__doc__,'arithmetic_replay_passed':True,'rankone_outer_model_witness':passed,
        'status':'exact_rankone_outer_model_witness'if passed else 'single_fixed_seed_pilot_not_a_rankone_witness',
        'source_sha256_start':inputs,'source_sha256_end':inputs,'all_sources_unchanged':True,
        'normalized_gap_point':list(map(str,y)),'energy_slack':'0','linear_rows_checked':5803,
        'negative_linear_rows':len(violations),'violations':violations,'worst_normalized_linear_slack':worst,
        'minimum_by_row_family':byfamily,'rank_one_blocks_checked':len(blocks),'rank_one_entries_checked':entry_count,
        'pointwise_polynomial_qvv_identities_checked':True,'blocks':blocks,
        'negative_q00_multipliers':sum(not b['nonnegative_at_rank_one']for b in blocks),
        'producer_imports':0,'optimizer_calls':0,'eigh_calls':0,'Lean_invocations':0,
        'failure_proves_nonexistence_of_rankone_point':False,'actual_F_evaluated':False,'actual_KKT_verified':False,
        'actual_sublevel_verified':False,'cell_exclusion_proven':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-began}
    if args.write_receipt:OUT.write_text(json.dumps(out,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({k:out[k]for k in ['arithmetic_replay_passed','rankone_outer_model_witness','linear_rows_checked','negative_linear_rows','rank_one_entries_checked','negative_q00_multipliers','seconds']}),flush=True)
if __name__=='__main__':
    assert __debug__
    main()
