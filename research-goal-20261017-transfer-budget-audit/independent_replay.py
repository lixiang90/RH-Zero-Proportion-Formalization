"""Independent stdlib replay of the one fixed legacy-analytic transfer budget.

Rebuild L6/P5/E6 and all181 row hashes, the exact odd/even box supports,
all180 scalar costs and19 integer-factor column-l1 bounds/costs. This
audits the fixed failed budget, without changing it. No producer import,
optimizer, eigenvalue, point/kernel evaluation or Lean. Default read-only;
--write-receipt creates an absent receipt once.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations_with_replacement
import argparse,gzip,hashlib,json,sys,time
if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(0)
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent;PACK=ROOT/'research-goal-20261017-old-analytic-transfer-budget'
OUT=HERE/'independent-replay.json';D=10**12
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def add(a,b,s=F(1)):
    out=a.copy()
    for k,v in b.items():
        out[k]=out.get(k,F(0))+s*v
        if not out[k]:del out[k]
    return out
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--write-receipt',action='store_true');args=ap.parse_args()
    if args.write_receipt:assert not OUT.exists()
    began=time.monotonic();path=PACK/'transfer-budget.json';receipt=PACK/'budget-receipt.json'
    assert digest(path)=='2352833fe99336a786c96bde7d48a45fc9fac5a22932aba2201825d9fecead46'
    assert digest(receipt)=='9b33b3aac3714fcf88f9f5e478bcd9a79130582dd1dc5be93fac770507a69be7'
    p=json.loads(path.read_bytes());producer=json.loads(receipt.read_bytes());assert p['schema']=='fixed-old-analytic-transfer-budget-v1'
    inputs={**p['source_sha256'],path.relative_to(ROOT).as_posix():digest(path),receipt.relative_to(ROOT).as_posix():digest(receipt),Path(__file__).relative_to(ROOT).as_posix():digest(Path(__file__))}
    assert producer['source_sha256_start']==producer['source_sha256_end']==p['source_sha256']and producer['all_inputs_unchanged']
    for n,h in inputs.items():assert digest(ROOT/n)==h
    ray=json.loads(gzip.decompress((ROOT/'research-goal-20261017-actual-sextic-exact-ray/quantized-ray.json.gz').read_bytes()))
    cert=json.loads((ROOT/'research-goal-20261017-actual-sextic-exact-ray/exact-enclosure-certificate.json').read_bytes())
    old=json.loads(gzip.decompress((ROOT/'research-goal-20261017-quartic/quartic-model.json.gz').read_bytes()))
    model=json.loads(gzip.decompress((ROOT/'research-goal-20261017-degree6-static/degree6-model.json.gz').read_bytes()))
    actual=json.loads(gzip.decompress((ROOT/'research-goal-20261017-actual-sextic-static/actual-sextic.json.gz').read_bytes()))
    rowhash=json.loads((ROOT/'research-goal-20261017-actual-sextic-cone/new-row-hashes.json').read_bytes())
    mon=[m for d in range(7)for m in combinations_with_replacement(range(9),d)];idx={m:k for k,m in enumerate(mon)}
    assert list(map(list,mon))==actual['monomials']==model['monomials']and list(map(list,mon[:715]))==old['monomials']
    assert actual['normalized_gap_center']==old['normalized_gap_center']and actual['normalized_gap_radius']==old['normalized_gap_radius']
    assert all(v>0 for v in actual['all_nine_original_free_margins_SC_units'])
    c=F(actual['target']);margin=F(cert['strict_margin']);assert c==F(11,1250)and 0<margin<1
    def upper(poly):
        value=F(0)
        for mid,a in poly.items():
            if mid==0:value+=a
            elif all(mon[mid].count(j)%2==0 for j in set(mon[mid])):value+=max(F(0),a)
            else:value+=abs(a)
        return value
    powers=[{k:F(v)for k,v in q['terms']}for q in actual['span_powers']]
    L6={k:F(v)for k,v in actual['pressure_polynomial']};P5=[{0:F(v)}for v in actual['pressure_coefficients_b']];E6=[{}for _ in range(9)]
    parts=[]
    for e in actual['edges']:
        atom=[]
        for field in['absolute_L6_coefficients_in_d','derivative_U5_coefficients_in_d','derivative_E6_coefficients_in_d']:
            q={}
            for degree,v in enumerate(e[field]):q=add(q,powers[e['power_ids'][degree]],F(v)*F(e['weight']))
            atom.append(q)
        parts.append(atom);L6=add(L6,atom[0])
    for coordinate,edges in enumerate(actual['coordinate_incident_edges']):
        for eid in edges:P5[coordinate]=add(P5[coordinate],parts[eid][1]);E6[coordinate]=add(E6[coordinate],parts[eid][2])
    assert len(actual['new_scalar_rows'])==len(rowhash['rows'])==181
    for descriptor,record in zip(actual['new_scalar_rows'],rowhash['rows']):
        if descriptor['kind']=='absolute_energy_L6':q=add({0:c},L6,F(-1));meta=['actual_sextic_absolute_energy_unsoftened']
        else:
            r=descriptor['coordinate'];test=descriptor['test_monomial_id'];sgn=descriptor['sign']
            shifted={idx[tuple(sorted(mon[k]+mon[test]))]:v for k,v in P5[r].items()};q=add(E6[r],shifted,F(sgn));meta=['actual_sextic_free_KKT',r,test,sgn]
        bound=q.get(0,F(0));scale=max([F(1,1000),abs(bound)]+[abs(v)for k,v in q.items()if k]);assert scale==F(record['scale'])
        row={'coefficients':[[k-1,str(-v)]for k,v in sorted(q.items())if k],'bound':str(bound),'scale':str(scale),'meta':meta}
        assert hashlib.sha256(json.dumps(row,sort_keys=True,separators=(',',':')).encode()).hexdigest()==record['exact_canonical_row_sha256']
    P3=[{k:F(v)for k,v in q}for q in old['KKT_cubic_polynomials']];E4=[{k:F(v)for k,v in q}for q in old['KKT_dynamic_error_polynomials']]
    L2={k:F(v)for k,v in old['old_quadratic_L2']};eps=[];gradientrecords=[]
    for r in range(9):
        difference_error=add(E6[r],E4[r],F(-1));new_minus_old_gradient=add(P5[r],P3[r],F(-1))
        # Reverse the producer's intermediate gradient sign; check both exact bounds.
        minus=upper(add(difference_error,new_minus_old_gradient));plus=upper(add(difference_error,new_minus_old_gradient,F(-1)))
        epsilon=max(F(0),plus,minus);eps.append(epsilon)
        gradientrecords.append({'coordinate':r,'upper_E6_minus_E4_plus_P3_minus_P5':str(plus),
            'upper_E6_minus_E4_minus_P3_plus_P5':str(minus),'epsilon':str(epsilon)})
    assert gradientrecords==p['epsilon_gradient']
    epsilon0_upper=upper({k:v/c for k,v in add(L2,L6,F(-1)).items()});epsilon0=max(F(0),epsilon0_upper)
    q0=add({0:F(1)},L2,F(-1)/c);assert q0=={k:F(v)for k,v in model['multipliers'][1]['terms']}
    weights=ray['scalar_weight_numerators'];assert ray['scalar_weight_denominator']==D and weights[5793]==weights[5794]==0
    scalar=[];kscalar=F(0)
    for rid,row in enumerate(old['linear_rows']):
        if row['meta'][0]!='free_KKT_with_dynamic_error':continue
        _,r,test,sgn=row['meta'];shift={idx[tuple(sorted(mon[k]+mon[test]))]:v for k,v in P3[r].items()};expected=add(E4[r],shift,F(sgn))
        source={k+1:-F(v)for k,v in row['coefficients']};source[0]=F(row['bound']);source={k:v for k,v in source.items()if v};assert source==expected
        scale=F(row['scale']);weight=F(weights[rid],D);assert scale>0 and weight>=0;cost=weight*eps[r]/scale;kscalar+=cost
        scalar.append({'scalar_row':rid,'coordinate':r,'test_monomial_id':test,'sign':sgn,'normalized_weight':str(weight),'row_scale':str(scale),'cost':str(cost)})
    assert len(scalar)==180 and scalar==p['scalar180_costs']
    def column_bound(bid):
        f=ray['PSD_factors'][bid];block=model['blocks'][bid];n=block['size'];rank=f['column_count'];rows=f['factor_numerators_by_row']
        assert f['block_id']==bid and f['factor_denominator']==D and f['multiplier_id']==block['multiplier_id']and len(rows)==n and all(len(v)==rank for v in rows)
        # Independently expand each column's sum of absolute products instead
        # of trusting a floating norm or a supplied Gram matrix.
        numerator=sum(sum(abs(rows[i][k]*rows[j][k])for i in range(n)for j in range(n))for k in range(rank))
        assert numerator==sum(sum(abs(row[k])for row in rows)**2 for k in range(rank))
        divisor=max([F(1)]+[abs(F(v))for mid,v in model['multipliers'][block['multiplier_id']]['terms']])
        assert divisor==F(f['positive_rational_block_divisor'])>0
        return numerator,F(numerator,D*D),divisor
    gram=[];kgram=F(0)
    for bid,block in enumerate(model['blocks']):
        multiplier=model['multipliers'][block['multiplier_id']];meta=multiplier['meta']
        if meta[0]!='free_gradient_E_plus_sign_P':continue
        _,r,sgn=meta;assert {k:F(v)for k,v in multiplier['terms']}==add(E4[r],P3[r],F(sgn))
        numerator,B,divisor=column_bound(bid);cost=eps[r]*B/divisor;kgram+=cost
        gram.append({'Gram_block':bid,'coordinate':r,'sign':sgn,'column_l1_square_sum_integer':numerator,
            'Gram_factor_denominator_squared':D*D,'SOS_upper_B':str(B),'block_divisor':str(divisor),'cost':str(cost)})
    assert len(gram)==18 and gram==p['old_gradient18_Gram_costs']
    numerator,B,divisor=column_bound(1);ksub=epsilon0*B/divisor
    sub={'Gram_block':1,'upper_L2_minus_L6_divided_by_c':str(epsilon0_upper),'epsilon0':str(epsilon0),'c':str(c),
        'column_l1_square_sum_integer':numerator,'Gram_factor_denominator_squared':D*D,'SOS_upper_B':str(B),'block_divisor':str(divisor),'cost':str(ksub)}
    assert sub==p['old_sublevel_Gram_cost']
    K=kscalar+kgram+ksub;assert str(K)==p['total_cost_K']and str(margin)==p['fixed_full_certificate_margin']
    assert str(kscalar)==p['total_old_scalar180_cost']and str(kgram)==p['total_old_gradient18_Gram_cost']and str(ksub)==p['total_old_sublevel_Gram_cost']
    assert str(margin-K)==p['remaining_margin']and not(K<margin)and not p['strict_K_less_than_margin']
    assert K>1970>1>margin and not p['old_analytic_dependencies_removed_by_this_budget']and p['eight_swap_analytic_dependencies_retained']
    for n,h in inputs.items():assert digest(ROOT/n)==h
    out={'scope':__doc__,'arithmetic_replay_passed':True,'source_sha256_start':inputs,'source_sha256_end':inputs,'all_inputs_unchanged':True,
        'all181_new_scalar_hashes_rebuilt':True,'gradient_box_upper_bounds_checked':18,'gradient_epsilons_checked':9,
        'sublevel_epsilon_includes_exact_inverse_c':True,'scalar_costs_checked':180,'old_gradient_Gram_costs_checked':18,'old_sublevel_Gram_costs_checked':1,
        'all180_scalar_normalization_scales_checked':True,'all19_Gram_block_divisors_checked':True,
        'all19_column_l1_bounds_rebuilt_from_integer_factors':True,'Dlambda':D,'DL':D,'same_fixed_ray_unchanged':True,
        'total_K_fraction_sha256':hashlib.sha256(str(K).encode()).hexdigest(),'K_denominator_bits':K.denominator.bit_length(),
        'K_lower_integer':K.numerator//K.denominator,'K_upper_integer':-((-K.numerator)//K.denominator),
        'K_hint':float(K),'scalar_cost_hint':float(kscalar),'gradient_Gram_cost_hint':float(kgram),'sublevel_cost_hint':float(ksub),'margin':str(margin),
        'strict_K_less_than_margin':False,'budget_gate_failed':True,'exact_comparison':'K>1970>1>margin',
        'real_point_deficit_argument_not_a_general_pseudomoment_substitution':True,'old_analytic_premises_not_removed':True,
        'failure_scope':'This fixed expanded-y box/column-l1 payment exceeds the fixed ray margin; no impossibility of analytic transfer or other bounds is implied.',
        'original_exact_ray_certificate_remains_valid_with_its_premises':True,'alternate_bound_attempted':False,
        'producer_imports':0,'solver_calls':0,'eigh_calls':0,'kernel_evaluations':0,'new_points':0,'Lean_invocations':0,
        'actual_cell_exclusion_Lean_proved':False,'global_cover_completed':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-began}
    if args.write_receipt:OUT.write_text(json.dumps(out,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({k:out[k]for k in['arithmetic_replay_passed','K_hint','scalar_cost_hint','gradient_Gram_cost_hint','sublevel_cost_hint','strict_K_less_than_margin','seconds']}),flush=True)
if __name__=='__main__':
    assert __debug__
    main()
