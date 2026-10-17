"""Independent exact replay of the ONE completed stationary-swap packet.

Stdlib only. Do not import the producer or its polynomial/interval helper.
Rebuild normalized-W jets2..6, the selected q7,d16 cells, weighted t-power
integrals, eight actual-ledger polynomial sums and the fixed 714 expectation.
No new function sample, solver, Lean, point, parameter or family is selected.
Default read-only; --write-receipt creates an absent receipt once.
"""
from pathlib import Path
from fractions import Fraction as F
from math import factorial,comb
import argparse
import gzip
import hashlib
import json
import sys
import time

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
OUT=HERE/'independent-replay.json'
SC=32768
DS=10**15


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()


def add(a,b,k=F(1)):
    out=a.copy()
    for m,c in b.items():
        out[m]=out.get(m,F(0))+k*c
        if not out[m]:del out[m]
    return out


def product(a,b):
    out={}
    for m,c in a.items():
        for n,d in b.items():
            key=tuple(sorted(m+n));out[key]=out.get(key,F(0))+c*d
            if not out[key]:del out[key]
    return out


def scale(a,c):return {m:v*c for m,v in a.items() if v*c}


def power(a,n):
    out={():F(1)}
    for _ in range(n):out=product(out,a)
    return out


def interval_add(a,b):return (a[0]+b[0],a[1]+b[1])


def interval_mul(a,b):
    c=[x*y for x in a for y in b]
    return (min(c),max(c))


def interval_horner(table,order,x):
    coefficients=[tuple(v*F(factorial(j),factorial(j-order)) for v in table[j])
                  for j in range(order,24)]
    value=coefficients[-1]
    for c in reversed(coefficients[:-1]):value=interval_add(c,interval_mul(value,x))
    return value


def integrate_t(poly):
    """Integrate (1-t)*poly over 0..1, with temporary variable t=index9."""
    out={}
    for m,c in poly.items():
        k=m.count(9);key=tuple(r for r in m if r!=9)
        out=add(out,{key:c/F((k+1)*(k+2))})
    return out


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--write-receipt',action='store_true');args=ap.parse_args()
    if args.write_receipt:assert not OUT.exists()
    began=time.monotonic()
    producer=ROOT/'research-goal-20261017-stationary-swap/stationary-swap-static.json'
    packet=json.loads(producer.read_bytes())
    paths=[Path(__file__),producer]
    for name,h in packet['source_sha256_start'].items():
        p=ROOT/name;assert sha(p)==h
        if p not in paths:paths.append(p)
    assert packet['source_sha256_start']==packet['source_sha256_end']
    initial={p.relative_to(ROOT).as_posix():sha(p) for p in paths}
    family_path=ROOT/'research-goal-20261017-swap-family-quartic/swap-family-normalized.json.gz'
    family=json.loads(gzip.decompress(family_path.read_bytes()))
    parent=json.loads(gzip.decompress((ROOT/'research-goal-20261017-quartic/quartic-model.json.gz').read_bytes()))
    proof=json.loads((ROOT/'research-goal-20261017-swap-family-quartic/swap-family-exact-primal.json').read_bytes())
    wdoc=json.loads((ROOT/'research-goal-20261016/window_normalized_interval.json').read_bytes())
    params=json.loads((ROOT/'research-20261016-followup/window_reweight_rational.json').read_bytes())
    assert parent['path']==family['path']==proof['path']==packet['path']=='r001000001000100110011001'
    mon=[tuple(m) for m in parent['monomials']];index={m:k for k,m in enumerate(mon)}
    assert len(mon)==715 and mon==[tuple(m) for m in packet['monomials']]==[tuple(m) for m in family['monomials']]
    moments=[F(1)]+list(map(F,proof['rational_714_moments']))
    assert len(moments)==715 and proof['energy_slack']=='0'
    def unpack(p):return {mon[k]:F(v) for k,v in p if F(v)}
    def expectation(p):return sum(c*moments[index[m]] for m,c in p.items())
    center=list(map(F,parent['normalized_gap_center']));radius=list(map(F,parent['normalized_gap_radius']))
    gaps=[{():center[r],(r,):radius[r]} for r in range(9)]
    h=add(gaps[6],gaps[7],F(-1))
    assert unpack(packet['positive_h_polynomial'])==h
    state=parent['cell'];margins=[n-31488 for n in state[0][:9]]
    assert min(margins)>0 and F(state[0][6]-state[1][7],SC)==F(117,32768)
    assert F(packet['positive_h_lower_bound'])==F(117,32768)
    W={int(n):[tuple(map(F,values)) for values in row] for n,row in wdoc['integer_w_Taylor_coefficients'].items()}
    M24=F(44,7)**24;cache={}
    def seventh(k):
        if k in cache:return cache[k]
        n=round(F(2*k+1,128));x=(F(k,64)-n,F(k+1,64)-n)
        assert 1<=n<=32 and -F(1,2)<=x[0]<=x[1]<=F(1,2)
        lo,hi=interval_horner(W[n],7,x)
        rem=M24*F(1,2)**17/factorial(17)
        raw=max(abs(lo-rem),abs(hi+rem))*DS
        cache[k]=F(-((-raw.numerator)//raw.denominator),DS)
        return cache[k]
    edges={(i,j):F(a,params['denominator']) for i,j,a in params['a_upper'] if a and (i==7 or j==7)}
    records=packet['scalar_path_packets'];assert len(records)==len(edges)==8
    chosen=family['maps'][6];assert chosen['swap_zero_based']==[6,7]
    lookup={tuple(r['edge']):r for r in chosen['changed_edge_packets']}
    aggregate={};central_total=F(0);error_total=F(0);point_checks=0;J_checks=0
    for record in records:
        edge=tuple(record['edge']);assert edge in edges
        i,j=edge;sign=-1 if j==7 else 1
        assert record['path_direction']==sign and F(record['weight'])==edges[edge]
        reference=lookup[edge]
        old=family['scalar_packets'][reference['old_scalar_packet']]
        new=family['scalar_packets'][reference['new_scalar_packet']]
        s=unpack(old['span_polynomial']);image=unpack(new['span_polynomial'])
        assert add(image,s,F(-1))==scale(h,F(sign))
        assert unpack(record['old_span_polynomial'])==s and unpack(record['new_span_polynomial'])==image
        l=min(old['whole_span_integer_bounds'][0],new['whole_span_integer_bounds'][0])
        u=max(old['whole_span_integer_bounds'][1],new['whole_span_integer_bounds'][1])
        assert record['whole_path_hull_integer_bounds']==[l,u]
        p=F(l+u,2*SC);R=F(u-l,2*SC);n=round(p);delta=p-n
        assert p==F(record['anchor']) and R==F(record['radius_about_anchor']) and n==record['integer_jet_anchor']
        assert 1<=n<=32 and abs(delta)<=F(1,2)
        mu=[];eps=[]
        assert len(record['anchor_derivative_intervals_orders_2_to_6'])==5
        for q,stored in zip(range(2,7),record['anchor_derivative_intervals_orders_2_to_6']):
            lo,hi=interval_horner(W[n],q,(delta,delta))
            rem=M24*abs(delta)**(24-q)/factorial(24-q)
            actual=(lo-rem,hi+rem);assert actual==tuple(map(F,stored))
            mu.append(sum(actual)/2);eps.append((actual[1]-actual[0])/2);point_checks+=1
        assert mu==list(map(F,record['anchor_derivative_midpoints'])) and eps==list(map(F,record['anchor_derivative_errors']))
        ks=list(range(l//512,(u+511)//512));assert ks==record['whole_hull_w7_grid_cells']
        M7=max(map(seventh,ks));assert M7==F(record['whole_hull_absolute_w7_bound'])
        d=add(s,{():p},F(-1));qpoly=scale(h,F(sign))
        assert d==unpack(record['d0_polynomial'])
        # Expand in temporary t first, then integrate; independent of the
        # producer's binomial-loop implementation.
        affine=add(d,{tuple(sorted(m+(9,))):c for m,c in qpoly.items()})
        integrated=[]
        for r in range(5):
            J=integrate_t(power(affine,r));formula={}
            for k in range(r+1):
                formula=add(formula,product(power(d,r-k),power(qpoly,k)),F(comb(r,k),(k+1)*(k+2)))
            assert J==formula==unpack(record['integrals_one_minus_theta_times_d_powers'][r])
            integrated.append(J);J_checks+=1
        central={}
        for r,J in enumerate(integrated):central=add(central,J,mu[r]/factorial(r))
        error={():F(1,2)*(eps[0]+eps[1]*R)}
        error=add(error,integrated[2],eps[2]/2+eps[3]*R/6)
        error=add(error,integrated[4],eps[4]/24+M7*R/120)
        term=scale(add(central,error),edges[edge])
        assert central==unpack(record['central_quartic']) and error==unpack(record['nonnegative_error_quartic'])
        assert term==unpack(record['weighted_upper_quartic'])
        ec=edges[edge]*expectation(central);ee=edges[edge]*expectation(error);et=expectation(term)
        assert (ec,ee,et)==tuple(F(record[k]) for k in ['expected_weighted_central','expected_weighted_error','expected_weighted_upper'])
        central_total+=ec;error_total+=ee;aggregate=add(aggregate,term)
    assert point_checks==40 and J_checks==40 and len(cache)==391
    assert packet['normalized_W_w7_Taylor_degree']==16 and packet['w7_remainder_power']==17
    value=expectation(aggregate)
    assert aggregate==unpack(packet['upper_stationary_curvature_quartic']) and len(aggregate)==495
    assert value==F(packet['expected_upper_at_latest_exact714'])==central_total+error_total
    assert central_total==F(packet['expected_total_central']) and error_total==F(packet['expected_total_error'])
    assert value>0 and not packet['latest_exact714_separated']
    linear=packet['candidate_unsoftened_row']
    assert linear['meta']==['stationary_second_divided_global_swap67_necessary']
    coefficients=[[index[m]-1,str(-c)] for m,c in sorted(aggregate.items(),key=lambda z:index[z[0]]) if m]
    constant=aggregate.get((),F(0));divisor=max([F(1,1000),abs(constant)]+[abs(F(v)) for _,v in coefficients])
    assert linear['coefficients']==coefficients and F(linear['bound'])==constant and F(linear['scale'])==divisor
    final={p.relative_to(ROOT).as_posix():sha(p) for p in paths};assert initial==final
    assert not any(n.split('.')[0] in ['numpy','scipy','scs'] for n in sys.modules)
    result={'scope':__doc__,'status':'one_fixed_stationary_swap_packet_independently_replayed',
            'input_sha256_start':initial,'input_sha256_end':final,'all_inputs_unchanged':True,
            'anchor_derivative_intervals_orders_2_to_6_rebuilt':point_checks,
            'distinct_q7_degree16_cells_rebuilt':len(cache),'w7_remainder_power_and_factorial':17,
            'weighted_power_integrals_independently_integrated_and_formula_checked':J_checks,
            'positive_ledger_edges_aggregated':8,'common_polynomial_terms':len(aggregate),
            'fixed_exact_moments_read':714,'expected_upper':str(value),
            'expected_central':str(central_total),'expected_error':str(error_total),
            'upper_is_strictly_positive':True,'latest_exact714_separated':False,
            'candidate_linear_row_sign_and_normalization_checked':True,
            'pure_stdlib':True,'producer_or_helper_imported':False,'new_function_samples':0,
            'solver_calls':0,'Lean_invocations':0,'new_actual_analytic_obligations_discharged':False,
            'new_cell_exclusion':False,'new_zero_proportion_proven':False,
            'elapsed_milliseconds':int((time.monotonic()-began)*1000)}
    if args.write_receipt:OUT.write_text(json.dumps(result,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({'status':result['status'],'point_intervals':point_checks,'q7cells':len(cache),
                      'J_integrals':J_checks,'expected_upper_approx':float(value),
                      'strict_separation':False,'elapsed_milliseconds':result['elapsed_milliseconds']}))


if __name__=='__main__':
    if not __debug__:raise RuntimeError('Assertions must remain enabled')
    main()
