"""Independent stdlib audit of the fixed swap67 quartic competitor row.

No producer import, solver, sampling, new cover or Lean. Rebuild the eight
changed spans, every point jet and selected w5 interval, quartic/error
polynomials, and the exact expectation of the frozen714 pseudo-moments.
Default read-only; --write-receipt creates a previously absent receipt.
"""
from pathlib import Path
from fractions import Fraction as Q
from itertools import combinations_with_replacement
from math import factorial
import argparse, gzip, hashlib, json, time

HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
PACKET=ROOT/'research-goal-20261017-swap67-quartic/swap67-quartic-static.json'
OUT=HERE/'independent-replay.json';SC=32768;DS=10**15
PAIRS=[(i,i+1)for i in range(9)]+[(i,j)for i in range(9)for j in range(i+2,10)]
SLOT={e:k for k,e in enumerate(PAIRS)}
EXPECTED_PACKET='e315e2439ef5324719b317d8e1b652b995c0496f369be30f5f9b9c8bd4ba6a96'


def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def plus(p,q,s=Q(1)):
    r=p.copy()
    for m,v in q.items():
        r[m]=r.get(m,Q(0))+s*v
        if not r[m]:del r[m]
    return r
def scaled(p,c):return {m:v*c for m,v in p.items()if v*c}
def times(p,q):
    r={}
    for m,a in p.items():
        for n,b in q.items():
            key=tuple(sorted(m+n));assert len(key)<=4;r[key]=r.get(key,Q(0))+a*b
    return {k:v for k,v in r.items()if v}
def iadd(a,b):return a[0]+b[0],a[1]+b[1]
def imul(a,b):
    p=[x*y for x in a for y in b];return min(p),max(p)
def iscale(a,b):return imul(a,(b,b))


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--write-receipt',action='store_true');args=ap.parse_args()
    if args.write_receipt:assert not OUT.exists()
    began=time.monotonic();assert digest(PACKET)==EXPECTED_PACKET;p=json.loads(PACKET.read_bytes())
    inputs={**p['source_sha256_start'],PACKET.relative_to(ROOT).as_posix():EXPECTED_PACKET,
      Path(__file__).relative_to(ROOT).as_posix():digest(Path(__file__))}
    assert p['source_sha256_start']==p['source_sha256_end'] and p['all_sources_unchanged']
    for name,h in inputs.items():assert digest(ROOT/name)==h,('source changed',name)
    model=json.loads(gzip.decompress((ROOT/'research-goal-20261017-quartic/quartic-model.json.gz').read_bytes()))
    primal=json.loads((ROOT/'research-goal-20261017-quartic/quartic-exact-primal.json').read_bytes())
    prior=json.loads((ROOT/'research-goal-20261017-quartic/quartic-result-replay.json').read_bytes())
    pars=json.loads((ROOT/'research-20261016-followup/window_reweight_rational.json').read_bytes())
    wdoc=json.loads((ROOT/'research-goal-20261016/window_normalized_interval.json').read_bytes())
    udoc=json.loads((ROOT/'research-goal-20261016/cover_newjet.json').read_bytes())
    assert primal['status']=='strict_exact_shared_quartic_outer_relaxation_feasible'
    assert prior['status']=='strict_exact_shared_quartic_outer_relaxation_independently_verified'
    assert p['path']==model['path']==primal['path']=='r001000001000100110011001'
    assert wdoc['parameter_sha256']==udoc['receipt']['parameter_sha256']==digest(ROOT/'research-20261016-followup/window_reweight_rational.json')
    assert wdoc['source_sha256']==digest(ROOT/'research-goal-20261016/window_normalized_interval.py')
    mon=[m for d in range(5)for m in combinations_with_replacement(range(9),d)]
    assert mon==list(map(tuple,model['monomials']))==list(map(tuple,p['monomials'])) and len(mon)==715
    index={m:i for i,m in enumerate(mon)};mom=[Q(1)]+list(map(Q,primal['rational_714_moments']));assert len(mom)==715
    def packed(poly):return [[index[m],str(v)]for m,v in sorted(poly.items(),key=lambda kv:index[kv[0]])]
    def expectation(poly):return sum((v*mom[index[m]]for m,v in poly.items()),Q(0))
    state=model['cell'];center=list(map(Q,model['normalized_gap_center']));radius=list(map(Q,model['normalized_gap_radius']))
    assert center==list(map(Q,p['normalized_gap_center'])) and radius==list(map(Q,p['normalized_gap_radius']))
    assert all(center[r]==Q(state[0][r]+state[1][r],2*SC) and radius[r]==Q(state[1][r]-state[0][r],2*SC)>0 for r in range(9))
    sep=Q(p['SEP']);assert sep==Q(123,128) and all(Q(state[0][r],SC)>sep for r in range(9))
    gap=[{():center[r],(r,):radius[r]}for r in range(9)]
    perm=list(range(9));perm[6],perm[7]=7,6;assert p['permutation']==perm and p['swap_zero_based']==[6,7]
    def span(indices):
        poly={}
        for r in indices:poly=plus(poly,gap[r])
        return poly
    def bound(i,j):
        if i==j:return 0,0
        z=SLOT[i,j];return state[0][z],state[1][z]
    def image_bounds(i,j):
        ids=perm[i:j]
        rows=[{'identity':'sum_permuted_gap_boxes','lower':sum(state[0][r]for r in ids),'upper':sum(state[1][r]for r in ids)}]
        if j==7:
            l,u=bound(i,6);rows.append({'identity':'span(i,6)+g7','lower':l+state[0][7],'upper':u+state[1][7]})
            l,u=bound(i,8);rows.append({'identity':'span(i,8)-g6','lower':l-state[1][6],'upper':u-state[0][6]})
        else:
            assert i==7;l,u=bound(8,j);rows.append({'identity':'g6+span(8,j)','lower':state[0][6]+l,'upper':state[1][6]+u})
            l,u=bound(6,j);rows.append({'identity':'span(6,j)-g7','lower':l-state[1][7],'upper':u-state[0][7]})
        return max(r['lower']for r in rows),min(r['upper']for r in rows),rows
    wt={int(n):[tuple(map(Q,v))for v in row]for n,row in wdoc['integer_w_Taylor_coefficients'].items()}
    ut={int(n):[tuple(map(Q,v))for v in row]for n,row in udoc['integer_taylor_coefficients'].items()}
    assert set(wt)==set(ut)==set(range(33)) and all(len(v)==24 for v in wt.values()) and all(len(v)==23 for v in ut.values())
    assert all(l<=u for table in [wt,ut]for row in table.values()for l,u in row)
    M24=Q(44,7)**24;assert M24==Q(udoc['receipt']['global_taylor_derivative_bound'])
    selected={};scalar_count=0;midpoint_span_checks=[]
    def point_jets(anchor):
        n=round(anchor);d=anchor-n;assert abs(d)<=Q(1,2) and n in wt;values=[]
        for j in range(5):
            # Direct interval sum is independent of the producer's point Horner loop.
            total=(Q(0),Q(0))
            for k in range(j,24):total=iadd(total,iscale(wt[n][k],Q(factorial(k),factorial(k-j))*d**(k-j)))
            rem=M24*abs(d)**(24-j)/factorial(24-j);values.append((total[0]-rem,total[1]+rem))
        return n,values
    def fifth_grid(k):
        if k not in selected:
            n=round(Q(2*k+1,128));d=(Q(k,64)-n,Q(k+1,64)-n);assert -Q(1,2)<=d[0]<=d[1]<=Q(1,2)
            v=(Q(0),Q(0))
            for j in reversed(range(4,23)):v=iadd(imul(v,d),iscale(ut[n][j],Q(factorial(j),factorial(j-4))))
            rem=M24*Q(1,2)**19/factorial(19);abs_bound=max(abs(v[0]-rem),abs(v[1]+rem))
            x=abs_bound*DS;selected[k]=Q((x.numerator+x.denominator-1)//x.denominator,DS)
        return selected[k]
    def scalar(row,poly,l,u):
        nonlocal scalar_count
        assert row['whole_span_integer_bounds']==[l,u] and 0<=l<u<=32*SC
        assert row['whole_span_rational_bounds']==[str(Q(l,SC)),str(Q(u,SC))]
        anchor=Q(l+u,2*SC);R=Q(u-l,2*SC);n,jets=point_jets(anchor)
        assert Q(row['anchor'])==anchor and row['integer_jet_anchor']==n and Q(row['radius_about_anchor'])==R
        assert [[str(a),str(b)]for a,b in jets]==row['anchor_derivative_intervals_orders_0_to_4']
        mu=[(a+b)/2 for a,b in jets];eps=[(b-a)/2 for a,b in jets];assert all(e>=0 for e in eps)
        assert mu==list(map(Q,row['anchor_derivative_midpoints'])) and eps==list(map(Q,row['anchor_derivative_errors']))
        cells=list(range(l//512,(u+511)//512));assert cells==row['whole_span_w5_grid_cells']
        M5=max(fifth_grid(k)for k in cells);assert M5==Q(row['whole_span_absolute_w5_bound'])
        d=plus(poly,{():anchor},Q(-1));powers=[{():Q(1)}]
        for k in range(1,5):powers.append(times(powers[-1],d))
        central={}
        for k in range(5):central=plus(central,powers[k],mu[k]/factorial(k))
        c0=eps[0]+eps[1]*R;c2=eps[2]/2+eps[3]*R/6;c4=eps[4]/24+M5*R/120
        assert c0>=0 and c2>=0 and c4>=0
        error=plus(plus({():c0},powers[2],c2),powers[4],c4)
        upper=plus(central,error);lower=plus(central,error,Q(-1))
        for name,v in [('span_polynomial',poly),('d_polynomial',d),('central_quartic',central),('nonnegative_error_polynomial',error),('scalar_upper_quartic',upper),('scalar_lower_quartic',lower)]:assert packed(v)==row[name],name
        midpoint=poly.get((),Q(0));assert Q(l,SC)<=midpoint<=Q(u,SC)
        midpoint_span_checks.append(True);scalar_count+=1
        return upper,lower,central,error
    den=pars['denominator'];assert den>0
    pressure=scaled(plus(gap[7],gap[6],Q(-1)),Q(pars['b_numerators'][6]-pars['b_numerators'][7],den))
    assert packed(pressure)==p['pressure_difference_polynomial'];total=pressure;central_total=pressure;error_total={}
    rows={tuple(r['edge']):r for r in p['changed_edge_packets']};changed=[];cancel=[];all_changed=[]
    for i,j in PAIRS:
        if span(range(i,j))!=span(perm[i:j]):all_changed.append([i,j])
    for i,j,a in pars['a_upper']:
        assert a>=0
        if not a:continue
        before=span(range(i,j));after=span(perm[i:j])
        if before==after:cancel.append([i,j]);continue
        changed.append([i,j]);row=rows[i,j];weight=Q(a,den);assert weight==Q(row['weight'])>0
        l,u=bound(i,j);_,oldlower,oldcentral,olderror=scalar(row['old'],before,l,u)
        l,u,sources=image_bounds(i,j);assert sources==row['image_bound_sources']
        newupper,_,newcentral,newerror=scalar(row['new'],after,l,u)
        diff=scaled(plus(newupper,oldlower,Q(-1)),weight)
        assert packed(diff)==row['weighted_difference_upper_quartic'] and expectation(diff)==Q(row['expected_weighted_difference_upper'])
        total=plus(total,diff);central_total=plus(central_total,scaled(plus(newcentral,oldcentral,Q(-1)),weight))
        error_total=plus(error_total,scaled(plus(newerror,olderror),weight))
    assert len(all_changed)==9 and [7,9]in all_changed
    assert len(changed)==8 and len(cancel)==33 and cancel==p['unchanged_edges_cancelled']
    assert set(rows)==set(map(tuple,changed)) and sum(a!=0 for _,_,a in pars['a_upper'])==41
    assert next(a for i,j,a in pars['a_upper']if[i,j]==[7,9])==0
    assert packed(total)==p['difference_upper_quartic'] and len(total)==450
    expected=expectation(total);assert expected==Q(p['expected_upper_difference_at_exact714']) and expected<Q(-17,10000)<0
    assert total.get((),Q(0))==Q(p['midpoint_upper_difference']) and total==plus(central_total,error_total)
    assert len(selected)==p['w5_grid_cells_rebuilt']==391 and scalar_count==16 and all(midpoint_span_checks)
    for name,h in inputs.items():assert digest(ROOT/name)==h
    # Only a loose diagnostic. It is not an optimization or a cell exclusion.
    box_l1_upper=total.get((),Q(0))+sum(abs(v)for m,v in total.items()if m)
    out={'scope':__doc__,'passed':True,'source_sha256_start':inputs,'source_sha256_end':inputs,'all_inputs_unchanged':True,
      'geometric_changed_spans':all_changed,'positive_weight_changed_spans':changed,'exact_cancelled_positive_weight_terms':len(cancel),
      'zero_weight_changed_span':[7,9],'same_nine_normalized_variables':True,'polynomial_terms':len(total),'monomials_checked':715,
      'point_scalar_jets_rebuilt':16,'selected_w5_grid_cells_rebuilt':391,'actual_interval_table_semantics_assumed_not_newly_Lean_proved':True,
      'upper_minus_lower_and_all_nonnegative_error_payments_checked':True,'global_Orthant_minimum_required_not_local_KKT':True,
      'swap_preserves_sep_for_every_actual_gap_vector':True,'competitor_need_not_remain_in_original_cell_or_pressure_box':True,
      'expected_upper_difference':str(expected),'expected_upper_difference_strictly_below':'-17/10000',
      'expectation_pressure':str(expectation(pressure)),'expectation_central_difference':str(expectation(central_total)-expectation(pressure)),
      'expectation_error_payment':str(expectation(error_total)),'box_L1_upper_diagnostic':str(box_l1_upper),
      'exact714_point_violates_new_necessary_row':True,'cell_exclusion_proven':False,'new_solver_infeasibility_proven':False,
      'optimizer_calls':0,'producer_imports':0,'Lean_invocations':0,'new_zero_proportion_proven':False,'seconds':time.monotonic()-began}
    if args.write_receipt:OUT.write_text(json.dumps(out,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({'passed':True,'expected_upper_difference':str(expected),'strict_below_minus17_over10000':True,
      'changed':len(changed),'cancelled':len(cancel),'selected_w5_cells':len(selected),'source_sha256':digest(Path(__file__)),
      'receipt_sha256':digest(OUT)if args.write_receipt else None,'seconds':out['seconds']}),flush=True)


if __name__=='__main__':
    assert __debug__
    main()
