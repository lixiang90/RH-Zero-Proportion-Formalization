"""Independent stdlib replay of the fixed positive-divided swap67 row.

Rebuild whole old/image domains, normalized-W point jets and q6 grid,
expand the common y/theta path in a tenth formal variable, integrate each
theta monomial exactly, then apply the fixed714 moment functional.
No producer import, solver, sampling, eigensolve or Lean. Default read-only;
--write-receipt creates an absent receipt once.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations_with_replacement
from math import factorial
import argparse, gzip, hashlib, json, time

HERE=Path(__file__).resolve().parent;ROOT=HERE.parent;SC=32768;DS=10**15
PACKET=ROOT/'research-goal-20261017-swap67-divided-difference/divided-static.json'
SHA='ecfe92df87e673b8cfbc37afb8dc5776e6e34e2afa39796f2d403f3e1d89a3b9';OUT=HERE/'independent-replay.json'
PAIRS=[(i,i+1)for i in range(9)]+[(i,j)for i in range(9)for j in range(i+2,10)];SLOT={e:k for k,e in enumerate(PAIRS)}
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def add(a,b,c=F(1)):
    r=a.copy()
    for m,v in b.items():
        r[m]=r.get(m,F(0))+c*v
        if not r[m]:del r[m]
    return r
def scale(p,c):return {m:v*c for m,v in p.items()if v*c}
def mul(a,b):
    r={}
    for m,v in a.items():
        for n,w in b.items():
            k=tuple(sorted(m+n));r[k]=r.get(k,F(0))+v*w
    return {m:v for m,v in r.items()if v}
def iadd(a,b):return a[0]+b[0],a[1]+b[1]
def imul(a,b):
    values=[x*y for x in a for y in b];return min(values),max(values)
def iscale(a,c):return imul(a,(c,c))

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--write-receipt',action='store_true');args=ap.parse_args()
    if args.write_receipt:assert not OUT.exists()
    began=time.monotonic();assert digest(PACKET)==SHA;p=json.loads(PACKET.read_bytes())
    inputs={**p['source_sha256_start'],PACKET.relative_to(ROOT).as_posix():SHA,Path(__file__).relative_to(ROOT).as_posix():digest(Path(__file__))}
    assert p['source_sha256_start']==p['source_sha256_end']and p['all_sources_unchanged']
    for name,h in inputs.items():assert digest(ROOT/name)==h,('changed input',name)
    family=json.loads(gzip.decompress((ROOT/'research-goal-20261017-swap-family-quartic/swap-family-normalized.json.gz').read_bytes()))
    model=json.loads(gzip.decompress((ROOT/'research-goal-20261017-quartic/quartic-model.json.gz').read_bytes()))
    proof=json.loads((ROOT/'research-goal-20261017-swap-family-quartic/swap-family-exact-primal.json').read_bytes())
    pars=json.loads((ROOT/'research-20261016-followup/window_reweight_rational.json').read_bytes())
    wdoc=json.loads((ROOT/'research-goal-20261016/window_normalized_interval.json').read_bytes())
    assert wdoc['parameter_sha256']==digest(ROOT/'research-20261016-followup/window_reweight_rational.json')
    assert wdoc['source_sha256']==digest(ROOT/'research-goal-20261016/window_normalized_interval.py')
    mon=[m for d in range(5)for m in combinations_with_replacement(range(9),d)];idx={m:k for k,m in enumerate(mon)}
    assert list(map(list,mon))==p['monomials']==family['monomials']==model['monomials']and len(mon)==715
    moments=[F(1)]+list(map(F,proof['rational_714_moments']));assert len(moments)==715
    assert p['path']==family['path']==model['path']==proof['path']=='r001000001000100110011001'
    def pack(v):return [[idx[m],str(c)]for m,c in sorted(v.items(),key=lambda z:idx[z[0]])]
    def unpack(v):return {mon[k]:F(c)for k,c in v}
    def expect(v):return sum((c*moments[idx[m]]for m,c in v.items()),F(0))
    state=model['cell'];centers=list(map(F,model['normalized_gap_center']));radii=list(map(F,model['normalized_gap_radius']))
    assert centers==list(map(F,family['normalized_gap_center']))and radii==list(map(F,family['normalized_gap_radius']))
    assert all(centers[i]==F(state[0][i]+state[1][i],2*SC)and radii[i]==F(state[1][i]-state[0][i],2*SC)>0 for i in range(9))
    gap=[{():centers[i],(i,):radii[i]}for i in range(9)]
    def span(ids):
        result={}
        for i in ids:result=add(result,gap[i])
        return result
    def bound(i,j):return (0,0)if i==j else(state[0][SLOT[i,j]],state[1][SLOT[i,j]])
    h=add(gap[6],gap[7],F(-1));hl=F(state[0][6]-state[1][7],SC)
    assert state[0][6]==p['original_gap6_lower_integer']==64179 and state[1][7]==p['original_gap7_upper_integer']==64062
    assert hl==F(p['divisor_lower_bound'])==F(117,32768)>0 and pack(h)==p['positive_divisor_polynomial']and p['scale']==SC
    pressure=F(pars['b_numerators'][7]-pars['b_numerators'][6],pars['denominator'])
    assert pressure==F(p['pressure_difference_divided_by_h'])and pack(scale(h,pressure))==family['maps'][6]['pressure_difference_polynomial']
    perm=list(range(9));perm[6],perm[7]=7,6
    wt={int(n):[tuple(map(F,v))for v in row]for n,row in wdoc['integer_w_Taylor_coefficients'].items()}
    assert set(wt)==set(range(33))and all(len(v)==24 for v in wt.values());M24=F(44,7)**24;grid={}
    def grid6(k):
        if k not in grid:
            n=round(F(2*k+1,128));d=(F(k,64)-n,F(k+1,64)-n);assert 1<=n<=32 and -F(1,2)<=d[0]<=d[1]<=F(1,2)
            value=(F(0),F(0))
            for j in reversed(range(6,24)):value=iadd(imul(value,d),iscale(wt[n][j],F(factorial(j),factorial(j-6))))
            rem=M24*F(1,2)**18/factorial(18);raw=max(abs(value[0]-rem),abs(value[1]+rem))*DS
            grid[k]=F((raw.numerator+raw.denominator-1)//raw.denominator,DS)
        return grid[k]
    total={():pressure};central_total={():pressure};error_total={};checked=0
    mapping=family['maps'][6];assert len(mapping['changed_edge_packets'])==len(p['scalar_path_packets'])==8
    for edge,a in zip(mapping['changed_edge_packets'],p['scalar_path_packets']):
        i,j=edge['edge'];direction=-1 if j==7 else 1;assert j==7 or i==7
        assert a['edge']==[i,j]and a['path_direction_and_derivative_sign']==direction
        before=span(range(i,j));after=span(perm[i:j]);assert add(after,before,F(-1))==scale(h,F(direction))
        assert pack(before)==a['old_span_polynomial']and pack(after)==a['new_span_polynomial']
        old=family['scalar_packets'][edge['old_scalar_packet']];new=family['scalar_packets'][edge['new_scalar_packet']]
        assert pack(before)==old['span_polynomial']and pack(after)==new['span_polynomial']
        oldl,oldu=bound(i,j);candidates=[(sum(state[0][k]for k in perm[i:j]),sum(state[1][k]for k in perm[i:j]))]
        if j==7:
            l,u=bound(i,6);candidates.append((l+state[0][7],u+state[1][7]));l,u=bound(i,8);candidates.append((l-state[1][6],u-state[0][6]))
        else:
            l,u=bound(8,j);candidates.append((state[0][6]+l,state[1][6]+u));l,u=bound(6,j);candidates.append((l-state[1][7],u-state[0][7]))
        newl=max(l for l,u in candidates);newu=min(u for l,u in candidates)
        assert old['whole_span_integer_bounds']==a['old_whole_span_integer_bounds']==[oldl,oldu]
        assert new['whole_span_integer_bounds']==a['new_whole_span_integer_bounds']==[newl,newu]
        l,u=min(oldl,newl),max(oldu,newu);anchor=F(l+u,2*SC);R=F(u-l,2*SC);n=round(anchor);delta=anchor-n
        assert a['whole_path_hull_integer_bounds']==[l,u]and 0<l<u<=32*SC and R>0
        assert F(a['anchor'])==anchor and a['integer_jet_anchor']==n and F(a['radius_about_anchor'])==R and abs(delta)<=F(1,2)
        jets=[]
        for order in range(1,6):
            val=(F(0),F(0))
            for k in range(order,24):val=iadd(val,iscale(wt[n][k],F(factorial(k),factorial(k-order))*delta**(k-order)))
            rem=M24*abs(delta)**(24-order)/factorial(24-order);jets.append((val[0]-rem,val[1]+rem))
        assert [[str(lo),str(hi)]for lo,hi in jets]==a['anchor_derivative_intervals_orders_1_to_5']
        mu=[(lo+hi)/2 for lo,hi in jets];eps=[(hi-lo)/2 for lo,hi in jets];assert min(eps)>=0
        assert mu==list(map(F,a['anchor_derivative_midpoints']))and eps==list(map(F,a['anchor_derivative_errors']))
        cells=list(range(l//512,(u+511)//512));M6=max(grid6(k)for k in cells)
        assert a['whole_hull_w6_grid_cells']==cells and F(a['whole_hull_absolute_w6_bound'])==M6>=0
        d0=add(before,{():anchor},F(-1));assert pack(d0)==a['d0_polynomial']
        # Directly expand in formal theta(variable9), rather than using the producer binomial formula.
        path=add(d0,mul(h,{(9,):F(1)}),F(direction));powers=[{():F(1)}];integrated=[]
        for k in range(5):
            if k:powers.append(mul(powers[-1],path))
            integral={}
            for m,c in powers[k].items():
                theta_power=m.count(9);ym=tuple(v for v in m if v!=9)
                integral=add(integral,{ym:c/F(theta_power+1)})
            integrated.append(integral)
        assert [pack(v)for v in integrated]==a['integrated_theta_powers_degree_0_to_4']
        central={}
        for k in range(5):central=add(central,integrated[k],direction*mu[k]/factorial(k))
        error={():eps[0]+eps[1]*R}
        error=add(error,integrated[2],eps[2]/2+eps[3]*R/6)
        error=add(error,integrated[4],eps[4]/24+M6*R/120)
        assert pack(central)==a['signed_integrated_derivative_central_quartic']and pack(error)==a['integrated_error_dynamic_quartic']
        weight=F(edge['weight']);assert weight==F(a['weight'])>0;term=scale(add(central,error),weight)
        assert pack(term)==a['weighted_integrated_derivative_upper_quartic']
        assert F(a['expected_weighted_central'])==weight*expect(central)
        assert F(a['expected_weighted_error'])==weight*expect(error)and F(a['expected_weighted_upper'])==expect(term)
        total=add(total,term);central_total=add(central_total,central,weight);error_total=add(error_total,error,weight);checked+=1
    assert checked==8 and len(grid)==p['w6_grid_cells_rebuilt']==391 and len(total)==495 and pack(total)==p['upper_G_quartic']
    value=expect(total);assert value==F(p['expected_upper_G_at_latest_exact714'])>0 and not p['latest_exact714_separated_by_necessary_row']
    const=total.get((),F(0));coeff=[[idx[m]-1,str(-v)]for m,v in sorted(total.items(),key=lambda z:idx[z[0]])if m]
    row=p['candidate_unsoftened_row'];assert row['coefficients']==coeff and F(row['bound'])==const
    assert F(row['scale'])==max([F(1,1000),abs(const)]+[abs(F(v))for _,v in coeff])and row['meta']==['positive_divided_global_swap67_necessary']
    assert all(0<=k<714 for k,_ in coeff)and p['normalized_W_w6_Taylor_degree']==17 and p['normalized_W_w6_Taylor_terms']==18 and p['w6_remainder_power']==18
    for name,hsh in inputs.items():assert digest(ROOT/name)==hsh
    receipt={'scope':__doc__,'passed':True,'source_sha256':digest(Path(__file__)),'packet_sha256':SHA,
        'source_sha256_start':inputs,'source_sha256_end':inputs,'all_sources_unchanged':True,
        'positive_h_lower_bound':str(hl),'changed_edges':8,'shared_normalized_gap_variables':9,
        'whole_image_bounds_and_path_identity_checked':True,'anchor_derivative_orders_rebuilt':[1,2,3,4,5],
        'selected_normalized_W_w6_grid_cells_rebuilt':len(grid),'theta_integration_by_tenth_formal_variable':True,
        'upper_G_polynomial_terms':len(total),'candidate_row_no_energy_slack_coefficient':True,
        'expected_upper_G':str(value),'expected_upper_G_positive':True,
        'expected_central_including_pressure':str(expect(central_total)),'expected_error':str(expect(error_total)),
        'producer_imports':0,'solver_calls':0,'eigh_calls':0,'Lean_invocations':0,
        'actual_FTC_and_scalar_envelopes_newly_Lean_proved':False,'pseudo_point_separation_proven':False,
        'cell_exclusion_proven':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-began}
    if args.write_receipt:OUT.write_text(json.dumps(receipt,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({'passed':True,'edges':8,'grid_cells':len(grid),'terms':len(total),'expected_upper_G':float(value),
        'receipt_sha256':digest(OUT)if args.write_receipt else None,'seconds':receipt['seconds']}),flush=True)

if __name__=='__main__':
    assert __debug__
    main()
