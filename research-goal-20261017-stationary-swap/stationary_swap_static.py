"""One stationary second-divided swap comparison, shared degree four.

For swap67, v=-e6+e7 and h=g6-g7>0. At an actual free stationary
global minimum, F(Tg)-F(g)=h^2 integral_0^1 (1-t) v'HessF(g+thv)v dt.
Only the eight changed positive edges occur; pressure disappears exactly.
Build ONE fixed quartic upper envelope of that curvature integral using
normalized-W jets2..6 and q7,d16 whole-path bounds. No solver or Lean.
"""
from pathlib import Path
from fractions import Fraction as F
from math import comb, factorial
import gzip, hashlib, importlib.util, json, time

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
FAMILY=ROOT/'research-goal-20261017-swap-family-quartic'
PARENT=ROOT/'research-goal-20261017-quartic'
OLD=ROOT/'research-goal-20261016'
HELPER=ROOT/'research-goal-20261017-swap67-quartic/swap67_quartic_static.py'
OUT=HERE/'stationary-swap-static.json'
SC=32768
DS=10**15
spec=importlib.util.spec_from_file_location('stationary_swap_frozen_algebra', HELPER)
algebra=importlib.util.module_from_spec(spec)
spec.loader.exec_module(algebra)
Interval=algebra.Interval
add=algebra.add
mul=algebra.mul
scale=algebra.scale


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


class WJet:
    def __init__(self, doc):
        self.w={int(n):[Interval(*v) for v in row]
                for n,row in doc['integer_w_Taylor_coefficients'].items()}
        assert len(self.w)==33 and set(map(len,self.w.values()))=={24}
        self.M24=F(44,7)**24
        self.cache={}

    def anchor(self, p):
        n=round(p)
        d=p-n
        assert 1<=n<=32 and abs(d)<=F(1,2)
        jets=[]
        for q in range(2,7):
            value=Interval(0)
            for j in range(23,q-1,-1):
                value=value*d+self.w[n][j]*F(factorial(j),factorial(j-q))
            rem=self.M24*abs(d)**(24-q)/factorial(24-q)
            jets.append(Interval(value.l-rem,value.u+rem))
        return n,jets

    def seventh_cell(self, k):
        if k not in self.cache:
            n=round(F(2*k+1,128))
            d=Interval(F(k,64)-n,F(k+1,64)-n)
            assert 1<=n<=32 and F(-1,2)<=d.l<=d.u<=F(1,2)
            value=Interval(0)
            for j in range(23,6,-1):
                value=value*d+self.w[n][j]*F(factorial(j),factorial(j-7))
            rem=self.M24*F(1,2)**17/factorial(17)
            raw=max(abs(value.l-rem),abs(value.u+rem))*DS
            self.cache[k]=F(-((-raw.numerator)//raw.denominator),DS)
        return self.cache[k]

    def seventh(self,l,u):
        assert 0<=l<u<=32*SC
        ks=list(range(l//512,(u+511)//512))
        assert ks
        return max(self.seventh_cell(k) for k in ks),ks


def main():
    assert not OUT.exists()
    began=time.monotonic()
    paths=[Path(__file__),HELPER,FAMILY/'swap-family-files.json',
        FAMILY/'swap-family-normalized.json.gz',FAMILY/'swap-family-normalized-build.json',
        FAMILY/'swap-family-exact-primal.json',FAMILY/'swap-family-result-replay.json',
        PARENT/'quartic-model.json.gz',OLD/'window_normalized_interval.json',
        OLD/'window_normalized_interval.py',
        ROOT/'research-20261016-followup/window_reweight_rational.json',
        ROOT/'StructuralGoal20261016/WindowMinimizerCover.lean',
        ROOT/'StructuralGoal20261016/WindowGlobalCompetitor.lean',
        ROOT/'StructuralGoal20261016/WindowCellDerivative.lean']
    pins={p.relative_to(ROOT).as_posix():sha(p) for p in paths}
    manifest=json.loads(paths[2].read_bytes())
    for row in manifest['package_files']+manifest['dependency_files']:
        assert sha(ROOT/row['path'])==row['sha256']
    raw=gzip.decompress(paths[3].read_bytes())
    family=json.loads(raw)
    build=json.loads(paths[4].read_bytes())
    proof=json.loads(paths[5].read_bytes())
    replay=json.loads(paths[6].read_bytes())
    assert sha(paths[3])==build['packet_compressed_sha256']
    assert hashlib.sha256(raw).hexdigest()==build['packet_uncompressed_sha256']
    assert proof['exact_eight_swap_quartic_outer_relaxation_feasible'] and replay['passed']
    parent=json.loads(gzip.decompress(paths[7].read_bytes()))
    wdoc=json.loads(paths[8].read_bytes())
    assert wdoc['source_sha256']==sha(paths[9]) and wdoc['parameter_sha256']==sha(paths[10])
    assert parent['path']==family['path']==proof['path']=='r001000001000100110011001'
    mon=[tuple(m) for m in family['monomials']]
    index={m:k for k,m in enumerate(mon)}
    mom=[F(1)]+list(map(F,proof['rational_714_moments']))
    assert len(mon)==len(mom)==715 and family['monomials']==parent['monomials']

    def pack(poly):
        return [[index[m],str(v)] for m,v in sorted(poly.items(),key=lambda z:index[z[0]])]

    def unpack(poly):
        return {mon[k]:F(v) for k,v in poly}

    def expect(poly):
        return sum(v*mom[index[m]] for m,v in poly.items())

    center=list(map(F,parent['normalized_gap_center']))
    radius=list(map(F,parent['normalized_gap_radius']))
    state=parent['cell']
    assert all(l>123*SC//128 for l in state[0][:9])
    gap=[{():center[r],(r,):radius[r]} for r in range(9)]
    h=add(gap[6],gap[7],F(-1))
    h_lower=F(state[0][6]-state[1][7],SC)
    assert h_lower==F(117,32768)>0
    hp=[{():F(1)}]
    for _ in range(4):
        hp.append(mul(hp[-1],h))
    item=family['maps'][6]
    assert item['swap_zero_based']==[6,7] and len(item['changed_edge_packets'])==8
    oracle=WJet(wdoc)
    upper={}
    packets=[]
    for edge in item['changed_edge_packets']:
        i,j=edge['edge']
        sign=-1 if j==7 else 1
        assert j==7 or i==7
        old=family['scalar_packets'][edge['old_scalar_packet']]
        new=family['scalar_packets'][edge['new_scalar_packet']]
        s=unpack(old['span_polynomial'])
        t=unpack(new['span_polynomial'])
        assert add(t,s,F(-1))==scale(h,F(sign))
        l=min(old['whole_span_integer_bounds'][0],new['whole_span_integer_bounds'][0])
        u=max(old['whole_span_integer_bounds'][1],new['whole_span_integer_bounds'][1])
        p=F(l+u,2*SC)
        R=F(u-l,2*SC)
        n,jets=oracle.anchor(p)
        mu=[(q.l+q.u)/2 for q in jets]
        eps=[(q.u-q.l)/2 for q in jets]
        M7,ks=oracle.seventh(l,u)
        d0=add(s,{():p},F(-1))
        dp=[{():F(1)}]
        for _ in range(4):
            dp.append(mul(dp[-1],d0))
        integrated=[]
        for k in range(5):
            value={}
            for r in range(k+1):
                coefficient=F(comb(k,r)*sign**r,(r+1)*(r+2))
                value=add(value,mul(dp[k-r],hp[r]),coefficient)
            integrated.append(value)
        assert integrated[0]=={():F(1,2)}
        central={}
        for k in range(5):
            central=add(central,integrated[k],mu[k]/factorial(k))
        error={():F(1,2)*(eps[0]+eps[1]*R)}
        error=add(error,integrated[2],eps[2]/2+eps[3]*R/6)
        error=add(error,integrated[4],eps[4]/24+M7*R/120)
        weight=F(edge['weight'])
        assert weight>0
        term=scale(add(central,error),weight)
        upper=add(upper,term)
        packets.append({'edge':[i,j],'path_direction':sign,'weight':str(weight),
            'whole_path_hull_integer_bounds':[l,u],
            'old_span_polynomial':pack(s),'new_span_polynomial':pack(t),
            'd0_polynomial':pack(d0),'anchor':str(p),'radius_about_anchor':str(R),
            'integer_jet_anchor':n,
            'anchor_derivative_intervals_orders_2_to_6':[[str(q.l),str(q.u)] for q in jets],
            'anchor_derivative_midpoints':list(map(str,mu)),
            'anchor_derivative_errors':list(map(str,eps)),
            'whole_hull_absolute_w7_bound':str(M7),'whole_hull_w7_grid_cells':ks,
            'integrals_one_minus_theta_times_d_powers':[pack(q) for q in integrated],
            'central_quartic':pack(central),'nonnegative_error_quartic':pack(error),
            'weighted_upper_quartic':pack(term),
            'expected_weighted_central':str(weight*expect(central)),
            'expected_weighted_error':str(weight*expect(error)),
            'expected_weighted_upper':str(expect(term))})
    value=expect(upper)
    coeff=[[index[m]-1,str(-v)] for m,v in sorted(upper.items(),key=lambda z:index[z[0]]) if m]
    constant=upper.get((),F(0))
    divisor=max([F(1,1000),abs(constant)]+[abs(F(v)) for _,v in coeff])
    final={p.relative_to(ROOT).as_posix():sha(p) for p in paths}
    assert final==pins
    out={'scope':__doc__,'status':'fixed_stationary_second_divided_swap67_upper_evaluated',
        'path':family['path'],'source_sha256_start':pins,'source_sha256_end':final,
        'all_sources_unchanged':True,'swap_zero_based':[6,7],
        'same_underlying_normalized_variables':9,'monomials':[list(m) for m in mon],
        'positive_h_polynomial':pack(h),'positive_h_lower_bound':str(h_lower),
        'all_nine_coordinates_strictly_above_SEP':True,
        'exact_stationary_identity':'F(Tg)-F(g)=h^2*sum_changed a*integral_0^1 (1-theta)*wsecond(s+sign*theta*h)',
        'additional_actual_premise':'DF(g)(-e6+e7)=0 at the putative free global minimum',
        'necessary_direction':'Global minimality and h>0 imply curvature integral>=0; its upper envelope must therefore be>=0.',
        'pressure_terms_disappear_exactly':True,
        'integration_identity':'integral_0^1 (1-theta)*theta^r=1/((r+1)*(r+2))',
        'scalar_path_packets':packets,'upper_stationary_curvature_quartic':pack(upper),
        'expected_upper_at_latest_exact714':str(value),
        'expected_total_central':str(sum(F(q['expected_weighted_central']) for q in packets)),
        'expected_total_error':str(sum(F(q['expected_weighted_error']) for q in packets)),
        'latest_exact714_separated':value<0,
        'candidate_unsoftened_row':{'coefficients':coeff,'bound':str(constant),'scale':str(divisor),
            'meta':['stationary_second_divided_global_swap67_necessary']},
        'normalized_W_w7_Taylor_degree':16,'normalized_W_w7_Taylor_terms':17,
        'w7_remainder_power':17,'w7_grid_cells_rebuilt':len(oracle.cache),
        'new_actual_scalar_sampling_positions':0,'solver_calls':0,'Lean_invocations':0,
        'actual_Taylor_FTC_and_concrete_envelopes_newly_Lean_proved':False,
        'cell_exclusion_proven':False,'new_zero_proportion_proven':False,
        'elapsed_milliseconds':int((time.monotonic()-began)*1000)}
    OUT.write_text(json.dumps(out,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({'status':out['status'],'expected_upper':float(value),
        'expected_central':float(F(out['expected_total_central'])),
        'expected_error':float(F(out['expected_total_error'])),
        'separated':value<0,'polynomial_terms':len(upper),
        'w7_grid_cells':len(oracle.cache),'elapsed_milliseconds':out['elapsed_milliseconds']}),flush=True)


if __name__=='__main__':
    if not __debug__:
        raise RuntimeError('Assertions must remain enabled')
    main()
