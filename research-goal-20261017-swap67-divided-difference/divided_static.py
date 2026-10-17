"""One positive-divided global swap67 comparison, shared degree four.

Prove h=g6-g7>=117/32768>0 from the original parent cell. The exact
swap difference is h*G, with derivative integrals over common real paths.
Use normalized-W jets1..5 and q6,d17 interval bounds on w6, integrate
every theta monomial exactly BEFORE evaluating the fixed714 moments.
No solver, independent endpoint averaging, midpoint division, or Lean.
"""
from pathlib import Path
from fractions import Fraction as F
from math import comb,factorial
import gzip,hashlib,importlib.util,json,time
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
FAMILY=ROOT/'research-goal-20261017-swap-family-quartic';PARENT=ROOT/'research-goal-20261017-quartic'
OLD=ROOT/'research-goal-20261016';SINGLE=ROOT/'research-goal-20261017-swap67-quartic'
OUT=HERE/'divided-static.json';SC=32768;DS=10**15
spec=importlib.util.spec_from_file_location('frozen_interval_algebra',SINGLE/'swap67_quartic_static.py')
algebra=importlib.util.module_from_spec(spec);spec.loader.exec_module(algebra)
Interval=algebra.Interval;add=algebra.add;mul=algebra.mul;scale=algebra.scale

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
class WJet:
    def __init__(self,doc):
        self.w={int(n):[Interval(*v) for v in row] for n,row in doc['integer_w_Taylor_coefficients'].items()}
        assert len(self.w)==33 and set(map(len,self.w.values()))=={24}
        self.M24=F(44,7)**24;self.cache={}
    def anchor(self,p):
        n=round(p);d=p-n;assert 1<=n<=32 and abs(d)<=F(1,2);jets=[]
        for j in range(1,6):
            value=Interval(0)
            for k in range(23,j-1,-1):value=value*d+self.w[n][k]*F(factorial(k),factorial(k-j))
            rem=self.M24*abs(d)**(24-j)/factorial(24-j)
            jets.append(Interval(value.l-rem,value.u+rem))
        return n,jets
    def sixth_cell(self,k):
        if k not in self.cache:
            n=round(F(2*k+1,128));assert 1<=n<=32
            d=Interval(F(k,64)-n,F(k+1,64)-n);assert F(-1,2)<=d.l<=d.u<=F(1,2)
            value=Interval(0)
            for j in range(23,5,-1):value=value*d+self.w[n][j]*F(factorial(j),factorial(j-6))
            rem=self.M24*F(1,2)**18/factorial(18)
            raw=max(abs(value.l-rem),abs(value.u+rem))*DS
            self.cache[k]=F(-((-raw.numerator)//raw.denominator),DS)
        return self.cache[k]
    def sixth(self,l,u):
        assert 0<=l<u<=32*SC;ks=list(range(l//512,(u+511)//512));assert ks
        return max(self.sixth_cell(k) for k in ks),ks

def main():
    assert not OUT.exists();began=time.monotonic()
    paths=[Path(__file__),SINGLE/'swap67_quartic_static.py',FAMILY/'swap-family-files.json',
        FAMILY/'swap-family-normalized.json.gz',FAMILY/'swap-family-normalized-build.json',
        FAMILY/'swap-family-exact-primal.json',FAMILY/'swap-family-result-replay.json',PARENT/'quartic-model.json.gz',
        OLD/'window_normalized_interval.json',OLD/'window_normalized_interval.py',
        ROOT/'research-20261016-followup/window_reweight_rational.json',ROOT/'StructuralGoal20261016/WindowMinimizerCover.lean',
        ROOT/'StructuralGoal20261016/WindowGlobalCompetitor.lean',ROOT/'StructuralGoal20261016/WindowCellDerivative.lean']
    pins={p.relative_to(ROOT).as_posix():sha(p) for p in paths};manifest=json.loads(paths[2].read_bytes())
    for row in manifest['package_files']+manifest['dependency_files']:assert sha(ROOT/row['path'])==row['sha256']
    raw=gzip.decompress(paths[3].read_bytes());family=json.loads(raw);build=json.loads(paths[4].read_bytes());proof=json.loads(paths[5].read_bytes());replay=json.loads(paths[6].read_bytes())
    assert sha(paths[3])==build['packet_compressed_sha256'] and hashlib.sha256(raw).hexdigest()==build['packet_uncompressed_sha256']
    parent=json.loads(gzip.decompress(paths[7].read_bytes()));wdoc=json.loads(paths[8].read_bytes());params=json.loads(paths[10].read_bytes())
    assert wdoc['source_sha256']==sha(paths[9]) and wdoc['parameter_sha256']==sha(paths[10])
    assert proof['exact_eight_swap_quartic_outer_relaxation_feasible'] and replay['passed']
    assert parent['path']==family['path']==proof['path']=='r001000001000100110011001'
    mon=[tuple(m) for m in family['monomials']];index={m:k for k,m in enumerate(mon)};mom=[F(1)]+list(map(F,proof['rational_714_moments']))
    assert family['monomials']==parent['monomials'] and len(mon)==len(mom)==715
    def pack(p):return [[index[m],str(v)] for m,v in sorted(p.items(),key=lambda z:index[z[0]])]
    def unpack(p):return {mon[k]:F(v) for k,v in p}
    def expect(p):return sum(v*mom[index[m]] for m,v in p.items())
    center=list(map(F,parent['normalized_gap_center']));radius=list(map(F,parent['normalized_gap_radius']));state=parent['cell']
    gap=[{():center[r],(r,):radius[r]} for r in range(9)];h=add(gap[6],gap[7],F(-1))
    h_lower=F(state[0][6]-state[1][7],SC);assert h_lower==F(117,32768)>0
    assert state[0][6]==64179 and state[1][7]==64062
    h_powers=[{():F(1)}]
    for _ in range(4):h_powers.append(mul(h_powers[-1],h))
    item=family['maps'][6];assert item['swap_zero_based']==[6,7] and len(item['changed_edge_packets'])==8
    den=params['denominator'];pressure=F(params['b_numerators'][7]-params['b_numerators'][6],den)
    assert scale(h,pressure)==unpack(item['pressure_difference_polynomial'])
    oracle=WJet(wdoc);upper={():pressure};packets=[]
    for edge in item['changed_edge_packets']:
        i,j=edge['edge'];sign=-1 if j==7 else 1;assert j==7 or i==7
        old=family['scalar_packets'][edge['old_scalar_packet']];new=family['scalar_packets'][edge['new_scalar_packet']]
        s=unpack(old['span_polynomial']);t=unpack(new['span_polynomial']);assert add(t,s,F(-1))==scale(h,F(sign))
        oldlo,oldhi=old['whole_span_integer_bounds'];newlo,newhi=new['whole_span_integer_bounds']
        l,u=min(oldlo,newlo),max(oldhi,newhi);p=F(l+u,2*SC);R=F(u-l,2*SC);assert R>0
        n,jets=oracle.anchor(p);mu=[(v.l+v.u)/2 for v in jets];eps=[(v.u-v.l)/2 for v in jets];M6,ks=oracle.sixth(l,u)
        d0=add(s,{():p},F(-1));d0powers=[{():F(1)}]
        for _ in range(4):d0powers.append(mul(d0powers[-1],d0))
        integrated=[]
        for k in range(5):
            value={}
            for r in range(k+1):
                coefficient=F(comb(k,r)*sign**r,r+1)
                value=add(value,mul(d0powers[k-r],h_powers[r]),coefficient)
            integrated.append(value)
        central={}
        for k in range(5):central=add(central,integrated[k],sign*mu[k]/factorial(k))
        # A single common theta-path error is integrated exactly. Odd
        # coefficient errors use the same proved whole-hull radius R.
        error={():eps[0]+eps[1]*R}
        error=add(error,integrated[2],eps[2]/2+eps[3]*R/6)
        error=add(error,integrated[4],eps[4]/24+M6*R/120)
        term=add(central,error);weight=F(edge['weight']);assert weight>0;upper=add(upper,term,weight)
        packets.append({'edge':[i,j],'path_direction_and_derivative_sign':sign,'weight':str(weight),
            'old_span_polynomial':pack(s),'new_span_polynomial':pack(t),'d0_polynomial':pack(d0),
            'old_whole_span_integer_bounds':[oldlo,oldhi],'new_whole_span_integer_bounds':[newlo,newhi],
            'whole_path_hull_integer_bounds':[l,u],'anchor':str(p),'integer_jet_anchor':n,'radius_about_anchor':str(R),
            'anchor_derivative_intervals_orders_1_to_5':[[str(v.l),str(v.u)] for v in jets],
            'anchor_derivative_midpoints':list(map(str,mu)),'anchor_derivative_errors':list(map(str,eps)),
            'whole_hull_absolute_w6_bound':str(M6),'whole_hull_w6_grid_cells':ks,
            'integrated_theta_powers_degree_0_to_4':[pack(v) for v in integrated],
            'signed_integrated_derivative_central_quartic':pack(central),'integrated_error_dynamic_quartic':pack(error),
            'weighted_integrated_derivative_upper_quartic':pack(scale(term,weight)),
            'expected_weighted_central':str(weight*expect(central)),'expected_weighted_error':str(weight*expect(error)),
            'expected_weighted_upper':str(weight*expect(term))})
    value=expect(upper);constant=upper.get((),F(0));coeff=[[index[m]-1,str(-v)] for m,v in sorted(upper.items(),key=lambda z:index[z[0]]) if m]
    divisor=max([F(1,1000),abs(constant)]+[abs(F(v)) for _,v in coeff])
    final={p.relative_to(ROOT).as_posix():sha(p) for p in paths};assert final==pins
    out={'scope':__doc__,'status':'fixed_positive_divided_swap67_upper_integral_evaluated',
        'source_sha256_start':pins,'source_sha256_end':final,'all_sources_unchanged':True,'path':family['path'],
        'swap_zero_based':[6,7],'same_normalized_variables':9,'monomials':[list(m) for m in mon],
        'positive_divisor_polynomial':pack(h),'divisor_lower_bound':str(h_lower),
        'original_gap6_lower_integer':state[0][6],'original_gap7_upper_integer':state[1][7],'scale':SC,
        'pressure_difference_divided_by_h':str(pressure),'scalar_path_packets':packets,'upper_G_quartic':pack(upper),
        'expected_upper_G_at_latest_exact714':str(value),'latest_exact714_separated_by_necessary_row':value<0,
        'candidate_unsoftened_row':{'coefficients':coeff,'bound':str(constant),'scale':str(divisor),'meta':['positive_divided_global_swap67_necessary']},
        'exact_actual_identity':'Fw24(Tg)-Fw24(g)=h*((b7-b6)+sum_left(-a*integral_0^1 wprime(s-theta*h))+sum_right(a*integral_0^1 wprime(s+theta*h)))',
        'necessary_direction':'Relevant and h>0 imply actual G>=0; upper_G_quartic>=G implies moment expectation>=0.',
        'theta_integrals':'Every theta^r is integrated exactly as 1/(r+1), with all original y correlations retained.',
        'normalized_W_w6_Taylor_degree':17,'normalized_W_w6_Taylor_terms':18,'w6_remainder_power':18,
        'w6_grid_cells_rebuilt':len(oracle.cache),'M6_dynamic_payment':'M6*R*integral(d(theta)^4)/120',
        'new_actual_scalar_sampling_positions':0,'solver_calls':0,'Lean_invocations':0,
        'actual_FTC_and_concrete_scalar_envelopes_newly_Lean_proved':False,
        'cell_exclusion_proven':False,'new_zero_proportion_proven':False,'elapsed_milliseconds':int((time.monotonic()-began)*1000)}
    OUT.write_text(json.dumps(out,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({'status':out['status'],'expected_upper_G':float(value),'latest_exact714_separated':value<0,
        'polynomial_terms':len(upper),'w6_grid_cells':len(oracle.cache),'elapsed_milliseconds':out['elapsed_milliseconds']}),flush=True)
if __name__=='__main__':
    if not __debug__:raise RuntimeError('Assertions must remain enabled')
    main()
