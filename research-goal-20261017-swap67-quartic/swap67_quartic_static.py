"""One fixed global-competitor quartic row, at the frozen exact 714 point.

T exchanges gap coordinates 6 and 7 (zero based). Only vertex 7 moves.
Unchanged spans cancel exactly before any scalar enclosure is made. Each
remaining old/new span is a single affine polynomial in the SAME nine y.
No optimizer, new actual scalar table, parameter scan, or Lean invocation.
"""
from pathlib import Path
from fractions import Fraction as F
from math import factorial
import gzip,hashlib,json,time

HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
PARENT=ROOT/'research-goal-20261017-quartic';OLD=ROOT/'research-goal-20261016'
OUT=HERE/'swap67-quartic-static.json';SC=32768;DS=10**15
ALL=[(i,i+1) for i in range(9)]+[(i,j) for i in range(9) for j in range(i+2,10)]
LOOK={e:k for k,e in enumerate(ALL)}

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def add(p,q,s=F(1)):
    out=p.copy()
    for m,v in q.items():
        v=out.get(m,F(0))+s*v
        if v:out[m]=v
        else:out.pop(m,None)
    return out
def mul(p,q):
    out={}
    for m,a in p.items():
        for n,b in q.items():
            mon=tuple(sorted(m+n));assert len(mon)<=4
            out=add(out,{mon:a*b})
    return out
def scale(p,a):return {m:a*v for m,v in p.items() if a*v}
def at_zero(p):return p.get((),F(0))

class Interval:
    def __init__(self,l,u=None):self.l=F(l);self.u=F(l if u is None else u);assert self.l<=self.u
    def __add__(self,x):
        if not isinstance(x,Interval):x=Interval(x)
        return Interval(self.l+x.l,self.u+x.u)
    __radd__=__add__
    def __mul__(self,x):
        if not isinstance(x,Interval):x=Interval(x)
        v=[self.l*x.l,self.l*x.u,self.u*x.l,self.u*x.u]
        return Interval(min(v),max(v))
    __rmul__=__mul__

class IntegerJet:
    def __init__(self,wdoc,udoc):
        self.w={int(n):[Interval(*v) for v in row] for n,row in wdoc['integer_w_Taylor_coefficients'].items()}
        self.u={int(n):[Interval(*v) for v in row] for n,row in udoc['integer_taylor_coefficients'].items()}
        assert len(self.w)==len(self.u)==33 and set(map(len,self.w.values()))=={24} and set(map(len,self.u.values()))=={23}
        assert udoc['receipt']['grid_step']==64 and udoc['receipt']['order']==24
        self.M24=F(44,7)**24;self.cache={}
    def jets(self,p):
        n=round(p);d=p-n;assert abs(d)<=F(1,2) and n in self.w
        result=[]
        for j in range(5):
            value=Interval(0)
            for k in range(23,j-1,-1):value=value*d+self.w[n][k]*F(factorial(k),factorial(k-j))
            err=self.M24*abs(d)**(24-j)/factorial(24-j)
            result.append(Interval(value.l-err,value.u+err))
        return n,result
    def fifth_cell(self,k):
        if k not in self.cache:
            n=round(F(2*k+1,128));d=Interval(F(k,64)-n,F(k+1,64)-n);value=Interval(0)
            for j in range(22,3,-1):value=value*d+self.u[n][j]*F(factorial(j),factorial(j-4))
            rem=self.M24*F(1,2)**19/factorial(19)
            raw=max(abs(value.l-rem),abs(value.u+rem))*DS
            self.cache[k]=F(-((-raw.numerator)//raw.denominator),DS)
        return self.cache[k]
    def fifth(self,l,u):
        assert 0<=l<u<=32*SC
        ks=list(range(l//512,(u+511)//512));assert ks
        return max(self.fifth_cell(k) for k in ks),ks

def main():
    assert not OUT.exists();began=time.monotonic()
    paths=[Path(__file__),PARENT/'quartic-model.json.gz',PARENT/'quartic-files.json',PARENT/'quartic-exact-primal.json',
        PARENT/'quartic-result-replay.json',OLD/'window_normalized_interval.json',OLD/'window_normalized_interval.py',
        OLD/'cover_newjet.json',ROOT/'research-20261016-followup/window_reweight_rational.json',
        ROOT/'StructuralGoal20261016/WindowMinimizerCover.lean',
        ROOT/'research-goal-20261017-adjacent-swap-family/swap-family-files.json']
    pins={p.relative_to(ROOT).as_posix():sha(p) for p in paths}
    model=json.loads(gzip.decompress(paths[1].read_bytes()));manifest=json.loads(paths[2].read_bytes())
    for row in manifest['package_files']+manifest['dependency_files']:assert sha(ROOT/row['path'])==row['sha256']
    proof=json.loads(paths[3].read_bytes());prior=json.loads(paths[4].read_bytes());wdoc=json.loads(paths[5].read_bytes());udoc=json.loads(paths[7].read_bytes());params=json.loads(paths[8].read_bytes())
    assert wdoc['source_sha256']==sha(paths[6]) and wdoc['parameter_sha256']==sha(paths[8])==udoc['receipt']['parameter_sha256']
    assert prior['status']=='strict_exact_shared_quartic_outer_relaxation_independently_verified'
    assert proof['status']=='strict_exact_shared_quartic_outer_relaxation_feasible' and model['path']==proof['path']=='r001000001000100110011001'
    mon=[tuple(m) for m in model['monomials']];mi={m:k for k,m in enumerate(mon)};moments=[F(1)]+list(map(F,proof['rational_714_moments']))
    assert len(mon)==len(moments)==715 and mon[0]==()
    def pack(p):return [[mi[m],str(v)] for m,v in sorted(p.items(),key=lambda z:mi[z[0]])]
    def expect(p):return sum(v*moments[mi[m]] for m,v in p.items())
    state=model['cell'];center=list(map(F,model['normalized_gap_center']));radius=list(map(F,model['normalized_gap_radius']))
    assert all(F(l,SC)>F(123,128) for l in state[0][:9])
    gap=[{():center[r],(r,):radius[r]} for r in range(9)]
    perm=list(range(9));perm[6],perm[7]=perm[7],perm[6]
    def polynomial(indices):
        out={}
        for r in indices:out=add(out,gap[r])
        return out
    def bounds(i,j):
        if i==j:return (0,0)
        assert i<j;k=LOOK[i,j];return state[0][k],state[1][k]
    def image_bounds(i,j):
        indices=perm[i:j];sources=[{'identity':'sum_permuted_gap_boxes','lower':sum(state[0][r] for r in indices),'upper':sum(state[1][r] for r in indices)}]
        if j==7:
            l,u=bounds(i,6);sources.append({'identity':'span(i,6)+g7','lower':l+state[0][7],'upper':u+state[1][7]})
            l,u=bounds(i,8);sources.append({'identity':'span(i,8)-g6','lower':l-state[1][6],'upper':u-state[0][6]})
        else:
            assert i==7;l,u=bounds(8,j);sources.append({'identity':'g6+span(8,j)','lower':state[0][6]+l,'upper':state[1][6]+u})
            l,u=bounds(6,j);sources.append({'identity':'span(6,j)-g7','lower':l-state[1][7],'upper':u-state[0][7]})
        l=max(s['lower'] for s in sources);u=min(s['upper'] for s in sources);assert l<u
        return l,u,sources
    oracle=IntegerJet(wdoc,udoc)
    def scalar_packet(poly,l,u):
        p=F(l+u,2*SC);R=F(u-l,2*SC);assert F(l,SC)<=p<=F(u,SC)
        n,jets=oracle.jets(p);mu=[(v.l+v.u)/2 for v in jets];eps=[(v.u-v.l)/2 for v in jets]
        M5,ks=oracle.fifth(l,u);d=add(poly,{():p},F(-1));powers=[{():F(1)}]
        for _ in range(4):powers.append(mul(powers[-1],d))
        central={}
        for k in range(5):central=add(central,powers[k],mu[k]/factorial(k))
        error={():eps[0]+eps[1]*R}
        error=add(error,powers[2],eps[2]/2+eps[3]*R/6)
        error=add(error,powers[4],eps[4]/24+M5*R/120)
        upper=add(central,error);lower=add(central,error,F(-1))
        return {'whole_span_integer_bounds':[l,u],'whole_span_rational_bounds':[str(F(l,SC)),str(F(u,SC))],
            'anchor':str(p),'integer_jet_anchor':n,'anchor_is_whole_span_midpoint':True,'radius_about_anchor':str(R),
            'anchor_derivative_intervals_orders_0_to_4':[[str(v.l),str(v.u)] for v in jets],
            'anchor_derivative_midpoints':list(map(str,mu)),'anchor_derivative_errors':list(map(str,eps)),
            'whole_span_absolute_w5_bound':str(M5),'whole_span_w5_grid_cells':ks,'span_polynomial':pack(poly),
            'd_polynomial':pack(d),'central_quartic':pack(central),'nonnegative_error_polynomial':pack(error),
            'scalar_upper_quartic':pack(upper),'scalar_lower_quartic':pack(lower)},upper,lower
    den=params['denominator'];pressure=scale(add(gap[7],gap[6],F(-1)),F(params['b_numerators'][6]-params['b_numerators'][7],den))
    upper=pressure;changed=[];cancelled=[]
    for i,j,a in params['a_upper']:
        if not a:continue
        assert a>0
        oldpoly=polynomial(range(i,j));newpoly=polynomial(perm[i:j])
        if i!=7 and j!=7:
            assert oldpoly==newpoly;cancelled.append([i,j]);continue
        l,u=bounds(i,j);old,_,oldlower=scalar_packet(oldpoly,l,u)
        l,u,sources=image_bounds(i,j);new,newupper,_=scalar_packet(newpoly,l,u)
        weight=F(a,den);difference=scale(add(newupper,oldlower,F(-1)),weight);upper=add(upper,difference)
        changed.append({'edge':[i,j],'weight':str(weight),'image_bound_sources':sources,'old':old,'new':new,
            'weighted_difference_upper_quartic':pack(difference),'expected_weighted_difference_upper':str(expect(difference))})
    value=expect(upper);midpoint=at_zero(upper);assert len(changed)==8 and len(cancelled)==33
    final={p.relative_to(ROOT).as_posix():sha(p) for p in paths};assert final==pins
    out={'scope':__doc__,'status':'fixed_swap67_shared_quartic_upper_difference_evaluated',
        'source_sha256_start':pins,'source_sha256_end':final,'all_sources_unchanged':True,'path':model['path'],
        'swap_zero_based':[6,7],'moved_vertex':7,'permutation':perm,'normalized_gap_center':list(map(str,center)),
        'normalized_gap_radius':list(map(str,radius)),'monomials':[list(m) for m in mon],'SEP':'123/128','scale':SC,
        'global_minimum_interface':'WindowMinimizerCover.Relevant.2.2 compares Fw24 g with every Orthant SEP y, even if y is not ordered.',
        'unchanged_edges_cancelled':cancelled,'changed_edge_packets':changed,'pressure_difference_polynomial':pack(pressure),
        'difference_upper_quartic':pack(upper),'expected_upper_difference_at_exact714':str(value),
        'midpoint_upper_difference':str(midpoint),'exact714_excluded_by_this_necessary_row':value<0,
        'necessary_row_direction':'Global minimum implies 0<=F(Tg)-F(g)<=difference_upper_quartic, hence its moment expectation must be nonnegative.',
        'actual_analytic_inputs':['integer_w_Taylor_coefficients enclose actual w^(j)(n)/j! for j=0..23',
            'integer_taylor_coefficients enclose actual w^(j+1)(n)/j! for j=0..22','global |w24|<=(44/7)^24',
            'actual gap vector belongs to parent DBM cell','all 41 ledger weights are nonnegative','global orthant minimum, not just cell-local KKT'],
        'actual_analytic_inputs_newly_Lean_proved':False,'actual_w_scalar_sampling_positions_added':0,
        'new_integer_Taylor_tables':0,'w5_grid_cells_rebuilt':len(oracle.cache),'solver_calls':0,'Lean_invocations':0,
        'cell_exclusion_proven':False,'new_zero_proportion_proven':False,'elapsed_milliseconds':int((time.monotonic()-began)*1000)}
    OUT.write_text(json.dumps(out,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({'status':out['status'],'expected_upper_difference':float(value),'exact714_excluded':value<0,
        'midpoint_upper':float(midpoint),'changed_edges':len(changed),'cancelled_edges':len(cancelled),
        'w5_grid_cells':len(oracle.cache),'elapsed_milliseconds':out['elapsed_milliseconds']}),flush=True)
if __name__=='__main__':
    if not __debug__:raise RuntimeError('Assertions must remain enabled')
    main()
