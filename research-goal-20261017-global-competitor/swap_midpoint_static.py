"""One fixed adjacent-gap swap at the frozen parent's midpoint, no scan.

Choose swap(g5,g6) from the short/long gap boundary before evaluation.
It changes only vertex6, so every span not ending at vertex6 cancels.
Use the existing degree23 actual-w integer Taylor table and its M24
remainder.  No optimizer, new scalar table, moment model, or Lean.
"""
from pathlib import Path
from fractions import Fraction as F
from math import factorial
import gzip,hashlib,json,time
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent;PARENT=ROOT/'research-goal-20261017-quartic'
OUT=HERE/'swap-midpoint-static.json'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    assert not OUT.exists();began=time.monotonic()
    paths=[Path(__file__),PARENT/'quartic-files.json',PARENT/'quartic-model.json.gz',PARENT/'quartic-exact-primal.json',
        ROOT/'research-20261016-followup/window_reweight_rational.json',ROOT/'research-goal-20261016/window_normalized_interval.json',
        ROOT/'research-goal-20261016/window_normalized_interval.py',ROOT/'research-goal-20261016/cover_competitor_diagnostic.py']
    pins={p.relative_to(ROOT).as_posix():sha(p) for p in paths};model=json.loads(gzip.decompress(paths[2].read_bytes()));proof=json.loads(paths[3].read_bytes())
    params=json.loads(paths[4].read_bytes());table=json.loads(paths[5].read_bytes());assert table['source_sha256']==sha(paths[6]) and table['parameter_sha256']==sha(paths[4])
    coefficients={int(n):[tuple(map(F,v)) for v in row] for n,row in table['integer_w_Taylor_coefficients'].items()}
    assert len(coefficients)==33 and all(len(row)==24 for row in coefficients.values())
    g=list(map(F,model['normalized_gap_center']));radii=list(map(F,model['normalized_gap_radius']));mean=[v+r*F(y) for v,r,y in zip(g,radii,proof['rational_714_moments'][:9])]
    swapped=g.copy();swapped[5],swapped[6]=g[6],g[5];assert min(g)>=F(123,128) and min(swapped)>=F(123,128)
    M24=F(44,7)**24
    def w_interval(x):
        n=round(x);delta=x-n;assert n in coefficients and abs(delta)<=F(1,2)
        lo=hi=F(0)
        for l,u in reversed(coefficients[n]):
            a,b=lo*delta,hi*delta;lo,hi=min(a,b)+l,max(a,b)+u
        remainder=M24*abs(delta)**24/factorial(24)
        return lo-remainder,hi+remainder,n,str(remainder)
    den=params['denominator'];pressure=F(params['b_numerators'][5]-params['b_numerators'][6],den)*(g[6]-g[5])
    lo=hi=pressure;changed=[];cancelled=[]
    for i,j,a in params['a_upper']:
        if not a:continue
        old=sum(g[i:j]);new=sum(swapped[i:j])
        if i!=6 and j!=6:
            assert old==new;cancelled.append([i,j]);continue
        oldinterval=w_interval(old);newinterval=w_interval(new);weight=F(a,den)
        l=weight*(newinterval[0]-oldinterval[1]);u=weight*(newinterval[1]-oldinterval[0]);lo+=l;hi+=u
        changed.append({'edge':[i,j],'weight':str(weight),'old_span':str(old),'new_span':str(new),
            'old_w_interval':[str(v) for v in oldinterval[:2]],'new_w_interval':[str(v) for v in newinterval[:2]],
            'old_integer_Taylor_anchor':oldinterval[2],'new_integer_Taylor_anchor':newinterval[2],
            'old_M24_remainder':oldinterval[3],'new_M24_remainder':newinterval[3],
            'weighted_difference_interval':[str(l),str(u)]})
    assert len(changed)==9 and len(cancelled)==32
    final={p.relative_to(ROOT).as_posix():sha(p) for p in paths};assert final==pins
    out={'scope':__doc__,'status':'fixed_swap_midpoint_strictly_increases_F_stop' if lo>0 else 'fixed_swap_midpoint_decrease_hint' if hi<0 else 'fixed_swap_midpoint_interval_inconclusive_stop',
        'source_sha256_start':pins,'source_sha256_end':final,'all_sources_unchanged':True,'path':model['path'],
        'fixed_map':'swap physical gaps g5 and g6, zero-based; moves vertex6 only','selection_before_values':'boundary between first six short gaps and last three long gaps',
        'parent_midpoint':list(map(str,g)),'exact_714_point_physical_mean':list(map(str,mean)),
        'midpoint_competitor':list(map(str,swapped)),'pressure_difference':str(pressure),
        'unchanged_edges_cancelled':cancelled,'changed_edge_packets':changed,'difference_interval':[str(lo),str(hi)],
        'mathematical_quantity':'F(Tg)-F(g); global-minimizer necessity is >=0',
        'feasible_map_preserves_global_orthant':True,'map_need_not_preserve_artificial_parent_cell':True,
        'actual_function_Taylor_enclosures_assumed':True,'table_function':'actual w, 24 coefficients, degree23, remainder order24',
        'new_actual_scalar_Taylor_tables':0,'swap_candidates_tested':1,'optimizer_calls':0,'new_moment_model_built':False,'Lean_invocations':0,
        'exact_714_point_excluded':False,'cell_exclusion_proven':False,'new_zero_proportion_proven':False,
        'elapsed_milliseconds':int((time.monotonic()-began)*1000)}
    OUT.write_text(json.dumps(out,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({'status':out['status'],'difference_interval_hint':[float(lo),float(hi)],'changed_edges':9,'cancelled_edges':32,'elapsed_milliseconds':out['elapsed_milliseconds']}))
if __name__=='__main__':
    if not __debug__:raise RuntimeError('Assertions must remain enabled')
    main()
