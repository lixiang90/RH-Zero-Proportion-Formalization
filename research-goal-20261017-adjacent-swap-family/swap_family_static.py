"""The fixed complete family of eight adjacent swaps at one exact midpoint.

This is a finite family of global-minimizer necessary conditions, not a
chosen best map promoted to a global statement.  Exactly the eight maps,
one parent midpoint, old actual-w Taylor table, no optimizer or new model.
"""
from pathlib import Path
from fractions import Fraction as F
from math import factorial
import gzip,hashlib,json,time
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
OUT=HERE/'swap-family-static.json'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    assert not OUT.exists();began=time.monotonic()
    paths=[Path(__file__),ROOT/'research-goal-20261017-quartic/quartic-model.json.gz',
        ROOT/'research-goal-20261017-quartic/quartic-files.json',ROOT/'research-20261016-followup/window_reweight_rational.json',
        ROOT/'research-goal-20261016/window_normalized_interval.json',ROOT/'research-goal-20261016/window_normalized_interval.py',
        ROOT/'research-goal-20261017-global-competitor/swap-files.json']
    pins={p.relative_to(ROOT).as_posix():sha(p) for p in paths};model=json.loads(gzip.decompress(paths[1].read_bytes()));params=json.loads(paths[3].read_bytes());table=json.loads(paths[4].read_bytes())
    assert table['source_sha256']==sha(paths[5]) and table['parameter_sha256']==sha(paths[3])
    coefficients={int(n):[tuple(map(F,v)) for v in row] for n,row in table['integer_w_Taylor_coefficients'].items()}
    assert len(coefficients)==33 and all(len(row)==24 for row in coefficients.values())
    g=list(map(F,model['normalized_gap_center']));assert min(g)>F(123,128);cache={};evaluations=0;M24=F(44,7)**24
    def w_interval(x):
        nonlocal evaluations
        if x not in cache:
            n=round(x);d=x-n;assert n in coefficients and abs(d)<=F(1,2);lo=hi=F(0)
            for l,u in reversed(coefficients[n]):
                a,b=lo*d,hi*d;lo,hi=min(a,b)+l,max(a,b)+u
            error=M24*abs(d)**24/factorial(24);cache[x]=(lo-error,hi+error,n,str(error));evaluations+=1
        return cache[x]
    rows=[];den=params['denominator']
    for r in range(8):
        T=g.copy();T[r],T[r+1]=g[r+1],g[r];assert min(T)>F(123,128);vertex=r+1;delta=g[r+1]-g[r]
        pressure=F(params['b_numerators'][r]-params['b_numerators'][r+1],den)*delta;lo=hi=pressure;changed=[];cancelled=[]
        for i,j,a in params['a_upper']:
            if not a:continue
            x,y=sum(g[i:j]),sum(T[i:j])
            if i!=vertex and j!=vertex:assert x==y;cancelled.append([i,j]);continue
            old,new=w_interval(x),w_interval(y);weight=F(a,den);dl=weight*(new[0]-old[1]);du=weight*(new[1]-old[0]);lo+=dl;hi+=du
            changed.append({'edge':[i,j],'old_span':str(x),'new_span':str(y),'weight':str(weight),
                'old_w_interval':list(map(str,old[:2])),'new_w_interval':list(map(str,new[:2])),
                'old_integer_anchor':old[2],'new_integer_anchor':new[2],'old_remainder':old[3],'new_remainder':new[3],
                'weighted_difference_interval':[str(dl),str(du)]})
        sign='negative' if hi<0 else 'positive' if lo>0 else 'inconclusive'
        rows.append({'swap':[r,r+1],'moved_vertex':vertex,'pressure_difference':str(pressure),'difference_interval':[str(lo),str(hi)],
            'sign':sign,'changed_edge_packets':changed,'unchanged_edges_cancelled':cancelled,
            'midpoint_competitor':list(map(str,T)),'all_global_gap_constraints_preserved':True})
    assert len(rows)==8 and [row['swap'] for row in rows]==[[r,r+1] for r in range(8)]
    final={p.relative_to(ROOT).as_posix():sha(p) for p in paths};assert final==pins
    out={'scope':__doc__,'status':'fixed_complete_adjacent_swap_family_midpoint_differences_computed',
        'source_sha256_start':pins,'source_sha256_end':final,'all_sources_unchanged':True,'path':model['path'],
        'parent_midpoint':list(map(str,g)),'fixed_maps':8,'rows':rows,'unique_scalar_arguments_evaluated':evaluations,
        'new_actual_scalar_tables':0,'actual_Taylor_enclosures_remain_analytic_inputs':True,
        'necessary_conditions':'For every actual global minimizer in the original SEP orthant, ALL eight F(T_r g)-F(g)>=0 simultaneously.',
        'negative_midpoint_maps':[row['swap'] for row in rows if row['sign']=='negative'],
        'optimizer_calls':0,'new_moment_model_built':False,'Lean_invocations':0,'exact_714_point_excluded':False,
        'cell_exclusion_proven':False,'new_zero_proportion_proven':False,'elapsed_milliseconds':int((time.monotonic()-began)*1000)}
    OUT.write_text(json.dumps(out,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({'status':out['status'],'rows':[[row['swap'],row['sign'],[float(F(v)) for v in row['difference_interval']]] for row in rows],
        'unique_scalar_arguments':evaluations,'elapsed_milliseconds':out['elapsed_milliseconds']}),flush=True)
if __name__=='__main__':
    if not __debug__:raise RuntimeError('Assertions must remain enabled')
    main()
