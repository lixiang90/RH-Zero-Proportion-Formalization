"""One fixed period9 necessary gate for a W24/W10 overlap potential.

Use precisely the old hard-parent normalized gap center, with no adjustment,
repeat it periodically and enclose all nine cyclic9-gap window energies.
Reuse the frozen normalized-W integer Taylor23 table and order24 bound.
No new tables, search, LP, potential fit, optimizer, sampling sweep or Lean.
Default read-only; --write-receipt creates an absent receipt once.
"""
from pathlib import Path
from fractions import Fraction as F
from math import factorial
import argparse, gzip, hashlib, json, time
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent;OUT=HERE/'period9-receipt.json'
MODEL=ROOT/'research-goal-20261017-quartic/quartic-model.json.gz'
PARAMS=ROOT/'research-20261016-followup/window_reweight_rational.json'
TABLE=ROOT/'research-goal-20261016/window_normalized_interval.json'
MODEL_SHA='080f60fe1a3392e12a37219be13cbd6d9ae305651acebfe01fa1920a74e11233'
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--write-receipt',action='store_true');args=ap.parse_args()
    if args.write_receipt:assert not OUT.exists()
    began=time.monotonic();paths=[Path(__file__),MODEL,PARAMS,TABLE,ROOT/'research-goal-20261016/window_normalized_interval.py',
        ROOT/'research-goal-20261017-swap67-audit/table-identity.json',ROOT/'StructuralResearch20261016/Coboundary.lean']
    pins={p.relative_to(ROOT).as_posix():digest(p)for p in paths};assert digest(MODEL)==MODEL_SHA
    model=json.loads(gzip.decompress(MODEL.read_bytes()));params=json.loads(PARAMS.read_bytes());table=json.loads(TABLE.read_bytes())
    assert model['path']=='r001000001000100110011001'and table['parameter_sha256']==digest(PARAMS)
    assert table['source_sha256']==digest(ROOT/'research-goal-20261016/window_normalized_interval.py')
    center=list(map(F,model['normalized_gap_center']));state=model['cell'];SC=32768;sep=F(123,128)
    assert len(center)==9 and all(center[i]==F(state[0][i]+state[1][i],2*SC)for i in range(9))and min(center)>=sep
    den=params['denominator'];b=[F(v,den)for v in params['b_numerators']]
    edges=[(i,j,F(v,den))for i,j,v in params['a_upper']if v];assert len(edges)==41 and all(v>0 for _,_,v in edges)
    w={int(n):[tuple(map(F,p))for p in row]for n,row in table['integer_w_Taylor_coefficients'].items()}
    assert set(w)==set(range(33))and all(len(v)==24 for v in w.values());M24=F(44,7)**24;cache={}
    def scalar(x):
        if x not in cache:
            n=round(x);d=x-n;assert 0<=n<=32 and abs(d)<=F(1,2)
            lo=hi=F(0)
            for k in range(24):
                a,c=w[n][k];v=d**k;lo+=min(a*v,c*v);hi+=max(a*v,c*v)
            rem=M24*abs(d)**24/factorial(24);lo-=rem;hi+=rem
            cache[x]={'x':str(x),'integer_center':n,'delta':str(d),'remainder':str(rem),'interval':[str(lo),str(hi)]}
        return tuple(map(F,cache[x]['interval']))
    windows=[];total_lo=total_hi=F(0)
    for shift in range(9):
        gaps=center[shift:]+center[:shift];pressure=sum((b[i]*gaps[i]for i in range(9)),F(0));lo=hi=pressure;terms=[]
        for i,j,a in edges:
            x=sum(gaps[i:j],F(0));l,u=scalar(x);lo+=a*l;hi+=a*u
            terms.append({'edge':[i,j],'weight':str(a),'span':str(x),'weighted_interval':[str(a*l),str(a*u)]})
        windows.append({'shift':shift,'gaps':list(map(str,gaps)),'pressure':str(pressure),'terms':terms,'energy_interval':[str(lo),str(hi)]})
        total_lo+=lo;total_hi+=hi
    average=(total_lo/9,total_hi/9)
    # Independently sum by rank length. Each ledger edge of length l sees
    # every cyclic l-span exactly once across the nine shifts.
    grouped_lo=grouped_hi=sum(b,F(0))*sum(center,F(0))/9
    for length in range(1,10):
        mass=sum((a for i,j,a in edges if j-i==length),F(0))
        for shift in range(9):
            x=sum((center[(shift+r)%9]for r in range(length)),F(0));l,u=scalar(x)
            grouped_lo+=mass*l/9;grouped_hi+=mass*u/9
    assert average==(grouped_lo,grouped_hi)
    comparisons=[]
    for c in [F(221,25000),F(11,1250)]:
        comparisons.append({'target':str(c),'average_lower_above_target':average[0]>c,'average_upper_below_target':average[1]<c,
            'interval_minus_target':[str(average[0]-c),str(average[1]-c)]})
    for path in paths:assert digest(path)==pins[path.relative_to(ROOT).as_posix()]
    out={'scope':__doc__,'arithmetic_checks_passed':True,'source_sha256_start':pins,'source_sha256_end':pins,'all_sources_unchanged':True,
        'path':model['path'],'period':9,'gap_cycle':list(map(str,center)),'separation':str(sep),'cycle_is_orthant_feasible':True,
        'center_claimed_to_satisfy_all_parent_DBM_constraints':False,'window_points':10,'gap_variables_per_window':9,'potential_state_gaps':8,
        'windows':windows,'mean_energy_interval':list(map(str,average)),'rank_length_aggregate_exactly_matches':True,
        'positive_edges_per_window':41,'scalar_calls':369,'unique_scalar_queries':len(cache),'scalar_enclosures':list(cache.values()),
        'normalized_W_Taylor_degree':23,'global_w24_bound':str(M24),'comparisons':comparisons,
        'necessary_coboundary_statement':'If every orthant9-gap g satisfies F(g)+V(head8 g)-V(tail8 g)>=c, summing this exact period9 cycle gives c<=meanF.',
        'periodic_endpoint_potential_difference':'0 exactly; head8 of the next window equals tail8 of the current window, modulo9',
        'interpretation':'A high lower endpoint only means this particular fixed cycle does not refute either target; it proves no global mean floor.',
        'new_actual_tables_generated':0,'producer_imports':0,'optimizer_calls':0,'LP_calls':0,'new_Lean_invocations':0,
        'actual_scalar_obligations_newly_Lean_proved_here':False,'global_mean_floor_proven':False,'cell_exclusion_proven':False,'new_zero_proportion_proven':False,
        'seconds':time.monotonic()-began}
    if args.write_receipt:OUT.write_text(json.dumps(out,indent=2,allow_nan=False)+'\n',encoding='utf8')
    elif OUT.exists():
        saved=json.loads(OUT.read_bytes());assert {k:v for k,v in saved.items()if k!='seconds'}=={k:v for k,v in out.items()if k!='seconds'}
    print(json.dumps({'passed':True,'mean_interval_hint':list(map(float,average)),'targets':comparisons,'unique_scalar_queries':len(cache),
        'receipt_sha256':digest(OUT)if OUT.exists()else None,'seconds':out['seconds']}),flush=True)
if __name__=='__main__':
    assert __debug__
    main()
