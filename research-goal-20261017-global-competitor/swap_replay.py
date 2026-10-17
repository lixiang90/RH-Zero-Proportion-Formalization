"""Read-only stdlib replay of the single fixed swap midpoint comparison.

Evaluate existing coefficient intervals by direct powers, independent of
the producer's interval Horner.  No map selection, optimizer, new scalar
table, quartic difference model or actual minimizer claim.
"""
from pathlib import Path
from fractions import Fraction as F
from math import factorial
import argparse,gzip,hashlib,json,time
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent;OUT=HERE/'swap-replay.json'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    parser=argparse.ArgumentParser();parser.add_argument('--write-receipt',action='store_true');args=parser.parse_args();began=time.monotonic()
    if args.write_receipt:assert not OUT.exists()
    paths=[Path(__file__),HERE/'swap-midpoint-static.json'];record=json.loads(paths[1].read_bytes());assert record['source_sha256_start']==record['source_sha256_end']
    for relative,h in record['source_sha256_start'].items():
        p=ROOT/relative;assert sha(p)==h
        if p not in paths:paths.append(p)
    pins={p.relative_to(ROOT).as_posix():sha(p) for p in paths}
    model=json.loads(gzip.decompress((ROOT/'research-goal-20261017-quartic/quartic-model.json.gz').read_bytes()))
    params=json.loads((ROOT/'research-20261016-followup/window_reweight_rational.json').read_bytes())
    table=json.loads((ROOT/'research-goal-20261016/window_normalized_interval.json').read_bytes())['integer_w_Taylor_coefficients']
    g=[F(l+u,65536) for l,u in zip(model['cell'][0][:9],model['cell'][1][:9])];assert list(map(str,g))==record['parent_midpoint']
    Tg=g.copy();Tg[5],Tg[6]=g[6],g[5];assert list(map(str,Tg))==record['midpoint_competitor'] and min(Tg)>F(123,128)
    def interval(x):
        n=round(x);d=x-n;assert abs(d)<=F(1,2);lo=hi=F(0)
        for j,(l,u) in enumerate(table[str(n)]):
            a,b=F(l)*d**j,F(u)*d**j;lo+=min(a,b);hi+=max(a,b)
        error=F(44,7)**24*abs(d)**24/factorial(24)
        return lo-error,hi+error,n,str(error)
    pressure=F(params['b_numerators'][5]-params['b_numerators'][6],params['denominator'])*(g[6]-g[5]);assert str(pressure)==record['pressure_difference']
    lower=upper=pressure;changed=[];cancelled=[]
    packets={tuple(p['edge']):p for p in record['changed_edge_packets']}
    for i,j,a in params['a_upper']:
        if not a:continue
        old,new=sum(g[i:j]),sum(Tg[i:j])
        if i!=6 and j!=6:assert old==new;cancelled.append([i,j]);continue
        p=packets[i,j];l=interval(old);u=interval(new);weight=F(a,params['denominator'])
        assert list(map(str,l[:2]))==p['old_w_interval'] and list(map(str,u[:2]))==p['new_w_interval']
        assert l[2]==p['old_integer_Taylor_anchor'] and u[2]==p['new_integer_Taylor_anchor']
        assert l[3]==p['old_M24_remainder'] and u[3]==p['new_M24_remainder']
        dl=weight*(u[0]-l[1]);du=weight*(u[1]-l[0]);assert [str(dl),str(du)]==p['weighted_difference_interval']
        lower+=dl;upper+=du;changed.append([i,j])
    assert cancelled==record['unchanged_edges_cancelled'] and len(changed)==9 and len(cancelled)==32
    assert [str(lower),str(upper)]==record['difference_interval'] and lower>0 and record['status']=='fixed_swap_midpoint_strictly_increases_F_stop'
    final={p.relative_to(ROOT).as_posix():sha(p) for p in paths};assert final==pins
    out={'scope':__doc__,'status':'single_fixed_swap_midpoint_increase_independently_verified',
        'source_sha256_start':pins,'source_sha256_end':final,'all_sources_unchanged':True,'changed_edges_checked':9,'cancelled_edges_checked':32,
        'difference_interval':[str(lower),str(upper)],'actual_Taylor_enclosures_remain_analytic_inputs':True,
        'optimizer_calls':0,'new_maps_tested':0,'new_moment_model_built':False,'Lean_invocations':0,
        'exact_714_pseudomoment_excluded':False,'cell_exclusion_proven':False,'new_zero_proportion_proven':False,
        'elapsed_milliseconds':int((time.monotonic()-began)*1000)}
    if args.write_receipt:OUT.write_text(json.dumps(out,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({k:out[k] for k in ['status','changed_edges_checked','cancelled_edges_checked','elapsed_milliseconds']}))
if __name__=='__main__':main()
