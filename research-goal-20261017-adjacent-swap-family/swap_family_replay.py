"""Read-only stdlib direct-power replay of all eight fixed midpoint swaps."""
from pathlib import Path
from fractions import Fraction as F
from math import factorial
import argparse,gzip,hashlib,json,time
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent;OUT=HERE/'swap-family-replay.json'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    parser=argparse.ArgumentParser();parser.add_argument('--write-receipt',action='store_true');args=parser.parse_args();began=time.monotonic()
    if args.write_receipt:assert not OUT.exists()
    paths=[Path(__file__),HERE/'swap-family-static.json'];record=json.loads(paths[1].read_bytes());assert record['source_sha256_start']==record['source_sha256_end']
    for relative,h in record['source_sha256_start'].items():
        p=ROOT/relative;assert sha(p)==h
        if p not in paths:paths.append(p)
    pins={p.relative_to(ROOT).as_posix():sha(p) for p in paths};model=json.loads(gzip.decompress((ROOT/'research-goal-20261017-quartic/quartic-model.json.gz').read_bytes()))
    table=json.loads((ROOT/'research-goal-20261016/window_normalized_interval.json').read_bytes())['integer_w_Taylor_coefficients'];params=json.loads((ROOT/'research-20261016-followup/window_reweight_rational.json').read_bytes())
    g=[F(l+u,65536) for l,u in zip(model['cell'][0][:9],model['cell'][1][:9])];assert list(map(str,g))==record['parent_midpoint'];cache={}
    def value(x):
        if x not in cache:
            n=round(x);d=x-n;lo=hi=F(0)
            for j,(l,u) in enumerate(table[str(n)]):
                v,w=F(l)*d**j,F(u)*d**j;lo+=min(v,w);hi+=max(v,w)
            e=F(44,7)**24*abs(d)**24/factorial(24);cache[x]=(lo-e,hi+e,n,str(e))
        return cache[x]
    assert [row['swap'] for row in record['rows']]==[[r,r+1] for r in range(8)];negative=[];changedtotal=0
    for r,row in enumerate(record['rows']):
        T=g.copy();T[r],T[r+1]=g[r+1],g[r];assert min(T)>F(123,128) and list(map(str,T))==row['midpoint_competitor']
        pressure=F(params['b_numerators'][r]-params['b_numerators'][r+1],params['denominator'])*(g[r+1]-g[r]);assert str(pressure)==row['pressure_difference']
        lo=hi=pressure;packets={tuple(p['edge']):p for p in row['changed_edge_packets']};cancel=[]
        for i,j,a in params['a_upper']:
            if not a:continue
            x,y=sum(g[i:j]),sum(T[i:j])
            if i!=r+1 and j!=r+1:assert x==y;cancel.append([i,j]);continue
            p=packets[i,j];old,new=value(x),value(y)
            assert list(map(str,old[:2]))==p['old_w_interval'] and list(map(str,new[:2]))==p['new_w_interval']
            assert old[2:]==(p['old_integer_anchor'],p['old_remainder']) and new[2:]==(p['new_integer_anchor'],p['new_remainder'])
            weight=F(a,params['denominator']);dl=weight*(new[0]-old[1]);du=weight*(new[1]-old[0]);assert list(map(str,[dl,du]))==p['weighted_difference_interval']
            lo+=dl;hi+=du;changedtotal+=1
        assert cancel==row['unchanged_edges_cancelled'] and [str(lo),str(hi)]==row['difference_interval']
        sign='negative' if hi<0 else 'positive' if lo>0 else 'inconclusive';assert sign==row['sign']
        if sign=='negative':negative.append([r,r+1])
    assert negative==record['negative_midpoint_maps'] and len(cache)==record['unique_scalar_arguments_evaluated']==87
    final={p.relative_to(ROOT).as_posix():sha(p) for p in paths};assert final==pins
    out={'scope':__doc__,'status':'all_eight_fixed_adjacent_swap_midpoint_differences_independently_verified',
        'source_sha256_start':pins,'source_sha256_end':final,'all_sources_unchanged':True,'fixed_maps':8,
        'negative_maps':negative,'unique_scalar_arguments_checked':87,'changed_edge_packets_checked':changedtotal,
        'new_moment_model_built':False,'optimizer_calls':0,'Lean_invocations':0,'exact_714_point_excluded':False,
        'cell_exclusion_proven':False,'new_zero_proportion_proven':False,'elapsed_milliseconds':int((time.monotonic()-began)*1000)}
    if args.write_receipt:OUT.write_text(json.dumps(out,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({k:out[k] for k in ['status','fixed_maps','negative_maps','elapsed_milliseconds']}))
if __name__=='__main__':main()
