"""Bounded deterministic closed-DBM adjacency checks of the first 7/24 leaves.
No solver, kernel sampling, finite certificate regeneration or Lean run.
Graphs are outer feasible graphs: a negative DBM cycle certifies exclusion;
a retained edge is only box feasibility, not actual energy attainability.
"""
from pathlib import Path
from fractions import Fraction
from hashlib import sha256
import json,gzip,itertools,time
HERE=Path(__file__).resolve().parent
PR=[(i,j) for i in range(9) for j in range(i+2,9)]
ALL=[(i,i+1) for i in range(8)]+PR
LOOK={x:i for i,x in enumerate(ALL)}
def bounds(s,i,j,rev):
    if rev:i,j=8-j,8-i
    k=LOOK[i,j];return s['state'][2*k],s['state'][2*k+1]
def joint(x,y,rx,ry):
    contradictions=[]
    for i in range(1,9):
        for j in range(i+1,9):
            l,u=bounds(x,i,j,rx);v,w=bounds(y,i-1,j-1,ry)
            if u<v or w<l:contradictions.append({'shared_span':[i,j],'prefix':[l,u],'suffix':[v,w]})
    d=[[10**30]*10 for _ in range(10)]
    for i in range(10):d[i][i]=0
    for shift,s,rev in [(0,x,rx),(1,y,ry)]:
        for i,j in ALL:
            l,u=bounds(s,i,j,rev);i+=shift;j+=shift
            d[i][j]=min(d[i][j],u);d[j][i]=min(d[j][i],-l)
    for k in range(10):
        for i in range(10):
            for j in range(10):d[i][j]=min(d[i][j],d[i][k]+d[k][j])
    feasible=all(d[i][i]>=0 for i in range(10))
    witness=None
    if feasible:
        witness=d[0]
        assert witness[0]==0
        for shift,s,rev in [(0,x,rx),(1,y,ry)]:
            for i,j in ALL:
                l,u=bounds(s,i,j,rev)
                assert l<=witness[j+shift]-witness[i+shift]<=u
    return {'prefix_reversed':rx,'suffix_reversed':ry,'literal_contradictions':contradictions,'DBM_feasible':feasible,'feasible_witness_10_integer_positions':witness,'negative_diagonal':[d[i][i] for i in range(10) if d[i][i]<0]}
def graph_check(leaves,n):
    rows=[];adj={i:[] for i in range(2*n)}
    for i,j in itertools.product(range(n),repeat=2):
        for rx,ry in itertools.product([False,True],repeat=2):
            r={'prefix_rank':i,'suffix_rank':j,**joint(leaves[i],leaves[j],rx,ry)};rows.append(r)
            if r['DBM_feasible']:adj[2*i+rx].append(2*j+ry)
    colour=[0]*(2*n);path=[];cycle=None;order=[]
    def visit(v):
        nonlocal cycle
        colour[v]=1;path.append(v)
        for w in adj[v]:
            if colour[w]==0:visit(w)
            elif colour[w]==1 and cycle is None:cycle=path[path.index(w):]+[w]
        path.pop();colour[v]=2;order.append(v)
    for v in adj:
        if colour[v]==0:visit(v)
    dist=None;maxpath=None
    if cycle is None:
        dist={v:1 for v in adj};parent={}
        for v in reversed(order):
            for w in adj[v]:
                if dist[w]<dist[v]+1:dist[w]=dist[v]+1;parent[w]=v
        v=max(dist,key=dist.get);maxpath=[v]
        while v in parent:v=parent[v];maxpath.append(v)
        maxpath.reverse()
    return {'n':n,'vertex_encoding':'2*zero_based_leaf_rank + bool(reversed)',
      'pair_orientation_checks':len(rows),'literal_excluded':sum(bool(x['literal_contradictions']) for x in rows),
      'DBM_excluded':sum(not x['DBM_feasible'] for x in rows),'retained_edges':[(u,v) for u in adj for v in adj[u]],
      'acyclic':cycle is None,'cycle':cycle,'topological_order':list(reversed(order)) if cycle is None else None,
      'longest_vertex_count':max(dist.values()) if dist else None,'longest_path':maxpath,'ranks':dist,'rows':rows}
def main():
    t=time.monotonic();leaves=[json.loads(x) for x in gzip.open(HERE/'numeric-leaves-sorted.jsonl.gz','rt')]
    groups={n:graph_check(leaves,n) for n in [7,24]}
    quantiles=[]
    for d in ['1e-8','1e-7','1e-6','1e-5','2e-5']:
        debit=335544320000000000*10**20*Fraction(d)
        quantiles.append({'floor_increment':d,'integer_debit':str(debit),'exception_count':sum(x['margin']<debit for x in leaves)})
    debit_raise=leaves[7]['margin']//335544320000000000
    original_cn=893029029923108825;sa=10**20
    base_kappa=Fraction(3337881639516708570682858853672166187793,4955348548503844558750000000000000000000)
    graph_floor=Fraction(original_cn,sa)+Fraction(debit_raise,5*sa)
    composed=base_kappa*(1-Fraction(original_cn,sa))/(1-graph_floor)
    out={'scope':'Original source integer margins and closed DBM geometry only; no new unconditional record or Lean theorem claimed.',
      'source_sha256':'241068ee5abab772ea1aba7533ec33b9140df7dc1728aeb4c61bfb648fe195c7',
      'numeric_leaves_input_sha256':sha256((HERE/'numeric-leaves-sorted.jsonl.gz').read_bytes()).hexdigest(),
      'quantiles':quantiles,'first24':leaves[:24],
      'proposed_gate':{'exception_count':7,'threshold_CN':original_cn+debit_raise,'threshold_raise_CN':debit_raise,
         'source_first_good_leaf_rank_zero_based':7,'debit':335544320000000000*debit_raise,
         'source_first_good_leaf_margin':leaves[7]['margin'],'first_good_residual':leaves[7]['margin']-335544320000000000*debit_raise,
         'tau_exact':str(Fraction(original_cn+debit_raise,sa)),'source_floor_exact':str(Fraction(original_cn,sa)),
         'maximum_bad_run_vertices':4,'every_block_of_windows':5,'proposed_average_floor_exact':str(graph_floor),
         'proposed_ratio_if_full_coverage_formalized':str(composed),'proposed_proportion_gain_if_formalized':str(composed-base_kappa),
         'proposed_percentage_point_gain_decimal':float(100*(composed-base_kappa)),
         'open_gate':'Need upgraded exterior true-WZ/tail/small guards, all analytic floor localization/reflection, bad-state exclusion and all sliding-window counting in Lean; graph alone does not prove the full floor.'},'graphs':groups,'seconds':time.monotonic()-t}
    (HERE/'geometry-audit.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'seconds':out['seconds'],'quantiles':quantiles,'graphs':{n:{k:v for k,v in g.items() if k not in ['rows','ranks']} for n,g in groups.items()}}))
if __name__=='__main__':main()
