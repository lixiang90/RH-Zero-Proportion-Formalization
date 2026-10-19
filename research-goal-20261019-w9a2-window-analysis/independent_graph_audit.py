"""Independent 7-leaf audit: Bellman-Ford, Kahn order, exact arithmetic.
No imported producer code; no LP, kernel evaluation, Lean, or graph expansion.
The existing 24-leaf result is checked only on its published cycle witnesses.
"""
from pathlib import Path
from fractions import Fraction as F
from decimal import Decimal, localcontext
import ast, collections, gzip, hashlib, json, re

ROOT = Path(__file__).resolve().parents[1]
PROD = ROOT/'research-goal-20261019-w9a2-certificate-analysis'
SOURCE = ROOT/'research-goal-20261019-w9a2-record/official/proof/Solution.lean'

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def rat(x):
    with localcontext() as c:
        c.prec=60
        return {'fraction':str(x),'decimal':str(Decimal(x.numerator)/Decimal(x.denominator))}

src=SOURCE.read_text(encoding='utf-8')
cert=src.split('namespace AMW.Cert.PC9QB6M',1)[1]
pr=ast.literal_eval(re.search(r'def PR : List \(ℕ × ℕ\) := (\[[^\n]+\])',cert)[1])
assert pr==[(i,j) for i in range(9) for j in range(i+2,9)]
bs=ast.literal_eval(re.search(r'def BS : List ℕ := (\[[^\n]+\])',cert)[1])
smax=ast.literal_eval(re.search(r'def SMAX[^\n]*:= (\[[^\n]+?\])\.getD',cert)[1])
span_order=[(i,i+1) for i in range(8)]+pr
leaves=[json.loads(s) for s in gzip.open(PROD/'numeric-leaves-sorted.jsonl.gz','rt',encoding='utf-8')]
baseline=json.loads((PROD/'baseline-replay.json').read_text(encoding='utf-8'))
geometry=json.loads((PROD/'geometry-audit.json').read_text(encoding='utf-8'))
first=geometry['graphs']['7']
assert len(leaves)==11794 and geometry['first24']==leaves[:24]
assert all(leaves[i]['margin']<=leaves[i+1]['margin'] for i in range(len(leaves)-1))
assert baseline['source_sha256']==sha(SOURCE)==geometry['source_sha256']
assert baseline['CN']==893029029923108825 and baseline['SA']==10**20
for row in leaves[:24]:
    assert len(row['state'])==73 and row['state'][-1]==0
    assert row['state'][:16:2]==row['lo'] and row['state'][1:16:2]==row['hi']

def physical_intervals(row, flip, start):
    out={}
    for k,(i,j) in enumerate(span_order):
        a,b=(8-j,8-i) if flip else (i,j)
        out[a+start,b+start]=(row['state'][2*k],row['state'][2*k+1])
    assert len(out)==36
    return out

def constraints(row1,row2,flip1,flip2):
    a=physical_intervals(row1,flip1,0)
    b=physical_intervals(row2,flip2,1)
    edges=[]
    for label,box in [('prefix',a),('suffix',b)]:
        for (i,j),(lo,hi) in sorted(box.items()):
            assert 0<=lo<=hi
            edges += [(i,j,hi,label,'upper'),(j,i,-lo,label,'lower')]
    assert len(edges)==144
    conflict=None
    for span in sorted(set(a)&set(b)):
        l,u=a[span];v,w=b[span]
        if u<v or w<l:
            # This is itself a two-edge strictly negative difference cycle.
            conflict={'span':span,'prefix':a[span],'suffix':b[span],
                      'negative_cycle_sum':min(u-v,w-l)}
            break
    return edges, conflict

def bellman_ford(edges):
    # Implicit super-source gives all 10 vertices initial distance zero.
    d=[0]*10
    for step in range(10):
        changed=False
        for i,j,w,*_ in edges:
            if d[j]>d[i]+w:
                d[j]=d[i]+w;changed=True
        if not changed:
            x=[v-d[0] for v in d]
            assert all(x[j]-x[i]<=w for i,j,w,*_ in edges)
            return True,x
    return False,None

published={(2*r['prefix_rank']+int(r['prefix_reversed']),2*r['suffix_rank']+int(r['suffix_reversed'])):r
           for r in first['rows']}
assert len(published)==196
rows=[];adj={v:set() for v in range(14)}
for u in range(14):
    for v in range(14):
        edges,conflict=constraints(leaves[u//2],leaves[v//2],bool(u%2),bool(v%2))
        feasible,witness=bellman_ford(edges)
        assert feasible==published[u,v]['DBM_feasible']
        assert feasible == (conflict is None)  # specific to these 196 boxes
        if feasible: adj[u].add(v)
        rows.append({'source':u,'target':v,'feasible':feasible,
                     'feasible_integer_positions':witness,'direct_exclusion':conflict})

# Kahn's algorithm, independent of the producer's DFS order.
indegree={v:0 for v in adj}
for u in adj:
    for v in adj[u]:indegree[v]+=1
queue=collections.deque(v for v in sorted(adj) if not indegree[v]);order=[]
while queue:
    u=queue.popleft();order.append(u)
    for v in sorted(adj[u]):
        indegree[v]-=1
        if not indegree[v]:queue.append(v)
assert len(order)==14
dist={v:1 for v in adj};parent={}
for u in order:
    for v in sorted(adj[u]):
        if dist[v]<dist[u]+1:dist[v]=dist[u]+1;parent[v]=u
end=max(dist,key=dist.get);path=[end]
while end in parent:end=parent[end];path.append(end)
path.reverse()
assert max(dist.values())==4 and path==[9,4,5,8]
edges7=sorted((u,v) for u in adj for v in adj[u])
assert edges7==[tuple(e) for e in geometry['graphs']['7']['retained_edges']]

CN=baseline['CN'];SA=baseline['SA'];slope=baseline['SLOPE'];SC=32768
assert slope==335544320000000000
q=leaves[7]['margin']//slope
assert q==121390593524
assert all(row['margin']>=slope*q for row in leaves[7:])
assert all(row['margin']<slope*q for row in leaves[:7])
c=F(CN,SA);tau=c+F(q,SA);average=c+F(q,5*SA)
H=F(6721237468782417141365717707344332375586,10**40)
B=F(sum(bs),SA);kappa=(H-B)/(1-c);candidate=(H-B)/(1-average)
gate=geometry['proposed_gate']
assert F(gate['proposed_average_floor_exact'])==average
assert F(gate['proposed_ratio_if_full_coverage_formalized'])==candidate
assert F(gate['proposed_proportion_gain_if_formalized'])==candidate-kappa

# Exterior arithmetic on the separated domain g_r >= 17/20.
# True-WZ uses only one nonlinear term to pay CN, so ALL pressure remains.
# A tail uses only beta_r*g_r to pay CN, so every other pressure term remains.
sep=F(17,20)
tail=[]
for r in range(8):
    own=F(bs[r]*smax[r],SC)
    assert own>=CN
    uplift=sep*F(sum(bs)-bs[r],SA)
    assert uplift>F(q,SA)
    tail.append({'gap':r,'tail_baseline_payment_unscaled':rat(own),
                 'other_pressure_uplift':rat(uplift)})
true_wz_uplift=sep*B
assert true_wz_uplift>F(q,SA)

# No new 24-leaf graph search: check the already published cycle's 5 witnesses.
g24=geometry['graphs']['24'];cycle=g24['cycle']
lookup24={(2*r['prefix_rank']+int(r['prefix_reversed']),2*r['suffix_rank']+int(r['suffix_reversed'])):r for r in g24['rows']}
cycle_witnesses=[]
assert cycle==[10,14,11,19,18,10]
for u,v in zip(cycle,cycle[1:]):
    row=lookup24[u,v];x=row['feasible_witness_10_integer_positions']
    es,_=constraints(leaves[u//2],leaves[v//2],bool(u%2),bool(v%2))
    assert row['DBM_feasible'] and len(x)==10 and x[0]==0
    assert all(x[j]-x[i]<=w for i,j,w,*_ in es)
    cycle_witnesses.append({'source':u,'target':v,'witness':x,'all_144_constraints_checked':True})

out={'scope':'Independent exact audit of first 7 leaf geometry with Bellman-Ford (196 cases), Kahn DAG analysis, rational average bound and exterior pressure arithmetic. No LP/Lean/kernel calculation. Existing 24-leaf graph checked only on its five cycle witnesses.',
     'passed':True,'input_sha256':{str(p.relative_to(ROOT)).replace('\\','/'):sha(p) for p in [SOURCE,PROD/'numeric-leaves-sorted.jsonl.gz',PROD/'baseline-replay.json',PROD/'geometry-audit.json']},
     'physical_scale':SC,'first7_pair_orientation_checks':len(rows),'excluded':sum(not r['feasible'] for r in rows),
     'retained_edges':edges7,'topological_order':order,'rank':dist,'longest_bad_run_vertices':4,'longest_path':path,'rows':rows,
     'average_candidate':{'q':q,'tau':rat(tau),'delta_good':rat(F(q,SA)),'average_floor':rat(average),
        'finite_sum_statement':'sum_i F_i >= N*(c0+q/(5*SA))-4*q/(5*SA), provided global separated localization of low windows into the seven reflected cells is formalized.',
        'candidate_K_if_formalized':rat(candidate),'gain_proportion_if_formalized':rat(candidate-kappa),'gain_percentage_points_if_formalized':rat(100*(candidate-kappa)),
        'new_unconditional_record_proven':False,'new_Lean_theorem':False},
     'exterior_separated_paper_lemma':{'separation':str(sep),'source_coverChk_sound_lines':'9397-9435',
        'true_WZ_extra_pressure':rat(true_wz_uplift),'tail_cases':tail,
        'minimum_tail_extra_pressure':rat(min(sep*F(sum(bs)-b,SA) for b in bs)),
        'small_gap_case':'g<=1/2 is impossible when g>=17/20.',
        'scope':'Exact arithmetic and paper consequence of existing coverChk_sound and pressure nonnegativity. true-WZ tables retain official Lean soundness dependency; no new global localization Lean proof or new-kernel replay performed.'},
     'existing24cycle_audit':{'cycle':cycle,'witnesses':cycle_witnesses,'meaning':'Only a cycle in the pairwise outer box graph. The independent ten-point witnesses do not prove a single periodic physical sequence or low-energy counterexample.'}}
dest=Path(__file__).with_name('independent-graph-audit.json')
dest.write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:out[k] for k in ['passed','first7_pair_orientation_checks','excluded','retained_edges','longest_path','average_candidate']},ensure_ascii=False,indent=2))
